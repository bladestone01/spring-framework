/*
 * Copyright 2002-2022 the original author or authors.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      https://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package org.springframework.http.server.reactive;

import java.io.IOException;
import java.io.OutputStream;
import java.lang.reflect.Method;
import java.net.URISyntaxException;
import java.nio.ByteBuffer;
import java.nio.charset.Charset;

import jakarta.servlet.AsyncContext;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletRequestWrapper;
import jakarta.servlet.http.HttpServletResponse;
import jakarta.servlet.http.HttpServletResponseWrapper;
import org.eclipse.jetty.http.HttpFields;
import org.eclipse.jetty.server.HttpOutput;
import org.eclipse.jetty.server.Request;
import org.eclipse.jetty.server.Response;

import org.springframework.core.io.buffer.DataBuffer;
import org.springframework.core.io.buffer.DataBufferFactory;
import org.springframework.http.HttpHeaders;
import org.springframework.http.MediaType;
import org.springframework.lang.Nullable;
import org.springframework.util.Assert;
import org.springframework.util.ClassUtils;
import org.springframework.util.MultiValueMap;
import org.springframework.util.ReflectionUtils;

/**
 * {@link ServletHttpHandlerAdapter} extension that uses Jetty APIs for writing
 * to the response with {@link ByteBuffer}.
 *
 * @author Violeta Georgieva
 * @author Brian Clozel
 * @since 5.0
 * @see org.springframework.web.server.adapter.AbstractReactiveWebInitializer
 */
public class JettyHttpHandlerAdapter extends ServletHttpHandlerAdapter {

	private static final boolean jetty11Present = ClassUtils.isPresent(
			"org.eclipse.jetty.server.HttpOutput", JettyHttpHandlerAdapter.class.getClassLoader());

	/* Jetty 12: see spring-web.gradle
	private static final boolean jetty12Present = ClassUtils.isPresent(
			"org.eclipse.jetty.ee10.servlet.HttpOutput", JettyHttpHandlerAdapter.class.getClassLoader());
	*/

	@Nullable
	private static final Method getRequestHeadersMethod =
			ClassUtils.getMethodIfAvailable(Request.class, "getHeaders");

	@Nullable
	private static final Method getResponseHeadersMethod =
			ClassUtils.getMethodIfAvailable(Response.class, "getHeaders");


	public JettyHttpHandlerAdapter(HttpHandler httpHandler) {
		super(httpHandler);
	}


	@Override
	protected ServletServerHttpRequest createRequest(HttpServletRequest request, AsyncContext context)
			throws IOException, URISyntaxException {

		Assert.state(getServletPath() != null, "Servlet path is not initialized");
		return new JettyServerHttpRequest(
				request, context, getServletPath(), getDataBufferFactory(), getBufferSize());
	}

	@Override
	protected ServletServerHttpResponse createResponse(HttpServletResponse response,
			AsyncContext context, ServletServerHttpRequest request) throws IOException {

		return new JettyServerHttpResponse(
				response, context, getDataBufferFactory(), getBufferSize(), request);
	}


	private static final class JettyServerHttpRequest extends ServletServerHttpRequest {

		JettyServerHttpRequest(HttpServletRequest request, AsyncContext asyncContext,
				String servletPath, DataBufferFactory bufferFactory, int bufferSize)
				throws IOException, URISyntaxException {

			super(createHeaders(request), request, asyncContext, servletPath, bufferFactory, bufferSize);
		}

		private static MultiValueMap<String, String> createHeaders(HttpServletRequest servletRequest) {
			Request request = getRequest(servletRequest);
			HttpFields fields;
			if (getRequestHeadersMethod != null) {
				fields = (HttpFields) ReflectionUtils.invokeMethod(getRequestHeadersMethod, request);
			}
			else {
				fields = request.getHttpFields();
			}
			return new JettyHeadersAdapter(fields);
		}

		private static Request getRequest(HttpServletRequest request) {
			if (request instanceof Request jettyRequest) {
				return jettyRequest;
			}
			else if (request instanceof HttpServletRequestWrapper wrapper) {
				HttpServletRequest wrappedRequest = (HttpServletRequest) wrapper.getRequest();
				return getRequest(wrappedRequest);
			}
			else {
				throw new IllegalArgumentException("Cannot convert [" + request.getClass() +
						"] to org.eclipse.jetty.server.Request");
			}
		}
	}


	private static final class JettyServerHttpResponse extends ServletServerHttpResponse {

		JettyServerHttpResponse(HttpServletResponse response, AsyncContext asyncContext,
				DataBufferFactory bufferFactory, int bufferSize, ServletServerHttpRequest request)
				throws IOException {

			super(createHeaders(response), response, asyncContext, bufferFactory, bufferSize, request);
		}

		private static HttpHeaders createHeaders(HttpServletResponse servletResponse) {
			Response response = getResponse(servletResponse);
			HttpFields fields;
			if (getResponseHeadersMethod != null) {
				fields = (HttpFields) ReflectionUtils.invokeMethod(getResponseHeadersMethod, response);
			}
			else {
				fields = response.getHttpFields();
			}
			return new HttpHeaders(new JettyHeadersAdapter(fields));
		}

		private static Response getResponse(HttpServletResponse response) {
			if (response instanceof Response jettyResponse) {
				return jettyResponse;
			}
			else if (response instanceof HttpServletResponseWrapper wrapper) {
				HttpServletResponse wrappedResponse = (HttpServletResponse) wrapper.getResponse();
				return getResponse(wrappedResponse);
			}
			else {
				throw new IllegalArgumentException("Cannot convert [" + response.getClass() +
						"] to org.eclipse.jetty.server.Response");
			}
		}

		@Override
		protected int writeToOutputStream(DataBuffer dataBuffer) throws IOException {
			OutputStream output = getOutputStream();
			if (jetty11Present) {
				if (output instanceof HttpOutput httpOutput) {
					ByteBuffer input = dataBuffer.toByteBuffer();
					int len = input.remaining();
					httpOutput.write(input);
					return len;
				}
			}
			/* Jetty 12: see spring-web.gradle
			else if (jetty12Present) {
				if (output instanceof org.eclipse.jetty.ee10.servlet.HttpOutput httpOutput) {
					ByteBuffer input = dataBuffer.toByteBuffer();
					int len = input.remaining();
					httpOutput.write(input);
					return len;
				}
			}
			*/
			return super.writeToOutputStream(dataBuffer);
		}

		@Override
		protected void applyHeaders() {
			HttpServletResponse response = getNativeResponse();

			MediaType contentType = null;
			try {
				contentType = getHeaders().getContentType();
			}
			catch (Exception ex) {
				String rawContentType = getHeaders().getFirst(HttpHeaders.CONTENT_TYPE);
				response.setContentType(rawContentType);
			}
			if (response.getContentType() == null && contentType != null) {
				response.setContentType(contentType.toString());
			}

			Charset charset = (contentType != null ? contentType.getCharset() : null);
			if (response.getCharacterEncoding() == null && charset != null) {
				response.setCharacterEncoding(charset.name());
			}

			long contentLength = getHeaders().getContentLength();
			if (contentLength != -1) {
				response.setContentLengthLong(contentLength);
			}
		}
	}

}
