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

package org.springframework.beans.factory.support;

import org.springframework.beans.BeanUtils;
import org.springframework.beans.factory.config.BeanDefinitionHolder;
import org.springframework.beans.factory.config.DependencyDescriptor;
import org.springframework.lang.Nullable;

/**
 * 用于推断一个特定的beanDefinition是否能作为指定依赖的候选者的策略接口
 *
 * Strategy interface for determining whether a specific bean definition
 * qualifies as an autowire candidate for a specific dependency.
 *
 * @author Juergen Hoeller
 * @author Mark Fisher
 * @since 2.5
 */
public interface AutowireCandidateResolver {

	/**
	 * 	// 默认情况下直接根据bd中的定义返回，如果没有进行特殊配置的话为true
	 *
	 * Determine whether the given bean definition qualifies as an
	 * autowire candidate for the given dependency.
	 * <p>The default implementation checks
	 * {@link org.springframework.beans.factory.config.BeanDefinition#isAutowireCandidate()}.
	 * @param bdHolder the bean definition including bean name and aliases
	 * @param descriptor the descriptor for the target method parameter or field
	 * @return whether the bean definition qualifies as autowire candidate
	 * @see org.springframework.beans.factory.config.BeanDefinition#isAutowireCandidate()
	 */
	default boolean isAutowireCandidate(BeanDefinitionHolder bdHolder, DependencyDescriptor descriptor) {
		return bdHolder.getBeanDefinition().isAutowireCandidate();
	}

	/**
	 *  // 指定的依赖是否是必要的
	 *
	 * Determine whether the given descriptor is effectively required.
	 * <p>The default implementation checks {@link DependencyDescriptor#isRequired()}.
	 * @param descriptor the descriptor for the target method parameter or field
	 * @return whether the descriptor is marked as required or possibly indicating
	 * non-required status some other way (e.g. through a parameter annotation)
	 * @since 5.0
	 * @see DependencyDescriptor#isRequired()
	 */
	default boolean isRequired(DependencyDescriptor descriptor) {
		return descriptor.isRequired();
	}

	/**
	 * // QualifierAnnotationAutowireCandidateResolver做了实现，判断是否有@Qualifier注解
	 *     // 一共有两种注解：
	 *     // 1.Spring内置的@Qualifier注解，org.springframework.beans.factory.annotation.Qualifier
	 *     // 2.添加了JSR-330相关依赖，javax.inject.Qualifier注解
	 *     // 默认情况下返回false
	 * Determine whether the given descriptor declares a qualifier beyond the type
	 * (typically - but not necessarily - a specific kind of annotation).
	 * <p>The default implementation returns {@code false}.
	 * @param descriptor the descriptor for the target method parameter or field
	 * @return whether the descriptor declares a qualifier, narrowing the candidate
	 * status beyond the type match
	 * @since 5.1
	 * @see org.springframework.beans.factory.annotation.QualifierAnnotationAutowireCandidateResolver#hasQualifier
	 */
	default boolean hasQualifier(DependencyDescriptor descriptor) {
		return false;
	}

	/**
	 * // QualifierAnnotationAutowireCandidateResolver做了实现
	 * // 获取一个该依赖一个建议的值
	 *
	 * Determine whether a default value is suggested for the given dependency.
	 * <p>The default implementation simply returns {@code null}.
	 * @param descriptor the descriptor for the target method parameter or field
	 * @return the value suggested (typically an expression String),
	 * or {@code null} if none found
	 * @since 3.0
	 */
	@Nullable
	default Object getSuggestedValue(DependencyDescriptor descriptor) {
		return null;
	}

	/**
	 * // 对某个依赖我们想要延迟注入，但是在创建Bean的过程中这个依赖又是必须的
	 * // 通过下面这个方法就能为延迟注入的依赖先生成一个代理注入到bean中
	 *
	 * Build a proxy for lazy resolution of the actual dependency target,
	 * if demanded by the injection point.
	 * <p>The default implementation simply returns {@code null}.
	 * @param descriptor the descriptor for the target method parameter or field
	 * @param beanName the name of the bean that contains the injection point
	 * @return the lazy resolution proxy for the actual dependency target,
	 * or {@code null} if straight resolution is to be performed
	 * @since 4.0
	 */
	@Nullable
	default Object getLazyResolutionProxyIfNecessary(DependencyDescriptor descriptor, @Nullable String beanName) {
		return null;
	}

	/**
	 * Determine the proxy class for lazy resolution of the dependency target,
	 * if demanded by the injection point.
	 * <p>The default implementation simply returns {@code null}.
	 * @param descriptor the descriptor for the target method parameter or field
	 * @param beanName the name of the bean that contains the injection point
	 * @return the lazy resolution proxy class for the dependency target, if any
	 * @since 6.0
	 */
	@Nullable
	default Class<?> getLazyResolutionProxyClass(DependencyDescriptor descriptor, @Nullable String beanName) {
		return null;
	}

	/**
	 * Return a clone of this resolver instance if necessary, retaining its local
	 * configuration and allowing for the cloned instance to get associated with
	 * a new bean factory, or this original instance if there is no such state.
	 * <p>The default implementation creates a separate instance via the default
	 * class constructor, assuming no specific configuration state to copy.
	 * Subclasses may override this with custom configuration state handling
	 * or with standard {@link Cloneable} support (as implemented by Spring's
	 * own configurable {@code AutowireCandidateResolver} variants), or simply
	 * return {@code this} (as in {@link SimpleAutowireCandidateResolver}).
	 * @since 5.2.7
	 * @see GenericTypeAwareAutowireCandidateResolver#cloneIfNecessary()
	 * @see DefaultListableBeanFactory#copyConfigurationFrom
	 */
	default AutowireCandidateResolver cloneIfNecessary() {
		return BeanUtils.instantiateClass(getClass());
	}

}
