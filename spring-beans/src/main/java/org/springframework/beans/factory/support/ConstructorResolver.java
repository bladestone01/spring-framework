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

import java.beans.ConstructorProperties;
import java.lang.reflect.Array;
import java.lang.reflect.Constructor;
import java.lang.reflect.Executable;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.Deque;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.function.Supplier;

import org.apache.commons.logging.Log;

import org.springframework.beans.BeanMetadataElement;
import org.springframework.beans.BeanUtils;
import org.springframework.beans.BeanWrapper;
import org.springframework.beans.BeanWrapperImpl;
import org.springframework.beans.BeansException;
import org.springframework.beans.TypeConverter;
import org.springframework.beans.TypeMismatchException;
import org.springframework.beans.factory.BeanCreationException;
import org.springframework.beans.factory.BeanDefinitionStoreException;
import org.springframework.beans.factory.FactoryBean;
import org.springframework.beans.factory.InjectionPoint;
import org.springframework.beans.factory.NoSuchBeanDefinitionException;
import org.springframework.beans.factory.NoUniqueBeanDefinitionException;
import org.springframework.beans.factory.UnsatisfiedDependencyException;
import org.springframework.beans.factory.config.AutowireCapableBeanFactory;
import org.springframework.beans.factory.config.BeanDefinition;
import org.springframework.beans.factory.config.BeanReference;
import org.springframework.beans.factory.config.ConstructorArgumentValues;
import org.springframework.beans.factory.config.ConstructorArgumentValues.ValueHolder;
import org.springframework.beans.factory.config.DependencyDescriptor;
import org.springframework.beans.factory.config.RuntimeBeanReference;
import org.springframework.core.CollectionFactory;
import org.springframework.core.MethodParameter;
import org.springframework.core.NamedThreadLocal;
import org.springframework.core.ParameterNameDiscoverer;
import org.springframework.core.ResolvableType;
import org.springframework.lang.Nullable;
import org.springframework.util.Assert;
import org.springframework.util.ClassUtils;
import org.springframework.util.MethodInvoker;
import org.springframework.util.ObjectUtils;
import org.springframework.util.ReflectionUtils;
import org.springframework.util.StringUtils;

/**
 * 解析构造函数跟工厂方法的代理者,通过参数匹配的方式来进行推断构造方法或者工厂方法
 *
 * Delegate for resolving constructors and factory methods.
 *
 * <p>Performs constructor resolution through argument matching.
 *
 * @author Juergen Hoeller
 * @author Rob Harrop
 * @author Mark Fisher
 * @author Costin Leau
 * @author Sebastien Deleuze
 * @author Sam Brannen
 * @author Stephane Nicoll
 * @author Phil Webb
 * @since 2.0
 * @see #autowireConstructor
 * @see #instantiateUsingFactoryMethod
 * @see #resolveConstructorOrFactoryMethod
 * @see AbstractAutowireCapableBeanFactory
 */
class ConstructorResolver {

	private static final Object[] EMPTY_ARGS = new Object[0];

	/**
	 * Marker for autowired arguments in a cached argument array, to be replaced
	 * by a {@linkplain #resolveAutowiredArgument resolved autowired argument}.
	 */
	private static final Object autowiredArgumentMarker = new Object();

	private static final NamedThreadLocal<InjectionPoint> currentInjectionPoint =
			new NamedThreadLocal<>("Current injection point");


	private final AbstractAutowireCapableBeanFactory beanFactory;

	private final Log logger;


	/**
	 * Create a new ConstructorResolver for the given factory and instantiation strategy.
	 * @param beanFactory the BeanFactory to work with
	 */
	public ConstructorResolver(AbstractAutowireCapableBeanFactory beanFactory) {
		this.beanFactory = beanFactory;
		this.logger = beanFactory.getLogger();
	}


	// BeanWrapper-based construction

	/**
	 * "autowire constructor" (with constructor arguments by type) behavior.
	 * Also applied if explicit constructor argument values are specified,
	 * matching all remaining arguments with beans from the bean factory.
	 * <p>This corresponds to constructor injection: In this mode, a Spring
	 * bean factory is able to host components that expect constructor-based
	 * dependency resolution.
	 * @param beanName the name of the bean
	 * @param mbd the merged bean definition for the bean
	 * @param chosenCtors chosen candidate constructors (or {@code null} if none)
	 * @param explicitArgs argument values passed in programmatically via the getBean method,
	 * or {@code null} if none (-> use constructor argument values from bean definition)
	 * @return a BeanWrapper for the new instance
	 */
	public BeanWrapper autowireConstructor(String beanName, RootBeanDefinition mbd,
			@Nullable Constructor<?>[] chosenCtors, @Nullable Object[] explicitArgs) {

		BeanWrapperImpl bw = new BeanWrapperImpl();
		this.beanFactory.initBeanWrapper(bw);

		Constructor<?> constructorToUse = null;
		ArgumentsHolder argsHolderToUse = null;
		Object[] argsToUse = null;

		if (explicitArgs != null) {
			argsToUse = explicitArgs;
		}
		else {
			Object[] argsToResolve = null;
			synchronized (mbd.constructorArgumentLock) {
				constructorToUse = (Constructor<?>) mbd.resolvedConstructorOrFactoryMethod;
				if (constructorToUse != null && mbd.constructorArgumentsResolved) {
					// Found a cached constructor...
					argsToUse = mbd.resolvedConstructorArguments;
					if (argsToUse == null) {
						argsToResolve = mbd.preparedConstructorArguments;
					}
				}
			}
			if (argsToResolve != null) {
				argsToUse = resolvePreparedArguments(beanName, mbd, bw, constructorToUse, argsToResolve);
			}
		}

		if (constructorToUse == null || argsToUse == null) {
			// Take specified constructors, if any.
			Constructor<?>[] candidates = chosenCtors;
			if (candidates == null) {
				Class<?> beanClass = mbd.getBeanClass();
				try {
					candidates = (mbd.isNonPublicAccessAllowed() ?
							beanClass.getDeclaredConstructors() : beanClass.getConstructors());
				}
				catch (Throwable ex) {
					throw new BeanCreationException(mbd.getResourceDescription(), beanName,
							"Resolution of declared constructors on bean Class [" + beanClass.getName() +
							"] from ClassLoader [" + beanClass.getClassLoader() + "] failed", ex);
				}
			}

			if (candidates.length == 1 && explicitArgs == null && !mbd.hasConstructorArgumentValues()) {
				Constructor<?> uniqueCandidate = candidates[0];
				if (uniqueCandidate.getParameterCount() == 0) {
					synchronized (mbd.constructorArgumentLock) {
						mbd.resolvedConstructorOrFactoryMethod = uniqueCandidate;
						mbd.constructorArgumentsResolved = true;
						mbd.resolvedConstructorArguments = EMPTY_ARGS;
					}
					bw.setBeanInstance(instantiate(beanName, mbd, uniqueCandidate, EMPTY_ARGS));
					return bw;
				}
			}

			// Need to resolve the constructor.
			boolean autowiring = (chosenCtors != null ||
					mbd.getResolvedAutowireMode() == AutowireCapableBeanFactory.AUTOWIRE_CONSTRUCTOR);
			ConstructorArgumentValues resolvedValues = null;

			int minNrOfArgs;
			if (explicitArgs != null) {
				minNrOfArgs = explicitArgs.length;
			}
			else {
				ConstructorArgumentValues cargs = mbd.getConstructorArgumentValues();
				resolvedValues = new ConstructorArgumentValues();
				minNrOfArgs = resolveConstructorArguments(beanName, mbd, bw, cargs, resolvedValues);
			}

			AutowireUtils.sortConstructors(candidates);
			int minTypeDiffWeight = Integer.MAX_VALUE;
			Set<Constructor<?>> ambiguousConstructors = null;
			Deque<UnsatisfiedDependencyException> causes = null;

			for (Constructor<?> candidate : candidates) {
				int parameterCount = candidate.getParameterCount();

				if (constructorToUse != null && argsToUse != null && argsToUse.length > parameterCount) {
					// Already found greedy constructor that can be satisfied ->
					// do not look any further, there are only less greedy constructors left.
					break;
				}
				if (parameterCount < minNrOfArgs) {
					continue;
				}

				ArgumentsHolder argsHolder;
				Class<?>[] paramTypes = candidate.getParameterTypes();
				if (resolvedValues != null) {
					try {
						String[] paramNames = ConstructorPropertiesChecker.evaluate(candidate, parameterCount);
						if (paramNames == null) {
							ParameterNameDiscoverer pnd = this.beanFactory.getParameterNameDiscoverer();
							if (pnd != null) {
								paramNames = pnd.getParameterNames(candidate);
							}
						}
						argsHolder = createArgumentArray(beanName, mbd, resolvedValues, bw, paramTypes, paramNames,
								getUserDeclaredConstructor(candidate), autowiring, candidates.length == 1);
					}
					catch (UnsatisfiedDependencyException ex) {
						if (logger.isTraceEnabled()) {
							logger.trace("Ignoring constructor [" + candidate + "] of bean '" + beanName + "': " + ex);
						}
						// Swallow and try next constructor.
						if (causes == null) {
							causes = new ArrayDeque<>(1);
						}
						causes.add(ex);
						continue;
					}
				}
				else {
					// Explicit arguments given -> arguments length must match exactly.
					if (parameterCount != explicitArgs.length) {
						continue;
					}
					argsHolder = new ArgumentsHolder(explicitArgs);
				}

				int typeDiffWeight = (mbd.isLenientConstructorResolution() ?
						argsHolder.getTypeDifferenceWeight(paramTypes) : argsHolder.getAssignabilityWeight(paramTypes));
				// Choose this constructor if it represents the closest match.
				if (typeDiffWeight < minTypeDiffWeight) {
					constructorToUse = candidate;
					argsHolderToUse = argsHolder;
					argsToUse = argsHolder.arguments;
					minTypeDiffWeight = typeDiffWeight;
					ambiguousConstructors = null;
				}
				else if (constructorToUse != null && typeDiffWeight == minTypeDiffWeight) {
					if (ambiguousConstructors == null) {
						ambiguousConstructors = new LinkedHashSet<>();
						ambiguousConstructors.add(constructorToUse);
					}
					ambiguousConstructors.add(candidate);
				}
			}

			if (constructorToUse == null) {
				if (causes != null) {
					UnsatisfiedDependencyException ex = causes.removeLast();
					for (Exception cause : causes) {
						this.beanFactory.onSuppressedException(cause);
					}
					throw ex;
				}
				throw new BeanCreationException(mbd.getResourceDescription(), beanName,
						"Could not resolve matching constructor on bean class [" + mbd.getBeanClassName() + "] " +
						"(hint: specify index/type/name arguments for simple parameters to avoid type ambiguities)");
			}
			else if (ambiguousConstructors != null && !mbd.isLenientConstructorResolution()) {
				throw new BeanCreationException(mbd.getResourceDescription(), beanName,
						"Ambiguous constructor matches found on bean class [" + mbd.getBeanClassName() + "] " +
						"(hint: specify index/type/name arguments for simple parameters to avoid type ambiguities): " +
						ambiguousConstructors);
			}

			if (explicitArgs == null && argsHolderToUse != null) {
				argsHolderToUse.storeCache(mbd, constructorToUse);
			}
		}

		Assert.state(argsToUse != null, "Unresolved constructor arguments");
		bw.setBeanInstance(instantiate(beanName, mbd, constructorToUse, argsToUse));
		return bw;
	}

	private Object instantiate(
			String beanName, RootBeanDefinition mbd, Constructor<?> constructorToUse, Object[] argsToUse) {

		try {
			InstantiationStrategy strategy = this.beanFactory.getInstantiationStrategy();
			return strategy.instantiate(mbd, beanName, this.beanFactory, constructorToUse, argsToUse);
		}
		catch (Throwable ex) {
			throw new BeanCreationException(mbd.getResourceDescription(), beanName, ex.getMessage(), ex);
		}
	}

	/**
	 * Resolve the factory method in the specified bean definition, if possible.
	 * {@link RootBeanDefinition#getResolvedFactoryMethod()} can be checked for the result.
	 * @param mbd the bean definition to check
	 */
	public void resolveFactoryMethodIfPossible(RootBeanDefinition mbd) {
		Class<?> factoryClass;
		boolean isStatic;
		if (mbd.getFactoryBeanName() != null) {
			factoryClass = this.beanFactory.getType(mbd.getFactoryBeanName());
			isStatic = false;
		}
		else {
			factoryClass = mbd.getBeanClass();
			isStatic = true;
		}
		Assert.state(factoryClass != null, "Unresolvable factory class");
		factoryClass = ClassUtils.getUserClass(factoryClass);

		Method[] candidates = getCandidateMethods(factoryClass, mbd);
		Method uniqueCandidate = null;
		for (Method candidate : candidates) {
			if ((!isStatic || isStaticCandidate(candidate, factoryClass)) && mbd.isFactoryMethod(candidate)) {
				if (uniqueCandidate == null) {
					uniqueCandidate = candidate;
				}
				else if (isParamMismatch(uniqueCandidate, candidate)) {
					uniqueCandidate = null;
					break;
				}
			}
		}
		mbd.factoryMethodToIntrospect = uniqueCandidate;
	}

	private boolean isParamMismatch(Method uniqueCandidate, Method candidate) {
		int uniqueCandidateParameterCount = uniqueCandidate.getParameterCount();
		int candidateParameterCount = candidate.getParameterCount();
		return (uniqueCandidateParameterCount != candidateParameterCount ||
				!Arrays.equals(uniqueCandidate.getParameterTypes(), candidate.getParameterTypes()));
	}

	/**
	 * Retrieve all candidate methods for the given class, considering
	 * the {@link RootBeanDefinition#isNonPublicAccessAllowed()} flag.
	 * Called as the starting point for factory method determination.
	 */
	private Method[] getCandidateMethods(Class<?> factoryClass, RootBeanDefinition mbd) {
		return (mbd.isNonPublicAccessAllowed() ?
				ReflectionUtils.getUniqueDeclaredMethods(factoryClass) : factoryClass.getMethods());
	}

	private boolean isStaticCandidate(Method method, Class<?> factoryClass) {
		return (Modifier.isStatic(method.getModifiers()) && method.getDeclaringClass() == factoryClass);
	}

	/**
	 * 基于工厂方法，实例化Bean instance.
	 *  推断需要使用的factoryMethod以及调用这个FactoryMethod所需的参数； 然后反射调用这个方法，实例化出一个对象.
	 *
	 * Instantiate the bean using a named factory method. The method may be static, if the
	 * bean definition parameter specifies a class, rather than a "factory-bean", or
	 * an instance variable on a factory object itself configured using Dependency Injection.
	 * <p>Implementation requires iterating over the static or instance methods with the
	 * name specified in the RootBeanDefinition (the method may be overloaded) and trying
	 * to match with the parameters. We don't have the types attached to constructor args,
	 * so trial and error is the only way to go here. The explicitArgs array may contain
	 * argument values passed in programmatically via the corresponding getBean method.
	 * @param beanName the name of the bean
	 * @param mbd the merged bean definition for the bean
	 * @param explicitArgs argument values passed in programmatically via the getBean
	 * method, or {@code null} if none (-> use constructor argument values from bean definition)
	 * @return a BeanWrapper for the new instance
	 */
	public BeanWrapper instantiateUsingFactoryMethod(
			String beanName, RootBeanDefinition mbd, @Nullable Object[] explicitArgs) {

		//创建并初始化一个BeanWrapper对象，初始化其属性转换器：ConversionService, PropertyEditor
		//包装一个实例化的对象，对其属性进行类型转换
		BeanWrapperImpl bw = new BeanWrapperImpl();
		this.beanFactory.initBeanWrapper(bw);

		//实例化Bean的工厂Bean
		Object factoryBean;
		//工厂Bean的class
		Class<?> factoryClass;
		//静态工厂方法或者实例化工厂方法
		boolean isStatic;

		//工厂Bean实例名称
		String factoryBeanName = mbd.getFactoryBeanName();
		//安全性检查：beanName未创建; 处理FactoryBeanName与BeanName之间的关系.
		//为工厂Bean、Class、静态状态标识赋值: 静态工厂方法（Class + static factory-mehod)、实例工厂方法(FactoryClass + factory-method)
		if (factoryBeanName != null) {
			if (factoryBeanName.equals(beanName)) {
				throw new BeanDefinitionStoreException(mbd.getResourceDescription(), beanName,
						"factory-bean reference points back to the same bean definition");
			}
			factoryBean = this.beanFactory.getBean(factoryBeanName);

			//当前beanName是否已经创建，创建则异常
			if (mbd.isSingleton() && this.beanFactory.containsSingleton(beanName)) {
				throw new ImplicitlyAppearedSingletonException();
			}

			//将FactoryBeanName 依赖于 beanName，建立依赖关系Cache
			this.beanFactory.registerDependentBean(factoryBeanName, beanName);
			factoryClass = factoryBean.getClass();
			isStatic = false;
		}
		//非工厂Bean实例：静态工厂方法
		else {
			// It's a static factory method on the bean class.
			if (!mbd.hasBeanClass()) {
				throw new BeanDefinitionStoreException(mbd.getResourceDescription(), beanName,
						"bean definition declares neither a bean class nor a factory-bean reference");
			}
			factoryBean = null;
			factoryClass = mbd.getBeanClass();
			isStatic = true;
		}

		//最终确定的创建对象的方法
		Method factoryMethodToUse = null;
		ArgumentsHolder argsHolderToUse = null;
		Object[] argsToUse = null;

		//调用方法之时，传递进来的参数；如无显示输入，则为null
		// Block Description:  提取工厂方法factoryMethodToUse, 方法参数:argsToUse
		if (explicitArgs != null) {
			argsToUse = explicitArgs;
		}
		else {
			Object[] argsToResolve = null;
			synchronized (mbd.constructorArgumentLock) {
				factoryMethodToUse = (Method) mbd.resolvedConstructorOrFactoryMethod;
				if (factoryMethodToUse != null && mbd.constructorArgumentsResolved) {
					// Found a cached factory method...
					//构造方法参数Cache:
					//应用场景： 直接使用解析好的构造的参数，因为这样会导致创建出来的所有Bean都引用同一个属性
					//1 preparedConstructorArguments, resolve之后 => resolvedConstructorArguments
					//2 resolvedConstructorArguments
					argsToUse = mbd.resolvedConstructorArguments;
					if (argsToUse == null) {
						argsToResolve = mbd.preparedConstructorArguments;
					}
				}
			}
			//解析过程: preparedConstructorArguments需要再次进行解析
			if (argsToResolve != null) {
				argsToUse = resolvePreparedArguments(beanName, mbd, bw, factoryMethodToUse, argsToResolve);
			}
		}

		//现在是第一次实例化对象beanName
		if (factoryMethodToUse == null || argsToUse == null) {
			// Need to determine the factory method...
			// Try all methods with this name to see if they match the given arguments.
			// 如果被cglib代理的话，获取父类的class,即其实际的Class
			factoryClass = ClassUtils.getUserClass(factoryClass);

			List<Method> candidates = null;
			//如果FactoryMethod只有一个，则将其转换为List
			//走个捷径
			if (mbd.isFactoryMethodUnique) {
				if (factoryMethodToUse == null) {
					factoryMethodToUse = mbd.getResolvedFactoryMethod();
				}
				if (factoryMethodToUse != null) {
					candidates = Collections.singletonList(factoryMethodToUse);
				}
			}

			//未解析过，或多个方法
			if (candidates == null) {
				candidates = new ArrayList<>();
				// 获取到工厂类中的所有方法，接下来要一步步从这些方法中筛选出来符合要求的方法
				Method[] rawCandidates = getCandidateMethods(factoryClass, mbd);
				for (Method candidate : rawCandidates) {
					//静态方法， 或当前类的方法
					if ((!isStatic || isStaticCandidate(candidate, factoryClass)) && mbd.isFactoryMethod(candidate)) {
						candidates.add(candidate);
					}
				}
			}

			//只有一个工厂方法，且入口参数为null, 且工厂方法没有参数
			//快捷路径: 无参工厂方法; 大部分的情况下，会走这个路径
			if (candidates.size() == 1 && explicitArgs == null && !mbd.hasConstructorArgumentValues()) {
				Method uniqueCandidate = candidates.get(0);
				if (uniqueCandidate.getParameterCount() == 0) {
					mbd.factoryMethodToIntrospect = uniqueCandidate;
					synchronized (mbd.constructorArgumentLock) {
						mbd.resolvedConstructorOrFactoryMethod = uniqueCandidate;
						mbd.constructorArgumentsResolved = true;
						mbd.resolvedConstructorArguments = EMPTY_ARGS;
					}
					//实例化，然后set到BW
					bw.setBeanInstance(instantiate(beanName, mbd, factoryBean, uniqueCandidate, EMPTY_ARGS));
					return bw;
				}
			}

			//如果匹配到重载方法，排序，public跟参数多的优先级越高
			if (candidates.size() > 1) {  // explicitly skip immutable singletonList
				candidates.sort(AutowireUtils.EXECUTABLE_COMPARATOR);
			}

			ConstructorArgumentValues resolvedValues = null;
			//是否设置了，基于构造方法自动装配
			boolean autowiring = (mbd.getResolvedAutowireMode() == AutowireCapableBeanFactory.AUTOWIRE_CONSTRUCTOR);
			int minTypeDiffWeight = Integer.MAX_VALUE;
			// 可能出现多个符合要求的方法，用这个集合保存，实际上如果这个集合有值，就会抛出异常了
			Set<Method> ambiguousFactoryMethods = null;

			int minNrOfArgs;
			if (explicitArgs != null) {
				minNrOfArgs = explicitArgs.length;
			}
			else {
				// We don't have arguments passed in programmatically, so we need to resolve the
				// arguments specified in the constructor arguments held in the bean definition.
				//就是说配置文件中指定了要使用的参数，那么需要对其进行解析，解析后的值就存储在resolvedValues这个集合中
				if (mbd.hasConstructorArgumentValues()) {
					ConstructorArgumentValues cargs = mbd.getConstructorArgumentValues();
					resolvedValues = new ConstructorArgumentValues();
					//解析配置文件中指定的方法参数:
					//cargs: 解析标签得到的属性，但是没有经过解析(类型转换)
					//resolvedValues: 已经解析过的参数
					//返回值：方法所需要的最小参数个数
					minNrOfArgs = resolveConstructorArguments(beanName, mbd, bw, cargs, resolvedValues);
				}
				// 配置文件中没有指定要使用的参数，所以执行方法的最小参数个数就是0
				else {
					minNrOfArgs = 0;
				}
			}

			// 保存在创建方法参数数组过程中发生的异常，如果最终没有找到合适的方法，那么将这个异常信息封装后抛出
			Deque<UnsatisfiedDependencyException> causes = null;

			for (Method candidate : candidates) {
				int parameterCount = candidate.getParameterCount();
                // 候选的方法的参数必须要大于推断出来的最小参数个数
				if (parameterCount >= minNrOfArgs) {
					//参数数组
					ArgumentsHolder argsHolder;

					Class<?>[] paramTypes = candidate.getParameterTypes();
					//基于入口传入的参数
					if (explicitArgs != null) {
						// Explicit arguments given -> arguments length must match exactly.
						if (paramTypes.length != explicitArgs.length) {
							continue;
						}
						argsHolder = new ArgumentsHolder(explicitArgs);
					}
					else {
						// Resolved constructor arguments: type conversion and/or autowiring necessary.
						//基于Method解析出其使用的参数
						try {
							String[] paramNames = null;
							ParameterNameDiscoverer pnd = this.beanFactory.getParameterNameDiscoverer();
							if (pnd != null) {
								paramNames = pnd.getParameterNames(candidate);
							}
							// 根据方法的参数名称以及配置文件中配置的参数创建一个参数数组用于执行工厂方法
							argsHolder = createArgumentArray(beanName, mbd, resolvedValues, bw,
									paramTypes, paramNames, candidate, autowiring, candidates.size() == 1);
						}
						catch (UnsatisfiedDependencyException ex) {
							if (logger.isTraceEnabled()) {
								logger.trace("Ignoring factory method [" + candidate + "] of bean '" + beanName + "': " + ex);
							}
							// Swallow and try next overloaded factory method.
							if (causes == null) {
								causes = new ArrayDeque<>(1);
							}
							// 在创建参数数组的时候可能发生异常，这个时候的异常不能直接抛出，要确保所有的候选方法遍历完成
							// 只要有一个方法符合要求即可，但是如果遍历完所有方法还是没找到合适的构造器，那么直接抛出这些异常
							causes.add(ex);
							continue;
						}
					}
					// 计算类型差异
					// 首先判断bd中是宽松模式还是严格模式，目前看来只有@Bean标注的方法解析得到的Bean会使用严格模式来计算类型差异，其余都是使用宽松模式
					int typeDiffWeight = (mbd.isLenientConstructorResolution() ?
							argsHolder.getTypeDifferenceWeight(paramTypes) : argsHolder.getAssignabilityWeight(paramTypes));
					// Choose this factory method if it represents the closest match.
					// 选择一个类型差异最小的方法
					if (typeDiffWeight < minTypeDiffWeight) {
						factoryMethodToUse = candidate;
						argsHolderToUse = argsHolder;
						argsToUse = argsHolder.arguments;
						minTypeDiffWeight = typeDiffWeight;
						ambiguousFactoryMethods = null;
					}
					// Find out about ambiguity: In case of the same type difference weight
					// for methods with the same number of parameters, collect such candidates
					// and eventually raise an ambiguity exception.
					// However, only perform that check in non-lenient constructor resolution mode,
					// and explicitly ignore overridden methods (with the same parameter signature).
					else if (factoryMethodToUse != null && typeDiffWeight == minTypeDiffWeight &&
							!mbd.isLenientConstructorResolution() &&
							paramTypes.length == factoryMethodToUse.getParameterCount() &&
							!Arrays.equals(paramTypes, factoryMethodToUse.getParameterTypes())) {
						if (ambiguousFactoryMethods == null) {
							ambiguousFactoryMethods = new LinkedHashSet<>();
							ambiguousFactoryMethods.add(factoryMethodToUse);
						}
						ambiguousFactoryMethods.add(candidate);
					}
				}
			}

			// 对推断出来的方法做验证
			// 1.推断出来的方法 或参数不能为null； 为空，则抛出异常
			// 2.推断出来的方法返回值不能为void
			// 3.推断出来的方法不能有多个
			if (factoryMethodToUse == null || argsToUse == null) {
				if (causes != null) {
					UnsatisfiedDependencyException ex = causes.removeLast();
					for (Exception cause : causes) {
						this.beanFactory.onSuppressedException(cause);
					}
					throw ex;
				}
				List<String> argTypes = new ArrayList<>(minNrOfArgs);
				if (explicitArgs != null) {
					for (Object arg : explicitArgs) {
						argTypes.add(arg != null ? arg.getClass().getSimpleName() : "null");
					}
				}
				else if (resolvedValues != null) {
					Set<ValueHolder> valueHolders = new LinkedHashSet<>(resolvedValues.getArgumentCount());
					valueHolders.addAll(resolvedValues.getIndexedArgumentValues().values());
					valueHolders.addAll(resolvedValues.getGenericArgumentValues());
					for (ValueHolder value : valueHolders) {
						String argType = (value.getType() != null ? ClassUtils.getShortName(value.getType()) :
								(value.getValue() != null ? value.getValue().getClass().getSimpleName() : "null"));
						argTypes.add(argType);
					}
				}
				String argDesc = StringUtils.collectionToCommaDelimitedString(argTypes);
				throw new BeanCreationException(mbd.getResourceDescription(), beanName,
						"No matching factory method found on class [" + factoryClass.getName() + "]: " +
						(mbd.getFactoryBeanName() != null ?
								"factory bean '" + mbd.getFactoryBeanName() + "'; " : "") +
						"factory method '" + mbd.getFactoryMethodName() + "(" + argDesc + ")'. " +
						"Check that a method with the specified name " +
						(minNrOfArgs > 0 ? "and arguments " : "") +
						"exists and that it is " +
						(isStatic ? "static" : "non-static") + ".");
			}
			//返回值不能为Void
			else if (void.class == factoryMethodToUse.getReturnType()) {
				throw new BeanCreationException(mbd.getResourceDescription(), beanName,
						"Invalid factory method '" + mbd.getFactoryMethodName() + "' on class [" +
						factoryClass.getName() + "]: needs to have a non-void return type!");
			}
			//不能存在多个方法
			else if (ambiguousFactoryMethods != null) {
				throw new BeanCreationException(mbd.getResourceDescription(), beanName,
						"Ambiguous factory method matches found on class [" + factoryClass.getName() + "] " +
						"(hint: specify index/type/name arguments for simple parameters to avoid type ambiguities): " +
						ambiguousFactoryMethods);
			}

			//参数缓存
			if (explicitArgs == null && argsHolderToUse != null) {
				mbd.factoryMethodToIntrospect = factoryMethodToUse;
				argsHolderToUse.storeCache(mbd, factoryMethodToUse);
			}
		}
		// 反射调用对应方法进行实例化
		// 1.获取InstantiationStrategy，主要就是SimpleInstantiationStrategy跟CglibSubclassingInstantiationStrategy，
		// 其中CglibSubclassingInstantiationStrategy主要是用来处理beanDefinition中的lookupMethod跟replaceMethod。通常来说我们使用的就是SimpleInstantiationStrategy
		// 2.SimpleInstantiationStrategy就是单纯的通过反射调用方法
		bw.setBeanInstance(instantiate(beanName, mbd, factoryBean, factoryMethodToUse, argsToUse));
		return bw;
	}

	private Object instantiate(String beanName, RootBeanDefinition mbd,
			@Nullable Object factoryBean, Method factoryMethod, Object[] args) {

		try {
			return this.beanFactory.getInstantiationStrategy().instantiate(
					mbd, beanName, this.beanFactory, factoryBean, factoryMethod, args);
		}
		catch (Throwable ex) {
			throw new BeanCreationException(mbd.getResourceDescription(), beanName, ex.getMessage(), ex);
		}
	}

	/**
	 * 解析： 将标签或注解中的值，进行类型转换
	 *
	 * Resolve the constructor arguments for this bean into the resolvedValues object.
	 * This may involve looking up other beans.
	 * <p>This method is also used for handling invocations of static factory methods.
	 */
	private int resolveConstructorArguments(String beanName, RootBeanDefinition mbd, BeanWrapper bw,
			ConstructorArgumentValues cargs, ConstructorArgumentValues resolvedValues) {
		// 是否有定制的类型转换器，没有的话直接使用BeanWrapper进行类型转换
		TypeConverter customConverter = this.beanFactory.getCustomTypeConverter();
		TypeConverter converter = (customConverter != null ? customConverter : bw);

		// 构造一个BeanDefinitionValueResolver，专门用于解析constructor-arg中的value属性，实际上还包括ref属性，内嵌bean标签等等
		BeanDefinitionValueResolver valueResolver =
				new BeanDefinitionValueResolver(this.beanFactory, beanName, mbd, converter);

		// minNrOfArgs 记录执行方法要求的最小参数个数，一般情况下就是等于constructor-arg标签指定的参数数量
		int minNrOfArgs = cargs.getArgumentCount();

		for (Map.Entry<Integer, ConstructorArgumentValues.ValueHolder> entry : cargs.getIndexedArgumentValues().entrySet()) {
			int index = entry.getKey();
			if (index < 0) {
				throw new BeanCreationException(mbd.getResourceDescription(), beanName,
						"Invalid constructor argument index: " + index);
			}
			if (index + 1 > minNrOfArgs) {
				minNrOfArgs = index + 1;
			}
			ConstructorArgumentValues.ValueHolder valueHolder = entry.getValue();
			// 如果已经转换过了，直接添加到resolvedValues集合中
			if (valueHolder.isConverted()) {
				resolvedValues.addIndexedArgumentValue(index, valueHolder);
			}
			else {
				// 解析value/ref/内嵌bean标签等
				Object resolvedValue =
						valueResolver.resolveValueIfNecessary("constructor argument", valueHolder.getValue());
				// 将解析后的resolvedValue封装成一个新的ValueHolder，并将其source设置为解析constructor-arg得到的那个ValueHolder，后期会用到这个属性进行判断
				ConstructorArgumentValues.ValueHolder resolvedValueHolder =
						new ConstructorArgumentValues.ValueHolder(resolvedValue, valueHolder.getType(), valueHolder.getName());
				resolvedValueHolder.setSource(valueHolder);
				resolvedValues.addIndexedArgumentValue(index, resolvedValueHolder);
			}
		}

		for (ConstructorArgumentValues.ValueHolder valueHolder : cargs.getGenericArgumentValues()) {
			if (valueHolder.isConverted()) {
				resolvedValues.addGenericArgumentValue(valueHolder);
			}
			else {
				// 解析value/ref/内嵌bean标签等
				Object resolvedValue =
						valueResolver.resolveValueIfNecessary("constructor argument", valueHolder.getValue());
				// 将解析后的resolvedValue封装成一个新的ValueHolder，并将其source设置为解析constructor-arg得到的那个ValueHolder，后期会用到这个属性进行判断
				ConstructorArgumentValues.ValueHolder resolvedValueHolder = new ConstructorArgumentValues.ValueHolder(
						resolvedValue, valueHolder.getType(), valueHolder.getName());
				resolvedValueHolder.setSource(valueHolder);
				resolvedValues.addGenericArgumentValue(resolvedValueHolder);
			}
		}

		return minNrOfArgs;
	}

	/**
	 * Create an array of arguments to invoke a constructor or factory method,
	 * given the resolved constructor argument values.
	 */
	/**
	 *  * beanName：要实例化的Bean的名称
	 *  * mbd：对应Bean的BeanDefinition
	 *  * resolvedValues：从配置文件中解析出来的并尝试过类型转换的参数
	 *  * bw：在这里主要就是用作类型转换器
	 *  * paramTypes：当前遍历到的候选的方法的参数类型数组
	 *  * paramNames：当前遍历到的候选的方法的参数名称
	 *  * executable：当前遍历到的候选的方法
	 *  * autowiring：是否时自动注入
	 * @param beanName
	 * @param mbd
	 * @param resolvedValues
	 * @param bw
	 * @param paramTypes
	 * @param paramNames
	 * @param executable
	 * @param autowiring
	 * @param fallback
	 * @return
	 * @throws UnsatisfiedDependencyException
	 */
	private ArgumentsHolder createArgumentArray(
			String beanName, RootBeanDefinition mbd, @Nullable ConstructorArgumentValues resolvedValues,
			BeanWrapper bw, Class<?>[] paramTypes, @Nullable String[] paramNames, Executable executable,
			boolean autowiring, boolean fallback) throws UnsatisfiedDependencyException {

		TypeConverter customConverter = this.beanFactory.getCustomTypeConverter();
		TypeConverter converter = (customConverter != null ? customConverter : bw);

		ArgumentsHolder args = new ArgumentsHolder(paramTypes.length);
		Set<ConstructorArgumentValues.ValueHolder> usedValueHolders = new HashSet<>(paramTypes.length);
		Set<String> autowiredBeanNames = new LinkedHashSet<>(4);

		// 遍历候选方法的参数，跟据方法实际需要的类型到resolvedValues中去匹配
		for (int paramIndex = 0; paramIndex < paramTypes.length; paramIndex++) {
			Class<?> paramType = paramTypes[paramIndex];
			String paramName = (paramNames != null ? paramNames[paramIndex] : "");
			// Try to find matching constructor argument value, either indexed or generic.
			ConstructorArgumentValues.ValueHolder valueHolder = null;
			if (resolvedValues != null) {
				// 首先，根据方法参数的下标到resolvedValues中找对应的下标的属性
				// 如果没找到再根据方法的参数名/类型去resolvedValues查找
				valueHolder = resolvedValues.getArgumentValue(paramIndex, paramType, paramName, usedValueHolders);
				// If we couldn't find a direct match and are not supposed to autowire,
				// let's try the next generic, untyped argument value as fallback:
				// it could match after type conversion (for example, String -> int).
				// 如果都没找到
				// 1.是自动注入并且方法的参数长度正好跟配置中的参数数量相等
				// 2.不是自动注入
				// 那么按照顺序一次选取
				if (valueHolder == null && (!autowiring || paramTypes.length == resolvedValues.getArgumentCount())) {
					valueHolder = resolvedValues.getGenericArgumentValue(null, null, usedValueHolders);
				}
			}
			// 在配置的参数中找到了合适的值可以应用于这个方法上
			if (valueHolder != null) {
				// 防止同一个参数被应用了多次
				// We found a potential match - let's give it a try.
				// Do not consider the same value definition multiple times!
				usedValueHolders.add(valueHolder);
				Object originalValue = valueHolder.getValue();
				Object convertedValue;
				// 已经进行过类型转换就不会需要再次进行类型转换
				if (valueHolder.isConverted()) {
					convertedValue = valueHolder.getConvertedValue();
					args.preparedArguments[paramIndex] = convertedValue;
				}
				else {
					// 尝试将配置的值转换成方法参数需要的类型
					MethodParameter methodParam = MethodParameter.forExecutable(executable, paramIndex);
					try {
						//进行类型转换
						convertedValue = converter.convertIfNecessary(originalValue, paramType, methodParam);
					}
					catch (TypeMismatchException ex) {
						throw new UnsatisfiedDependencyException(
								mbd.getResourceDescription(), beanName, new InjectionPoint(methodParam),
								"Could not convert argument value of type [" +
										ObjectUtils.nullSafeClassName(valueHolder.getValue()) +
										"] to required type [" + paramType.getName() + "]: " + ex.getMessage());
					}
					Object sourceHolder = valueHolder.getSource();
					// 只要是valueHolder存在，到这里这个判断必定成立
					if (sourceHolder instanceof ConstructorArgumentValues.ValueHolder) {
						Object sourceValue = ((ConstructorArgumentValues.ValueHolder) sourceHolder).getValue();
						args.resolveNecessary = true;
						args.preparedArguments[paramIndex] = sourceValue;
					}
				}
				args.arguments[paramIndex] = convertedValue;
				args.rawArguments[paramIndex] = originalValue;
			}
			else {
				// 方法执行需要参数，但是resolvedValues中没有提供这个参数，也就是说这个参数是要自动注入到Bean中的
				MethodParameter methodParam = MethodParameter.forExecutable(executable, paramIndex);
				// No explicit match found: we're either supposed to autowire or
				// have to fail creating an argument array for the given constructor.
				// 不是自动注入，直接抛出异常
				if (!autowiring) {
					throw new UnsatisfiedDependencyException(
							mbd.getResourceDescription(), beanName, new InjectionPoint(methodParam),
							"Ambiguous argument values for parameter of type [" + paramType.getName() +
							"] - did you specify the correct bean references as arguments?");
				}
				try {
					// 自动注入的情况下，调用getBean获取需要注入的Bean
					Object autowiredArgument = resolveAutowiredArgument(
							methodParam, beanName, autowiredBeanNames, converter, fallback);
					// 把getBean返回的Bean封装到本次方法执行时需要的参数数组中去
					args.rawArguments[paramIndex] = autowiredArgument;
					args.arguments[paramIndex] = autowiredArgument;
					// 标志这个参数是自动注入的
					args.preparedArguments[paramIndex] = autowiredArgumentMarker;
					// 自动注入的情况下，在第二次调用时，需要重新处理，不能直接缓存
					args.resolveNecessary = true;
				}
				catch (BeansException ex) {
					throw new UnsatisfiedDependencyException(
							mbd.getResourceDescription(), beanName, new InjectionPoint(methodParam), ex);
				}
			}
		}

		//注册Bean之间的依赖关系
		for (String autowiredBeanName : autowiredBeanNames) {
			this.beanFactory.registerDependentBean(autowiredBeanName, beanName);
			if (logger.isDebugEnabled()) {
				logger.debug("Autowiring by type from bean name '" + beanName +
						"' via " + (executable instanceof Constructor ? "constructor" : "factory method") +
						" to bean named '" + autowiredBeanName + "'");
			}
		}

		return args;
	}

	/**
	 * Resolve the prepared arguments stored in the given bean definition.
	 */
	private Object[] resolvePreparedArguments(String beanName, RootBeanDefinition mbd, BeanWrapper bw,
			Executable executable, Object[] argsToResolve) {

		TypeConverter customConverter = this.beanFactory.getCustomTypeConverter();
		TypeConverter converter = (customConverter != null ? customConverter : bw);
		BeanDefinitionValueResolver valueResolver =
				new BeanDefinitionValueResolver(this.beanFactory, beanName, mbd, converter);
		Class<?>[] paramTypes = executable.getParameterTypes();

		Object[] resolvedArgs = new Object[argsToResolve.length];
		for (int argIndex = 0; argIndex < argsToResolve.length; argIndex++) {
			Object argValue = argsToResolve[argIndex];
			MethodParameter methodParam = MethodParameter.forExecutable(executable, argIndex);
			if (argValue == autowiredArgumentMarker) {
				argValue = resolveAutowiredArgument(methodParam, beanName, null, converter, true);
			}
			else if (argValue instanceof BeanMetadataElement) {
				argValue = valueResolver.resolveValueIfNecessary("constructor argument", argValue);
			}
			else if (argValue instanceof String) {
				argValue = this.beanFactory.evaluateBeanDefinitionString((String) argValue, mbd);
			}
			Class<?> paramType = paramTypes[argIndex];
			try {
				resolvedArgs[argIndex] = converter.convertIfNecessary(argValue, paramType, methodParam);
			}
			catch (TypeMismatchException ex) {
				throw new UnsatisfiedDependencyException(
						mbd.getResourceDescription(), beanName, new InjectionPoint(methodParam),
						"Could not convert argument value of type [" + ObjectUtils.nullSafeClassName(argValue) +
						"] to required type [" + paramType.getName() + "]: " + ex.getMessage());
			}
		}
		return resolvedArgs;
	}

	protected Constructor<?> getUserDeclaredConstructor(Constructor<?> constructor) {
		Class<?> declaringClass = constructor.getDeclaringClass();
		Class<?> userClass = ClassUtils.getUserClass(declaringClass);
		if (userClass != declaringClass) {
			try {
				return userClass.getDeclaredConstructor(constructor.getParameterTypes());
			}
			catch (NoSuchMethodException ex) {
				// No equivalent constructor on user class (superclass)...
				// Let's proceed with the given constructor as we usually would.
			}
		}
		return constructor;
	}

	/**
	 * Template method for resolving the specified argument which is supposed to be autowired.
	 */
	@Nullable
	protected Object resolveAutowiredArgument(MethodParameter param, String beanName,
			@Nullable Set<String> autowiredBeanNames, TypeConverter typeConverter, boolean fallback) {

		Class<?> paramType = param.getParameterType();
		if (InjectionPoint.class.isAssignableFrom(paramType)) {
			InjectionPoint injectionPoint = currentInjectionPoint.get();
			if (injectionPoint == null) {
				throw new IllegalStateException("No current InjectionPoint available for " + param);
			}
			return injectionPoint;
		}
		try {
			return this.beanFactory.resolveDependency(
					new DependencyDescriptor(param, true), beanName, autowiredBeanNames, typeConverter);
		}
		catch (NoUniqueBeanDefinitionException ex) {
			throw ex;
		}
		catch (NoSuchBeanDefinitionException ex) {
			if (fallback) {
				// Single constructor or factory method -> let's return an empty array/collection
				// for e.g. a vararg or a non-null List/Set/Map parameter.
				if (paramType.isArray()) {
					return Array.newInstance(paramType.getComponentType(), 0);
				}
				else if (CollectionFactory.isApproximableCollectionType(paramType)) {
					return CollectionFactory.createCollection(paramType, 0);
				}
				else if (CollectionFactory.isApproximableMapType(paramType)) {
					return CollectionFactory.createMap(paramType, 0);
				}
			}
			throw ex;
		}
	}


	// AOT-oriented pre-resolution

	public Executable resolveConstructorOrFactoryMethod(String beanName, RootBeanDefinition mbd) {
		Supplier<ResolvableType> beanType = () -> getBeanType(beanName, mbd);
		List<ResolvableType> valueTypes = (mbd.hasConstructorArgumentValues() ?
				determineParameterValueTypes(mbd) : Collections.emptyList());
		Method resolvedFactoryMethod = resolveFactoryMethod(beanName, mbd, valueTypes);
		if (resolvedFactoryMethod != null) {
			return resolvedFactoryMethod;
		}

		Class<?> factoryBeanClass = getFactoryBeanClass(beanName, mbd);
		if (factoryBeanClass != null && !factoryBeanClass.equals(mbd.getResolvableType().toClass())) {
			ResolvableType resolvableType = mbd.getResolvableType();
			boolean isCompatible = ResolvableType.forClass(factoryBeanClass)
					.as(FactoryBean.class).getGeneric(0).isAssignableFrom(resolvableType);
			Assert.state(isCompatible, () -> String.format(
					"Incompatible target type '%s' for factory bean '%s'",
					resolvableType.toClass().getName(), factoryBeanClass.getName()));
			Executable executable = resolveConstructor(beanName, mbd,
					() -> ResolvableType.forClass(factoryBeanClass), valueTypes);
			if (executable != null) {
				return executable;
			}
			throw new IllegalStateException("No suitable FactoryBean constructor found for " +
					mbd + " and argument types " + valueTypes);

		}

		Executable resolvedConstructor = resolveConstructor(beanName, mbd, beanType, valueTypes);
		if (resolvedConstructor != null) {
			return resolvedConstructor;
		}

		throw new IllegalStateException("No constructor or factory method candidate found for " +
				mbd + " and argument types " + valueTypes);
	}

	private List<ResolvableType> determineParameterValueTypes(RootBeanDefinition mbd) {
		List<ResolvableType> parameterTypes = new ArrayList<>();
		for (ValueHolder valueHolder : mbd.getConstructorArgumentValues().getIndexedArgumentValues().values()) {
			parameterTypes.add(determineParameterValueType(mbd, valueHolder));
		}
		return parameterTypes;
	}

	private ResolvableType determineParameterValueType(RootBeanDefinition mbd, ValueHolder valueHolder) {
		if (valueHolder.getType() != null) {
			return ResolvableType.forClass(
					ClassUtils.resolveClassName(valueHolder.getType(), this.beanFactory.getBeanClassLoader()));
		}
		Object value = valueHolder.getValue();
		if (value instanceof BeanReference br) {
			if (value instanceof RuntimeBeanReference rbr) {
				if (rbr.getBeanType() != null) {
					return ResolvableType.forClass(rbr.getBeanType());
				}
			}
			return ResolvableType.forClass(this.beanFactory.getType(br.getBeanName(), false));
		}
		if (value instanceof BeanDefinition innerBd) {
			String nameToUse = "(inner bean)";
			ResolvableType type = getBeanType(nameToUse,
					this.beanFactory.getMergedBeanDefinition(nameToUse, innerBd, mbd));
			return (FactoryBean.class.isAssignableFrom(type.toClass()) ?
					type.as(FactoryBean.class).getGeneric(0) : type);
		}
		if (value instanceof Class<?> clazz) {
			return ResolvableType.forClassWithGenerics(Class.class, clazz);
		}
		return ResolvableType.forInstance(value);
	}

	@Nullable
	private Executable resolveConstructor(String beanName, RootBeanDefinition mbd,
			Supplier<ResolvableType> beanType, List<ResolvableType> valueTypes) {

		Class<?> type = ClassUtils.getUserClass(beanType.get().toClass());
		Constructor<?>[] ctors = this.beanFactory.determineConstructorsFromBeanPostProcessors(type, beanName);
		if (ctors == null) {
			if (!mbd.hasConstructorArgumentValues()) {
				ctors = mbd.getPreferredConstructors();
			}
			if (ctors == null) {
				ctors = (mbd.isNonPublicAccessAllowed() ? type.getDeclaredConstructors() : type.getConstructors());
			}
		}
		if (ctors.length == 1) {
			return ctors[0];
		}

		Function<Constructor<?>, List<ResolvableType>> parameterTypesFactory = executable -> {
			List<ResolvableType> types = new ArrayList<>();
			for (int i = 0; i < executable.getParameterCount(); i++) {
				types.add(ResolvableType.forConstructorParameter(executable, i));
			}
			return types;
		};
		List<? extends Executable> matches = Arrays.stream(ctors)
				.filter(executable -> match(parameterTypesFactory.apply(executable),
						valueTypes, FallbackMode.NONE))
				.toList();
		if (matches.size() == 1) {
			return matches.get(0);
		}
		List<? extends Executable> assignableElementFallbackMatches = Arrays
				.stream(ctors)
				.filter(executable -> match(parameterTypesFactory.apply(executable),
						valueTypes, FallbackMode.ASSIGNABLE_ELEMENT))
				.toList();
		if (assignableElementFallbackMatches.size() == 1) {
			return assignableElementFallbackMatches.get(0);
		}
		List<? extends Executable> typeConversionFallbackMatches = Arrays
				.stream(ctors)
				.filter(executable -> match(parameterTypesFactory.apply(executable),
						valueTypes, FallbackMode.TYPE_CONVERSION))
				.toList();
		return (typeConversionFallbackMatches.size() == 1 ? typeConversionFallbackMatches.get(0) : null);
	}

	@Nullable
	private Method resolveFactoryMethod(String beanName, RootBeanDefinition mbd, List<ResolvableType> valueTypes) {
		if (mbd.isFactoryMethodUnique) {
			Method resolvedFactoryMethod = mbd.getResolvedFactoryMethod();
			if (resolvedFactoryMethod != null) {
				return resolvedFactoryMethod;
			}
		}

		String factoryMethodName = mbd.getFactoryMethodName();
		if (factoryMethodName != null) {
			String factoryBeanName = mbd.getFactoryBeanName();
			Class<?> factoryClass;
			boolean isStatic;
			if (factoryBeanName != null) {
				factoryClass = this.beanFactory.getType(factoryBeanName);
				isStatic = false;
			}
			else {
				factoryClass = this.beanFactory.resolveBeanClass(mbd, beanName);
				isStatic = true;
			}

			Assert.state(factoryClass != null, () -> "Failed to determine bean class of " + mbd);
			Method[] rawCandidates = getCandidateMethods(factoryClass, mbd);
			List<Method> candidates = new ArrayList<>();
			for (Method candidate : rawCandidates) {
				if ((!isStatic || isStaticCandidate(candidate, factoryClass)) && mbd.isFactoryMethod(candidate)) {
					candidates.add(candidate);
				}
			}

			Method result = null;
			if (candidates.size() == 1) {
				result = candidates.get(0);
			}
			else if (candidates.size() > 1) {
				Function<Method, List<ResolvableType>> parameterTypesFactory = method -> {
					List<ResolvableType> types = new ArrayList<>();
					for (int i = 0; i < method.getParameterCount(); i++) {
						types.add(ResolvableType.forMethodParameter(method, i));
					}
					return types;
				};
				result = (Method) resolveFactoryMethod(candidates, parameterTypesFactory, valueTypes);
			}

			if (result == null) {
				throw new BeanCreationException(mbd.getResourceDescription(), beanName,
						"No matching factory method found on class [" + factoryClass.getName() + "]: " +
						(mbd.getFactoryBeanName() != null ?
								"factory bean '" + mbd.getFactoryBeanName() + "'; " : "") +
						"factory method '" + mbd.getFactoryMethodName() + "'. ");
			}
			return result;
		}

		return null;
	}

	@Nullable
	private Executable resolveFactoryMethod(List<Method> executables,
			Function<Method, List<ResolvableType>> parameterTypesFactory,
			List<ResolvableType> valueTypes) {

		List<? extends Executable> matches = executables.stream()
				.filter(executable -> match(parameterTypesFactory.apply(executable), valueTypes, FallbackMode.NONE))
				.toList();
		if (matches.size() == 1) {
			return matches.get(0);
		}
		List<? extends Executable> assignableElementFallbackMatches = executables.stream()
				.filter(executable -> match(parameterTypesFactory.apply(executable),
						valueTypes, FallbackMode.ASSIGNABLE_ELEMENT))
				.toList();
		if (assignableElementFallbackMatches.size() == 1) {
			return assignableElementFallbackMatches.get(0);
		}
		List<? extends Executable> typeConversionFallbackMatches = executables.stream()
				.filter(executable -> match(parameterTypesFactory.apply(executable),
						valueTypes, FallbackMode.TYPE_CONVERSION))
				.toList();
		Assert.state(typeConversionFallbackMatches.size() <= 1,
				() -> "Multiple matches with parameters '" + valueTypes + "': " + typeConversionFallbackMatches);
		return (typeConversionFallbackMatches.size() == 1 ? typeConversionFallbackMatches.get(0) : null);
	}

	private boolean match(
			List<ResolvableType> parameterTypes, List<ResolvableType> valueTypes, FallbackMode fallbackMode) {

		if (parameterTypes.size() != valueTypes.size()) {
			return false;
		}
		for (int i = 0; i < parameterTypes.size(); i++) {
			if (!isMatch(parameterTypes.get(i), valueTypes.get(i), fallbackMode)) {
				return false;
			}
		}
		return true;
	}

	private boolean isMatch(ResolvableType parameterType, ResolvableType valueType, FallbackMode fallbackMode) {
		if (isAssignable(valueType).test(parameterType)) {
			return true;
		}
		return switch (fallbackMode) {
			case ASSIGNABLE_ELEMENT -> isAssignable(valueType).test(extractElementType(parameterType));
			case TYPE_CONVERSION -> typeConversionFallback(valueType).test(parameterType);
			default -> false;
		};
	}

	private Predicate<ResolvableType> isAssignable(ResolvableType valueType) {
		return parameterType -> parameterType.isAssignableFrom(valueType);
	}

	private ResolvableType extractElementType(ResolvableType parameterType) {
		if (parameterType.isArray()) {
			return parameterType.getComponentType();
		}
		if (Collection.class.isAssignableFrom(parameterType.toClass())) {
			return parameterType.as(Collection.class).getGeneric(0);
		}
		return ResolvableType.NONE;
	}

	private Predicate<ResolvableType> typeConversionFallback(ResolvableType valueType) {
		return parameterType -> {
			if (valueOrCollection(valueType, this::isStringForClassFallback).test(parameterType)) {
				return true;
			}
			return valueOrCollection(valueType, this::isSimpleValueType).test(parameterType);
		};
	}

	private Predicate<ResolvableType> valueOrCollection(ResolvableType valueType,
			Function<ResolvableType, Predicate<ResolvableType>> predicateProvider) {

		return parameterType -> {
			if (predicateProvider.apply(valueType).test(parameterType)) {
				return true;
			}
			if (predicateProvider.apply(extractElementType(valueType)).test(extractElementType(parameterType))) {
				return true;
			}
			return (predicateProvider.apply(valueType).test(extractElementType(parameterType)));
		};
	}

	/**
	 * Return a {@link Predicate} for a parameter type that checks if its target
	 * value is a {@link Class} and the value type is a {@link String}. This is
	 * a regular use cases where a {@link Class} is defined in the bean
	 * definition as an FQN.
	 * @param valueType the type of the value
	 * @return a predicate to indicate a fallback match for a String to Class
	 * parameter
	 */
	private Predicate<ResolvableType> isStringForClassFallback(ResolvableType valueType) {
		return parameterType -> (valueType.isAssignableFrom(String.class) &&
				parameterType.isAssignableFrom(Class.class));
	}

	private Predicate<ResolvableType> isSimpleValueType(ResolvableType valueType) {
		return parameterType -> (BeanUtils.isSimpleValueType(parameterType.toClass()) &&
				BeanUtils.isSimpleValueType(valueType.toClass()));
	}

	@Nullable
	private Class<?> getFactoryBeanClass(String beanName, RootBeanDefinition mbd) {
		Class<?> beanClass = this.beanFactory.resolveBeanClass(mbd, beanName);
		return (beanClass != null && FactoryBean.class.isAssignableFrom(beanClass) ? beanClass : null);
	}

	private ResolvableType getBeanType(String beanName, RootBeanDefinition mbd) {
		ResolvableType resolvableType = mbd.getResolvableType();
		if (resolvableType != ResolvableType.NONE) {
			return resolvableType;
		}
		return ResolvableType.forClass(this.beanFactory.resolveBeanClass(mbd, beanName));
	}


	static InjectionPoint setCurrentInjectionPoint(@Nullable InjectionPoint injectionPoint) {
		InjectionPoint old = currentInjectionPoint.get();
		if (injectionPoint != null) {
			currentInjectionPoint.set(injectionPoint);
		}
		else {
			currentInjectionPoint.remove();
		}
		return old;
	}


	/**
	 * Private inner class for holding argument combinations.
	 */
	private static class ArgumentsHolder {

		public final Object[] rawArguments;

		public final Object[] arguments;

		public final Object[] preparedArguments;

		public boolean resolveNecessary = false;

		public ArgumentsHolder(int size) {
			this.rawArguments = new Object[size];
			this.arguments = new Object[size];
			this.preparedArguments = new Object[size];
		}

		public ArgumentsHolder(Object[] args) {
			this.rawArguments = args;
			this.arguments = args;
			this.preparedArguments = args;
		}

		public int getTypeDifferenceWeight(Class<?>[] paramTypes) {
			// If valid arguments found, determine type difference weight.
			// Try type difference weight on both the converted arguments and
			// the raw arguments. If the raw weight is better, use it.
			// Decrease raw weight by 1024 to prefer it over equal converted weight.
			int typeDiffWeight = MethodInvoker.getTypeDifferenceWeight(paramTypes, this.arguments);
			int rawTypeDiffWeight = MethodInvoker.getTypeDifferenceWeight(paramTypes, this.rawArguments) - 1024;
			return Math.min(rawTypeDiffWeight, typeDiffWeight);
		}

		public int getAssignabilityWeight(Class<?>[] paramTypes) {
			for (int i = 0; i < paramTypes.length; i++) {
				if (!ClassUtils.isAssignableValue(paramTypes[i], this.arguments[i])) {
					return Integer.MAX_VALUE;
				}
			}
			for (int i = 0; i < paramTypes.length; i++) {
				if (!ClassUtils.isAssignableValue(paramTypes[i], this.rawArguments[i])) {
					return Integer.MAX_VALUE - 512;
				}
			}
			return Integer.MAX_VALUE - 1024;
		}

		public void storeCache(RootBeanDefinition mbd, Executable constructorOrFactoryMethod) {
			synchronized (mbd.constructorArgumentLock) {
				mbd.resolvedConstructorOrFactoryMethod = constructorOrFactoryMethod;
				mbd.constructorArgumentsResolved = true;
				if (this.resolveNecessary) {
					mbd.preparedConstructorArguments = this.preparedArguments;
				}
				else {
					mbd.resolvedConstructorArguments = this.arguments;
				}
			}
		}
	}


	/**
	 * Delegate for checking Java's {@link ConstructorProperties} annotation.
	 */
	private static class ConstructorPropertiesChecker {

		@Nullable
		public static String[] evaluate(Constructor<?> candidate, int paramCount) {
			ConstructorProperties cp = candidate.getAnnotation(ConstructorProperties.class);
			if (cp != null) {
				String[] names = cp.value();
				if (names.length != paramCount) {
					throw new IllegalStateException("Constructor annotated with @ConstructorProperties but not " +
							"corresponding to actual number of parameters (" + paramCount + "): " + candidate);
				}
				return names;
			}
			else {
				return null;
			}
		}
	}


	private enum FallbackMode {

		NONE,

		ASSIGNABLE_ELEMENT,

		TYPE_CONVERSION
	}

}
