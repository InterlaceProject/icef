/*	
 * NullaryFunctionElement.java 
 * 
 * Copyright (C) 2010 Roozbeh Farahbod
 *
 * Licensed under the Academic Free License version 3.0 
 *   http://www.opensource.org/licenses/afl-3.0.php
 *   http://www.coreasm.org/afl-3.0.php
 *
 * This file contains source code contributed by the European FP7 research project BIOMICS (Grant no. 318202)
 * Copyright (C) 2016 Daniel Schreckling, Eric Rothstein (BIOMICS) 
 *
 * Licensed under the Academic Free License version 3.0 
 *   http://www.opensource.org/licenses/afl-3.0.php
 * 
 *
 */

package org.coreasim.engine.absstorage;

import java.util.HashSet;
import java.util.List;
import java.util.Set;

/**
 * Base implementation of a nullary function, one that has no argument.
 * 
 * @author Roozbeh Farahbod
 *
 */
public class NullaryFunctionElement extends FunctionElement {

	/**
	 * 
	 */
	private static final long serialVersionUID = -8623645691779618736L;
	private Element value; 
	
	public NullaryFunctionElement() {
		super();
	}

	public NullaryFunctionElement(Element defaultValue) {
		super(defaultValue);
	}

	public Element getValue() {
		return value;
	}

	@Override
	public Set<Location> getLocations(String name) {
		Location loc = new Location(name, ElementList.NO_ARGUMENT);
		HashSet<Location> set = new HashSet<Location>();
		set.add(loc);
		return set;
	}

	@Override
	public Element getValue(List<? extends Element> args) {
		if (args.size() == 0)
			return value;
		else
			return Element.UNDEF;
	}

	/**
	 * If the list of arguments is empty, it sets the value of this function
	 * to the given value. Otherwise, does nothing.
	 * 
	 *  @param args list of arguments
	 *  @param value the new value of this function
	 *  
	 *  @see FunctionElement#setValue(List, Element)
	 */
	@Override
	public void setValue(List<? extends Element> args, Element value)
			throws UnmodifiableFunctionException {
		super.setValue(args, value);
		if (args.size() == 0)
			setValue(value);
	}

	/**
	 * Sets the new value of this function.
	 * 
	 * @param value an instance of {@link Element}.
	 */
	public void setValue(Element value) {
		this.value = value;
	}
}
