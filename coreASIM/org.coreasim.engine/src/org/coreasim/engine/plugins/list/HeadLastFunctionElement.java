/*	
 * HeadLastFunctionElement.java  	
 * 
 * Copyright (C) 2007 Roozbeh Farahbod
 *
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
 */
 
package org.coreasim.engine.plugins.list;

import java.util.List;

import org.coreasim.engine.ControlAPI;
import org.coreasim.engine.CoreASIMError;
import org.coreasim.engine.absstorage.Element;
import org.coreasim.engine.absstorage.ElementBackgroundElement;
import org.coreasim.engine.absstorage.Signature;
import org.coreasim.engine.plugins.collection.AbstractListElement;

/** 
 * Impelementation of head and last functions on lists.
 *   
 * @author  Roozbeh Farahbod
 * 
 */
public class HeadLastFunctionElement extends ListFunctionElement {
	
	/**
	 * 
	 */
	private static final long serialVersionUID = 1855644832297346478L;
	public static final String HEAD_FUNC_NAME = "head";
	public static final String LAST_FUNC_NAME = "last";
	
	protected Signature signature = null;
	protected final boolean isHead;
	
	public HeadLastFunctionElement(ControlAPI capi, boolean isHead) {
		super(capi);
		this.isHead = isHead;
	}

	/* (non-Javadoc)
	 * @see org.coreasm.engine.absstorage.FunctionElement#getValue(java.util.List)
	 */
	@Override
	public Element getValue(List<? extends Element> args) {
		if (!checkArguments(args))
			throw new CoreASIMError("Illegal arguments for " + (isHead ? HEAD_FUNC_NAME : LAST_FUNC_NAME) + ".");
		
		AbstractListElement list = (AbstractListElement)args.get(0);
		return (isHead ? list.head() : list.last());
	}

	@Override
	public Signature getSignature() {
		if (signature == null) {
			signature = new Signature();
			signature.setDomain(ListBackgroundElement.LIST_BACKGROUND_NAME);
			signature.setRange(ElementBackgroundElement.ELEMENT_BACKGROUND_NAME);
		}
		return signature;
	}
	
	/*
	 * Checks the arguments of the function
	 */
	protected boolean checkArguments(List<? extends Element> args) {
		return (args.size() == 1) && (args.get(0) instanceof AbstractListElement);
	}

}
