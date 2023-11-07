(* ::Package:: *)

BeginPackage["GRGeometry`"]

trigseries::usage = "trigseries[x] uses trignometric identities to simplify expression x";
expansion::usage = "expansion[x] ";
guucomp::usage ="not sure";
guu::usage = "guu[gdd_] computes the contravariant metric";
\[CapitalGamma]c::usage = "\[CapitalGamma]c[gdd,var] computes the Christoffel symbols for metric gdd with coordiante system var. expansionparam is a 3 element of the type {\[Epsilon]p,x,Order} that computes an expansion of variable \[Epsilon]p, around value x up to order Order"
RiemannTensor ::usage = "RiemannTensor[gdd, var, expansionparam] computes the Riemann tensor for metric gdd with coordinate system var. expansionparam is a 3 element of the type {\[Epsilon]p,x,Order} that computes an expansion of variable \[Epsilon]p, around value x up to order Order"
RicciTensor ::usage = "RicciTensor[gdd, var, expansionparam] computes the Ricci tensor for metric gdd with coordinate system var. expansionparam is a 3 element of the type {\[Epsilon]p,x,Order} that computes an expansion of variable \[Epsilon]p, around value x up to order Order"
RicciScalar ::usage = "RicciScalar[gdd, var, expansionparam] computes the Ricci scalar for metric gdd with coordinate system var. expansionparam is a 3 element of the type {\[Epsilon]p,x,Order} that computes an expansion of variable \[Epsilon]p, around value x up to order Order"
EinsteinTensor ::usage = "EinsteinTensor[gdd, var, expansionparam] computes the Einstein tensor for metric gdd with coordinate system var. expansionparam is a 3 element of the type {\[Epsilon]p,x,Order} that computes an expansion of variable \[Epsilon]p, around value x up to order Order"
detM::usage = "detM[gdd, var, expansionparam] computes determinant of metric gdd with coordinate system var. expansionparam is a 3 element of the type {\[Epsilon]p,x,Order} that computes an expansion of variable \[Epsilon]p, around value x up to order Order"
\[Epsilon]\[Mu]\[Nu]\[Sigma]\[Lambda]::usage = "\[Epsilon]\[Mu]\[Nu]\[Sigma]\[Lambda][gdd, var, expansionparam] computes covariant Levi-Civita tensor for the metric gdd with coordinate system var. expansionparam is a 3 element of the type {\[Epsilon]p,x,Order} that computes an expansion of variable \[Epsilon]p, around value x up to order Order"
contravariantlevi::usage = "contravariantlevi[gdd, var, expansionparam] computes contrariant Levi-Civita tensor for the metric gdd with coordinate system var. expansionparam is a 3 element of the type {\[Epsilon]p,x,Order} that computes an expansion of variable \[Epsilon]p, around value x up to order Order"
Riemanndddd::usage = "Riemanndddd[gdd, var, expansionparam] computes the Riemann tensor \!\(\*SubscriptBox[\(R\), \(\[Rho]\[Sigma]\[Mu]\[Nu]\)]\), for the metric gdd with coordinate system var. expansionparam is a 3 element of the type {\[Epsilon]p,x,Order} that computes an expansion of variable \[Epsilon]p, around value x up to order Order"
Riemannuudd::usage = "Riemannuudd[gdd, var, expansionparam] computes the Riemann tensor \!\(\*SubscriptBox[SuperscriptBox[\(R\), \(\[Rho]\[Sigma]\)], \(\[Mu]\[Nu]\)]\), for the metric gdd with coordinate system var. expansionparam is a 3 element of the type {\[Epsilon]p,x,Order} that computes an expansion of variable \[Epsilon]p, around value x up to order Order"
PontryaginScalar::usage = "PontryaginScalar[gdd, var, expansionparam] computes the Pontryagin scalar for the metric gdd with coordinate system var. expansionparam is a 3 element of the type {\[Epsilon]p,x,Order} that computes an expansion of variable \[Epsilon]p, around value x up to order Order"
trigseries[Z_]:=Z//.Union[{X'[\[Theta]]^2->1-X[\[Theta]]^2,X''[\[Theta]]->-X[\[Theta]],X'[\[Theta]]^4->(1-X[\[Theta]]^2)^2}]
conditionalExpansion ::usage ="test";
Begin["`Private`"]
expansion[x_,y_]:=Simplify[trigseries[Series[x,Sequence@@Transpose[{y[[All,1]],y[[All,2]],y[[All,3]]}]]]]
conditionalExpansion[expr_, param_: Automatic] := 
 If[param === Automatic, Simplify[expr], Simplify[expansion[expr, param]]]

(*Computes the contravariant metric*)
guu[gdd_, expansionparam_: Automatic] := conditionalExpansion[trigseries[Inverse[gdd]], expansionparam];
(*Computes the christoffel symbols*)
\[CapitalGamma]c[gdd_, var_, expansionparam_: Automatic] :=  
	Module[{guutemp,dim},
		guutemp = guu[gdd, expansionparam];
		dim = Length[var];
		conditionalExpansion[Table[trigseries[1/2 Sum[guutemp[[\[Lambda],\[Kappa]]]*(D[gdd[[\[Kappa],\[Mu]]],var[[\[Nu]]]]+D[gdd[[\[Kappa],\[Nu]]],var[[\[Mu]]]]-D[gdd[[\[Mu],\[Nu]]],var[[\[Kappa]]]]),{\[Kappa],1,dim}]],{\[Lambda],1,dim},{\[Mu],1,dim},{\[Nu],1,dim}], expansionparam]
	]
RiemannTensor[gdd_, var_, expansionparam_: Automatic] := 
	Module[{\[CapitalGamma]ctemp,dim},
		\[CapitalGamma]ctemp = \[CapitalGamma]c[gdd,var,expansionparam];
		dim = Length[var];
	conditionalExpansion[Table[trigseries[D[\[CapitalGamma]ctemp[[\[Rho],\[Nu],\[Sigma]]],var[[\[Mu]]]]-D[\[CapitalGamma]ctemp[[\[Rho],\[Mu],\[Sigma]]],var[[\[Nu]]]]+Sum[\[CapitalGamma]ctemp[[\[Rho],\[Mu],\[Lambda]]] \[CapitalGamma]ctemp[[\[Lambda],\[Nu],\[Sigma]]],{\[Lambda],dim}]-Sum[\[CapitalGamma]ctemp[[\[Rho],\[Nu],\[Lambda]]] \[CapitalGamma]ctemp[[\[Lambda],\[Mu],\[Sigma]]],{\[Lambda],dim}]],{\[Rho],dim},{\[Sigma],dim},{\[Mu],dim},{\[Nu],dim}], expansionparam]
	]

RicciTensor[gdd_, var_, expansionparam_: Automatic] := 
	Module[{RiemannTensortemp,dim},
		RiemannTensortemp = RiemannTensor[gdd,var,expansionparam];
		dim = Length[var];
		conditionalExpansion[Table[trigseries[Sum[RiemannTensortemp[[\[Rho],\[Mu],\[Rho],\[Nu]]],{\[Rho],dim}]],{\[Mu],dim},{\[Nu],dim}],expansionparam]
		]

RicciScalar[gdd_, var_, expansionparam_: Automatic] :=
	Module[{RicciTensortemp,guutemp,dim},
		RicciTensortemp = RicciTensor[gdd, var, expansionparam];
		guutemp = guu[gdd, expansionparam];
		dim = Length[var];
		conditionalExpansion[trigseries[Sum[guutemp[[\[Mu],\[Nu]]] RicciTensortemp[[\[Mu],\[Nu]]],{\[Mu],dim},{\[Nu],dim}]]]
		]

EinsteinTensor[gdd_, var_, expansionparam_: Automatic] := 
	Module[{RicciTensortemp,RicciScalartemp,dim},
		RicciTensortemp = RicciTensor[gdd, var, expansionparam];
		RicciScalartemp = RicciScalar[gdd,var, expansionparam];
		dim = Length[var];
		conditionalExpansion[Table[trigseries[RicciTensortemp[[\[Mu],\[Nu]]]-1/2 gdd[[\[Mu],\[Nu]]] RicciScalartemp],{\[Mu],dim},{\[Nu],dim}]]
		]
		
detM[gdd_, var_, expansionparam_: Automatic] :=
	Module[{dim},
		dim = Length[var];
		conditionalExpansion[Table[trigseries[Det[gdd]],{\[Mu],dim},{\[Nu],dim}]]
		]
		
\[Epsilon]\[Mu]\[Nu]\[Sigma]\[Lambda][gdd_, var_, expansionparam_: Automatic] :=
	Module[{RicciTensortemp,RicciScalartemp,detMtemp,dim},
		detMtemp= detM[gdd, var, expansionparam];
		dim = Length[var];
		conditionalExpansion[trigseries[Sqrt[-detMtemp]LeviCivitaTensor[4]]]
		]
		
contravariantlevi[gdd_, var_, expansionparam_: Automatic] :=
	Module[{guutemp,\[Epsilon]\[Mu]\[Nu]\[Sigma]\[Lambda]temp,dim},
		guutemp = guu[gdd, expansionparam];
		\[Epsilon]\[Mu]\[Nu]\[Sigma]\[Lambda]temp= \[Epsilon]\[Mu]\[Nu]\[Sigma]\[Lambda][gdd, var, expansionparam];
		dim = Length[var];
		conditionalExpansion[Table[trigseries[Sum[guutemp[[\[Alpha]0,\[Mu]]]guutemp[[\[Beta],\[Nu]]]guutemp[[\[Gamma],\[Sigma]]]guutemp[[\[Delta],\[Lambda]]]\[Epsilon]\[Mu]\[Nu]\[Sigma]\[Lambda]temp[[\[Alpha]0,\[Beta],\[Gamma],\[Delta]]],{\[Alpha]0,1,4},{\[Beta],1,4},{\[Gamma],1,4},{\[Delta],1,4}]],{\[Mu],1,4},{\[Nu],1,4},{\[Sigma],1,4},{\[Lambda],1,4}]]
		]

Riemanndddd[gdd_, var_, expansionparam_: Automatic] :=
	Module[{RiemannTensortemp,dim},
		RiemannTensortemp = RiemannTensor[gdd,var, expansionparam];
		dim = Length[var];
		conditionalExpansion[Table[trigseries[Sum[gdd[[\[Rho],\[Lambda]]]RiemannTensortemp[[\[Lambda],\[Sigma],\[Mu],\[Nu]]],{\[Lambda],1,dim}]],{\[Rho],dim},{\[Sigma],dim},{\[Mu],dim},{\[Nu],dim}]]
		]

Riemannuudd[gdd_, var_, expansionparam_: Automatic] :=
	Module[{guutemp,RiemannTensortemp,dim},
		guutemp = guu[gdd, expansionparam];
		RiemannTensortemp = RiemannTensor[gdd,var, expansionparam];
		dim = Length[var];
		conditionalExpansion[Table[trigseries[Sum[guutemp[[\[Sigma],\[Lambda]]]RiemannTensortemp[[\[Rho],\[Lambda],\[Mu],\[Nu]]],{\[Lambda],dim}]],{\[Rho],dim},{\[Sigma],dim},{\[Mu],dim},{\[Nu],dim}]]
		]										
																														
PontryaginScalar[gdd_, var_, expansionparam_: Automatic] :=
	Module[{Riemannddddtemp, Riemannuuddtemp,contravariantlevitemp,dim},
		contravariantlevitemp = contravariantlevi[gdd, var,expansionparam];
		Riemannddddtemp = Riemanndddd[gdd, var,expansionparam];
		Riemannuuddtemp = Riemannuudd[gdd, var,expansionparam];
		dim = Length[var];
		conditionalExpansion[trigseries[Sum[1/2 Riemannddddtemp[[b,a,c,d]]contravariantlevitemp[[c,d,e,f]]Riemannuuddtemp[[a,b,e,f]],{a,1,4},{b,1,4},{c,1,4},{d,1,4},{e,1,4},{f,1,4}]]]
		]
		
Ctensor1[gdd_, var_, expansionparam_: Automatic] :=
	Module[{Riemannddddtemp, Riemannuuddtemp,contravariantlevitemp,dim},
		contravariantlevitemp =contravariantlevi[gdd, var,expansionparam];
		Riemannddddtemp = Riemanndddd[gdd, var,expansionparam];
		Riemannuuddtemp = Riemannuudd[gdd, var,expansionparam];
		dim = Length[var];
		conditionalExpansion[trigseries[Sum[contravariantlevitemp[[b,a,e,f]]Riemannuuddtemp[[c,d,e,f]],{a,1,4},{b,1,4},{c,1,4},{d,1,4},{e,1,4},{f,1,4}]]]
		]														
End[]

EndPackage[]

