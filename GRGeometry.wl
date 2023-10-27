(* ::Package:: *)

BeginPackage["GRGeometry`"]

MyFunction1::usage = "MyFunction1[x] computes some function of x.";
MyFunction2::usage = "MyFunction2[x, y] computes some function of x and y.";
trigseries::usage = "trigseries[x] uses trignometric identities to simplify expression x";
expansion::usage = "expansion[x] ";
guucomp::usage ="not sure";
guu::usage = "guu[gdd_] computes the contravariant metric";
\[CapitalGamma]c::usage = "\[CapitalGamma]c[gdd,var] computes the Christoffel symbols for metric gdd with coordiante system var. expansionparam is a 3 element of the type {\[Epsilon]p,x,Order} that computes an expansion of variable \[Epsilon]p, around value x up to order Order"
RiemannTensor ::usage = "RiemannTensor[gdd, var, expansionparam] computes the Riemann tensor for metric gdd with coordinate system var. expansionparam is a 3 element of the type {\[Epsilon]p,x,Order} that computes an expansion of variable \[Epsilon]p, around value x up to order Order"
RicciTensor ::usage = "RicciTensor[gdd, var, expansionparam] computes the Ricci tensor for metric gdd with coordinate system var. expansionparam is a 3 element of the type {\[Epsilon]p,x,Order} that computes an expansion of variable \[Epsilon]p, around value x up to order Order"
RicciScalar ::usage = "RicciScalar[gdd, var, expansionparam] computes the Ricci scalar for metric gdd with coordinate system var. expansionparam is a 3 element of the type {\[Epsilon]p,x,Order} that computes an expansion of variable \[Epsilon]p, around value x up to order Order"
EinsteinTensor ::usage = "EinsteinTensor[gdd, var, expansionparam] computes the Einstein tensor for metric gdd with coordinate system var. expansionparam is a 3 element of the type {\[Epsilon]p,x,Order} that computes an expansion of variable \[Epsilon]p, around value x up to order Order"
trigseries[Z_]:=Z//.Union[{X'[\[Theta]]^2->1-X[\[Theta]]^2,X''[\[Theta]]->-X[\[Theta]],X'[\[Theta]]^4->(1-X[\[Theta]]^2)^2}]
Begin["`Private`"]

MyFunction1[x_] := x^2
MyFunction2[x_, y_] := x + y
(*trigseries[Z_]:=Z//.Union[{X'[\[Theta]]^2->1-X[\[Theta]]^2,X''[\[Theta]]->-X[\[Theta]],X'[\[Theta]]^4->(1-X[\[Theta]]^2)^2}]*)
expansion[x_,y_]:=Simplify[trigseries[Series[x,{y[[1]],y[[2]],y[[3]]}]]]
conditionalExpansion[expr_, param_: Automatic] := 
 If[param === Automatic, Simplify[expr], Simplify[expansion[expr, param]]]

(*Computes the contravariant metric*)
guu[gdd_, expansionparam_: Automatic] := conditionalExpansion[trigseries[Inverse[gdd]], expansionparam];
(*Computes the christoffel symbols*)
\[CapitalGamma]c[gdd_, var_, expansionparam_: Automatic] :=  
	Module[{guutemp,dim},
		guutemp = guu[gdd, expansionparam];
		dim = Length[var];
		conditionalExpansion[Table[trigseries[1/2 Sum[guutemp[[\[Lambda],\[Kappa]]] (D[gdd[[\[Kappa],\[Mu]]],var[[\[Nu]]]]+D[gdd[[\[Kappa],\[Nu]]],var[[\[Mu]]]]-D[gdd[[\[Mu],\[Nu]]],var[[\[Kappa]]]]),{\[Kappa],dim}]],{\[Lambda],dim},{\[Mu],dim},{\[Nu],dim}], expansionparam]
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

End[]

EndPackage[]

