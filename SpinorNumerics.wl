(* ::Package:: *)

(* ::Chapter:: *)
(*SpinorNumerics*)


BeginPackage["SpinorNumerics`",{"SpinorBuildingBlocks`"}]


(*In order to allow the package to be reloaded we unprotect and clear all the symbol definitions*)
Unprotect@@Names["SpinorNumerics`*"];
ClearAll@@Names["SpinorNumerics`*"];


(* ::Section:: *)
(*Function description*)


GenSpinors::usage="GenSpinors[{{\!\(\*SubscriptBox[\(p\), \(1\)]\),...,\!\(\*SubscriptBox[\(p\), \(n\)]\)},{\!\(\*SubscriptBox[\(q\), \(1\)]\),...,\!\(\*SubscriptBox[\(q\), \(m\)]\)}},{Options}] generates numerical values for the spinors corresponding to on-shell, conserved, complex kinematics. The labels \!\(\*SubscriptBox[\(p\), \(i\)]\) correspond to massive particles and the \!\(\*SubscriptBox[\(q\), \(j\)]\) to massless ones. The input GenSpinors[{\!\(\*SubscriptBox[\(k\), \(1\)]\),...,\!\(\*SubscriptBox[\(k\), \(m\)]\)}] is also allowed and will generate spinors for massive particles if AllMassless is set to False, and all massless if it is set to True. The function allows for the following options: {AllMassless,DisplaySpinors,Parametric,ParameterName,ParameterRange,RationalKinematics,Seed,SetMomentum,Type3pt,SameMassess}. For further details type ?OptionName."
AllMassless::usage="AllMassless is a boolean option for GenSpinors, default is False, If set to True all the entries of GenSpinors are considered as massless. AllMassless->True is equivalent to using the input GenSpinors[{{},{\!\(\*SubscriptBox[\(p\), \(1\)]\),...,\!\(\*SubscriptBox[\(p\), \(n\)]\)}}]."
(*Dimension::usage="Dimension is an option for GenSpinors. It specifies the dimension of the generated kinematics. Default is 6, allowed are 6 and 4."*)
DisplaySpinors::usage="DisplaySpinors is an option for GenSpinors. If set to True the generated kinematics is displayed. Default is False."
Parametric::usage="Parametric is an option for GenSpinors. If set to True the kinematics is generated in terms of a minimal set of independent variables (3n-10 in 4 dimensions and 5n-15 is six-dimensions) instead of numbers. Default is False."
ParameterName::usage="ParameterName is an option for GenSpinors. It allows to choose a custom label for the independent variables in terms of which the kinematics is defined if Parametric->True. Default is $par."
ParameterRange::usage="ParameterRange is an option for GenSpinors. It allows to set the range in which the independent variables are chosen when numerical values of the kinmeatics are required. Default is 10000."
RationalKinematics::usage="RationalKinematics is an option for GenSpinors. It allows to to chose between rational (True) and real (False) kinematics. Default is True. "
Seed::usage="Seed is an option for GenSpinors. It allows to set a seed for SeedRandom so that the randomly generated kinematics can be rederived if necessary. Default is False, but any integer number is admitted."
RandomSpinors::usage="RandomSpinors is an option for GenSpinors. It allows to generate a random set of spinors, which lead to on-shell momenta but these do not satisfy momentum conservation"
$par::usage="Protected symbol. It is the default name of the variables in GenSpinors."
SetMomentum::usage="SetMomentum is an option for GenSpinors. It allows to set the numeric componenst of the first spinors to specific values. It allows as values spinor components as well as labels of already generated momenta."
Type3pt::usage="Type3pt is an option for GenSpinors. When generating three-particle kinematics it allows to specify which king of brackets, angle or square, are non-vanishing. Default value is $angle."
SameMasses::usage="SameMasses is an option for GenSpinors, which allows to set masses of different labels to be the same. Input form is either a list of labels {p1,p2,...,pn} or a list of lists {{\!\(\*SubscriptBox[\(p\), \(1\)]\),...,\!\(\*SubscriptBox[\(p\), \(n\)]\)},{\!\(\*SubscriptBox[\(p\), \(2\)]\),...,\!\(\*SubscriptBox[\(p\), \(k\)]\)},...} which sets \!\(\*SubscriptBox[\(m\), \(1\)]\)=...=\!\(\*SubscriptBox[\(m\), \(n\)]\), \!\(\*SubscriptBox[\(m\), \(2\)]\)=...=\!\(\*SubscriptBox[\(m\), \(k\)]\)"
(*MomMat4DN::usage="MomMat4DN[label][type] is the numeric momentum written as a matrix in spinor representation. Type is either $up or $down and represents the position of the spinor indices."
Mom4DN::usage="Mom4DN[label] is the four-dimensional numeric momentum vector associated to label."
MomMat6DN::usage="MomMat6DN[label][type] is the six-dimensional momentum matrix. The argument type represents the position of the Lorentz indices."
Mom6DN::usage="Mom6DN[label] is the six-dimensional numeric momentum vector associated to label."
PauliSix::usage="PauliSix[i] is the i'th six-dimensional pauli matrix."*)
MomToSpinors::usage="MomToSpinors[vector,label] generates the spinors associated to the given vector. This can be four-dimensional massless or massive or six-dimensional. The optional argument label allows to store the generated values of the spinors."
ClearKinematics::usage="ClearKinematics clears all the so far generated and stored numerical values for the kinematics."
(*ExtramassN::usage="ExtramassN[label] is the numerical equivalent of Extramass[label]."
ExtramasstildeN::usage="ExtramasstildeN[label] is the numerical equivalent of Extramasstilde[label]."
*)
ToNum::usage="ToNum[exp] return numeric value of exp. It requires some kind of numerical kinematics to be generated first using GenSpinors."



(* ::Section:: *)
(*Private context begins here*)


Begin["`Private`"]


(* ::Section:: *)
(*Auxiliary functions*)


(* ::Subsection::Closed:: *)
(*Infycheck*)


Attributes[Infycheck]={HoldAll};
Infycheck[x_]:=TrueQ[Quiet[Check[x,$Failed,{PowerMod::ninv,Power::infy,Infinity::indet,Power::indet}],{PowerMod::ninv,Power::infy,Infinity::indet,Power::indet}]==$Failed];


(* ::Subsection::Closed:: *)
(*ClearDownValues*)


ClearDownValues[f_]:=DownValues[f]=DeleteCases[DownValues[f],_?(FreeQ[First[#],Pattern]&)];


(* ::Subsection::Closed:: *)
(*ClearSubvalues*)


(*ClearSubValues[f_]:=(SubValues[f]=DeleteCases[SubValues[f],_?(FreeQ[First[#],HoldPattern[f[Pattern]]]&)]);*)

ClearSubValues[f_]:=(SubValues[f]=DeleteCases[SubValues[f],_?(FreeQ[First[#],Pattern]&)]);


(* ::Subsection::Closed:: *)
(*InverseDot*)


InverseDot[x_List,y_List]:=Table[i*j,{i,x},{j,y}];


(* ::Section:: *)
(*Kinematic generation in all the subcases*)


(*Since the algorithm is supposed to be as general as possible, there are a lot of options corresponding to lots
of different cases for the kinematics which the user might want to generate. We have a function for every specific subcase.
These functions are in this section*)


(* ::Subsection::Closed:: *)
(*KinematicCheck*)


(*KinematicCheck checks that the generated kinematic makes sense*)


Attributes[KinematicCheck]={HoldAll};
KinematicCheck[x_]:=TrueQ[Quiet[Check[x,$Failed,{PowerMod::ninv,Power::infy,Infinity::indet,Power::indet,GenSpinors::unsolvablekinematics}],{PowerMod::ninv,Power::infy,Infinity::indet,Power::indet,GenSpinors::unsolvablekinematics}]==$Failed];


(* ::Subsection:: *)
(*ClearDependentKinematics*)


(*This is just the same as ClearKinematics but private and only clears the dependent kinematics leaving the fundamental building blocks (SpinorUndotN,SpinorDotN,ExtramassN,ExtramasstildeN) intact*)

ClearDependentKinematics[]:=Block[{},

(*Clearing functions with DownValues*)
ClearDownValues[#]&/@{SpinorAngleBracketN,SpinorSquareBracketN,Mom4DN,ChainN,SNum,mpN};

(*Clearing functions with SubValues*)
(*ClearSubValues[#]&/@{SpinorUndotN,SpinorDotN,ExtramassN,ExtramasstildeN,MomMat4DN};*)
ClearSubValues[#]&/@{MomMat4DN};

];


(* ::Subsection::Closed:: *)
(*ClearKinematics*)


(*ClearKinematics:=(ClearSubValues[SpinorUndotN];
ClearSubValues[SpinorDotN];
ClearSubValues[ExtramassN];
ClearSubValues[ExtramasstildeN];
ClearDownValues[SpinorAngleBracketN];
ClearDownValues[SpinorSquareBracketN];

ClearDependentKinematics[];
);*)


ClearKinematics:=Block[{},

(*Clearing functions with DownValues*)
ClearDownValues[#]&/@{SpinorAngleBracketN,SpinorSquareBracketN,Mom4DN,ChainN,SNum,mpN};

(*Clearing functions with SubValues*)
ClearSubValues[#]&/@{SpinorUndotN,SpinorDotN,ExtramassN,ExtramasstildeN,MomMat4DN};

];


(* ::Subsection:: *)
(*Auxiliary functions for GenSpinors*)


(* ::Subsubsection::Closed:: *)
(*GenerateKinematics*)


(*Options[GenerateKinematics]={RationalKinematics->True,ParameterRange->1000,Parametric->False,ParameterName->$par}
{RationalKinematics->True,ParameterRange->1000,Parametric->False,ParameterName->$par}
GenerateKinematics[total_Integer,fourD_Integer,OptionsPattern[]]:=Catch[Module[{\[Xi],\[Eta],\[Xi]t,\[Eta]t,n,random,system,sol,par,count,out},

(*First we check that total \[GreaterEqual] fourD+2 *)
If[total<fourD+2,Throw["Please check input, impossible kinematics has been requested."];
];

n=total;

(*Next fix the components of the four-dimensional spinors*)
Do[
\[Xi][i+n]=0;
\[Eta][i+n]=0;
\[Eta]t[i+n]=\[Eta]t[i]*\[Xi]t[i+n]/\[Xi]t[i];
,{i,n-fourD+1,n}];

(*Based on the options given assign rational rather than real kinematics and the range of the interval over which to generate it*)
If[TrueQ[OptionValue[RationalKinematics]],
random:=RandomInteger[OptionValue[ParameterRange]],
random:=RandomReal[OptionValue[ParameterRange]];
];

(*Next generate the random spinor components. First the 3n*)

Do[
\[Xi][i+n]=random;
\[Eta][i+n]=random;
\[Eta]t[i+n]=random;
,{i,n-fourD}];

(*Then the 9:*)
\[Eta]t[1]=random;
\[Eta]t[2]=random;
\[Xi]t[1]=random;
\[Xi]t[2]=random;
\[Xi][3]=random;
\[Eta][3]=random;
\[Xi][4]=random;
\[Eta][1]=random;
\[Eta][4]=random;

(*Depending on whether a parametric expression is required or not, we set the other variables to either a parameter or a number*)

If[TrueQ[OptionValue[Parametric]],
(*Parametric components*)
par=OptionValue[ParameterName];
\[Eta]t[3]=par[1];
\[Eta]t[4]=par[2];
\[Xi]t[4]=par[3];
\[Xi]t[3+n]=par[4];
\[Xi]t[4+n]=par[5];
count=6;
Do[
\[Xi][i]=par[count++];
\[Eta][i]=par[count++];
\[Xi]t[i]=par[count++];
\[Eta]t[i]=par[count++];
\[Xi]t[i+n]=par[count++];
,{i,5,n}];
,
(*Numeric components*)
\[Eta]t[3]=random;
\[Eta]t[4]=random;
\[Xi]t[4]=random;
\[Xi]t[3+n]=random;
\[Xi]t[4+n]=random;
Do[
\[Xi][i]=random;
\[Eta][i]=random;
\[Xi]t[i]=random;
\[Eta]t[i]=random;
\[Xi]t[i+n]=random;
,{i,5,n}];
];

(*Generate momentum conservation:*)
system={Sum[\[Xi][i]\[Xi]t[i],{i,2*n}]==0,Sum[\[Xi][i]\[Eta]t[i],{i,2*n}]==0,Sum[\[Eta][i]\[Xi]t[i],{i,2*n}]==0,Sum[\[Eta][i]\[Eta]t[i],{i,2*n}]==0,Sum[\[Xi][i]\[Eta][i+n]-\[Xi][i+n]\[Eta][i],{i,n}]==0,Sum[\[Eta]t[i+n]\[Xi]t[i]-\[Xi]t[i+n]\[Eta]t[i],{i,n}]==0};

(*Solve momentum conservation*)
sol=Solve[system,{\[Xi][1],\[Xi][2],\[Eta][2],\[Xi]t[3],\[Xi]t[1+n],\[Xi]t[2+n]}];

(*Safety check*)
If[sol==={},
Message[GenSpinors::unsolvablekinematics];
Throw[$Failed],
sol=sol//First;
];

(*Now that all the spinor components have been generated we just need to return them in a suitably packaged output. The oupt will be divided into 6D and 4D and then further into {\[Lambda],\[Lambda]t,\[Lambda]',\[Lambda]t'}. Notice that these spinors will be considered all having upper indices so the spinors will be like \[Lambda]=\[LeftAngleBracket]\[Lambda]| and \[Lambda]t=|\[Lambda]t].*)

(*List of the 6D spinors*)
out=Table[{{\[Xi][i],\[Eta][i]},{\[Xi]t[i],\[Eta]t[i]},{\[Xi][i+n],\[Eta][i+n]},{\[Xi]t[i+n],\[Eta]t[i+n]}},{i,n-fourD}];

(*Then append the table of the 4D components and replece the solutions to momentum conservation*)
out={out,Table[{{\[Xi][i],\[Eta][i]},{\[Xi]t[i],\[Eta]t[i]}},{i,n-fourD+1,n}]}/.sol;

Return[out];
];
];*)


(*Options[GenerateKinematics]={RationalKinematics->True,ParameterRange->1000,Parametric->False,ParameterName->$par}
{RationalKinematics->True,ParameterRange->1000,Parametric->False,ParameterName->$par}

GenerateKinematics[total_Integer,fourD_Integer,OptionsPattern[]]:=Catch[Module[{\[Xi],\[Eta],\[Xi]t,\[Eta]t,n,random,system,sol,par,count,out},

(*First we check that total \[GreaterEqual] fourD+2 *)
If[total<fourD+2,Throw["Please check input, impossible kinematics has been requested."];
];

n=total;

(*Next fix the components of the four-dimensional spinors*)
Do[
\[Xi][i+n]=0;
\[Eta][i+n]=0;
\[Eta]t[i+n]=\[Eta]t[i]*\[Xi]t[i+n]/\[Xi]t[i];
,{i,n-fourD+1,n}];

(*Based on the options given assign rational rather than real kinematics and the range of the interval over which to generate it*)
If[TrueQ[OptionValue[RationalKinematics]],
random:=RandomInteger[OptionValue[ParameterRange]],
random:=RandomReal[OptionValue[ParameterRange]];
];

(*Next generate the random spinor components. First the 3n*)

Do[
\[Xi][i+n]=random;
\[Eta][i+n]=random;
\[Eta]t[i+n]=random;
,{i,n-fourD}];

(*Then the 9:*)
\[Eta]t[1]=random;
\[Eta]t[2]=random;
\[Xi]t[1]=random;
\[Xi]t[2]=random;
\[Xi][3]=random;
\[Eta][3]=random;
\[Xi][4]=random;
\[Eta][1]=random;
\[Eta][4]=random;

(*Depending on whether a parametric expression is required or not, we set the other variables to either a parameter or a number*)

If[TrueQ[OptionValue[Parametric]],
(*Parametric components*)
par=OptionValue[ParameterName];
\[Eta]t[3]=par[1];
\[Eta]t[4]=par[2];
\[Xi]t[4]=par[3];
\[Xi]t[3+n]=par[4];
\[Xi]t[4+n]=par[5];
count=6;
Do[
\[Xi][i]=par[count++];
\[Eta][i]=par[count++];
\[Xi]t[i]=par[count++];
\[Eta]t[i]=par[count++];
\[Xi]t[i+n]=par[count++];
,{i,5,n}];
,
(*Numeric components*)
\[Eta]t[3]=random;
\[Eta]t[4]=random;
\[Xi]t[4]=random;
\[Xi]t[3+n]=random;
\[Xi]t[4+n]=random;
Do[
\[Xi][i]=random;
\[Eta][i]=random;
\[Xi]t[i]=random;
\[Eta]t[i]=random;
\[Xi]t[i+n]=random;
,{i,5,n}];
];

(*Generate momentum conservation:*)
system={Sum[\[Xi][i]\[Xi]t[i],{i,2*n}]==0,Sum[\[Xi][i]\[Eta]t[i],{i,2*n}]==0,Sum[\[Eta][i]\[Xi]t[i],{i,2*n}]==0,Sum[\[Eta][i]\[Eta]t[i],{i,2*n}]==0,Sum[\[Xi][i]\[Eta][i+n]-\[Xi][i+n]\[Eta][i],{i,n}]==0,Sum[\[Eta]t[i+n]\[Xi]t[i]-\[Xi]t[i+n]\[Eta]t[i],{i,n}]==0};

(*Solve momentum conservation*)
sol=Solve[system,{\[Xi][1],\[Xi][2],\[Eta][2],\[Xi]t[3],\[Xi]t[1+n],\[Xi]t[2+n]}];

(*Safety check*)
If[sol==={},
Message[GenSpinors::unsolvablekinematics];
Throw[$Failed],
sol=sol//First;
];

(*Now that all the spinor components have been generated we just need to return them in a suitably packaged output. The oupt will be divided into 6D and 4D and then further into {\[Lambda],\[Lambda]t,\[Lambda]',\[Lambda]t'}. Notice that these spinors will be considered all having upper indices so the spinors will be like \[Lambda]=\[LeftAngleBracket]\[Lambda]| and \[Lambda]t=|\[Lambda]t].*)

(*List of the 6D spinors*)
out=Table[{{\[Xi][i],\[Eta][i]},{\[Xi]t[i],\[Eta]t[i]},{\[Xi][i+n],\[Eta][i+n]},{\[Xi]t[i+n],\[Eta]t[i+n]}},{i,n-fourD}];

(*Then append the table of the 4D components and replece the solutions to momentum conservation*)
out={out,Table[{{\[Xi][i],\[Eta][i]},{\[Xi]t[i],\[Eta]t[i]}},{i,n-fourD+1,n}]}/.sol;

Return[out];
];
];*)


(*First attempt at mixed kinematics, works nicely, but produces irrational kinematics...*)

(*Options[GenerateKinematics]={RationalKinematics->True,ParameterRange->1000,Parametric->False,ParameterName->$par}
{RationalKinematics->True,ParameterRange->1000,Parametric->False,ParameterName->$par}

(*Samemass is a list of integers representing the number of masses which have been requested as to be the same*)

GenerateKinematics[total_Integer,fourD_Integer,samemass_List,OptionsPattern[]]:=Catch[Module[{\[Xi],\[Eta],\[Xi]t,\[Eta]t,n,random,system,sol,par,count,out},

(*First we check that total \[GreaterEqual] fourD+2 *)
If[total<fourD+2,Throw["Please check input, impossible kinematics has been requested."];
];

(*The number of masses required to be the same must be less or equal to the total number of masses*)
If[total-fourD<Total@samemass,Throw["Please check input, impossible kinematics has been requested."];
];

n=total;

(*Next fix the components of the four-dimensional massless spinors*)
Do[
\[Xi][i+n]=0;
\[Eta][i+n]=0;
\[Eta]t[i+n]=\[Eta]t[i]*\[Xi]t[i+n]/\[Xi]t[i];
,{i,n-fourD+1,n}];
(*Do[
\[Xi][i+n]=0;
\[Eta][i+n]=0;
\[Eta]t[i+n]=0;
\[Xi]t[i+n]=0;
,{i,n-fourD+1,n}];*)

(*Based on the options given assign rational rather than real kinematics and the range of the interval over which to generate it*)
If[TrueQ[OptionValue[RationalKinematics]],
random:=RandomInteger[OptionValue[ParameterRange]],
random:=RandomReal[OptionValue[ParameterRange]];
];

(*Next generate the random spinor components. First the 3n*)

Do[
\[Xi][i+n]=random;
\[Eta][i+n]=random;
\[Eta]t[i+n]=random;
,{i,n-fourD}];

(*Then the 9 + the two for which we do not solve momcon in 4d:*)
\[Eta]t[1]=random;
\[Eta]t[2]=random;
\[Xi]t[1]=random;
\[Xi]t[2]=random;
\[Xi][3]=random;
\[Eta][3]=random;
\[Xi][4]=random;
\[Eta][1]=random;
\[Eta][4]=random;
\[Xi]t[1+n]=random;
\[Xi]t[2+n]=random;

(*Depending on whether a parametric expression is required or not, we set the other variables to either a parameter or a number*)

If[TrueQ[OptionValue[Parametric]],
(*Parametric components*)
par=OptionValue[ParameterName];
\[Eta]t[3]=par[1];
\[Eta]t[4]=par[2];
\[Xi]t[4]=par[3];
\[Xi]t[3+n]=par[4];
\[Xi]t[4+n]=par[5];
count=6;
Do[
\[Xi][i]=par[count++];
\[Eta][i]=par[count++];
\[Xi]t[i]=par[count++];
\[Eta]t[i]=par[count++];
\[Xi]t[i+n]=par[count++];
,{i,5,n}];
,
(*Numeric components*)
\[Eta]t[3]=random;
\[Eta]t[4]=random;
\[Xi]t[4]=random;
\[Xi]t[3+n]=random;
\[Xi]t[4+n]=random;
Do[
\[Xi][i]=random;
\[Eta][i]=random;
\[Xi]t[i]=random;
\[Eta]t[i]=random;
\[Xi]t[i+n]=random;
,{i,5,n}];
];

(*Fix the required msasses to be the same*)
count=1;
Do[
(*\[Xi]t[count+n]=random;*)
Do[
\[Xi]t[i+n]=(-\[Eta][-1+i+n] \[Eta]t[-1+i+n] \[Xi][-1+i] \[Xi]t[-1+i]+\[Eta][-1+i] \[Eta]t[-1+i+n] \[Xi][-1+i+n] \[Xi]t[-1+i]+\[Eta][i+n] \[Eta]t[i+n] \[Xi][i] \[Xi]t[i]-\[Eta][i] \[Eta]t[i+n] \[Xi][i+n] \[Xi]t[i]+\[Eta][-1+i+n] \[Eta]t[-1+i] \[Xi][-1+i] \[Xi]t[-1+i+n]-\[Eta][-1+i] \[Eta]t[-1+i] \[Xi][-1+i+n] \[Xi]t[-1+i+n])/(\[Eta]t[i] (\[Eta][i+n] \[Xi][i]-\[Eta][i] \[Xi][i+n]));
,{i,count+1,count+k-1}];
count=count+k;
,{k,samemass}];

(*Generate momentum conservation:*)
system={Sum[\[Xi][i]\[Xi]t[i],{i,2*n}]==0,Sum[\[Xi][i]\[Eta]t[i],{i,2*n}]==0,Sum[\[Eta][i]\[Xi]t[i],{i,2*n}]==0,Sum[\[Eta][i]\[Eta]t[i],{i,2*n}]==0(*,Sum[\[Xi][i]\[Eta][i+n]-\[Xi][i+n]\[Eta][i],{i,n}]==0,Sum[\[Eta]t[i+n]\[Xi]t[i]-\[Xi]t[i+n]\[Eta]t[i],{i,n}]==0*)};

Table[{\[Xi][i],\[Xi]t[i],\[Eta][i],\[Eta]t[i]},{i,2n}]//Echo;
(*Solve momentum conservation*)
sol=Solve[system,{\[Xi][1],\[Xi][2],\[Eta][2],\[Xi]t[3](*,\[Xi]t[1+n],\[Xi]t[2+n]*)}];

(*Safety check*)
If[sol==={},
Message[GenSpinors::unsolvablekinematics];
Throw[$Failed],
sol=sol//First;
];

(*Now that all the spinor components have been generated we just need to return them in a suitably packaged output. The oupt will be divided into 6D and 4D and then further into {\[Lambda],\[Lambda]t,\[Lambda]',\[Lambda]t'}. Notice that these spinors will be considered all having upper indices so the spinors will be like \[Lambda]=\[LeftAngleBracket]\[Lambda]| and \[Lambda]t=|\[Lambda]t].*)

(*List of the 6D spinors*)
out=Table[{{\[Xi][i],\[Eta][i]},{\[Xi]t[i],\[Eta]t[i]},{\[Xi][i+n],\[Eta][i+n]},{\[Xi]t[i+n],\[Eta]t[i+n]}},{i,n-fourD}];

(*Then append the table of the 4D components and replece the solutions to momentum conservation*)
out={out,Table[{{\[Xi][i],\[Eta][i]},{\[Xi]t[i],\[Eta]t[i]}},{i,n-fourD+1,n}]}/.sol;


Return[out];
];
];*)


(*Second attempt, improved but beyond a certain number of equal masses square roots appear again*)

(*Options[GenerateKinematics]={RationalKinematics->True,ParameterRange->1000,Parametric->False,ParameterName->$par}
{RationalKinematics->True,ParameterRange->1000,Parametric->False,ParameterName->$par}

(*Samemass is a list of integers representing the number of masses which have been requested as to be the same*)

GenerateKinematics[total_Integer,fourD_Integer,samemass_List,OptionsPattern[]]:=Catch[Module[{\[Xi],\[Eta],\[Xi]t,\[Eta]t,n,random,system,sol,par,count,out},

(*First we check that total \[GreaterEqual] fourD+2 *)
If[total<fourD+2,Throw["Please check input, impossible kinematics has been requested."];
];

(*The number of masses required to be the same must be less or equal to the total number of masses*)
If[total-fourD<Total@samemass,Throw["Please check input, impossible kinematics has been requested."];
];

n=total;

(*Next fix the components of the four-dimensional massless spinors*)
Do[
\[Xi][i+n]=0;
\[Eta][i+n]=0;
\[Eta]t[i+n]=\[Eta]t[i]*\[Xi]t[i+n]/\[Xi]t[i];
,{i,n-fourD+1,n}];
(*Do[
\[Xi][i+n]=0;
\[Eta][i+n]=0;
\[Eta]t[i+n]=0;
\[Xi]t[i+n]=0;
,{i,n-fourD+1,n}];*)

(*Based on the options given assign rational rather than real kinematics and the range of the interval over which to generate it*)
If[TrueQ[OptionValue[RationalKinematics]],
random:=RandomInteger[OptionValue[ParameterRange]],
random:=RandomReal[OptionValue[ParameterRange]];
];

(*Next generate the random spinor components. First the 3n*)

Do[
\[Xi][i+n]=random;
\[Eta][i+n]=random;
\[Eta]t[i+n]=random;
,{i,n-fourD}];

(*Then the 9 + the 2 for which we do not solve momcon in 4d:*)
\[Eta]t[1]=random;
\[Eta]t[2]=random;
\[Xi]t[1]=random;
\[Xi]t[2]=random;
\[Xi][3]=random;
\[Eta][3]=random;
(*\[Xi][4]=random;*)
\[Xi][2]=random;
\[Eta][1]=random;
\[Eta][4]=random;
\[Xi]t[1+n]=random;
\[Xi]t[2+n]=random;

(*Depending on whether a parametric expression is required or not, we set the other variables to either a parameter or a number*)

If[TrueQ[OptionValue[Parametric]],
(*Parametric components*)
par=OptionValue[ParameterName];
\[Eta]t[3]=par[1];
\[Eta]t[4]=par[2];
\[Xi]t[4]=par[3];
\[Xi]t[3+n]=par[4];
\[Xi]t[4+n]=par[5];
count=6;
Do[
\[Xi][i]=par[count++];
\[Eta][i]=par[count++];
\[Xi]t[i]=par[count++];
\[Eta]t[i]=par[count++];
\[Xi]t[i+n]=par[count++];
,{i,5,n}];
,
(*Numeric components*)
\[Eta]t[3]=random;
\[Eta]t[4]=random;
\[Xi]t[4]=random;
\[Xi]t[3+n]=random;
\[Xi]t[4+n]=random;
Do[
\[Xi][i]=random;
\[Eta][i]=random;
\[Xi]t[i]=random;
\[Eta]t[i]=random;
\[Xi]t[i+n]=random;
,{i,5,n}];
];

(*Fix the required msasses to be the same*)
count=1;
(*Do[
(*\[Xi]t[count+n]=random;*)
Do[
\[Xi]t[i+n]=(-\[Eta][-1+i+n] \[Eta]t[-1+i+n] \[Xi][-1+i] \[Xi]t[-1+i]+\[Eta][-1+i] \[Eta]t[-1+i+n] \[Xi][-1+i+n] \[Xi]t[-1+i]+\[Eta][i+n] \[Eta]t[i+n] \[Xi][i] \[Xi]t[i]-\[Eta][i] \[Eta]t[i+n] \[Xi][i+n] \[Xi]t[i]+\[Eta][-1+i+n] \[Eta]t[-1+i] \[Xi][-1+i] \[Xi]t[-1+i+n]-\[Eta][-1+i] \[Eta]t[-1+i] \[Xi][-1+i+n] \[Xi]t[-1+i+n])/(\[Eta]t[i] (\[Eta][i+n] \[Xi][i]-\[Eta][i] \[Xi][i+n]));
,{i,count+1,count+k-1}];
count=count+k;
,{k,samemass}];*)

Do[
Do[
\[Xi]t[i+n]=(-\[Eta][count+n] \[Eta]t[count+n] \[Xi][count] \[Xi]t[count]+\[Eta][count] \[Eta]t[count+n] \[Xi][count+n] \[Xi]t[count]+\[Eta][i+n] \[Eta]t[i+n] \[Xi][i] \[Xi]t[i]-\[Eta][i] \[Eta]t[i+n] \[Xi][i+n] \[Xi]t[i]+\[Eta][count+n] \[Eta]t[count] \[Xi][count] \[Xi]t[count+n]-\[Eta][count] \[Eta]t[count] \[Xi][count+n] \[Xi]t[count+n])/(\[Eta]t[i] (\[Eta][i+n] \[Xi][i]-\[Eta][i] \[Xi][i+n]));
,{i,count+1,count+k-1}];
count=count+k;
,{k,samemass}];

(*Generate momentum conservation:*)
system={Sum[\[Xi][i]\[Xi]t[i],{i,2*n}]==0,Sum[\[Xi][i]\[Eta]t[i],{i,2*n}]==0,Sum[\[Eta][i]\[Xi]t[i],{i,2*n}]==0,Sum[\[Eta][i]\[Eta]t[i],{i,2*n}]==0(*,Sum[\[Xi][i]\[Eta][i+n]-\[Xi][i+n]\[Eta][i],{i,n}]==0,Sum[\[Eta]t[i+n]\[Xi]t[i]-\[Xi]t[i+n]\[Eta]t[i],{i,n}]==0*)};

Table[{\[Xi][i],\[Xi]t[i],\[Eta][i],\[Eta]t[i]},{i,2n}]//Echo;
(*Solve momentum conservation*)
sol=Solve[system,{\[Xi][1],\[Xi][4],\[Eta][2],\[Xi]t[3](*,\[Xi]t[1+n],\[Xi]t[2+n]*)}];

(*Safety check*)
If[sol==={},
Message[GenSpinors::unsolvablekinematics];
Throw[$Failed],
sol=sol//First;
];

(*Now that all the spinor components have been generated we just need to return them in a suitably packaged output. The oupt will be divided into 6D and 4D and then further into {\[Lambda],\[Lambda]t,\[Lambda]',\[Lambda]t'}. Notice that these spinors will be considered all having upper indices so the spinors will be like \[Lambda]=\[LeftAngleBracket]\[Lambda]| and \[Lambda]t=|\[Lambda]t].*)

(*List of the 6D spinors*)
out=Table[{{\[Xi][i],\[Eta][i]},{\[Xi]t[i],\[Eta]t[i]},{\[Xi][i+n],\[Eta][i+n]},{\[Xi]t[i+n],\[Eta]t[i+n]}},{i,n-fourD}];

(*Then append the table of the 4D components and replece the solutions to momentum conservation*)
out={out,Table[{{\[Xi][i],\[Eta][i]},{\[Xi]t[i],\[Eta]t[i]}},{i,n-fourD+1,n}]}/.sol;


Return[out];
];
];*)


Options[GenerateKinematics]={RationalKinematics->True,ParameterRange->1000,Parametric->False,ParameterName->$par}
{RationalKinematics->True,ParameterRange->1000,Parametric->False,ParameterName->$par}

(*Samemass is a list of integers representing the number of masses which have been requested as to be the same*)

GenerateKinematics[total_Integer,fourD_Integer,samemass_List,OptionsPattern[]]:=Catch[Module[{\[Xi],\[Eta],\[Xi]t,\[Eta]t,n,random,system,sol,par,count,out},

(*First we check that total \[GreaterEqual] fourD+2 *)
If[total<fourD+2,Throw["Please check input, impossible kinematics has been requested."];
];

(*The number of masses required to be the same must be less or equal to the total number of masses*)
If[total-fourD<Total@samemass,Throw["Please check input, impossible kinematics has been requested."];
];

n=total;

(*Next fix the components of the four-dimensional massless spinors*)
Do[
\[Xi][i+n]=0;
\[Eta][i+n]=0;
\[Eta]t[i+n]=\[Eta]t[i]*\[Xi]t[i+n]/\[Xi]t[i];
,{i,n-fourD+1,n}];
(*Do[
\[Xi][i+n]=0;
\[Eta][i+n]=0;
\[Eta]t[i+n]=0;
\[Xi]t[i+n]=0;
,{i,n-fourD+1,n}];*)

(*Based on the options given assign rational rather than real kinematics and the range of the interval over which to generate it*)
If[TrueQ[OptionValue[RationalKinematics]],
random:=RandomInteger[OptionValue[ParameterRange]],
random:=RandomReal[OptionValue[ParameterRange]];
];

(*Next generate the random spinor components. First the 3n*)

Do[
\[Xi][i+n]=random;
\[Eta][i+n]=random;
\[Eta]t[i+n]=random;
,{i,n-fourD}];

(*Then the 9 + the 2 for which we do not solve momcon in 4d:*)
\[Eta]t[1]=random;
\[Eta]t[2]=random;
\[Xi]t[1]=random;
\[Xi]t[2]=random;
\[Xi][3]=random;
\[Eta][3]=random;
(*\[Xi][4]=random;*)
\[Xi][2]=random;
\[Eta][1]=random;
\[Eta][4]=random;
\[Xi]t[1+n]=random;
\[Xi]t[2+n]=random;

(*Depending on whether a parametric expression is required or not, we set the other variables to either a parameter or a number*)

If[TrueQ[OptionValue[Parametric]],
(*Parametric components*)
par=OptionValue[ParameterName];
\[Eta]t[3]=par[1];
\[Eta]t[4]=par[2];
\[Xi]t[4]=par[3];
\[Xi]t[3+n]=par[4];
\[Xi]t[4+n]=par[5];
count=6;
Do[
\[Xi][i]=par[count++];
\[Eta][i]=par[count++];
\[Xi]t[i]=par[count++];
\[Eta]t[i]=par[count++];
\[Xi]t[i+n]=par[count++];
,{i,5,n}];
,
(*Numeric components*)
\[Eta]t[3]=random;
\[Eta]t[4]=random;
\[Xi]t[4]=random;
\[Xi]t[3+n]=random;
\[Xi]t[4+n]=random;
Do[
\[Xi][i]=random;
\[Eta][i]=random;
\[Xi]t[i]=random;
\[Eta]t[i]=random;
\[Xi]t[i+n]=random;
,{i,5,n}];
];

(*Fix the required masses to be the same. We do so by fixing the two arbitrary variables below*)
count=1;

Do[
Do[
\[Xi][i+n]=(-\[Eta][count+n] \[Xi][count]+\[Eta][i+n] \[Xi][i]+\[Eta][count] \[Xi][count+n])/\[Eta][i];
\[Xi]t[i+n]=(-\[Eta]t[count+n] \[Xi]t[count]+\[Eta]t[i+n] \[Xi]t[i]+\[Eta]t[count] \[Xi]t[count+n])/\[Eta]t[i];
,{i,count+1,count+k-1}];
count=count+k;
,{k,samemass}];

(*Generate momentum conservation:*)
system={Sum[\[Xi][i]\[Xi]t[i],{i,2*n}]==0,Sum[\[Xi][i]\[Eta]t[i],{i,2*n}]==0,Sum[\[Eta][i]\[Xi]t[i],{i,2*n}]==0,Sum[\[Eta][i]\[Eta]t[i],{i,2*n}]==0};

(*Table[{\[Xi][i],\[Xi]t[i],\[Eta][i],\[Eta]t[i]},{i,2n}]//Echo;*)
(*Solve momentum conservation*)
sol=Solve[system,{\[Xi][1],\[Xi][4],\[Eta][2],\[Xi]t[3]}];

(*Safety check*)
If[sol==={},
Message[GenSpinors::unsolvablekinematics];
Throw[$Failed],
sol=sol//First;
];

(*Now that all the spinor components have been generated we just need to return them in a suitably packaged output. The oupt will be divided into 6D and 4D and then further into {\[Lambda],\[Lambda]t,\[Lambda]',\[Lambda]t'}. Notice that these spinors will be considered all having upper indices so the spinors will be like \[Lambda]=\[LeftAngleBracket]\[Lambda]| and \[Lambda]t=|\[Lambda]t].*)

(*List of the 6D spinors*)
out=Table[{{\[Xi][i],\[Eta][i]},{\[Xi]t[i],\[Eta]t[i]},{\[Xi][i+n],\[Eta][i+n]},{\[Xi]t[i+n],\[Eta]t[i+n]}},{i,n-fourD}];

(*Then append the table of the 4D components and replece the solutions to momentum conservation*)
out={out,Table[{{\[Xi][i],\[Eta][i]},{\[Xi]t[i],\[Eta]t[i]}},{i,n-fourD+1,n}]}/.sol;


Return[out];
];
];


(* ::Subsubsection::Closed:: *)
(*GenerateKinematics4D*)


Options[GenerateKinematics4D]={RationalKinematics->True,ParameterRange->1000,Parametric->False,ParameterName->$par};


GenerateKinematics4D[total_Integer,OptionsPattern[]]:=Catch[Module[{\[Xi],\[Eta],\[Xi]t,\[Eta]t,n,random,system,sol,par,count,out},

n=total;

(*Based on the options given assign rational rather than real kinematics and the range of the interval over which to generate it*)
If[TrueQ[OptionValue[RationalKinematics]],
random:=RandomInteger[OptionValue[ParameterRange]],
random:=RandomReal[OptionValue[ParameterRange]];
];

(*Next generate the random spinor components. First the n*)

Do[
\[Eta]t[i]=random;
,{i,n}];

(*Then the 6:*)
\[Xi][3]=random;
\[Xi][4]=random;
\[Eta][3]=random;
\[Eta][4]=random;
\[Xi]t[1]=random;
\[Xi]t[2]=random;

(*Depending on whether a parametric expression is required or not, we set the other variables to either a parameter or a number*)

If[TrueQ[OptionValue[Parametric]],
(*Parametric components*)
par=OptionValue[ParameterName];
\[Xi]t[3]=par[1];
\[Xi]t[4]=par[2];
count=3;
Do[
\[Xi]t[i]=par[count++];
\[Xi][i]=par[count++];
\[Eta][i]=par[count++];
,{i,5,n}];
,
(*Numeric components*)
\[Xi]t[3]=random;
\[Xi]t[4]=random;
Do[
\[Xi]t[i]=random;
\[Xi][i]=random;
\[Eta][i]=random;
,{i,5,n}];
];

(*Generate momentum conservation:*)
system={Sum[\[Xi][i]\[Xi]t[i],{i,n}]==0,Sum[\[Xi][i]\[Eta]t[i],{i,n}]==0,Sum[\[Eta][i]\[Xi]t[i],{i,n}]==0,Sum[\[Eta][i]\[Eta]t[i],{i,n}]==0};

(*Solve momentum conservation*)
sol=Solve[system,{\[Xi][1],\[Xi][2],\[Eta][1],\[Eta][2]}];

(*Safety check*)
If[sol==={},
Message[GenSpinors::unsolvablekinematics];
Throw[$Failed],
sol=sol//First;
];

(*Now that all the spinor components have been generated we just need to return them in a suitably packaged output. The oupt will be divided into {\[Lambda],\[Lambda]t}. Notice that these spinors will be considered all having upper indices so the spinors will be like \[Lambda]=\[LeftAngleBracket]\[Lambda]| and \[Lambda]t=|\[Lambda]t].*)

(*Table of the 4D components and replece the solutions to momentum conservation*)
out=Table[{{\[Xi][i],\[Eta][i]},{\[Xi]t[i],\[Eta]t[i]}},{i,n}]/.sol;

Return[out];
];
];


(* ::Subsubsection::Closed:: *)
(*GenerateKinematicsFixed4D*)


Options[GenerateKinematicsFixed4D]={ParameterRange->1000,RationalKinematics->True};

GenerateKinematicsFixed4D::overconstrained="Maximum number of momenta which can be fixed a priori is number of particles minus two. Overconstrained kinematics has been requested.";

GenerateKinematicsFixed4D::undeclaredmom="One of the fixing conditions is not well defined. Did you declare the necessary momenta? Proceed randomizing the undefined momentum.";

GenSpinors::unsolvablekinematics="Anomalous kinematic point has been randomly generated, momentum conservation could not be solved.";


GenerateKinematicsFixed4D[nlegs_Integer,fixedmom_List,OptionsPattern[]]:=Catch[Module[{\[Xi],\[Eta],\[Xi]t,\[Eta]t,random,system,sol,out,input},

(*First a safety check: the maximum number of momenta which can be fixed a priori is n-2*)
If[nlegs-Length[fixedmom]<2,
Message[GenerateKinematicsFixed4D::overconstrained];
Throw[$Failed];
];

(*Rational vs Real kinematics*)
If[TrueQ[OptionValue[RationalKinematics]],
random:=RandomInteger[OptionValue[ParameterRange]],
random:=RandomReal[OptionValue[ParameterRange]];
];

(*3 possible options: either the list of spinor components, or the label of the corresponding momentum, or constant times the label. It can also be mixed*)
input={};
Do[
Which[
MatchQ[i,{{_,_},{_,_}}],
(*Spinor components*)
input={input,i};
,
Head[i]===Symbol(*&&MemberQ[MomList,i]*),
(*Symbol, supposedely a momentum label*)
input={input,{SpinorUndotN[i][$lam][$up],SpinorDotN[i][$lam][$up]}};
,
MatchQ[i,Times[_?NumberQ,_Symbol]],
(*Number times symbol*)
input={input,{i[[1]]*SpinorUndotN[i[[2]]][$lam][$up],SpinorDotN[i[[2]]][$lam][$up]}};
,
MatchQ[i,Times[x_,y_]/;MemberQ[MomList,y]&&!MemberQ[MomList,x]],
(*symbol times symbol with one of them a declared momentum label*)
input={input,{Select[i,!MemberQ[MomList,#]&]*SpinorUndotN[Select[i,MemberQ[MomList,#]&]][$lam][$up],SpinorDotN[Select[i,MemberQ[MomList,#]&]][$lam][$up]}};
,
True,
Message[GenerateKinematicsFixed4D::undeclaredmom];
input={input,{{random,random},{random,random}}};
];
,{i,fixedmom}];

(*Fix spinor components to be the required ones, and generate the missing ones randomly*)
out=Table[{\[Xi][i],\[Eta][i],\[Xi]t[i],\[Eta]t[i]},{i,Length[fixedmom]}];
input=Flatten[input];
Evaluate[out//Flatten]=input;
Do[{\[Xi][i],\[Eta][i],\[Xi]t[i],\[Eta]t[i]}={random,random,random,random},{i,Length[fixedmom]+1,nlegs-2}];

(*Finally solve momentum conservation for the last two momenta, in particular solve for the angle components and set the squares to random numbers*)
{\[Xi]t[nlegs-1],\[Eta]t[nlegs-1],\[Xi]t[nlegs],\[Eta]t[nlegs]}={random,random,random,random};

(*Generate momentum conservation:*)
system={Sum[\[Xi][i]\[Xi]t[i],{i,nlegs}]==0,Sum[\[Xi][i]\[Eta]t[i],{i,nlegs}]==0,Sum[\[Eta][i]\[Xi]t[i],{i,nlegs}]==0,Sum[\[Eta][i]\[Eta]t[i],{i,nlegs}]==0};

(*Solve momentum conservation*)
sol=Solve[system,{\[Xi][nlegs-1],\[Xi][nlegs],\[Eta][nlegs-1],\[Eta][nlegs]}];

(*Safety check*)
If[sol==={},
Message[GenSpinors::unsolvablekinematics];
Throw[$Failed],
sol=sol//First;
];

(*Now that all the spinor components have been generated we just need to return them in a suitably packaged output. The oupt will be divided into {\[Lambda],\[Lambda]t}. Notice that these spinors will be considered all having upper indices so the spinors will be like \[Lambda]=\[LeftAngleBracket]\[Lambda]| and \[Lambda]t=|\[Lambda]t].*)

(*Table of the 4D components and replece the solutions to momentum conservation*)
out=Table[{{\[Xi][i],\[Eta][i]},{\[Xi]t[i],\[Eta]t[i]}},{i,nlegs}]/.sol;

Return[out];

];
];


(* ::Subsubsection::Closed:: *)
(*GenKinematics3pt*)


Options[GenKinematics3pt]={RationalKinematics->True,ParameterRange->1000,SetMomentum->{}};

GenKinematics3pt::invalidset="Invalid option for SetMomentum. Proceed ignoring the option.";


GenKinematics3pt[type_,OptionsPattern[]]:=Module[{random,lam,lamtil,a2,a3},

(*Based on the options given assign rational rather than real kinematics and the range of the interval over which to generate it*)
	If[TrueQ[OptionValue[RationalKinematics]],
	random:=RandomInteger[OptionValue[ParameterRange]],
	random:=RandomReal[OptionValue[ParameterRange]];
	];

(*Generate the \[Lambda] and \[Lambda] tilde for the first spinor. If SetMomentum is not empty set the spinors to the given spinor components or to the components of the label if any is given.*)

Which[OptionValue[SetMomentum]==={},
lam[1]={random,random};
lamtil[1]={random,random};
,
(*Here we could add the condition for the symbol to be a declared momentum, but not compulsory...*)
Head[OptionValue[SetMomentum]]===Symbol,
{lam[1],lamtil[1]}={SpinorUndotN[OptionValue[SetMomentum]][$lam][$up],SpinorDotN[OptionValue[SetMomentum]][$lam][$up]};
,
MatchQ[OptionValue[SetMomentum],{{_,_},{_,_}}],
{lam[1],lamtil[1]}=OptionValue[SetMomentum];
,
MatchQ[OptionValue[SetMomentum],Times[_?NumberQ,_Symbol]],
(*Number times symbol*)
{lam[1],lamtil[1]}={OptionValue[SetMomentum][[1]]*SpinorUndotN[OptionValue[SetMomentum][[2]]][$lam][$up],SpinorDotN[OptionValue[SetMomentum][[2]]][$lam][$up]};
,
MatchQ[OptionValue[SetMomentum],Times[x_,y_]/;MemberQ[MomList,y]&&!MemberQ[MomList,x]],
(*symbol times symbol with one of them a declared momentum label*)
{lam[1],lamtil[1]}={Select[OptionValue[SetMomentum],!MemberQ[MomList,#]&]*SpinorUndotN[Select[OptionValue[SetMomentum],MemberQ[MomList,#]&]][$lam][$up],SpinorDotN[Select[OptionValue[SetMomentum],MemberQ[MomList,#]&]][$lam][$up]};
,
True,
Message[GenKinematics3pt::invalidset];
lam[1]={random,random};
lamtil[1]={random,random};
];

(*Dependin on the type we set either all the \[Lambda] or the \[Lambda] tildes proportional to the one of p1, and generate the remaining spinors satisfying momentum conservation. No internal security condition on the type input, TO BE PUT IN THE EXTERNAL ENVIRONMENT!!!*)
a2=random;
a3=random;

Which[type===$angle,
lamtil[2]=a2*lamtil[1];
lamtil[3]=a3*lamtil[1];
lam[2]={random,random};
lam[3]=-lam[1]/a3-a2/a3*lam[2];
,
type===$square,
lam[2]=a2*lam[1];
lam[3]=a3*lam[1];
lamtil[2]={random,random};
lamtil[3]=-lamtil[1]/a3-a2/a3*lamtil[2];
];


Return[Table[{lam[i],lamtil[i]},{i,3}]];

];


(* ::Subsubsection::Closed:: *)
(*GenSpinorsAux*)


Options[GenSpinorsAux]={RationalKinematics->True,ParameterRange->1000,Parametric->False,ParameterName->$par,Seed->False,AllMassless->False,DisplaySpinors->False,SetMomentum->{},SameMasses->{}};

GenSpinors::parametric="Sorry, the option Parametric is not yet supported in the requested kinematics.";

GenSpinors::notsupported="Sorry, the requested kinematics is not supported in the current version.";


(*GenSpinorsAux[labels_List,OptionsPattern[]]:=Catch[Module[{lab4,lab6,type,ra,rs,la,ls,\[Xi],\[Xi]t,\[Eta],\[Eta]t,kinem,n,kinem2},

(*First of all, clear all the stored values of non-fundamental building blocks, like angle and square brackets and so on. This is achieved with ClearDownValues and ClearSubValues*)
ClearDependentKinematics[];

(*If labels is a list of two lists, then the first one is to be treated as the list of 6D momenta and the second one as the list of 4D momenta. If the option AllMassless is set to True then all the momenta are considered as massless. The variable type is flag for the 3 different cases*)
Which[
OptionValue[Dimension]===4,
lab4=labels;
lab6={};
(*Pure 4D*)
type=0;
,
MatchQ[labels,{_List,_List}],
lab6=labels[[1]];
lab4=labels[[2]];
(*Mixed kinematics*)
type=1;
(*If the list of 6D momenta is epty, this is equivalent to case 1*)
If[lab6==={},type=0;];
,
True,
lab6=labels;
lab4={};
(*Pure 6D*)
type=2;
];

(*If Seed has been defined then SeedRandom*)
If[MatchQ[Head[OptionValue[Seed]],Integer|String],
SeedRandom[OptionValue[Seed]];
];

(*Definition of the spinors in terms of the components. In the six-dimensional case there will be 2n of these spinors, where the first n refer to \[Lambda] and the second n to \[Lambda]' which is redefinition of the \[Mu] encoding also the masses, see package documentation.*)
	ra[i_]:={-\[Xi][i],\[Eta][i]}(*|i>*);
		   rs[i_]:={\[Xi]t[i],\[Eta]t[i]}(*|i]*);
		   la[i_]:={\[Eta][i],\[Xi][i]}(*<i|*);
		   ls[i_]:={-\[Eta]t[i],\[Xi]t[i]}(*[i|*);

(*Now actually generate the kinematics, depending on whether there are fixed momenta or not and the dimension we call different functions.*)

If[OptionValue[SetMomentum]==={},
(*Generate all momenta from scratch*)
Which[
type===0,
(*Pure 4D*)
n=Length[lab4];
kinem=Table[{la[i],rs[i]},{i,n}];
kinem2=GenerateKinematics4D[n,{RationalKinematics->OptionValue[RationalKinematics],ParameterRange->OptionValue[ParameterRange],Parametric->OptionValue[Parametric],ParameterName->OptionValue[ParameterName]}];
If[kinem2===$Failed,Throw[kinem2]];
Evaluate[kinem]=kinem2;
,
type===1,
(*Mixed*)
n=Length[lab4]+Length[lab6];
kinem={Table[{la[i],rs[i],la[i+n],rs[i+n]},{i,Length[lab6]}],Table[{la[i],rs[i]},{i,Length[lab6]+1,n}]};
kinem2=GenerateKinematics[n,Length[lab4],{RationalKinematics->OptionValue[RationalKinematics],ParameterRange->OptionValue[ParameterRange],Parametric->OptionValue[Parametric],ParameterName->OptionValue[ParameterName]}];
If[kinem2===$Failed,Throw[kinem2]];
Evaluate[kinem]=kinem2;
,
type===2,
(*Pure 6D*)
n=Length[lab6];
kinem={Table[{la[i],rs[i],la[i+n],rs[i+n]},{i,n}],{}};
kinem2=GenerateKinematics[n,0,{RationalKinematics->OptionValue[RationalKinematics],ParameterRange->OptionValue[ParameterRange],Parametric->OptionValue[Parametric],ParameterName->OptionValue[ParameterName]}];
If[kinem2===$Failed,Throw[kinem2]];
Evaluate[kinem]=kinem2;
];
,
(*Some of the spinors are fixed a priori*)
Which[
type===0,
(*Pure 4D*)
n=Length[lab4];
kinem=Table[{la[i],rs[i]},{i,n}];
kinem2=GenerateKinematicsFixed4D[n,If[(!Head[OptionValue[SetMomentum]]===List)||MatchQ[OptionValue[SetMomentum],{{_,_},{_,_}}],{OptionValue[SetMomentum]},OptionValue[SetMomentum]],{RationalKinematics->OptionValue[RationalKinematics],ParameterRange->OptionValue[ParameterRange]}];
If[TrueQ[OptionValue[Parametric]],
Message[GenSpinors::parametric];
];
If[kinem2===$Failed,Throw[kinem2]];
Evaluate[kinem]=kinem2;
,
type===1,
Message[GenSpinors::notsupported],
type===2,
Message[GenSpinors::notsupported]
];
];

(*Finally relate the generated kinematics to the spinor labels:*)
(*6D part*)
Do[
		(*\[Lambda] spinors*)
		SpinorUndotN[lab6[[i]]][$lam][$up]=la[i];
		SpinorUndotN[lab6[[i]]][$lam][$down]=ra[i];
		SpinorDotN[lab6[[i]]][$lam][$down]=ls[i];
		SpinorDotN[lab6[[i]]][$lam][$up]=rs[i];
		(*\[Mu] spinors*)
		SpinorUndotN[lab6[[i]]][$mu][$up]=la[i+n];
		SpinorUndotN[lab6[[i]]][$mu][$down]=ra[i+n];
		SpinorDotN[lab6[[i]]][$mu][$down]=ls[i+n];
		SpinorDotN[lab6[[i]]][$mu][$up]=rs[i+n];
		(*Masses:*)
		ExtramassN[lab6[[i]]]=la[i] . ra[i+n];
		ExtramasstildeN[lab6[[i]]]=ls[i+n] . rs[i];
		,{i,Length[lab6]}];
(*4D part*)
Do[
		(*\[Lambda] spinors*)
		SpinorUndotN[lab4[[i]]][$lam][$up]=la[i+Length[lab6]];
		SpinorUndotN[lab4[[i]]][$lam][$down]=ra[i+Length[lab6]];
		SpinorDotN[lab4[[i]]][$lam][$down]=ls[i+Length[lab6]];
		SpinorDotN[lab4[[i]]][$lam][$up]=rs[i+Length[lab6]];
(*Initialise the \[Mu] spinors to {Null,Null} for consistency reasons*)SpinorUndotN[lab4[[i]]][$mu][$up]={Null,Null};SpinorUndotN[lab4[[i]]][$mu][$down]={Null,Null};SpinorDotN[lab4[[i]]][$mu][$down]={Null,Null};SpinorDotN[lab4[[i]]][$mu][$up]={Null,Null};(*Masses to zero:*)
ExtramassN[lab4[[i]]]=0;
ExtramasstildeN[lab4[[i]]]=0;
		,{i,Length[lab4]}];

(*If DisplaySpinors is set to True display the generated kinematics*)
If[OptionValue[DisplaySpinors],
Print["Output reads {|\[Lambda]\[RightAngleBracket],|\[Lambda]],|\[Mu]\[RightAngleBracket],|\[Mu]]} and {|\[Lambda]\[RightAngleBracket],|\[Lambda]]} for 6D and 4D spinors respectively."];
Return[DeleteCases[{Table[{ra[i],rs[i],ra[i+n],rs[i+n]},{i,Length[lab6]}],Table[{ra[i],rs[i]},{i,Length[lab6]+1,n}]},{}]];
,
Return["Numerical kinematics has been generated."];
];


];
];*)


GenSpinors::duplicatemasses="There are duplicate labels among the masses given in the option SameMasses, option ignored."

GenSpinorsAux[labels_List,OptionsPattern[]]:=Catch[Module[{lab4,lab6,type,ra,rs,la,ls,\[Xi],\[Xi]t,\[Eta],\[Eta]t,kinem,n,kinem2,samemasses},

(*First of all, clear all the stored values of non-fundamental building blocks, like angle and square brackets and so on. This is achieved with ClearDownValues and ClearSubValues*)
ClearDependentKinematics[];

(*If labels is a list of two lists, then the first one is to be treated as the list of 6D momenta and the second one as the list of 4D momenta. If the option AllMassless is set to True then all the momenta are considered as massless. The variable type is flag for the 3 different cases*)
Which[
TrueQ[OptionValue[AllMassless]],
lab4=labels;
lab6={};
(*Pure 4D*)
type=0;
,
MatchQ[labels,{_List,_List}],
lab6=labels[[1]];
lab4=labels[[2]];
(*Mixed kinematics*)
type=1;
(*If the list of 6D momenta is epty, this is equivalent to case 1*)
If[lab6==={},type=0;];
,
True,
lab6=labels;
lab4={};
(*Pure 6D*)
type=2;
];

(*If the number of massive momenta is non-vanishing sort the labels accordingly*)
If[AllTrue[OptionValue[SameMasses],Head[#]===List&],
samemasses=OptionValue[SameMasses];
,
samemasses={OptionValue[SameMasses]}
];
If[samemasses=!={{}},
(*Check that all masses are indeed among the massive labels. Drop all elements which are no declared among the massive labels*)
samemasses=DeleteCases[#,_?(!MemberQ[lab6,#]&)]&/@samemasses;
(*Next drop all the instances where there is a single element in the list, since we do not need to do anything there*)
samemasses=DeleteCases[samemasses,_?(Length[#]==1&)];
(*Check there are no duplicates*)
If[Length@Flatten[samemasses]>Length@DeleteDuplicates[Flatten[samemasses]],
Message[GenSpinors::duplicatemasses];
samemasses={{}};
];

(*Reorder the labels*)
lab6=Join[Flatten[samemasses],Complement[lab6,Flatten[samemasses]]];
];

(*If Seed has been defined then SeedRandom*)
If[MatchQ[Head[OptionValue[Seed]],Integer|String],
SeedRandom[OptionValue[Seed]];
];

(*Definition of the spinors in terms of the components. In the six-dimensional case there will be 2n of these spinors, where the first n refer to \[Lambda] and the second n to \[Lambda]' which is redefinition of the \[Mu] encoding also the masses, see package documentation.*)
	ra[i_]:={-\[Xi][i],\[Eta][i]}(*|i>*);
		   rs[i_]:={\[Xi]t[i],\[Eta]t[i]}(*|i]*);
		   la[i_]:={\[Eta][i],\[Xi][i]}(*<i|*);
		   ls[i_]:={-\[Eta]t[i],\[Xi]t[i]}(*[i|*);

(*Now actually generate the kinematics, depending on whether there are fixed momenta or not and the dimension we call different functions.*)

If[OptionValue[SetMomentum]==={},
(*Generate all momenta from scratch*)
Which[
type===0,
(*Pure 4D*)
n=Length[lab4];
kinem=Table[{la[i],rs[i]},{i,n}];
kinem2=GenerateKinematics4D[n,{RationalKinematics->OptionValue[RationalKinematics],ParameterRange->OptionValue[ParameterRange],Parametric->OptionValue[Parametric],ParameterName->OptionValue[ParameterName]}];
If[kinem2===$Failed,Throw[kinem2]];
Evaluate[kinem]=kinem2;
,
type===1,
(*Mixed*)
n=Length[lab4]+Length[lab6];
kinem={Table[{la[i],rs[i],la[i+n],rs[i+n]},{i,Length[lab6]}],Table[{la[i],rs[i]},{i,Length[lab6]+1,n}]};
kinem2=GenerateKinematics[n,Length[lab4],Length/@samemasses,{RationalKinematics->OptionValue[RationalKinematics],ParameterRange->OptionValue[ParameterRange],Parametric->OptionValue[Parametric],ParameterName->OptionValue[ParameterName]}];
If[kinem2===$Failed,Throw[kinem2]];
Evaluate[kinem]=kinem2;
,
type===2,
(*Pure 6D*)
n=Length[lab6];
kinem={Table[{la[i],rs[i],la[i+n],rs[i+n]},{i,n}],{}};
(*kinem2=GenerateKinematics[n,0,{0},{RationalKinematics->OptionValue[RationalKinematics],ParameterRange->OptionValue[ParameterRange],Parametric->OptionValue[Parametric],ParameterName->OptionValue[ParameterName]}];*)
kinem2=GenerateKinematics[n,0,Length/@samemasses,{RationalKinematics->OptionValue[RationalKinematics],ParameterRange->OptionValue[ParameterRange],Parametric->OptionValue[Parametric],ParameterName->OptionValue[ParameterName]}];
If[kinem2===$Failed,Throw[kinem2]];
Evaluate[kinem]=kinem2;
];
,
(*Some of the spinors are fixed a priori*)
Which[
type===0,
(*Pure 4D*)
n=Length[lab4];
kinem=Table[{la[i],rs[i]},{i,n}];
kinem2=GenerateKinematicsFixed4D[n,If[(!Head[OptionValue[SetMomentum]]===List)||MatchQ[OptionValue[SetMomentum],{{_,_},{_,_}}],{OptionValue[SetMomentum]},OptionValue[SetMomentum]],{RationalKinematics->OptionValue[RationalKinematics],ParameterRange->OptionValue[ParameterRange]}];
If[TrueQ[OptionValue[Parametric]],
Message[GenSpinors::parametric];
];
If[kinem2===$Failed,Throw[kinem2]];
Evaluate[kinem]=kinem2;
,
type===1,
Message[GenSpinors::notsupported],
type===2,
Message[GenSpinors::notsupported]
];
];

(*Finally relate the generated kinematics to the spinor labels:*)
(*6D part*)
Do[
		(*\[Lambda] spinors*)
		SpinorUndotN[lab6[[i]]][$lam][$up]=la[i];
		SpinorUndotN[lab6[[i]]][$lam][$down]=ra[i];
		SpinorDotN[lab6[[i]]][$lam][$down]=ls[i];
		SpinorDotN[lab6[[i]]][$lam][$up]=rs[i];
		(*\[Mu] spinors*)
		SpinorUndotN[lab6[[i]]][$mu][$up]=la[i+n];
		SpinorUndotN[lab6[[i]]][$mu][$down]=ra[i+n];
		SpinorDotN[lab6[[i]]][$mu][$down]=ls[i+n];
		SpinorDotN[lab6[[i]]][$mu][$up]=rs[i+n];
		(*Masses:*)
		ExtramassN[lab6[[i]]]=la[i] . ra[i+n];
		ExtramasstildeN[lab6[[i]]]=ls[i+n] . rs[i];
		,{i,Length[lab6]}];
(*4D part*)
Do[
		(*\[Lambda] spinors*)
		SpinorUndotN[lab4[[i]]][$lam][$up]=la[i+Length[lab6]];
		SpinorUndotN[lab4[[i]]][$lam][$down]=ra[i+Length[lab6]];
		SpinorDotN[lab4[[i]]][$lam][$down]=ls[i+Length[lab6]];
		SpinorDotN[lab4[[i]]][$lam][$up]=rs[i+Length[lab6]];
		(*Initialise the \[Mu] spinors to {Null,Null} for consistency reasons*)
		(*SpinorUndotN[lab4[[i]]][$mu][$up]={Null,Null};
		SpinorUndotN[lab4[[i]]][$mu][$down]={Null,Null};
		SpinorDotN[lab4[[i]]][$mu][$down]={Null,Null};
		SpinorDotN[lab4[[i]]][$mu][$up]={Null,Null};*)
		(*Initialise to zero*)
		SpinorUndotN[lab4[[i]]][$mu][$up]={0,0};
		SpinorUndotN[lab4[[i]]][$mu][$down]={0,0};
		SpinorDotN[lab4[[i]]][$mu][$down]={0,0};
		SpinorDotN[lab4[[i]]][$mu][$up]={0,0};
		(*Masses to zero:*)
		ExtramassN[lab4[[i]]]=0;
		ExtramasstildeN[lab4[[i]]]=0;
		,{i,Length[lab4]}];

(*If DisplaySpinors is set to True display the generated kinematics*)
If[OptionValue[DisplaySpinors],
Print["Output reads {|\[Lambda]\[RightAngleBracket],|\[Lambda]],|\[Mu]\[RightAngleBracket],|\[Mu]]} and {|\[Lambda]\[RightAngleBracket],|\[Lambda]]} for massive and massless spinors respectively."];
Return[DeleteCases[{Table[{ra[i],rs[i],ra[i+n],rs[i+n]},{i,Length[lab6]}],Table[{ra[i],rs[i]},{i,Length[lab6]+1,n}]},{}]];
,
Return["Numerical kinematics has been generated."];
];


];
];


(* ::Subsection::Closed:: *)
(*GenSpinors*)


Options[GenSpinors]={RationalKinematics->True,ParameterRange->1000,Parametric->False,ParameterName->$par,Seed->False,AllMassless->False,DisplaySpinors->False,SetMomentum->{},Type3pt->$angle,SameMasses->{}};


GenSpinors[labels_List,OptionsPattern[]]:=Module[{test,out,labels3pt},

(*test is the test outcome on divergent kinematics. As long as test stays true we generate singular kinematics so we repeat the process.*)
test=True;
While[test,

(*Check if the required kinematics is singular (3pt) or not, also requires 4d kinematics*)
Which[Length[labels3pt=labels]===3&&TrueQ[OptionValue[AllMassless]],
ClearDependentKinematics[];
(*Generate kinematics*)
test=KinematicCheck[out=GenKinematics3pt[OptionValue[Type3pt],{RationalKinematics->OptionValue[RationalKinematics],ParameterRange->OptionValue[ParameterRange],SetMomentum->OptionValue[SetMomentum]}]];
(*Assign labels if non-singular kinematics has been generated*)
If[!test,
{{SpinorUndotN[labels3pt[[1]]][$lam][$up],SpinorDotN[labels3pt[[1]]][$lam][$up]},{SpinorUndotN[labels3pt[[2]]][$lam][$up],SpinorDotN[labels3pt[[2]]][$lam][$up]},{SpinorUndotN[labels3pt[[3]]][$lam][$up],SpinorDotN[labels3pt[[3]]][$lam][$up]}}=out;
Do[
SpinorUndotN[i][$lam][$down]={-SpinorUndotN[i][$lam][$up][[2]],SpinorUndotN[i][$lam][$up][[1]]};
SpinorDotN[i][$lam][$down]={-SpinorDotN[i][$lam][$up][[2]],SpinorDotN[i][$lam][$up][[1]]};
SpinorUndotN[i][$mu][$up]={Null,Null};
SpinorUndotN[i][$mu][$down]={Null,Null};
SpinorDotN[i][$mu][$up]={Null,Null};
SpinorDotN[i][$mu][$down]={Null,Null};
ExtramassN[i]=0;
ExtramasstildeN[i]=0;
,{i,labels3pt}];
];
(*Take into account the option DisplaySpinors*)
If[TrueQ[OptionValue[DisplaySpinors]],
Print["Output is a list of {\[LeftAngleBracket]\[Lambda]|,|\[Lambda]]} for each spinor:"];
,
out="Numerical kinematics has been generated.";
];
(*If the option parametric is set to true print error message*)
If[TrueQ[OptionValue[Parametric]],
Message[GenSpinors::parametric];
];
,
MatchQ[labels,{{},{_,_,_}}],
ClearDependentKinematics[];
labels3pt=labels[[2]];
(*Generate kinematics*)
test=KinematicCheck[out=GenKinematics3pt[OptionValue[Type3pt],{RationalKinematics->OptionValue[RationalKinematics],ParameterRange->OptionValue[ParameterRange],SetMomentum->OptionValue[SetMomentum]}]];
(*Assign labels if non-singular kinematics has been generated*)
If[!test,
{{SpinorUndotN[labels3pt[[1]]][$lam][$up],SpinorDotN[labels3pt[[1]]][$lam][$up]},{SpinorUndotN[labels3pt[[2]]][$lam][$up],SpinorDotN[labels3pt[[2]]][$lam][$up]},{SpinorUndotN[labels3pt[[3]]][$lam][$up],SpinorDotN[labels3pt[[3]]][$lam][$up]}}=out;
Do[
SpinorUndotN[i][$lam][$down]={-SpinorUndotN[i][$lam][$up][[2]],SpinorUndotN[i][$lam][$up][[1]]};
SpinorDotN[i][$lam][$down]={-SpinorDotN[i][$lam][$up][[2]],SpinorDotN[i][$lam][$up][[1]]};
SpinorUndotN[i][$mu][$up]={Null,Null};
SpinorUndotN[i][$mu][$down]={Null,Null};
SpinorDotN[i][$mu][$up]={Null,Null};
SpinorDotN[i][$mu][$down]={Null,Null};
ExtramassN[i]=0;
ExtramasstildeN[i]=0;
,{i,labels3pt}];
];
(*Take into account the option DisplaySpinors*)
If[TrueQ[OptionValue[DisplaySpinors]],
Print["Output is a list of {\[LeftAngleBracket]\[Lambda]|,|\[Lambda]]} for each spinor:"];
,
out="Numerical kinematics has been generated.";
];
(*If the option parametric is set to true print error message*)
If[TrueQ[OptionValue[Parametric]],
Message[GenSpinors::parametric];
];
,
Length[Flatten[labels]]===3,
(*This would be 3pt kinematics either in pure 6D or mixed 6D and 4D, not yet supported*)
Message[GenSpinors::notsupported];
out=$Failed;
Break[];
,
True,
(*Proceed with the higher point kinematics generation*)
test=KinematicCheck[out=GenSpinorsAux[labels,{RationalKinematics->OptionValue[RationalKinematics],ParameterRange->OptionValue[ParameterRange],Parametric->OptionValue[Parametric],ParameterName->OptionValue[ParameterName],Seed->OptionValue[Seed],AllMassless->OptionValue[AllMassless],DisplaySpinors->OptionValue[DisplaySpinors],SetMomentum->OptionValue[SetMomentum],SameMasses->OptionValue[SameMasses]}]];
];
];
Return[out];
];


(* ::Subsection::Closed:: *)
(*SpinorUndotN and SpinorDotN*)


SpinorDotN[OverBar[p_]][type_][pos_]:=SpinorDotN[OverBar[p]][type][pos]=SpinorDotN[p][$mu][pos];
SpinorUndotN[OverBar[p_]][type_][pos_]:=SpinorUndotN[OverBar[p]][type][pos]=SpinorUndotN[p][$mu][pos];


(* ::Subsection::Closed:: *)
(*SpinorAngleBracketN*)


SpinorAngleBracketN[x_,y_]:=SpinorAngleBracketN[x,y]=SpinorUndotN[x][$lam][$up] . SpinorUndotN[y][$lam][$down];
SpinorAngleBracketN[x_,OverBar[y_]]:=SpinorAngleBracketN[x,OverBar[y]]=SpinorUndotN[x][$lam][$up] . SpinorUndotN[y][$mu][$down];
SpinorAngleBracketN[OverBar[x_],y_]:=SpinorAngleBracketN[OverBar[x],y]=SpinorUndotN[x][$mu][$up] . SpinorUndotN[y][$lam][$down];
SpinorAngleBracketN[OverBar[x_],OverBar[y_]]:=SpinorAngleBracketN[OverBar[x],OverBar[y]]=SpinorUndotN[x][$mu][$up] . SpinorUndotN[y][$mu][$down];


(* ::Subsection::Closed:: *)
(*SpinorSquareBracketN*)


SpinorSquareBracketN[x_,y_]:=SpinorSquareBracketN[x,y]=SpinorDotN[x][$lam][$down] . SpinorDotN[y][$lam][$up];
SpinorSquareBracketN[x_,OverBar[y_]]:=SpinorSquareBracketN[x,OverBar[y]]=SpinorDotN[x][$lam][$down] . SpinorDotN[y][$mu][$up];
SpinorSquareBracketN[OverBar[x_],y_]:=SpinorSquareBracketN[OverBar[x],y]=SpinorDotN[x][$mu][$down] . SpinorDotN[y][$lam][$up];
SpinorSquareBracketN[OverBar[x_],OverBar[y_]]:=SpinorSquareBracketN[OverBar[x],OverBar[y]]=SpinorDotN[x][$mu][$down] . SpinorDotN[y][$mu][$up];


(* ::Subsection::Closed:: *)
(*MomMat4D*)


(*(*In order to avoid divergencies coming from us having set all the reference spinor components to zero, we have to have two distinc definitions*)
MomMat4DN[label_][$up]:=MomMat4DN[label][$up]=If[ExtramassN[label]ExtramasstildeN[label]===0,
InverseDot[SpinorDotN[label][$lam][$up],SpinorUndotN[label][$lam][$up]],
InverseDot[SpinorDotN[label][$lam][$up],SpinorUndotN[label][$lam][$up]]-(ExtramassN[label]ExtramasstildeN[label])/(SpinorDotN[label][$lam][$down] . SpinorDotN[label][$mu][$up] SpinorUndotN[label][$lam][$up] . SpinorUndotN[label][$mu][$down])*InverseDot[SpinorDotN[label][$mu][$up],SpinorUndotN[label][$mu][$up]]
];
MomMat4DN[label_][$down]:=MomMat4DN[label][$down]=If[ExtramassN[label]ExtramasstildeN[label]===0,
InverseDot[SpinorUndotN[label][$lam][$down],SpinorDotN[label][$lam][$down]],
InverseDot[SpinorUndotN[label][$lam][$down],SpinorDotN[label][$lam][$down]]-(ExtramassN[label]ExtramasstildeN[label])/(SpinorDotN[label][$lam][$down] . SpinorDotN[label][$mu][$up] SpinorUndotN[label][$lam][$up] . SpinorUndotN[label][$mu][$down])*InverseDot[SpinorUndotN[label][$mu][$down],SpinorDotN[label][$mu][$down]]
];*)


MomMat4DN[label_][$up]:=MomMat4DN[label][$up]=InverseDot[SpinorDotN[label][$lam][$up],SpinorUndotN[label][$lam][$up]]+InverseDot[SpinorDotN[label][$mu][$up],SpinorUndotN[label][$mu][$up]];
MomMat4DN[label_][$down]:=MomMat4DN[label][$down]=InverseDot[SpinorUndotN[label][$lam][$down],SpinorDotN[label][$lam][$down]]+InverseDot[SpinorUndotN[label][$mu][$down],SpinorDotN[label][$mu][$down]];


(* ::Subsection:: *)
(*Mom4DN*)


Mom4DN[label_]:=Mom4DN[label]=1/2*{Tr[MomMat4DN[label][$up] . PauliMatrix[0]],Tr[MomMat4DN[label][$up] . PauliMatrix[1]],Tr[MomMat4DN[label][$up] . PauliMatrix[2]],Tr[MomMat4DN[label][$up] . PauliMatrix[3]]};


(* ::Subsection:: *)
(*ChainN*)


ChainN[type1_,p1_,{p2__},p3_,type2_]:=ChainN[type1,p1,{p2},p3,type2]=Module[{loc,momenta,pos,count},
If[type2===$square,
loc=SpinorDotN[p3][$lam][$up];
count=0;
,
loc=SpinorUndotN[p3][$lam][$down];
count=1;
];
pos[n_?OddQ]:=$up;
pos[n_?EvenQ]:=$down;
Do[loc=MomMat4DN[i][pos[count++]] . loc,{i,Reverse[{p2}]}];
If[type1===$angle,
loc=SpinorUndotN[p1][$lam][$up] . loc;
,
loc=SpinorDotN[p1][$lam][$down] . loc;
];
Return[loc];
];


(* ::Subsection:: *)
(*mpN*)


mpN[i_]:=mpN[i]=mpN[i,i];
mpN[i_,j_]:=mpN[i,j]=-(1/2) SpinorDotN[i][$lam][$down] . SpinorDotN[j][$lam][$up] SpinorUndotN[i][$lam][$up] . SpinorUndotN[j][$lam][$down]-1/2 SpinorDotN[i][$lam][$down] . SpinorDotN[j][$mu][$up] SpinorUndotN[i][$lam][$up] . SpinorUndotN[j][$mu][$down]-1/2 SpinorDotN[i][$mu][$down] . SpinorDotN[j][$mu][$up] SpinorUndotN[i][$mu][$up] . SpinorUndotN[j][$mu][$down]-1/2 SpinorDotN[j][$lam][$down] . SpinorDotN[i][$mu][$up] SpinorUndotN[j][$lam][$up] . SpinorUndotN[i][$mu][$down];


(* ::Subsection:: *)
(*SNum*)


SNum[x__]:=SNum[x]=Total@Join[2*mpN@@@Subsets[{x},{2}],mpN/@{x}];


(* ::Subsection:: *)
(*ToNum*)


(*ToNum[exp_]:=exp/.S->S6/.{SpinorAngleBracket->SpinorAngleBracketN,SpinorSquareBracket->SpinorSquareBracketN,Extramass->ExtramassN,Extramasstilde->ExtramasstildeN,AngSquInvariant->AngSquInvariantN,SquAngInvariant->SquAngInvariantN,AngAngInvariant->AngAngInvariantN,SquSquInvariant->SquSquInvariantN,Chain->ChainN,mp->mpN6,SpinorUndot[mom_][$lam][a_][Null]:>SpinorUndotN[mom][$lam][$up],SpinorUndot[mom_][$lam][Null][a_]:>SpinorUndotN[mom][$lam][$down],SpinorUndot[mom_][$mu][a_][Null]:>SpinorUndotN[mom][$mu][$up],SpinorUndot[mom_][$mu][Null][a_]:>SpinorUndotN[mom][$mu][$down],
SpinorDot[mom_][$lam][a_][Null]:>SpinorDotN[mom][$lam][$up],SpinorDot[mom_][$lam][Null][a_]:>SpinorDotN[mom][$lam][$down],SpinorDot[mom_][$mu][a_][Null]:>SpinorDotN[mom][$mu][$up],SpinorDot[mom_][$mu][Null][a_]:>SpinorDotN[mom][$mu][$down],SpinorUndot6D[mom_][A_][Null][a_]:>SpinorUndot6DN[mom][$down][a],SpinorDot6D[mom_][A_][Null][a_]:>SpinorDot6DN[mom][$down][a]};*)


ToNum[exp_]:=Block[{S,SpinorAngleBracket,SpinorSquareBracket,Extramass,Extramasstilde,AngSquInvariant,SquAngInvariant,AngAngInvariant,SquSquInvariant,Chain,mp,SpinorUndot,SpinorDot,SpinorUndot6D,SpinorDot6D},
S=SNum;
SpinorAngleBracket=SpinorAngleBracketN;
SpinorSquareBracket=SpinorSquareBracketN;
(*Extramass=ExtramassN;
Extramasstilde=ExtramasstildeN;*)
Chain=ChainN;
mp=mpN;

SpinorUndot[mom_][$lam][a_Integer][Null]:=SpinorUndotN[mom][$lam][$up][[a]];
SpinorUndot[mom_][$lam][Null][a_Integer]:=SpinorUndotN[mom][$lam][$down][[a]];
SpinorUndot[mom_][$mu][a_Integer][Null]:=SpinorUndotN[mom][$mu][$up][[a]];
SpinorUndot[mom_][$mu][Null][a_Integer]:=SpinorUndotN[mom][$mu][$down][[a]];
SpinorDot[mom_][$lam][a_Integer][Null]:=SpinorDotN[mom][$lam][$up][[a]];
SpinorDot[mom_][$lam][Null][a_Integer]:=SpinorDotN[mom][$lam][$down][[a]];
SpinorDot[mom_][$mu][a_Integer][Null]:=SpinorDotN[mom][$mu][$up][[a]];
SpinorDot[mom_][$mu][Null][a_Integer]:=SpinorDotN[mom][$mu][$down][[a]];

SpinorUndot[mom_][$lam][a_][Null]:=SpinorUndotN[mom][$lam][$up];
SpinorUndot[mom_][$lam][Null][a_]:=SpinorUndotN[mom][$lam][$down];
SpinorUndot[mom_][$mu][a_][Null]:=SpinorUndotN[mom][$mu][$up];
SpinorUndot[mom_][$mu][Null][a_]:=SpinorUndotN[mom][$mu][$down];
SpinorDot[mom_][$lam][a_][Null]:=SpinorDotN[mom][$lam][$up];
SpinorDot[mom_][$lam][Null][a_]:=SpinorDotN[mom][$lam][$down];
SpinorDot[mom_][$mu][a_][Null]:=SpinorDotN[mom][$mu][$up];
SpinorDot[mom_][$mu][Null][a_]:=SpinorDotN[mom][$mu][$down];
exp
];


(* ::Section:: *)
(*End of context and package*)


(*End the private context*)
End[]

(*Protect all public symbols in the package*)
Protect@@Names["SpinorNumerics`*"];

(*End the package*)
EndPackage[]
