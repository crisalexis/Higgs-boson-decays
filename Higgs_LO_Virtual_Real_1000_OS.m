(* ::Package:: *)
(* ============================================================= *)
(* H -> mu mu, H -> tau tau: LO + virtual OS + real soft/hard       *)
(* 1000 masas mH = 95 ... 150 GeV (incluidos extremos).             *)
(* Sin Get, Needs ni << : reutiliza FeynCalc/FeynArts/FeynHelpers,  *)
(* LoopTools, FS0, FS1PV, dGammaReal, DeltaCTHMuMu y reglas OS       *)
(* YA cargados/definidos en el notebook Hmumu_program(1).m.        *)
(* ============================================================= *)

If[!And @@ {ValueQ[FS0],ValueQ[FS1PV],ValueQ[dGammaReal],
           ValueQ[rulesUV],ValueQ[rulesOS],
           Length[DownValues[DeltaCTHMuMu]]>0},
 Print["ERROR: ejecuta primero tu notebook hasta FS1PV, dGammaReal y contratérminos OS."];
 Abort[]
];

ClearAll[
  dvPVPattern, dvEps, dvMass, dvPhotonRules, dvReduce,
  dvDB1Rules, dvB1Rules, dvCKM, dvCKMRules,
  dvParameters, dvMu, dvTau, dvH, dvLambda,
  dvTree, dvLoop, dvDeltaCT, dvPrepare,
  dvGetPV, dvPVNumerical, dvPoint, dvBuildTau,
  dvOneChannel, dvExport, dvValidation, dvWork,
  dvSymbolicCoefficient, dvScalarRules,
  dvTauAmplitude, dvTauTree, dvTauLoop, dvTauScalar,
  dvListMuon, dvListTau, dvResult125, dvBuildAll,
  dvPrefactors, dvTermData, dvStart, dvNum,
  dvExportDir
];

If[!(ValueQ[FS0] && ValueQ[FS1PV] &&
      ValueQ[rulesUV] && ValueQ[rulesOS] &&
      Length[DownValues[DeltaCTHMuMu]] > 0),
  Print["ERROR: ejecutar primero el notebook original con FS0, FS1PV y CT OS."];
  Abort[]
];

LToolsLoadLibrary[];

(* -------- parametros usados en el notebook, en GeV -------- *)
(* Se mantienen alpha(0) y la relacion OS para sen(theta_W). *)
dvMu = 0.1056583755;
dvTau = 1.77693;
dvLambda = 1/10000; (* regulador de masa fotonica en GeV *)
dvExportDir = NotebookDirectory[];

dvParameters = {
  e -> Sqrt[4 Pi/137.035999084],
  mw -> 80.3625,
  sw -> Sqrt[1 - (80.3625/91.1876)^2],
  me -> 0.00051099895,
  mm -> dvMu,
  ml -> dvTau,
  muq -> 0.00216, md -> 0.00467, ms -> 0.093,
  mc -> 1.27, mb -> 4.18, mt -> 172.69
};

(* CKM unitaria: parametrizacion estandar exacta a partir de         *)
(* tres senos y fase. Valores orientativos; sustituir por un ajuste  *)
(* CKM de la referencia escogida si se requieren resultados precisos. *)
Module[{s12=225/1000, s23=41/1000, s13=37/10000,
        cp=6/5, c12, c23, c13},
  c12 = Sqrt[1-s12^2]; c23 = Sqrt[1-s23^2]; c13 = Sqrt[1-s13^2];
  dvCKM = {
    {c12 c13, s12 c13, s13 Exp[-I cp]},
    {-s12 c23-c12 s23 s13 Exp[I cp],
      c12 c23-s12 s23 s13 Exp[I cp], s23 c13},
    {s12 s23-c12 c23 s13 Exp[I cp],
      -c12 s23-s12 c23 s13 Exp[I cp], c23 c13}
  };
];
dvCKMRules = Flatten@Table[VCKM[i,j] -> dvCKM[[i,j]], {i,1,3},{j,1,3}];
Print["CKM: maximo error de unitariedad = ",
  N[Max[Abs[Flatten[ConjugateTranspose[N[dvCKM]].N[dvCKM] - IdentityMatrix[3]]]]]];

(* -------- convertir a base escalar sin eliminar D -------- *)
dvPVPattern = _A0 | _B0 | _C0 | _D0 | _DB0;

dvDB1Rules = HoldPattern[DB1[p_, a_, b_]] :>
   ((b-a-p) DB0[p,a,b] - B0[p,a,b])/(2 p) -
   (A0[a]-A0[b]+(b-a-p) B0[p,a,b])/(2 p^2);
dvB1Rules = HoldPattern[B1[p_, a_, b_]] :>
   (A0[a]-A0[b]+(b-a-p) B0[p,a,b])/(2 p);

(* Sustituciones EXCLUSIVAS en integrales de foton + lepton externo.  *)
(* C0[...,mw^2,mw^2,0] contiene un neutrino: NO se toca.           *)
dvPhotonRules[m_] := With[{m2=m^2}, {
  HoldPattern[PaVe[0,{m2},{0,m2}]] :>
      PaVe[0,{m2},{lambdaPhoton^2,m2}],
  HoldPattern[PaVe[0,{m2},{m2,0}]] :>
      PaVe[0,{m2},{m2,lambdaPhoton^2}],
  HoldPattern[PaVe[0,{mh^2,m2,m2},{m2,m2,0}]] :>
      PaVe[0,{mh^2,m2,m2},{m2,m2,lambdaPhoton^2}],
  HoldPattern[B0[m2,0,m2]] :> B0[m2,lambdaPhoton^2,m2],
  HoldPattern[B0[m2,m2,0]] :> B0[m2,m2,lambdaPhoton^2],
  HoldPattern[C0[mh^2,m2,m2,m2,m2,0]] :>
      C0[mh^2,m2,m2,m2,m2,lambdaPhoton^2]
}];

dvReduce[expr_, mass_] := Module[{x},
  x = expr /. dvPhotonRules[mass];
  x = PaVeToABCD[PaVeReduce[x]];
  x = x /. dvPhotonRules[mass];
  x = x /. dvDB1Rules /. dvB1Rules;
  x = PaVeToABCD[PaVeReduce[x]];
  If[!FreeQ[x, _PaVe | _B1 | _DB1 | _FeynAmpDenominator |
                _A00 | _B00 | _B11],
    Print["ERROR: hay coeficientes tensoriales o integrales sin reducir."];
    Print[Short[DeleteDuplicates@Cases[x,
      _PaVe | _B1 | _DB1 | _FeynAmpDenominator |
        _A00 | _B00 | _B11,Infinity],4]];
    Return[$Failed]
  ];
  x
];

(* -------- construir amplitud genuina del TAU --------------- *)
(* Usa momenta distintos para no alterar la cinematica del muon. *)
dvBuildTau[] := Module[
  {pht, pmt, ppt, lt, d0, d1, a0, a1, tree, vert,
   scal, dir, amp1, amp0, t0, t1},
  Print["Generando vertice genuino H -> tau+ tau- ..."];
  pht = Unique["pHTau"]; pmt = Unique["pMinusTau"];
  ppt = Unique["pPlusTau"]; lt = Unique["lTau"];
  t0 = CreateTopologies[0,1->2];
  t1 = CreateTopologies[1,1->2,
       ExcludeTopologies->{Tadpoles,SelfEnergies,WFCorrections}];
  d0 = InsertFields[t0,S[1]->{F[2,{3}],-F[2,{3}]},
       Model->"SM",InsertionLevel->{Classes}];
  d1 = InsertFields[t1,S[1]->{F[2,{3}],-F[2,{3}]},
       Model->"SM",InsertionLevel->{Classes}];
  a0 = CreateFeynAmp[d0,Truncated->False];
  a1 = CreateFeynAmp[d1,Truncated->False];
  amp0 = FCFAConvert[a0,IncomingMomenta->{pht},
     OutgoingMomenta->{pmt,ppt},ChangeDimension->D,
     SMP->True,List->False,UndoChiralSplittings->True];
  amp1 = FCFAConvert[a1,IncomingMomenta->{pht},
     OutgoingMomenta->{pmt,ppt},LoopMomenta->{lt},
     ChangeDimension->D,SMP->True,List->False,
     UndoChiralSplittings->True];
  amp0 = amp0 /. changes /. massRules /. {
     SMP["m_tau"]->ml, SMP["m_H"]->mh,
     SMP["m_W"]->mw, SMP["m_Z"]->mz};
  amp1 = amp1 /. changes /. massRules /. {
     SMP["m_tau"]->ml, SMP["m_H"]->mh,
     SMP["m_W"]->mw, SMP["m_Z"]->mz};
  SPD[pht,pht]=mh^2; SPD[pmt,pmt]=ml^2;
  SPD[ppt,ppt]=ml^2; SPD[pmt,ppt]=(mh^2-2 ml^2)/2;
  SPD[pht,pmt]=mh^2/2; SPD[pht,ppt]=mh^2/2;
  tree = DiracSimplify[Contract[amp0],DiracEquation->True];
  amp1 = TID[amp1,lt];
  amp1 = DiracSimplify[Contract[amp1],DiracEquation->True];
  amp1 = DiracSimplify[amp1 /.
      Momentum[pht,D] :> Momentum[pmt,D]+Momentum[ppt,D],
      DiracEquation->True];
  dir = Expand@DotExpand@DiracSubstitute67@
    DiracSimplify[DiracGammaExpand[DiracChainExpand[amp1]],
     DiracEquation->True];
  scal = Spinor[Momentum[pmt,D],ml,1].
      Spinor[-Momentum[ppt,D],ml,1];
  dvTauTree = Simplify[Coefficient[tree,scal]];
  dvTauLoop = Simplify[TID[Simplify[Coefficient[dir,scal]],
                                      lt,ToPaVe->True]];
  If[dvTauTree === 0 || dvTauLoop === 0,
    Print["ERROR: la extraccion del factor escalar para tau dio cero."];
    Return[$Failed]
  ];
  Print["Vertex tau listo. N PV del tau: ",
    Length[DeleteDuplicates@Cases[dvTauLoop,_PaVe|_A0|_B0|_C0,Infinity]]];
  True
];

(* --------- esquema OS: CT muon y tau --------------- *)
dvDeltaCT[2] := DeltaCTHMuMu[];
dvDeltaCT[3] := DeltaMf[2,3]/ML + DeltaZe[] -
  DeltaSWOverSW[] - DeltaMW2[]/(2 MW^2) + DeltaZH[]/2 +
  DeltaZfL[2,3,3]/2 + DeltaZfR[2,3,3]/2;

(* Formar las expresiones SIMBOLICAS una sola vez.            *)
(* NO aplicar .N a los indices de VCKM.                      *)
dvPrepare[g_Integer] := dvPrepare[g] = Module[{f0,f1,m,x},
  If[g==2,
    {f0,f1,m}={FS0,FS1PV,mm},
    If[!ValueQ[dvTauTree] || !ValueQ[dvTauLoop],
      If[dvBuildTau[] === $Failed, Return[$Failed]]
    ];
    {f0,f1,m}={dvTauTree,dvTauLoop,ml}
  ];
  x = f1/f0 + dvDeltaCT[g];
  x = x /. rulesUV /. rulesOS;
  x = dvReduce[x,m];
  If[x === $Failed,Return[$Failed]];
  (* Reglas CKM exactas en indices ANTES de any N[]. *)
  x = x /. dvCKMRules;
  If[!FreeQ[x,VCKM],
    Print["ERROR: quedan elementos CKM simbolicos."];
    Return[$Failed]
  ];
  <|"expression"->x,"tree"->f0,"mass"->m|>
];

(* Preparar y cachear la base de maestros PV UNA SOLA VEZ por canal. *)
dvTermData[g_Integer] := dvTermData[g] = Module[{p,ex,pvs,coeffs,rem},
  p=dvPrepare[g];If[p===$Failed,Return[$Failed]];
  ex=Expand[p["expression"]];
  pvs=DeleteDuplicates@Cases[ex,dvPVPattern,Infinity];
  coeffs=Coefficient[ex,#]&/@pvs;
  rem=ex/.Thread[pvs->ConstantArray[0,Length[pvs]]];
  If[!TrueQ[Expand[ex-rem-Total[coeffs pvs]]===0],
    Print["ERROR: amplitud no es lineal en maestros PV."];
    Return[$Failed]
  ];
  <|"PV"->pvs,"Coefficients"->coeffs,"Remainder"->rem,
    "tree"->p["tree"],"mass"->p["mass"]|>
];

(* -------- evaluacion y extraccion POR INTEGRAL ------------- *)
(* Devuelve {coeficiente 1/epsilon, parte finita}.              *)
(* LToolsDB0 es UV finita: su valor se usa sin expansion.        *)
dvPVNumerical[pv_,num_,scale_] := Module[{z,ret,a,pole,fin},
  z = pv /. num;
  a = List @@ z;
  If[!And@@(NumericQ /@ a),
    Print["ERROR: PV con argumentos simbolicos: ",InputForm[z]];
    Return[$Failed]
  ];
  ret = CheckAbort[
    If[Head[z]===DB0,
      LToolsDB0@@a,
      LToolsEvaluate[z,LToolsSetMudim->N[scale],
         LToolsFullResult->True,LToolsExpandInEpsilon->True]
    ],$Failed
  ];
  If[ret === $Failed || ret === $Aborted ||
     !FreeQ[ret,_A0|_B0|_C0|_D0|_PaVe|_DB0|
                   Indeterminate|ComplexInfinity],
    Print["ERROR al evaluar ",InputForm[z], " -> ",Short[ret,3]];
    Return[$Failed]
  ];
  If[Head[z]===DB0,
    {0,N[ret]},
    pole=SeriesCoefficient[ret,{Epsilon,0,-1}];
    fin=SeriesCoefficient[ret,{Epsilon,0,0}];
    If[!NumericQ[pole] || !NumericQ[fin],
      Print["ERROR: Laurent no numerico para ", InputForm[z]];
      Return[$Failed]
    ];
    {N[pole],N[fin]}
  ]
];

(* Factor D: c(D)=c(4)-2 epsilon c'(4)+...                   *)
(* Asi se conserva el termino finito epsilon * (1/epsilon) *)
(* SIN expandir series gigantes ni perder la contribucion.   *)
dvPoint[g_Integer,H_?NumericQ,lam_?NumericQ] := Module[
 {prep,ex,tree,m,pvs,rem,coeffs,dim,nums,pvValues,
  c0,c1,zz,pole,finite,lo,dGamma,remaining,rest,treeNum},
  prep=dvTermData[g]; If[prep === $Failed,Return[$Failed]];
  tree=prep["tree"]; m=prep["mass"];
  pvs=prep["PV"];coeffs=prep["Coefficients"];
  rem=prep["Remainder"];
  nums=Join[dvParameters,{mh->H,lambdaPhoton->lam}];
  pvValues=dvPVNumerical[#,nums,H^2]& /@ pvs;
  If[MemberQ[pvValues,$Failed],Return[$Failed]];
  dim=Unique["dim"];  (* evita derivar respecto a la funcion System`D *)
  c0= N[((#/.D->dim)/.dim->4)/.nums]& /@ coeffs;
  c1= N[(-2 (D[#/.D->dim,dim]/.dim->4))/.nums]& /@ coeffs;
  If[!And@@(NumericQ /@ Join[c0,c1]),
     Print["ERROR: coeficientes PV no numericos al fijar D=4."];
     Return[$Failed]
  ];
  rest=N[(rem/.D->4)/.nums];
  If[!NumericQ[rest],Print["ERROR: parte sin PV no numerica."];Return[$Failed]];
  pole=Total[c0 pvValues[[All,1]]];
  finite=Total[c0 pvValues[[All,2]]+c1 pvValues[[All,1]]]+rest;
  treeNum = N[(tree /. rulesUV /. rulesOS /. nums) /. D -> 4];
  (* LO analitico OS, para evitar simbolos pendientes en FS0 *)
  lo = N[H/(8 Pi) (1 - 4 N[m /. nums]^2/H^2)^(3/2) *
      ((e (m /. nums)/(2 mw sw))^2 /. dvParameters)];
  If[!And@@(NumericQ /@ {pole,finite,lo}),
     Print["ERROR: no se obtuvieron numeros para UV/finito/LO."];
     Return[$Failed]
  ];
  If[Abs[pole]>10^-7,
    Print["ERROR UV: canal ",g,", mH=",H,
      ", residuo 1/epsilon = ",N[pole,12],
      ". No se exporta un resultado no renormalizado."];
    Return[<|"Status"->"PoleNotCanceled","Pole"->pole,
             "FiniteCandidate"->finite|>]
  ];
  dGamma=N[2 lo Re[finite]];
  <|"Status"->"EvaluatedAtThisRegulator", "Pole"->pole,
    "DeltaRelative"->finite,"GammaLO_GeV"->lo,
    "DeltaGammaVirtual_GeV"->dGamma,
    "DeltaGammaVirtual_keV"->10^6 dGamma|>
];


(* ================================================================ *)
(* H -> mu+mu- / tau+tau- : Gamma_LO y Gamma_real = soft + hard      *)
(* Dos canales x dos contribuciones x 1000 puntos, 95..150 GeV.     *)
(* Se requiere dGammaReal evaluada en el notebook Hmumu_program.m.   *)
(* NO incluye el virtual, NO es el ancho NLO inclusivo completo.     *)
(* ================================================================ *)

If[!ValueQ[dGammaReal],
 Print["ERROR: primero ejecuta el bloque de radiacion real hasta dGammaReal."];
 Abort[]
];

ClearAll[prReal, alphaReal, eReal, mwReal, mzReal, swReal,
  mMuReal, mTauReal, corteReal, lambdaReal, atanhSobreXReal,
  GammaLOCanal, GammaSoftCanal, GammaHardCanal, GammaRealCanal,
  cuadradoNumReal, resultados125, masasHReal, tablaLOMu, tablaLOTau,
  tablaRealMu, tablaRealTau, construirTablasReal, guardarReal];

(* Parametros de entrada: GeV; alpha(0), sW definido en esquema OS. *)
alphaReal = 1/137.035999084;
mwReal = 80.3625;
mzReal = 91.1876;
swReal = Sqrt[1 - (mwReal/mzReal)^2];
eReal = Sqrt[4 Pi alphaReal];
mMuReal = 0.1056583755;
mTauReal = 1.77693;
corteReal = 0.1;                  (* GeV *)
lambdaReal = 0.0001;              (* GeV *)

(* Una sola tabla cinemática para los DOS canales. Solo se cambia
   la masa del lepton externo, no las masas de lazos virtuales. *)
cuadradoNumReal[H_?NumericQ, m_?NumericQ] :=
  dGammaReal /. {mh -> H, mm -> m, mw -> mwReal,
    sw -> swReal, e -> eReal};

GammaLOCanal[H_?NumericQ, m_?NumericQ] := Module[{b},
 If[H <= 2 m, Return[0]];
 b = Sqrt[1 - 4 m^2/H^2];
 N[H b^3/(8 Pi) (eReal m/(2 mwReal swReal))^2]
];

atanhSobreXReal[x_?NumericQ] :=
  If[Abs[x] < 10^-8, 1 + x^2/3 + x^4/5, ArcTanh[x]/x];

(* Soft eikonal con foton de masa ficticia lambdaReal;
   aproximacion de phase-space slicing a E_gamma < corteReal. *)
GammaSoftCanal[H_?NumericQ, m_?NumericQ,
    corte_?NumericQ, lam_?NumericQ] :=
 Module[{b, lo, tmax, integral},
  If[!TrueQ[H > 2 m && 0 < lam < corte <
       (H^2 - 4 m^2)/(2 H)], Return[$Failed]];
  b = Sqrt[1 - 4 m^2/H^2];
  lo = GammaLOCanal[H, m];
  tmax = ArcCosh[corte/lam];
  integral = NIntegrate[
    Tanh[t]^2 * ((1 + b^2) atanhSobreXReal[b Tanh[t]] -
       (1 - b^2)/(1 - b^2 Tanh[t]^2)),
    {t, 0, tmax},
    Method -> {"GlobalAdaptive", "SymbolicProcessing" -> 0},
    AccuracyGoal -> 8, PrecisionGoal -> 8
  ];
  N[lo eReal^2/(2 Pi^2) integral]
 ];

(* Integracion dura estable: E_gamma = corte Exp[q],
   s = H^2 - 2 H E_gamma, z = Tanh[a u]/b(s), a = ArcTanh[b(s)].
   Evita las regiones colineales concentradas cerca de z=+-1. *)
GammaHardCanal[H_?NumericQ, m_?NumericQ,
    corte_?NumericQ] :=
 Module[{qmax, s, b, a, z, jac, expr, integral},
  If[!TrueQ[H > 2 m && 0 < corte <
       (H^2 - 4 m^2)/(2 H)], Return[$Failed]];
  qmax = Log[(H^2 - 4 m^2)/(2 H corte)];
  s = H^2 - 2 H corte Exp[q];
  b = Sqrt[1 - 4 m^2/s];
  a = ArcTanh[b];
  z = Tanh[a u]/b;
  jac = 2 H corte Exp[q] (a/b) Sech[a u]^2;
  expr = Together[(cuadradoNumReal[H, m] /.
       {sInv -> s, zAng -> z}) jac];
  integral = Check[
    NIntegrate[
      Evaluate[expr], {q, 0, qmax}, {u, -1, 1},
      Method -> {"GlobalAdaptive", "SymbolicProcessing" -> 0},
      AccuracyGoal -> 7, PrecisionGoal -> 7, MaxRecursion -> 16
    ],
    $Failed
  ];
  If[!NumericQ[integral] || !FreeQ[integral, Indeterminate],
    Return[$Failed]];
  N[Re[integral]]
 ];

GammaRealCanal[H_?NumericQ, m_?NumericQ,
    corte_?NumericQ, lam_?NumericQ] := Module[{soft, hard},
  soft = GammaSoftCanal[H, m, corte, lam];
  hard = GammaHardCanal[H, m, corte];
  If[!NumericQ[soft] || !NumericQ[hard], Return[$Failed]];
  soft + hard
];



(* ============================================================= *)
(* Evaluacion conjunta; un solo calculo hard por masa.             *)
(* Los anchos estan en keV y la masa mH en GeV.                    *)
(* ============================================================= *)

ClearAll[hNLO125, hNLOGrid, hNLOAll, hNLOExport, hNLOCheck,
 hNLOMasses, hNLOMu, hNLOTau, hNLOValid, hNLOLambda,
 hNLOCut, hNLOOutputDir, hNLOTestIR];

hNLOLambda = 10^-5;   (* GeV: valor mas estable en la prueba IR *)
hNLOCut = 0.1;        (* GeV: corte energia del foton *)
hNLOOutputDir = NotebookDirectory[];
hNLOMasses = N[Subdivide[95, 150, 999], 16];

(* Hacer calculo real solo con expresion FeynCalc ya existente.
   Para radiacion a arbol el cambio mm -> ml es correcto pues solo
   la masa del lepton externo aparece en la amplitud radiativa. *)

hNLOValid[v_] := NumericQ[v] && FreeQ[v,
    Indeterminate|ComplexInfinity|DirectedInfinity|$Failed] &&
    TrueQ[Abs[Im[N[v]]] < 10^-9];

hNLO125[g_Integer, H_?NumericQ, lam_?NumericQ:hNLOLambda,
  corte_?NumericQ:hNLOCut] := Module[
 {m, v, lo, hard, soft, real, nlo, pv, pole},
 If[!MemberQ[{2,3},g], Return[$Failed]];
 m = If[g==2,mMuReal,mTauReal];
 v = dvPoint[g,H,lam];
 If[!AssociationQ[v] || !KeyExistsQ[v,"DeltaGammaVirtual_keV"],
   Print["ERROR virtual: canal ",g,"; mH = ",H,"; resultado = ",Short[v,3]];
   Return[$Failed]
 ];
 pole = v["Pole"];
 If[!hNLOValid[pole] || Abs[pole] > 10^-7,
   Print["ERROR: polo UV no cancelado. mH = ",H,"; canal = ",g,
     "; polo = ",pole];Return[$Failed]
 ];
 lo = GammaLOCanal[H,m];
 soft = GammaSoftCanal[H,m,corte,lam];
 hard = GammaHardCanal[H,m,corte];
 If[!And@@(hNLOValid /@ {lo,soft,hard}),
   Print["ERROR en integracion real: canal ",g,"; mH = ",H,
     "; soft = ",soft,"; hard = ",hard];
   Return[$Failed]
 ];
 real = soft+hard;
 nlo = 10^6 lo + v["DeltaGammaVirtual_keV"] + 10^6 real;
 <|
   "mH_GeV"->N[H],"GammaLO_keV"->N[10^6 lo],
   "DeltaGammaVirtual_keV"->N[v["DeltaGammaVirtual_keV"]],
   "GammaSoft_keV"->N[10^6 soft],"GammaHard_keV"->N[10^6 hard],
   "GammaReal_keV"->N[10^6 real],"GammaNLO_keV"->N[nlo],
   "PoloUV"->pole
 |>
];

(* Calculo de referencia; DESACTIVA la generacion si falla. *)
Print["========== PRUEBAS mH = 125 GeV =========="];
hNLOMu125 = hNLO125[2,125.];
hNLOTau125 = hNLO125[3,125.];
Print["MUON 125 GeV: ",hNLOMu125];
Print["TAU 125 GeV: ",hNLOTau125];
If[!AssociationQ[hNLOMu125] || !AssociationQ[hNLOTau125],
 Print["ERROR: algun canal fallo la comprobacion inicial."];
 Abort[]
];

(* Para comparar con las pruebas previas, valores orientativos:
   muon LO~0.882537, virtual~ -0.646117, real~ +0.654629,
   NLO~0.891048 keV para lambda=10^-5 GeV.
   tau  LO~249.311, virtual~ -109.441, real~ +116.745,
   NLO~256.615 keV.
   No se usan estos numeros como sustituciones o entradas. *)

(* Prueba automatizada IR: se recalcula el virtual y soft; hard
   tambien se evalua para cada punto de prueba. No se alteran polos. *)
hNLOTestIR[g_Integer] := Module[{r1,r2,rel},
  r1=hNLO125[g,125.,10^-4,hNLOCut];
  r2=hNLO125[g,125.,10^-5,hNLOCut];
  If[!AssociationQ[r1] || !AssociationQ[r2],Return[$Failed]];
  rel=Abs[r1["GammaNLO_keV"]-r2["GammaNLO_keV"]]/
        Max[Abs[r2["GammaNLO_keV"]],10^-30];
  Print["IR canal ",g,": NLO(1e-4) = ",r1["GammaNLO_keV"],
    " keV; NLO(1e-5) = ",r2["GammaNLO_keV"],
    " keV; desviacion relativa = ",rel];
  If[rel>0.001,
   Print["ADVERTENCIA: dependencia IR > 0.1%; no crear tablas."];
   Return[$Failed]
  ];
  rel
];

(* Lista de registros y CSV. Se detiene ANTES de exportar si falla
   cualquier punto, sin rellenar huecos con resultados inventados. *)
hNLOGrid[g_Integer] := Catch[
  Table[Module[{res},
    If[Mod[j,25]==0 || j==1,
      Print["Canal ",g,": ",j,"/1000; mH = ",hNLOMasses[[j]]]];
    res=hNLO125[g,hNLOMasses[[j]]];
    If[!AssociationQ[res] ||
      !And@@(hNLOValid /@ Values[res]),
      Print["STOP: punto no validado: ",j,"; canal ",g];
      Throw[$Failed,"NLObad"]
    ];
    res
  ],{j,Length[hNLOMasses]}],"NLObad"
];

hNLOExport[mu_List,tau_List] := Module[
 {names,data,paths,cols,j,res},
 cols={"mH_GeV","GammaLO_keV","DeltaGammaVirtual_keV",
       "GammaReal_keV","GammaNLO_keV","PoloUV"};
 names={"Higgs_Muon_LO_keV.csv","Higgs_Muon_DeltaVirtual_keV.csv",
    "Higgs_Muon_Real_keV.csv","Higgs_Tau_LO_keV.csv",
    "Higgs_Tau_DeltaVirtual_keV.csv","Higgs_Tau_Real_keV.csv",
    "Higgs_Muon_Todas_keV.csv","Higgs_Tau_Todas_keV.csv"};
 data=Join[
  Table[Prepend[({#["mH_GeV"],#[key]}& /@ mu),{"mH_GeV",key}],
    {key,{"GammaLO_keV","DeltaGammaVirtual_keV","GammaReal_keV"}}],
  Table[Prepend[({#["mH_GeV"],#[key]}& /@ tau),{"mH_GeV",key}],
    {key,{"GammaLO_keV","DeltaGammaVirtual_keV","GammaReal_keV"}}],
  {
   Prepend[(Lookup[#,cols]& /@ mu),cols],
   Prepend[(Lookup[#,cols]& /@ tau),cols]
  }
 ];
 paths=FileNameJoin[{hNLOOutputDir,#}]& /@ names;
 res=MapThread[Export[#1,#2,"CSV"]&,{paths,data}];
 Print["Exportados 8 CSV (6 contribuciones + 2 combinados):"];
 Scan[Print,paths];
 res
];

hNLOAll[] := Module[{irm,irt,m,t,paths},
  irm=hNLOTestIR[2]; irt=hNLOTestIR[3];
  If[irm===$Failed || irt===$Failed,
     Print["STOP: comprobacion IR fallida."]; Return[$Failed]];
  Print["Calculando 1000 puntos del MUON..."];
  m=hNLOGrid[2]; If[m===$Failed,Return[$Failed]];
  Print["Calculando 1000 puntos del TAU..."];
  t=hNLOGrid[3]; If[t===$Failed,Return[$Failed]];
  If[Length[m]!=1000 || Length[t]!=1000,
   Print["STOP: tamanos incorrectos"];Return[$Failed]];
  hNLOMu=m; hNLOTau=t;
  paths=hNLOExport[m,t];
  <|"Muon"->m,"Tau"->t,"Exports"->paths|>
];

Print["PRUEBAS: hNLOMu125; hNLOTau125;"];
Print["GENERAR 1000 PUNTOS: listasHiggs = hNLOAll[];"];
