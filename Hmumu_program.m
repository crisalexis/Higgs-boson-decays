(* ::Package:: *)

If[ $FrontEnd === Null,
                $FeynCalcStartupMessages = False;
                Print["Computation"];
];
Off[FrontEndObject::notavail]
$LoadAddOns={"FeynHelpers","FeynArts"};
<<FeynCalc`;
$FAVerbose =0;
Off[Paint::nolevel];



(* ================================================ *)
(* H -> mu- mu+ : Correcciones de vertice a un loop *)
(* Modelo Estandar - Gauge de Feynman               *)
(* ================================================ *)

FeynArts`$FeynmanGauge = True;


top0 = CreateTopologies[
  0,
  1 -> 2
];

diag0 = InsertFields[
  top0,
  S[1] -> {F[2, {2}], -F[2, {2}]},
  Model -> "SM",
  InsertionLevel -> {Classes}
];


top1 = CreateTopologies[
  1,
  1 -> 2,
  ExcludeTopologies -> {
    Tadpoles,
    SelfEnergies,
    WFCorrections
  }
];

diag1 = InsertFields[
  top1,
  S[1] -> {F[2, {2}], -F[2, {2}]},
  Model -> "SM",
  InsertionLevel -> {Classes}
];


fa0 = CreateFeynAmp[
  diag0,
  Truncated -> False
];

fa1 = CreateFeynAmp[
  diag1,
  Truncated -> False
];



Paint[diag1];


(* ========================================================== *)
(* 4. Conversion a FeynCalc                                    *)
(* ========================================================== *)

amp0 = FCFAConvert[
   fa0,
   IncomingMomenta -> {p1},
   OutgoingMomenta -> {p2, p3},
   ChangeDimension -> D,
   SMP -> True,
   List -> False,
   UndoChiralSplittings -> True
];

amp1 = FCFAConvert[
   fa1,
   IncomingMomenta -> {p1},
   OutgoingMomenta -> {p2, p3},
   LoopMomenta -> {l},
   ChangeDimension -> D,
   SMP -> True,
   List -> False,
   UndoChiralSplittings -> True
];


(* ========================================================== *)
(* 5. Notacion para masas y acoplamientos                      *)
(* ========================================================== *)

changes = {
   EL -> e,   ME -> me,   MT -> mt,   MC -> mc,   MB -> mb,
     ML -> ml,   MZ -> mz,   MM -> mm,   MH -> mh,   MW -> mw
};

massRules = {
   SMP["m_mu"] -> mm,   SMP["m_H"] -> mh,
   SMP["m_W"] -> mw,   SMP["m_Z"] -> mz
};

amp0New = amp0 /. changes /. massRules;
amp1New = amp1 /. changes /. massRules;



(* ========================================================== *)
(* 6. Condiciones cinematicas on-shell                         *)
(* ========================================================== *)

FCClearScalarProducts[];

SPD[p1, p1] = mh^2;
SPD[p2, p2] = mm^2;
SPD[p3, p3] = mm^2;

SPD[p2, p3] = (mh^2 - 2 mm^2)/2;

SPD[p1, p2] = mh^2/2;
SPD[p1, p3] = mh^2/2;



(* ========================================================== *)
(* 7. Amplitud a nivel arbol                                   *)
(* ========================================================== *)

amp0Red = Contract[amp0New];

amp0OS = DiracSimplify[
   amp0Red,
   DiracEquation -> True
];


(* ========================================================== *)
(* 8. Reduccion tensorial a un loop                            *)
(* ========================================================== *)

(* Primera reduccion, sin convertir aun a B0 y C0 *)

amp1PV = TID[amp1New, l];

amp1Red = Contract[amp1PV];

amp1OS = DiracSimplify[
   amp1Red,
   DiracEquation -> True
];

(* Conservacion del cuadrimomento *)

amp1Final = DiracSimplify[
   amp1OS /.
      Momentum[p1, D] :>
         Momentum[p2, D] + Momentum[p3, D],
   DiracEquation -> True
];


(* ========================================================== *)
(* 9. Extraccion de las estructuras de Dirac                   *)
(* ========================================================== *)

s = Spinor[Momentum[p2, D], mm, 1];
v = Spinor[-Momentum[p3, D], mm, 1];

scalar = s . v;
pseudo = s . DiracGamma[5] . v;

(* Expandir proyectores quirales y productos no conmutativos *)

amp1SP = Expand @ DotExpand @ DiracSubstitute67 @
   DiracSimplify[
      DiracGammaExpand[
         DiracChainExpand[amp1Final]
      ],
      DiracEquation -> True
   ];



FS0 = Simplify[
   Coefficient[amp0OS, scalar]
];


(* ========================================================== *)
(* 10. Factores de forma antes de la reduccion escalar         *)
(* ========================================================== *)

FS1 = Simplify[
   Coefficient[amp1SP, scalar]
];

FP1 = Simplify[
   Coefficient[amp1SP, pseudo]
];

(* Verificar la reconstruccion de la amplitud *)

checkAmplitude = FullSimplify[
   amp1SP - FS1 scalar - FP1 pseudo
];

Print["Reconstruccion correcta: ",
   TrueQ[checkAmplitude === 0]
];


(* ========================================================== *)
(* 11. Reduccion a integrales escalares PV                     *)
(* ========================================================== *)

FS1PV = Simplify[
   TID[FS1, l, ToPaVe -> True]
];

FP1PV = Simplify[
   TID[FP1, l, ToPaVe -> True]
];

(* Comprobacion de la componente pseudoescalar *)

checkPseudo = FullSimplify[
   FP1PV == 0
];

Print["FP1PV = 0: ", checkPseudo];


(* ========================================================== *)
(* 12. Identificar integrales escalares PV                     *)
(* ========================================================== *)

ClearAll[PVFunctions];

PVFunctions[expr_] := DeleteDuplicates @ Cases[
   expr,
   _PaVe | _A0 | _B0 | _B1 | _C0 | _D0 | _DB0 | _DB1,
   Infinity
];

PVfunctions1PI =PVFunctions[FS1PV];
Print["Numero de integrales PV: ",
   Length[PVfunctions1PI]
];

Print["Integrales escalares:"];

PVfunctions1PI // TableForm


(* ========================================================== *)
(* 13. Colectar FS1PV por integrales escalares                 *)
(* ========================================================== *)

FS1Collected = Collect[
   Expand[FS1PV],
   PVfunctions,
   Simplify
];

PVcoefficients = (
   Simplify[
      Coefficient[FS1Collected, #]
   ] &
) /@ PVfunctions;

(* Comprobar que no quedan terminos independientes *)

FS1Remainder = FullSimplify[
   FS1Collected -
      Total[PVcoefficients PVfunctions]
];

Print["Resto de la descomposicion: ",
   FS1Remainder
];


(* ========================================================== *)
(* 14. Resultados finales en representacion PV                 *)
(* ========================================================== *)

FS1Result = FS1Collected;
FP1Result = FP1PV;

Print["FS1 obtenido en terminos de integrales PV."];
Print["FP1 obtenido en terminos de integrales PV."];



(* ========================================================== *)
(* 15. Extraccion de divergencias UV e IR                      *)
(* ========================================================== *)

(* Cargar FeynHelpers y Package-X si no estan cargados *)


(* Polo ultravioleta de la amplitud 1PI *)

FS1UV = PaXEvaluateUV[FS1PV] // Simplify;

(* Polo infrarrojo de la amplitud 1PI *)

FS1IR = PaXEvaluateIR[FS1PV] // Simplify;

(* Mostrar los resultados *)

Print["Polo UV:"];
FS1UV

Print["Polo IR:"];
FS1IR


(* ::Subtitle:: *)
(*COUNTER TERMS*)


ClearAll[DeltaCTHMuMu, MCTHMuMu];

Get[
  "/home/acer/Desktop/ubuntu/FTeorica/Projects/Hmm_2026/Programs/DennerLeptons.wl"
];


(* ::Title:: *)
(*COMPARACIONES*)


(* ========================================================== *)
(* CANCELACION UV DE H -> mu+ mu- A UN LOOP                     *)
(* MODELO ESTANDAR - ESQUEMA ON-SHELL                 *)
(* GAUGE DE 'T HOOFT-FEYNMAN: xi = 1                            *)
(* ========================================================== *)



Get[
  FileNameJoin[{
    NotebookDirectory[],
    "DennerLeptons.wl"
  }]
];

ClearAll[
  uvNormalize, ckUV,
  uvMassMu, uvZMuL, uvZMuR,
  uvZHiggs, uvMassW, uvMassZ,
  uvCharge, uvAngleW,
  uvCTPartes, uvCTDirecto, uvCT,
  uvVertice, uvTotal,
  checkCT, testUV,
  rulesUV, rulesOS
];

(* 2. UNIFICAR CONVENCIONES                                    *)


rulesUV = {
  EL -> e,

  ME -> me,
  MM -> mm,
  ML -> ml,

  MU -> muq,
  MC -> mc,
  MT -> mt,

  MD -> md,
  MS -> ms,
  MB -> mb,

  MW -> mw,
  MZ -> mz,
  MH -> mh,

  SMP["e"] -> e,

  SMP["m_e"] -> me,
  SMP["m_mu"] -> mm,
  SMP["m_tau"] -> ml,

  SMP["m_u"] -> muq,
  SMP["m_c"] -> mc,
  SMP["m_t"] -> mt,

  SMP["m_d"] -> md,
  SMP["m_s"] -> ms,
  SMP["m_b"] -> mb,

  SMP["m_W"] -> mw,
  SMP["m_Z"] -> mz,
  SMP["m_H"] -> mh,

  SMP["sin_W"] -> sw,
  SMP["cos_W"] -> cw
};

(* Relaciones de masa del esquema OS *)

rulesOS = {
  cw -> Sqrt[1 - sw^2],
  mz -> mw/Sqrt[1 - sw^2]
};


(* Funcion de normalizacion y unitariedad CKM *)

uvNormalize[expr_] := Module[{res},

  res = expr /. rulesUV;

  (* CKM: |Vij|^2 *)

  res = res /.
    HoldPattern[
      Abs[VCKM[i_Integer, j_Integer]]^2
    ] :> ckUV[i, j];

  (* Unitariedad por filas *)

  Do[
    res = res /.
      ckUV[i, 3] ->
        (1 - ckUV[i, 1] - ckUV[i, 2]),
    {i, 1, 3}
  ];

  (* Unitariedad por columnas *)

  Do[
    res = res /.
      ckUV[3, j] ->
        (1 - ckUV[1, j] - ckUV[2, j]),
    {j, 1, 2}
  ];

  res = res /. rulesOS;

  Factor[Together[res]]
];


PaXEvaluateUV[FS1PV]//uvNormalize
PaXEvaluateUV[DeltaCTHMuMu[]]//uvNormalize//FullSimplify


(* ========================================================== *)
(* 3. POLOS UV DE LAS CONSTANTES OS                             *)
(* ========================================================== *)

Print["========================================"];
Print["CONSTANTES DE RENORMALIZACION OS"];
Print["========================================"];

(* Masa del muon *)

uvMassMu = PaXEvaluateUV[
  DeltaMf[2, 2]/MM
];

(* Renormalizacion de campos del muon *)

uvZMuL = PaXEvaluateUV[
  DeltaZfL[2, 2, 2]/2
];

uvZMuR = PaXEvaluateUV[
  DeltaZfR[2, 2, 2]/2
];

(* Campo del Higgs *)

uvZHiggs = PaXEvaluateUV[
  DeltaZH[]/2
];

(* Masa del W *)

uvMassW = PaXEvaluateUV[
  -DeltaMW2[]/(2 MW^2)
];

(* Masa del Z, para comprobar el esquema OS *)

uvMassZ = PaXEvaluateUV[
  DeltaMZ2[]
];

(* Carga electrica *)

uvCharge = PaXEvaluateUV[
  DeltaZe[]
];

(* Angulo de Weinberg *)

uvAngleW = PaXEvaluateUV[
  -DeltaSWOverSW[]
];


(* ========================================================== *)
(* 4. CONTRIBUCIONES UV INDIVIDUALES                            *)
(* ========================================================== *)

Print["========================================"];
Print["POLOS UV INDIVIDUALES"];
Print["========================================"];

Print["delta m_mu / m_mu:"];
Print[uvNormalize[uvMassMu]];

Print["delta Z_mu^L / 2:"];
Print[uvNormalize[uvZMuL]];

Print["delta Z_mu^R / 2:"];
Print[uvNormalize[uvZMuR]];

Print["delta Z_H / 2:"];
Print[uvNormalize[uvZHiggs]];

Print["-delta MW^2 / (2 MW^2):"];
Print[uvNormalize[uvMassW]];

Print["delta Ze:"];
Print[uvNormalize[uvCharge]];

Print["-delta sw / sw:"];
Print[uvNormalize[uvAngleW]];


(* ========================================================== *)
(* 5. RECONSTRUIR EL CONTRATERMINO TOTAL                        *)
(* ========================================================== *)

uvCTPartes = uvNormalize[
  (
    uvMassMu
    + uvZMuL
    + uvZMuR
    + uvZHiggs
    + uvMassW
    + uvCharge
    + uvAngleW
  )
];

(* Calcular tambien el CT directamente del paquete *)

uvCTDirecto = uvNormalize[
  PaXEvaluateUV[
    DeltaCTHMuMu[]
  ]
];

(* Comprobar consistencia interna *)

checkCT = Factor[
  Together[
    uvCTPartes - uvCTDirecto
  ]
];

Print["========================================"];
Print["CONTRATERMINO TOTAL"];
Print["========================================"];

Print["UV de la suma de constantes:"];
Print[uvCTPartes];

Print["UV directamente de DeltaCTHMuMu[]:"];
Print[uvCTDirecto];

Print["Diferencia entre ambas evaluaciones:"];
Print[checkCT];

Print["Consistencia interna del CT: ",
  TrueQ[checkCT === 0]
];

uvCT = uvCTPartes;


(* ==========================================================  *)
(* 6. VERTICE 1PI H -> mu+ mu-                                  *)
(* ==========================================================  *)

Print["========================================"];
Print["VERTICE 1PI"];
Print["========================================"];

If[!ValueQ[FS1PV] || !ValueQ[FS0],

  Print["ERROR: FS1PV o FS0 no estan definidos."];
  Print["Ejecuta primero el calculo del vertice 1PI."];

  Abort[]
];

(* Factor relativo a la amplitud de arbol *)

uvVertice = uvNormalize[
  PaXEvaluateUV[
    FS1PV/FS0
  ]
];

Print["Polo UV del vertice 1PI:"];
Print[uvVertice];


(* ========================================================== *)
(* 7. CANCELACION UV TOTAL                                     *)
(* ========================================================== *)

uvTotal = Factor[
  Together[
    uvVertice + uvCT
  ]
];

testUV = TrueQ[
  uvTotal === 0
];

Print["========================================"];
Print["CANCELACION ULTRAVIOLETA"];
Print["========================================"];

Print["UV vertice 1PI:"];
Print[uvVertice];

Print["UV contrat\[EAcute]rmino OS:"];
Print[uvCT];

Print["========================================"];
Print["RESIDUO ULTRAVIOLETA TOTAL"];
Print["========================================"];

Print["UV total: ", uvTotal];

Print["Cancelacion UV exacta: ", testUV];


(* ========================================================== *)
(* 8. DIAGNOSTICO SI LA CANCELACION NO ES EXACTA                *)
(* ========================================================== *)

If[!testUV,

  Print["========================================"];
  Print["DIAGNOSTICO DEL RESIDUO"];
  Print["========================================"];

  Print["Coeficiente de mt^2: ",
    Factor[
      Coefficient[Expand[uvTotal], mt^2]
    ]
  ];

  Print["Coeficiente de mh^2: ",
    Factor[
      Coefficient[Expand[uvTotal], mh^2]
    ]
  ];

  Print["Coeficiente de mm^2: ",
    Factor[
      Coefficient[Expand[uvTotal], mm^2]
    ]
  ];

  Print[
    "Hay un polo UV residual. ",
    "Revisar las contribuciones y convenciones ",
    "antes de modificar el contratermino."
  ];

];



FS1Ren = (
  FS1PV + FS0 DeltaCTHMuMu[]
);

deltaVirtual = (
  FS1Ren/FS0
);


deltaVirtual = FS1PV/FS0 + DeltaCTHMuMu[];


(* ::Title:: *)
(*IR DIV*)


(* ============================================================ *)
(* H -> mu+ mu- : DIVERGENCIAS IR Y UV EN EL ESQUEMA OS          *)
(* ============================================================ *)

ClearAll[
  PVFunctions, PVPhoton, evaluarIR,
  CoefLogPhoton, DetectarIRPhoton,
  ct, pvPhoton, expansionesIR, ctExpandido,
  ir1PI, ACT, uvCTOriginal, uvCTExpandido,
  testUV
];





(* ============================================================ *)
(* 1. FUNCIONES AUXILIARES                                      *)
(* ============================================================ *)

(* Extraer integrales maestras sin repeticiones *)

PVFunctions[expr_] := DeleteDuplicates @ Cases[
   expr,
   _PaVe | _A0 | _B0 | _B1 | _C0 | _D0 | _DB0 | _DB1,
   Infinity
];


(* Seleccionar integrales que contienen la masa fotonica *)

PVPhoton[expr_] := Select[
   PVFunctions[expr],
   ! FreeQ[#, lambdaPhoton] &
];


(* ============================================================ *)
(* 2. EVALUACION Y EXPANSION EN lambdaPhoton -> 0                *)
(* ============================================================ *)

evaluarIR[pv_] := evaluarIR[pv] = Module[{s, expr},

   s = Unique["s"];

   expr = Switch[Head[pv],

     DB0,
     D[
        PaXEvaluate[
           B0[s, pv[[2]], pv[[3]]],
           PaXAnalytic -> True
        ],
        s
     ] /. s -> pv[[1]],

     DB1,
     D[
        PaXEvaluate[
           B1[s, pv[[2]], pv[[3]]],
           PaXAnalytic -> True
        ],
        s
     ] /. s -> pv[[1]],

     _,
     PaXEvaluate[pv, PaXAnalytic -> True]
   ];

   Normal @ Assuming[
      MM > 0 && MW > 0 && lambdaPhoton > 0,
      FullSimplify[
         Series[expr, {lambdaPhoton, 0, 0}]
      ]
   ]
];


(* ============================================================ *)
(* 3. COEFICIENTE DEL LOGARITMO FOTONICO                         *)
(* ============================================================ *)

(* Si I = A Log[lambdaPhoton] + B + o(1), devuelve A *)

CoefLogPhoton[pv_] := CoefLogPhoton[pv] = Module[{res},

   res = evaluarIR[pv];

   FullSimplify[
      Limit[
         lambdaPhoton D[res, lambdaPhoton],
         lambdaPhoton -> 0,
         Direction -> "FromAbove"
      ],
      Assumptions -> MM > 0 && MW > 0
   ]
];


(* Identificar integrales con divergencia logaritmica fotonica *)

DetectarIRPhoton[expr_] := Module[{lista, tabla},

   lista = PVPhoton[expr];

   tabla = ({#, CoefLogPhoton[#]} & /@ lista);

   Select[
      tabla,
      TrueQ[
         FullSimplify[
            Last[#] != 0,
            Assumptions -> MM > 0 && MW > 0
         ]
      ] &
   ]
];


(* ============================================================ *)
(* 4. CONTRATERMINO OS                                          *)
(* ============================================================ *)

ct = DeltaCTHMuMu[];

(* Integrales que contienen lambdaPhoton *)

pvPhoton = PVPhoton[ct];


(* Identificar las IR divergentes *)

DetectarIRPhoton[ct] // TableForm

(* Evaluar y expandir todas las integrales fotonicas *)

expansionesIR = (
   Rule[#, evaluarIR[#]] & /@ pvPhoton
);


(* Contratermino con integrales fotonicas expandidas *)

ctExpandido = ct /. expansionesIR;



(* ============================================================ *)
(* 5. COEFICIENTES IR                                           *)
(* ============================================================ *)

(* 5.1. Vertice 1PI: polo dimensional *)

ir1PI = FullSimplify[
   PaXEvaluateIR[FS1PV/FS0]
];


(* 5.2. Contratermino: coeficiente de Log[lambdaPhoton^2] *)

ACT = FullSimplify[
   Limit[
      Coefficient[
         Expand[ctExpandido],
         Log[lambdaPhoton]
      ]/2,
      lambdaPhoton -> 0,
      Direction -> "FromAbove"
   ] /. rulesUV /. rulesOS,
   Assumptions -> 0 < sw < 1 && mm > 0 && mw > 0
];

ACT = Factor[ACT];


(* ============================================================ *)
(* 6. POLOS UV DEL CONTRATERMINO                                *)
(* ============================================================ *)

(* 6.1. Contratermino original *)

uvCTOriginal = FullSimplify[
   uvNormalize[
      PaXEvaluateUV[ct]
   ],
   Assumptions -> 0 < sw < 1 && mm > 0 && mw > 0
];


(* 6.2. Contratermino con integrales fotonicas expandidas *)

uvCTExpandido = FullSimplify[
   uvNormalize[
      PaXEvaluateUV[ctExpandido]
   ] /. lambdaPhoton -> 0,
   Assumptions -> 0 < sw < 1 && mm > 0 && mw > 0
];

(* ============================================================ *)
(* 7. COMPROBACION UV                                           *)
(* ============================================================ *)

testUV = TrueQ[
   FullSimplify[
      uvCTOriginal == uvCTExpandido,
      Assumptions -> 0 < sw < 1 && mm > 0 && mw > 0
   ]
];



(* ============================================================ *)
(* 8. RESULTADOS                                                *)
(* ============================================================ *)

Print["Integrales fotonicas: ", Length[pvPhoton]];

Print["Integrales IR divergentes:"];
DetectarIRPhoton[ct] // TableForm

Print["Coeficiente IR del contrat\[EAcute]rmino:"];
ACT // TraditionalForm

Print["Polo UV del contrat\[EAcute]rmino original:"];
uvCTOriginal // TraditionalForm

Print["Polo UV del contrat\[EAcute]rmino expandido:"];
uvCTExpandido // TraditionalForm

Print["Coincidencia UV: ", testUV];

Print["Polo IR dimensional del v\[EAcute]rtice 1PI:"];
ir1PI // TraditionalForm


(* ::Title:: *)
(*Finite, UV and IR parts of 1PI*)


(* Parte UV *)
UV1PI = PaXEvaluateUV[FS1PV/FS0];

(* Parte IR *)
IR1PI = PaXEvaluateIR[FS1PV/FS0];

(* Evaluacion completa *)
Full1PI = PaXEvaluateUVIRSplit[
   FS1PV/FS0,
   PaXAnalytic -> True,
   PaXC0Expand -> True
];

(* Parte finita *)
Fin1PI = SeriesCoefficient[
   SeriesCoefficient[Full1PI, {EpsilonUV, 0, 0}],
   {EpsilonIR, 0, 0}
];


(* ::Title:: *)
(*Finite, UV and IR parts of the counterterm*)


ct = DeltaCTHMuMu[];

(* Identificar solo integrales con masa fotonica *)
pvPhoton = PVPhoton[ct];

(* Evaluarlas individualmente *)
expansionesIR = Rule[#, evaluarIR[#]] & /@ pvPhoton;

(* Incorporar los resultados al contratermino *)
ctExpandido = ct /. expansionesIR;

ACT = Factor @ FullSimplify[
   Limit[
      Coefficient[Expand[ctExpandido], Log[lambdaPhoton]]/2,
      lambdaPhoton -> 0,
      Direction -> "FromAbove"
   ] /. rulesUV /. rulesOS,
   Assumptions -> 0 < sw < 1 && mm > 0 && mw > 0
];


(* ::Title:: *)
(*DECAY WIDTH NLO VIRTUAL*)


(* Contratermino OS relativo *)
deltaCT = DeltaCTHMuMu[];

(* Correccion relativa renormalizada *)
deltaVirtual = FS1PV/FS0 + deltaCT;

(* Factor cinematico *)
beta = Sqrt[1 - 4 mm^2/mh^2];

(* Ancho a nivel arbol *)
GammaLO = mh beta^3/(8 Pi) Abs[FS0]^2;

(* Correccion virtual a NLO *)
DeltaGammaVirtual =
  2 GammaLO Re[deltaVirtual];

(* Ancho virtual a NLO *)
GammaVirtualNLO =
  GammaLO + DeltaGammaVirtual;


(* ::Title:: *)
(*Bresmtralumh*)


(* ============================================================ *)
(* H -> mu- mu+ gamma                                           *)
(* FEYNARTS + FEYNCALC                                         *)
(* Amplitud real y ancho radiativo                              *)
(* ============================================================ *)


(* ============================================================ *)
(* 1. GENERACION DE DIAGRAMAS                                  *)
(* ============================================================ *)

top = CreateTopologies[
   0,
   1 -> 3
];

diag = InsertFields[
   top,
   S[1] -> {F[2, {2}], -F[2, {2}], V[1]},
   Model -> "SM",
   InsertionLevel -> {Particles},
   ExcludeParticles -> {S[2]}
];

Paint[
   diag,
   ColumnsXRows -> {2, 1},
   Numbering -> Simple,
   SheetHeader -> None
];


(* ============================================================ *)
(* 2. AMPLITUDES DE FEYNARTS                                   *)
(* ============================================================ *)

ampFA = CreateFeynAmp[
   diag,
   Truncated -> True,
   PreFactor -> 1
];


(* ============================================================ *)
(* 3. CONVERSION A FEYNCALC                                    *)
(* ============================================================ *)

ampFC = FCFAConvert[
   ampFA,
   IncomingMomenta -> {p},
   OutgoingMomenta -> {p1, p2, k},
   LoopMomenta -> {},
   ChangeDimension -> 4,
   UndoChiralSplittings -> True,
   SMP -> True,
   List -> False,
   Contract -> True
];

(* Unificar parametros *)

ampFC = ampFC /. {
   SMP["m_mu"] -> mm,
   SMP["m_W"] -> mw,
   SMP["sin_W"] -> sw,
   SMP["e"] -> e
};


(* ============================================================ *)
(* 4. CONDICIONES ON-SHELL                                     *)
(* ============================================================ *)

FCClearScalarProducts[];

SP[p1, p1] = mm^2;
SP[p2, p2] = mm^2;
SP[k, k] = 0;
SP[p, p] = mh^2;


(* ============================================================ *)
(* 5. AMPLITUD FISICA                                          *)
(* ============================================================ *)

(* p1 = mu-
   p2 = mu+
   k  = photon *)

ampReal = FCI[
   SpinorUBar[p1, mm] .
   ampFC .
   SpinorV[p2, mm] *
   Pair[
     LorentzIndex[Lor1],
     Momentum[Polarization[k, -I]]
   ]
];


(* ============================================================ *)
(* 6. MODULO CUADRADO                                          *)
(* ============================================================ *)

ampProducto =
   ampReal ComplexConjugate[ampReal];

(* Suma de polarizaciones del foton sin masa *)

ampPol = DoPolarizationSums[
   ampProducto,
   k,
   0
];

(* Suma de espines fermionicos *)

ampSpin = FermionSpinSum[
   ampPol,
   ExtraFactor -> 1
];

(* Evaluacion de trazas y contracciones *)

ampSquared = ampSpin //
   DiracSimplify //
   Contract //
   ExpandScalarProduct //
   FeynAmpDenominatorExplicit //
   Together //
   Factor;


(* ====================================================== *)
(* H -> mu+ mu- gamma : ANCHO REAL E IR                    *)
(* Partir de ampSquared ya calculado                      *)
(* ====================================================== *)

ClearAll[
  sInv, zAng, xSoft, betaS, betaH,
  ampSquaredKin, dGammaReal,
  coefSoftAngular, coefLogReal, AReal,
  GammaLOFA, atanhSobreX,
  GammaSoftRealNLO, GammaHardRealNLO,
  GammaRealPartesNLO,
  resIR1PI, coefIR1PI, coefIRCT,
  AIVirtualNuevo
];

assIR = mh > 2 mm > 0 && mw > 0 &&
        e > 0 && 0 < sw < 1;

(* ====================================================== *)
(* 1. CINEMATICA Y ANCHO DIFERENCIAL                      *)
(* ====================================================== *)

betaS = Sqrt[1 - 4 mm^2/sInv];
betaH = Sqrt[1 - 4 mm^2/mh^2];

reglasCinematicas = {
  FCI[SP[p1, p2]] -> (sInv - 2 mm^2)/2,

  FCI[SP[k, p1]] ->
    (mh^2 - sInv) (1 - betaS zAng)/4,

  FCI[SP[k, p2]] ->
    (mh^2 - sInv) (1 + betaS zAng)/4
};

ampSquaredKin = Factor[
  Together[ampSquared /. reglasCinematicas]
];

dGammaReal =
  (mh^2 - sInv) betaS/(512 Pi^3 mh^3) *
  ampSquaredKin;

Print["Cinematica reducida: ",
  FreeQ[FCI[ampSquaredKin],
    Momentum[p1] | Momentum[p2] | Momentum[k]]
];

(* ====================================================== *)
(* 2. COEFICIENTE IR DEL ANCHO REAL                       *)
(* ====================================================== *)

coefSoftAngular = FullSimplify[
  Limit[
    xSoft^2 (
      ampSquaredKin /. sInv -> mh^2 - xSoft
    ),
    xSoft -> 0,
    Direction -> "FromAbove"
  ],
  Assumptions -> assIR && -1 < zAng < 1
];

coefLogReal = FullSimplify[
  betaH/(512 Pi^3 mh^3) *
    Integrate[
      coefSoftAngular,
      {zAng, -1, 1},
      Assumptions -> assIR
    ],
  Assumptions -> assIR
];

(* Coeficiente de Log[lambdaPhoton^2/mm^2] *)

AReal = -coefLogReal/2;

(* Normalizacion LO correcta *)

GammaLOFA =
  mh betaH^3/(8 Pi) *
  (e mm/(2 mw sw))^2;

Print["Coeficiente IR real:"];
AReal // TraditionalForm


(* ====================================================== *)
(* 3. ANCHO SOFT CON REGULADOR DE MASA FOTONICA           *)
(* ====================================================== *)

atanhSobreX[x_?NumericQ] :=
  If[Abs[x] < 10^-8,
    1 + x^2/3 + x^4/5,
    ArcTanh[x]/x
  ];

GammaSoftRealNLO[pr_List, corte_?NumericQ,
   lam_?NumericQ] :=
 Module[{H, M, W, SW, EE, b, lo, t},

  {H, M, W, SW, EE} =
    N[{mh, mm, mw, sw, e} /. pr];

  If[
    !TrueQ[
      H > 2 M > 0 &&
      0 < lam < corte <
        (H^2 - 4 M^2)/(2 H)
    ],
    Return[$Failed]
  ];

  b = Sqrt[1 - 4 M^2/H^2];

  lo = H b^3/(8 Pi) *
    (EE M/(2 W SW))^2;

  lo EE^2/(2 Pi^2) *
    NIntegrate[
      Tanh[t]^2 *
       (
        (1 + b^2) *
          atanhSobreX[b Tanh[t]]
        -
        (1 - b^2)/
          (1 - b^2 Tanh[t]^2)
       ),
      {t, 0, ArcCosh[corte/lam]},
      Method -> "GlobalAdaptive"
    ]
];


(* ====================================================== *)
(* 4. ANCHO HARD A PARTIR DE FeynCalc                     *)
(* ====================================================== *)

GammaHardRealNLO[pr_List, corte_?NumericQ] :=
 Module[{H, M, expr},

  {H, M} = N[{mh, mm} /. pr];

  If[
    !TrueQ[
      H > 2 M > 0 &&
      0 < corte < (H^2 - 4 M^2)/(2 H)
    ],
    Return[$Failed]
  ];

  expr = N[dGammaReal /. pr];

  NIntegrate[
    Evaluate[expr],
    {sInv, 4 M^2, H^2 - 2 H corte},
    {zAng, -1, 1},
    Method -> "GlobalAdaptive",
    MaxRecursion -> 15
  ]
];


(* ====================================================== *)
(* 5. ANCHO REAL TOTAL = SOFT + HARD                      *)
(* ====================================================== *)

GammaRealPartesNLO[pr_List, corte_?NumericQ,
   lam_?NumericQ] :=
 Module[{gs, gh},

  gs = GammaSoftRealNLO[pr, corte, lam];
  gh = GammaHardRealNLO[pr, corte];

  If[!And @@ (NumericQ /@ {gs, gh}),
    Return[$Failed]
  ];

  <|
    "GammaSoft" -> gs,
    "GammaHard" -> gh,
    "GammaReal" -> gs + gh,
    "CoefIRReal" -> N[AReal /. pr]
  |>
];


(* ====================================================== *)
(* 6. COEFICIENTE IR VIRTUAL: 1PI + CT OS                 *)
(* ====================================================== *)

(* Residuo del polo dimensional del 1PI *)

resIR1PI = FullSimplify[
  Limit[
    EpsilonIR *
      PaXEvaluateIR[FS1PV/FS0],
    EpsilonIR -> 0
  ] /. rulesUV /. rulesOS,
  Assumptions -> assIR
];

coefIR1PI = FullSimplify[
  ComplexExpand[Re[resIR1PI]],
  Assumptions -> assIR
];

(* ACT fue extraido previamente del CT con lambdaPhoton *)

coefIRCT = ACT;

(* Factor 2 de interferencia: aparece UNA sola vez *)

AIVirtualNuevo = FullSimplify[
  2 GammaLOFA (coefIR1PI + coefIRCT),
  Assumptions -> assIR
];

Print["Coeficiente IR virtual:"];
AIVirtualNuevo // TraditionalForm


(* ====================================================== *)
(* 7. COMPARACION DE COEFICIENTES IR                      *)
(* ====================================================== *)

parsIR = {
  mh -> 125.25,
  mm -> 0.1056583755,
  mw -> 80.379,
  sw -> Sqrt[1 - (80.379/91.1876)^2],
  e -> Sqrt[4 Pi/137.035999084]
};

comparacionIR = N[
  {
    AIVirtualNuevo,
    AReal,
    AIVirtualNuevo + AReal,
    AIVirtualNuevo/(-AReal)
  } /. parsIR,
  16
];

Print["IR virtual = ", comparacionIR[[1]]];
Print["IR real    = ", comparacionIR[[2]]];
Print["Suma IR    = ", comparacionIR[[3]]];
Print["Relacion   = ", comparacionIR[[4]]];


(* ====================================================== *)
(* 8. EVALUAR EL ANCHO REAL                               *)
(* ====================================================== *)

ResultadoReal = GammaRealPartesNLO[
  parsIR, 0.1, 0.0001
];

If[AssociationQ[ResultadoReal],
  ResultadoReal // Dataset
]


(* Par\[AAcute]metros num\[EAcute]ricos para H -> mu+ mu- *)

parSMNLO = {
  e -> Sqrt[4 Pi/137.035999084],
  mw -> 80.3625,
  mz -> 91.1876,
  sw -> Sqrt[1 - (80.3625/91.1876)^2],

  me -> 0.00051099895,
  mm -> 0.1056583755,
  ml -> 1.77693,

  muq -> 0.00216,
  md -> 0.00467,
  ms -> 0.093,
  mc -> 1.27,
  mb -> 4.18,
  mt -> 172.69
};




(* ============================================== *)
(* 1. CARGAR LAS FUNCIONES DEL CALCULO            *)
(* ============================================== *)

Get[
  FileNameJoin[{
    NotebookDirectory[],
    "Tablas_GammaLO_GammaReal_Muon_Tau_1000.m"
  }]
];

(* ============================================== *)
(* 2. CREAR LAS CUATRO LISTAS                     *)
(* ============================================== *)

construirTablasReal[];

(* Las listas ya quedan definidas como:
   tablaLOMu, tablaLOTau,
   tablaRealMu, tablaRealTau
*)

Print["LO muon: ", Length[tablaLOMu]];
Print["Real muon: ", Length[tablaRealMu]];
Print["LO tau: ", Length[tablaLOTau]];
Print["Real tau: ", Length[tablaRealTau]];

(* ============================================== *)
(* 3. EXPORTAR LAS LISTAS EN GeV                  *)
(* ============================================== *)

guardarReal[NotebookDirectory[]];

(* ============================================== *)
(* 4. CREAR TAMBIEN LAS LISTAS EN keV             *)
(* ============================================== *)

tablaLOMuKeV =
  {#[[1]], 10^6 #[[2]]} & /@ tablaLOMu;

tablaLOTauKeV =
  {#[[1]], 10^6 #[[2]]} & /@ tablaLOTau;

tablaRealMuKeV =
  {#[[1]], 10^6 #[[2]]} & /@ tablaRealMu;

tablaRealTauKeV =
  {#[[1]], 10^6 #[[2]]} & /@ tablaRealTau;

(* ============================================== *)
(* 5. EXPORTAR LAS LISTAS EN keV                  *)
(* ============================================== *)

listasKeV = {
  tablaLOMuKeV,
  tablaLOTauKeV,
  tablaRealMuKeV,
  tablaRealTauKeV
};

nombresKeV = {
  "GammaLO_Muon_keV.csv",
  "GammaLO_Tau_keV.csv",
  "GammaReal_Muon_keV.csv",
  "GammaReal_Tau_keV.csv"
};

MapThread[
  Export[
    FileNameJoin[{NotebookDirectory[], #1}],
    Prepend[#2, {"mH_GeV", "Gamma_keV"}],
    "CSV"
  ] &,
  {nombresKeV, listasKeV}
];

Print["Todas las listas exportadas."];




