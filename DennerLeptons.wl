(* ::Package:: *)

Needs["FeynCalc`"];

ClearAll[
  DeltaMf, DeltaZfL, DeltaZfR,
  sigL, sigR, sigS,
  sigmaSum, sigmaSumPrime
];


(* AUTOENERGIAS DE LEPTONES                           *)


sigL[x_, m_] := -EL^2/(16 Pi^2) (
    2 B1[x, m^2, lambdaPhoton^2] + 1

    + (SMP["sin_W"]^2 - 1/2)^2/
        (SMP["sin_W"]^2 SMP["cos_W"]^2) *
        (2 B1[x, m^2, MZ^2] + 1)

    + m^2/(4 SMP["sin_W"]^2 MW^2) *
        (B1[x, m^2, MZ^2] + B1[x, m^2, MH^2])

    + (2 B1[x, 0, MW^2] + 1)/(2 SMP["sin_W"]^2)
);

sigR[x_, m_] := -EL^2/(16 Pi^2) (
    2 B1[x, m^2, lambdaPhoton^2] + 1

    + SMP["sin_W"]^2/SMP["cos_W"]^2 *
        (2 B1[x, m^2, MZ^2] + 1)

    + m^2/(4 SMP["sin_W"]^2 MW^2) *
        (B1[x, m^2, MZ^2] + B1[x, m^2, MH^2])

    + m^2/(2 SMP["sin_W"]^2 MW^2) *
        B1[x, 0, MW^2]
);

sigS[x_, m_] := -EL^2/(16 Pi^2) (
    4 B0[x, m^2, lambdaPhoton^2] - 2

    + (SMP["sin_W"]^2 - 1/2)/SMP["cos_W"]^2 *
        (4 B0[x, m^2, MZ^2] - 2)

    + m^2/(4 SMP["sin_W"]^2 MW^2) *
        (B0[x, m^2, MZ^2] - B0[x, m^2, MH^2])
);

sigmaSum[x_, m_] :=
  sigL[x, m] + sigR[x, m] + 2 sigS[x, m];


(* ================================================== *)
(* DERIVADA RESPECTO A p^2                            *)
(* ================================================== *)

ClearAll[sigmaSumPrime, pSquaredAux];

sigmaSumPrime[x_, m_] := Module[{expr},

  expr = D[
    sigmaSum[pSquaredAux, m],
    pSquaredAux
  ];

  expr = expr /. {
    Derivative[1, 0, 0][B0][q_, a_, b_] :>
      DB0[q, a, b],

    Derivative[1, 0, 0][B1][q_, a_, b_] :>
      DB1[q, a, b]
  };

  expr /. pSquaredAux -> x
];



(* CONSTANTES OS DE MASA Y CAMPOS FERMIONICOS         *)


DeltaMf[2, j_Integer /; 1 <= j <= 3] :=
  With[{m = {ME, MM, ML}[[j]]},
    m/2 sigmaSum[m^2, m]
  ];

DeltaZfL[2, i_Integer, j_Integer] /;
    1 <= i <= 3 && 1 <= j <= 3 && i == j :=
  With[{m = {ME, MM, ML}[[i]]},
    -sigL[m^2, m] - m^2 sigmaSumPrime[m^2, m]
  ];

DeltaZfR[2, i_Integer, j_Integer] /;
    1 <= i <= 3 && 1 <= j <= 3 && i == j :=
  With[{m = {ME, MM, ML}[[i]]},
    -sigR[m^2, m] - m^2 sigmaSumPrime[m^2, m]
  ];

DeltaZfL[2, i_Integer, j_Integer] /;
    1 <= i <= 3 && 1 <= j <= 3 && i != j := 0;

DeltaZfR[2, i_Integer, j_Integer] /;
    1 <= i <= 3 && 1 <= j <= 3 && i != j := 0;



(* PARAMETROS                    *)

denS = SMP["sin_W"];
denC = SMP["cos_W"];

(* {masa, carga, isospin, color} *)

denFermions = {
  {0, 0, 1/2, 1},
  {0, 0, 1/2, 1},
  {0, 0, 1/2, 1},

  {ME, -1, -1/2, 1},
  {MM, -1, -1/2, 1},
  {ML, -1, -1/2, 1},

  {MU, 2/3, 1/2, 3},
  {MC, 2/3, 1/2, 3},
  {MT, 2/3, 1/2, 3},

  {MD, -1/3, -1/2, 3},
  {MS, -1/3, -1/2, 3},
  {MB, -1/3, -1/2, 3}
};

denGM[q_, t_] :=
  (t - q denS^2)/(denS denC);

denGP[q_, t_] :=
  -q denS/denC;

denUp = {MU, MC, MT};
denDown = {MD, MS, MB};

denCKM[i_, j_] := VCKM[i, j];



(* 1. AUTOENERGIA DEL FOTON - DENNER (B.1)            *)


sigAA[x_] := -EL^2/(16 Pi^2) (

  2/3 Total[
    (
      #[[4]] 2 #[[2]]^2 *
      (
        -(x + 2 #[[1]]^2) *
          B0[x, #[[1]]^2, #[[1]]^2]

        + 2 #[[1]]^2 *
          B0[0, #[[1]]^2, #[[1]]^2]

        + x/3
      )
    ) & /@ denFermions
  ]

  + (3 x + 4 MW^2) B0[x, MW^2, MW^2]

  - 4 MW^2 B0[0, MW^2, MW^2]
);


(* Derivada en x=0 *)

sigAAPrime[] := -EL^2/(16 Pi^2) (

  2/3 Total[
    (
      #[[4]] 2 #[[2]]^2 *
      (
        -B0[0, #[[1]]^2, #[[1]]^2]

        - 2 #[[1]]^2 *
          DB0[0, #[[1]]^2, #[[1]]^2]

        + 1/3
      )
    ) & /@ denFermions
  ]

  + 3 B0[0, MW^2, MW^2]

  + 4 MW^2 DB0[0, MW^2, MW^2]
);



(* 2. MEZCLA FOTON-Z - DENNER (B.2)                   *)


sigAZ[x_] := -EL^2/(16 Pi^2) (

  2/3 Total[
    (
      #[[4]] (-#[[2]]) *
      (
        denGM[#[[2]], #[[3]]]
        + denGP[#[[2]], #[[3]]]
      ) *
      (
        -(x + 2 #[[1]]^2) *
          B0[x, #[[1]]^2, #[[1]]^2]

        + 2 #[[1]]^2 *
          B0[0, #[[1]]^2, #[[1]]^2]

        + x/3
      )
    ) & /@ denFermions
  ]

  - 1/(3 denS denC) *
    (
      (
        (9 denC^2 + 1/2) x
        + (12 denC^2 + 4) MW^2
      ) B0[x, MW^2, MW^2]

      - (12 denC^2 - 2) MW^2 *
        B0[0, MW^2, MW^2]

      + x/3
    )
);



(* 3. AUTOENERGIA DEL Z - DENNER (B.3)                *)


sigZZ[x_] := -EL^2/(16 Pi^2) (

  2/3 Total[
    (
      #[[4]] *
      (
        (
          denGM[#[[2]], #[[3]]]^2
          + denGP[#[[2]], #[[3]]]^2
        ) *
        (
          -(x + 2 #[[1]]^2) *
            B0[x, #[[1]]^2, #[[1]]^2]

          + 2 #[[1]]^2 *
            B0[0, #[[1]]^2, #[[1]]^2]

          + x/3
        )

        + 3 #[[1]]^2/(4 denS^2 denC^2) *
          B0[x, #[[1]]^2, #[[1]]^2]
      )
    ) & /@ denFermions
  ]

  + 1/(6 denS^2 denC^2) *
    (
      (
        (18 denC^4 + 2 denC^2 - 1/2) x
        + (24 denC^4 + 16 denC^2 - 10) MW^2
      ) B0[x, MW^2, MW^2]

      - (24 denC^4 - 8 denC^2 + 2) MW^2 *
        B0[0, MW^2, MW^2]

      + (4 denC^2 - 1) x/3
    )

  + 1/(12 denS^2 denC^2) *
    (
      (2 MH^2 - 10 MZ^2 - x) *
        B0[x, MZ^2, MH^2]

      - 2 MZ^2 B0[0, MZ^2, MZ^2]

      - 2 MH^2 B0[0, MH^2, MH^2]

      - (MZ^2 - MH^2)^2/x *
        (
          B0[x, MZ^2, MH^2]
          - B0[0, MZ^2, MH^2]
        )

      - 2 x/3
    )
);



(* 4. AUTOENERGIA DEL W - DENNER (B.4)                *)


sigWW[x_] := -EL^2/(16 Pi^2) (

  (* Contribuciones leptonicas *)

  2/3 * 1/(2 denS^2) *
    Total[
      (
        (-x + #^2/2) B0[x, 0, #^2]

        + x/3

        + #^2 B0[0, #^2, #^2]

        + #^4/(2 x) *
          (
            B0[x, 0, #^2]
            - B0[0, 0, #^2]
          )
      ) & /@ {ME, MM, ML}
    ]

  (* Contribuciones de quarks *)

  + 2/3 * 1/(2 denS^2) *
    Sum[
      3 Abs[denCKM[i, j]]^2 *
      (
        (
          -x
          + (denUp[[i]]^2 + denDown[[j]]^2)/2
        ) *
          B0[
            x,
            denUp[[i]]^2,
            denDown[[j]]^2
          ]

        + x/3

        + denUp[[i]]^2 *
          B0[
            0,
            denUp[[i]]^2,
            denUp[[i]]^2
          ]

        + denDown[[j]]^2 *
          B0[
            0,
            denDown[[j]]^2,
            denDown[[j]]^2
          ]

        + (denUp[[i]]^2 - denDown[[j]]^2)^2/
            (2 x) *
          (
            B0[
              x,
              denUp[[i]]^2,
              denDown[[j]]^2
            ]

            - B0[
              0,
              denUp[[i]]^2,
              denDown[[j]]^2
            ]
          )
      ),
      {i, 1, 3},
      {j, 1, 3}
    ]

  (* Sector W-gamma *)

  + 2/3 *
    (
      (2 MW^2 + 5 x) *
        B0[x, MW^2, lambdaPhoton^2]

      - 2 MW^2 B0[0, MW^2, MW^2]

      - MW^4/x *
        (
          B0[x, MW^2, lambdaPhoton^2]
          - B0[0, MW^2, lambdaPhoton^2]
        )

      + x/3
    )

  (* Sector W-Z *)

  + 1/(12 denS^2) *
    (
      (
        (40 denC^2 - 1) x
        + (16 denC^2 + 54 - 10/denC^2) MW^2
      ) B0[x, MW^2, MZ^2]

      - (16 denC^2 + 2) *
        (
          MW^2 B0[0, MW^2, MW^2]

          + MZ^2 B0[0, MZ^2, MZ^2]
        )

      + (4 denC^2 - 1) (2 x/3)

      - (8 denC^2 + 1) *
        (MW^2 - MZ^2)^2/x *
        (
          B0[x, MW^2, MZ^2]
          - B0[0, MW^2, MZ^2]
        )
    )

  (* Sector W-H *)

  + 1/(12 denS^2) *
    (
      (2 MH^2 - 10 MW^2 - x) *
        B0[x, MW^2, MH^2]

      - 2 MW^2 B0[0, MW^2, MW^2]

      - 2 MH^2 B0[0, MH^2, MH^2]

      - (MW^2 - MH^2)^2/x *
        (
          B0[x, MW^2, MH^2]
          - B0[0, MW^2, MH^2]
        )

      - 2 x/3
    )
);



(* 5. AUTOENERGIA DEL HIGGS - DENNER (B.5)            *)


sigH[x_] := -EL^2/(16 Pi^2) (

  Total[
    (
      #[[4]] #[[1]]^2/(2 denS^2 MW^2) *
      (
        2 A0[#[[1]]^2]

        + (4 #[[1]]^2 - x) *
          B0[x, #[[1]]^2, #[[1]]^2]
      )
    ) & /@ denFermions
  ]

  - 1/(2 denS^2) *
    (
      (6 MW^2 - 2 x + MH^4/(2 MW^2)) *
        B0[x, MW^2, MW^2]

      + (3 + MH^2/(2 MW^2)) *
        A0[MW^2]

      - 6 MW^2
    )

  - 1/(4 denS^2 denC^2) *
    (
      (6 MZ^2 - 2 x + MH^4/(2 MZ^2)) *
        B0[x, MZ^2, MZ^2]

      + (3 + MH^2/(2 MZ^2)) *
        A0[MZ^2]

      - 6 MZ^2
    )

  - 9 MH^4/(8 denS^2 MW^2) *
      B0[x, MH^2, MH^2]

  - 3 MH^2/(8 denS^2 MW^2) *
      A0[MH^2]
);



(* DERIVADA DE LA AUTOENERGIA DEL HIGGS               *)


sigHPrime[x_] := -EL^2/(16 Pi^2) (

  Total[
    (
      #[[4]] #[[1]]^2/(2 denS^2 MW^2) *
      (
        -B0[x, #[[1]]^2, #[[1]]^2]

        + (4 #[[1]]^2 - x) *
          DB0[x, #[[1]]^2, #[[1]]^2]
      )
    ) & /@ denFermions
  ]

  - 1/(2 denS^2) *
    (
      -2 B0[x, MW^2, MW^2]

      + (6 MW^2 - 2 x + MH^4/(2 MW^2)) *
        DB0[x, MW^2, MW^2]
    )

  - 1/(4 denS^2 denC^2) *
    (
      -2 B0[x, MZ^2, MZ^2]

      + (6 MZ^2 - 2 x + MH^4/(2 MZ^2)) *
        DB0[x, MZ^2, MZ^2]
    )

  - 9 MH^4/(8 denS^2 MW^2) *
      DB0[x, MH^2, MH^2]
);



(* CONSTANTES DE RENORMALIZACION EN EL ESQUEMA OS                   *)


DeltaMW2[] := sigWW[MW^2];

DeltaMZ2[] := sigZZ[MZ^2];

DeltaZH[] := -sigHPrime[MH^2];



(* RENORMALIZACION DE LA CARGA ELECTRICA              *)


DeltaZe[] := (
    1/2 sigAAPrime[]

  - denS/denC * sigAZ[0]/MZ^2
);



(* RENORMALIZACION DEL ANGULO DE WEINBERG             *)


DeltaSWOverSW[] :=
  -denC^2/(2 denS^2) *
    (
      DeltaMW2[]/MW^2
      - DeltaMZ2[]/MZ^2
    );



(* CONTRATERMINO TOTAL H -> ell+ ell-                    *)


DeltaCTHMuMu[] := (
    DeltaMf[2, 2]/MM

  + DeltaZe[]

  - DeltaSWOverSW[]

  - DeltaMW2[]/(2 MW^2)

  + DeltaZH[]/2

  + DeltaZfL[2, 2, 2]/2

  + DeltaZfR[2, 2, 2]/2
);



(* COEFICIENTE DEL VERTICE DE CONTRATERMINO           *)


MCTHMuMu[] :=
  EL MM/(2 SMP["sin_W"] MW) *
    DeltaCTHMuMu[];

