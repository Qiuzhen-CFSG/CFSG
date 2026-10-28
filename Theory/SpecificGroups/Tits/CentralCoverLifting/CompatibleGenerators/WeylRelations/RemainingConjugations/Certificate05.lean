module
public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.WeylRelations.RemainingConjugations.Certificate04
/-!
# Checked central word identities, block 6

Every line is an application of the group-law replay lemmas. The words and
integer central-error coordinates are explicit, so Lean checks every
concatenation, inverse, rotation, and coefficient equality by reduction.
Inputs are precisely `Source D`, connected to the literal normalized
presentation in `SourceSetup`. This block is used by `DefectBounds`.

Source: Parrott (1972), §5, p.683. The discovery trace is untrusted;
these proof terms, rather than its search algorithm, certify the identities.
-/
public section
namespace Tits.CentralCoverLifting.CompatibleGenerators.RemainingConjugations
variable {G : Type*} [Group G]
theorem n1992 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 1, 2, -2, 0) [.h, .g] [.G, .f, .h, .c] :=
  (((Context.Holds.replace [] [.h, .g] (n11 D H)).symm).trans (Context.Holds.replace [.G] [] (n1974 D H)))

theorem n1993 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -1, -2, 2, 0) [.G, .f, .h, .c] [.h, .g] :=
  ((n1992 D H).symm)

theorem n1998 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 1, 4, 2, 0) [.b, .c, .d, .f] [.e, .b, .g, .I] :=
  ((((((((Context.Holds.replace [] [.b, .c] (n300 D H)).trans (Context.Holds.replace [.f] [.c] (n36 D H))).trans (Context.Holds.replace [] [.d, .c] (n40 D H))).trans (Context.Holds.replace [.b] [.c] (n25 D H))).trans (Context.Holds.replace [.b, .d] [] (n495 D H))).trans (Context.Holds.replace [.b] [.f] (n17 D H))).symm).trans (Context.Holds.cut [.h, .f, .b, .c] [.e, .b, .g, .I] (Context.Holds.rotate [.c, .i, .G, .b, .E] [.h, .f, .b] ((n1943 D H).relator))))

theorem n1999 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -1, -4, -2, 0) [.e, .b, .g, .I] [.b, .c, .d, .f] :=
  ((n1998 D H).symm)

theorem n2014 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 1, 2, 2, 0) [.d, .f] [.E, .c, .f, .E] :=
  (((((((Context.Holds.replace [.b, .f] [] (n36 D H)).trans (Context.Holds.replace [.b] [.d] (n40 D H))).trans (Context.Holds.replace [] [.f, .d] (n1 D H))).trans (Context.Holds.replace [] [] (n25 D H))).symm).trans (Context.Holds.cut [.b, .f, .h, .b] [.E, .f, .E, .c] (Context.Holds.rotate [.f, .e] [.b, .f, .h, .b, .c, .e] ((n1958 D H).relator)))).trans (Context.Holds.replace [.E] [] (n499 D H)))

theorem n2015 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -1, -2, -2, 0) [.E, .c, .f, .E] [.d, .f] :=
  ((n2014 D H).symm)

theorem n2016 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -5, -10, -2, 0) [.c, .f, .E] [.d, .e, .f] :=
  ((((Context.Holds.replace [] [.c, .f, .E] (n4 D H)).symm).trans (Context.Holds.replace [.e] [] (n2015 D H))).trans (Context.Holds.replace [] [.f] (n945 D H)))

theorem n2017 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 5, 10, 2, 0) [.d, .e, .f] [.c, .f, .E] :=
  ((n2016 D H).symm)

theorem n2018 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 1, 2, 2, 0) [.d, .f, .e] [.E, .c, .f] :=
  (((Context.Holds.replace [] [.e] (n2015 D H)).symm).trans (Context.Holds.replace [.E, .c, .f] [] (n10 D H)))

theorem n2019 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -5, -10, -2, 0) [.f, .E, .f] [.c, .d, .e] :=
  ((Context.Holds.cut [.f, .E, .f] [.c, .e, .d] (Context.Holds.rotate [.E, .c] [.f, .E, .f, .d] ((n2015 D H).relator))).trans (Context.Holds.replace [.c] [] (n945 D H)))

theorem n2020 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -1, -2, -2, 0) [.E, .d, .f] [.G, .E, .g] :=
  ((((Context.Holds.replace [.E] [] (n25 D H)).symm).trans (Context.Holds.cut [.E, .f, .d] [.f, .c, .e] (Context.Holds.rotate [.E, .c, .f] [.E, .f, .d] ((n2015 D H).relator)))).trans ((Context.Holds.replace [] [.e] (n495 D H)).trans (Context.Holds.replace [] [] (n496 D H))))

theorem n2021 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 1, 2, 2, 0) [.G, .E, .g] [.E, .d, .f] :=
  ((n2020 D H).symm)

theorem n2022 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -1, -2, -2, 0) [.d, .f, .E] [.c, .e, .f] :=
  ((((Context.Holds.replace [] [.E] (n25 D H)).symm).trans (Context.Holds.cut [.f, .d, .E] [.e, .f, .c] (Context.Holds.rotate [.E, .c, .f, .E] [.f, .d] ((n2015 D H).relator)))).trans ((Context.Holds.replace [.e] [] (n495 D H)).trans (Context.Holds.replace [] [.f] (n20 D H))))

theorem n2023 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 3, 6, -2, 0) [.E, .c, .d] [.f, .e, .f] :=
  ((((Context.Holds.replace [] [.c] (n943 D H)).trans (Context.Holds.replace [.E] [] (n17 D H))).symm).trans (Context.Holds.cut [.d, .E, .c] [.f, .e, .f] (Context.Holds.rotate [.E, .c, .f, .E, .f] [.d] ((n2015 D H).relator))))

theorem n2024 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -3, -6, 2, 0) [.f, .e, .f] [.E, .c, .d] :=
  ((n2023 D H).symm)

theorem n2025 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 3, 6, 2, 0) [.E, .f, .E] [.c, .d, .f] :=
  ((((Context.Holds.replace [] [] (n884 D H)).symm).trans (Context.Holds.cut [.e, .f, .e] [.d, .c, .f] (Context.Holds.rotate [.d] [.e, .f, .e, .f, .c] ((n2017 D H).relator)))).trans (Context.Holds.replace [] [.f] (n17 D H)))

theorem n2026 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -3, -6, -2, 0) [.c, .d, .f] [.E, .f, .E] :=
  ((n2025 D H).symm)

theorem n2027 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 5, 10, 2, 0) [.E, .g, .f] [.f, .E, .g] :=
  ((Context.Holds.cut [.E, .g, .f] [.g, .E, .d] (Context.Holds.rotate [.G] [.E, .g, .f, .d, .e] ((n2021 D H).relator))).trans (Context.Holds.replace [] [] (n950 D H)))

theorem n2028 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -5, -10, -2, 0) [.f, .E, .g] [.E, .g, .f] :=
  ((n2027 D H).symm)

theorem n2029 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 1, 2, 2, 0) [.g, .d, .f] [.d, .f, .g] :=
  ((((Context.Holds.replace [.g] [] (n25 D H)).symm).trans (Context.Holds.cut [.g, .f, .d] [.e, .g, .E] (Context.Holds.rotate [.G, .E] [.g, .f, .d, .e] ((n2021 D H).relator)))).trans (Context.Holds.replace [] [] (n1186 D H)))

theorem n2030 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -3, -6, 2, 0) [.G, .e, .f] [.f, .G, .e] :=
  (((Context.Holds.replace [] [] (n956 D H)).symm).trans (Context.Holds.cut [.d, .e, .G] [.f, .G, .e] (Context.Holds.rotate [.G, .E, .g, .f] [.d, .e] ((n2021 D H).relator))))

theorem n2031 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 3, 6, -2, 0) [.f, .G, .e] [.G, .e, .f] :=
  ((n2030 D H).symm)

theorem n2032 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 1, 2, 2, 0) [.G, .d, .f] [.d, .f, .G] :=
  (((Context.Holds.replace [] [] (n1187 D H)).symm).trans (Context.Holds.cut [.e, .G, .E] [.d, .f, .G] (Context.Holds.rotate [.G, .E, .g, .f, .d] [.e] ((n2021 D H).relator))))

theorem n2033 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -1, -2, -2, 0) [.d, .f, .G] [.G, .d, .f] :=
  ((n2032 D H).symm)

theorem n2034 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -7, -14, -2, 0) [.G, .f, .g] [.E, .f, .e] :=
  ((((Context.Holds.replace [] [] (n1202 D H)).symm).trans (Context.Holds.cut [.g, .f, .G] [.e, .f, .E] (Context.Holds.rotate [.f, .E] [.g, .f, .G, .e] ((n2028 D H).relator)))).trans (Context.Holds.replace [] [] (n886 D H)))

theorem n2035 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 1, 2, 2, 0) [.f, .G, .f] [.d, .G, .d] :=
  (Context.Holds.cut [.f, .G, .f] [.d, .G, .d] (Context.Holds.rotate [.g, .d] [.f, .G, .f, .d] ((n2029 D H).relator)))

theorem n2036 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 1, 2, 2, 0) [.d, .g, .d] [.f, .g, .f] :=
  (Context.Holds.cut [.d, .g, .d] [.f, .g, .f] (Context.Holds.rotate [.g, .d, .f, .G, .f] [.d] ((n2029 D H).relator)))

theorem n2037 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -1, -2, -2, 0) [.f, .g, .f] [.d, .g, .d] :=
  ((n2036 D H).symm)

theorem n2038 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -11, -22, -2, 0) [.E, .g, .d] [.c, .e, .g] :=
  ((((Context.Holds.replace [] [] (n963 D H)).symm).trans (Context.Holds.cut [.f, .g, .E] [.g, .E, .f] (Context.Holds.rotate [.G] [.f, .g, .E, .f, .e] ((n2034 D H).relator)))).trans (Context.Holds.replace [] [] (n487 D H)))

theorem n2039 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 11, 22, 2, 0) [.c, .e, .g] [.E, .g, .d] :=
  ((n2038 D H).symm)

theorem n2043 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 23, 46, 2, 0) [.G, .d, .g] [.E, .E, .c] :=
  ((((Context.Holds.replace [] [] (n1164 D H)).symm).trans (Context.Holds.cut [.g, .d, .G] [.E, .c, .E] (Context.Holds.rotate [.c, .e] [.g, .d, .G, .e] ((n2039 D H).relator)))).trans (Context.Holds.replace [.E] [] (n18 D H)))

theorem n2044 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 11, 22, 2, 0) [.E, .f, .G] [.d, .G, .E] :=
  ((((Context.Holds.replace [.G] [] (n20 D H)).trans (Context.Holds.replace [] [] (n485 D H))).symm).trans (Context.Holds.cut [.G, .e, .c] [.d, .G, .E] (Context.Holds.rotate [.c, .e, .g, .d] [.G, .e] ((n2039 D H).relator))))

theorem n2045 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -11, -22, -2, 0) [.d, .G, .E] [.E, .f, .G] :=
  ((n2044 D H).symm)

theorem n2049 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 23, 46, 2, 0) [.c, .d, .g] [.g, .E, .E] :=
  ((((Context.Holds.replace [.d] [] (n23 D H)).trans (Context.Holds.replace [] [.g] (n17 D H))).symm).trans (Context.Holds.cut [.d, .g, .c] [.g, .E, .E] (Context.Holds.rotate [.G] [.d, .g, .c, .e, .e] ((n2043 D H).relator))))

theorem n2050 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -23, -46, -2, 0) [.g, .E, .E] [.c, .d, .g] :=
  ((n2049 D H).symm)

theorem n2051 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 27, 54, 2, 0) [.c, .g, .e] [.E, .f, .g] :=
  ((((Context.Holds.replace [] [.e] (n23 D H)).symm).trans (Context.Holds.cut [.g, .c, .e] [.d, .g, .E] (Context.Holds.rotate [.G, .d] [.g, .c, .e, .e] ((n2043 D H).relator)))).trans (Context.Holds.replace [] [] (n1183 D H)))

theorem n2052 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 23, 46, 2, 0) [.E, .E, .G] [.G, .c, .d] :=
  ((((Context.Holds.replace [] [.G] (n13 D H)).symm).trans (Context.Holds.cut [.e, .e, .G] [.c, .G, .d] (Context.Holds.rotate [.G, .d, .g, .c] [.e, .e] ((n2043 D H).relator)))).trans (Context.Holds.replace [] [.d] (n21 D H)))

theorem n2053 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -23, -46, -2, 0) [.G, .c, .d] [.E, .E, .G] :=
  ((n2052 D H).symm)

theorem n2054 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 27, 54, 2, 0) [.G, .f, .e] [.E, .G, .c] :=
  ((((Context.Holds.replace [] [] (n1178 D H)).symm).trans (Context.Holds.cut [.e, .G, .d] [.E, .c, .G] (Context.Holds.rotate [.G, .d, .g, .c, .e] [.e] ((n2043 D H).relator)))).trans (Context.Holds.replace [.E] [] (n21 D H)))

theorem n2057 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -23, -46, -2, 0) [.c, .g, .E] [.d, .g, .e] :=
  (Context.Holds.cut [.c, .g, .E] [.d, .g, .e] (Context.Holds.rotate [.g, .E, .E, .G, .d] [.c] ((n2050 D H).relator)))

theorem n2058 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 23, 46, 2, 0) [.d, .g, .e] [.c, .g, .E] :=
  ((n2057 D H).symm)

theorem n2059 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 5, 10, 2, 0) [.E, .E, .c, .g] [.g, .d] :=
  ((((Context.Holds.replace [] [.e] (n2028 D H)).trans (Context.Holds.replace [.E] [] (n483 D H))).symm).trans (n526 D H))

theorem n2067 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 7, 14, 2, 0) [.E, .G, .E, .c] [.G, .f] :=
  (((Context.Holds.replace [.E] [] (n484 D H)).symm).trans (((Context.Holds.replace [] [.G] (n2034 D H)).symm).trans (Context.Holds.replace [.G, .f] [] (n6 D H))))

theorem n2068 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -7, -14, -2, 0) [.G, .c, .f] [.E, .G, .E] :=
  (((Context.Holds.replace [.G] [] (n495 D H)).symm).trans (((Context.Holds.replace [] [.c] (n2067 D H)).symm).trans (Context.Holds.replace [.E, .G, .E] [] (n2 D H))))

theorem n2069 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 7, 14, 2, 0) [.c, .f, .g] [.e, .g, .e] :=
  (Context.Holds.cut [.c, .f, .g] [.e, .g, .e] (Context.Holds.rotate [.E, .G, .E] [.c, .f, .g] ((n2067 D H).relator)))

theorem n2070 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -7, -14, -2, 0) [.e, .g, .e] [.c, .f, .g] :=
  ((n2069 D H).symm)

theorem n2071 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 11, 22, 2, 0) [.c, .g] [.E, .E, .g, .d] :=
  (((Context.Holds.replace [] [.g] (n277 D H)).symm).trans (Context.Holds.replace [.E] [] (n2039 D H)))

theorem n2072 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -11, -22, -2, 0) [.E, .E, .g, .d] [.c, .g] :=
  ((n2071 D H).symm)

theorem n2073 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -23, -46, -2, 0) [.E, .E, .G, .c] [.G, .d] :=
  (((Context.Holds.replace [.E, .E] [] (n21 D H)).symm).trans (((Context.Holds.replace [] [.G] (n2043 D H)).symm).trans (Context.Holds.replace [.G, .d] [] (n6 D H))))

theorem n2074 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 19, 38, 2, 0) [.E, .c, .f, .g] [.g, .e] :=
  ((((Context.Holds.replace [.c] [] (n1183 D H)).trans (Context.Holds.replace [] [.f, .g] (n18 D H))).symm).trans (((Context.Holds.replace [] [.E] (n2050 D H)).symm).trans (Context.Holds.replace [.g] [] (n274 D H))))

theorem n2077 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 5, 10, 2, 0) [.I, .E, .f, .E] [.G, .G, .I] :=
  (((Context.Holds.replace [.I] [] (n2026 D H)).symm).trans (n1876 D H))

theorem n2078 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 1, 2, 2, 0) [.E, .f, .E, .i] [.i, .G, .G] :=
  (((Context.Holds.replace [] [.i] (n2026 D H)).symm).trans (n1870 D H))

theorem n2079 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 25, 50, 6, 0) [.I, .f, .i] [.E, .G, .E, .G] :=
  (((((((((((Context.Holds.replace [] [.G, .f, .e] (n2054 D H)).trans (Context.Holds.replace [.E, .G] [.f, .e] (n21 D H))).trans (Context.Holds.replace [.E, .G] [.e] (n2068 D H))).trans (Context.Holds.replace [] [.e] (n1724 D H))).trans (Context.Holds.replace [.g] [] (n2070 D H))).trans (Context.Holds.replace [] [.f, .g] (n23 D H))).trans (Context.Holds.replace [] [.g] (n497 D H))).trans (Context.Holds.replace [] [] (n1909 D H))).symm).trans ((n2054 D H).mul (n2054 D H))).trans ((((Context.Holds.replace [.E, .G] [.G, .c] (n18 D H)).trans (Context.Holds.replace [] [.G, .c] (n2067 D H))).trans (Context.Holds.replace [.G] [] (n501 D H))).trans (Context.Holds.replace [] [.G] (n2068 D H))))

theorem n2080 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -25, -50, -6, 0) [.E, .G, .E, .G] [.I, .f, .i] :=
  ((n2079 D H).symm)

theorem n2083 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -5, -10, -2, 0) [.G, .G, .I, .e] [.I, .E, .f] :=
  (((Context.Holds.replace [] [.e] (n2077 D H)).symm).trans (Context.Holds.replace [.I, .E, .f] [] (n10 D H)))

theorem n2085 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 5, 10, 2, 0) [.E, .i, .G, .G] [.f, .e, .i] :=
  (((Context.Holds.replace [.E, .i] [] (n14 D H)).symm).trans (Context.Holds.cut [.E, .i, .g, .g] [.f, .e, .i] (Context.Holds.rotate [.I, .E, .f] [.E, .i, .g, .g] ((n2077 D H).relator))))

theorem n2087 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 5, 10, 2, 0) [.g, .I, .E, .f] [.G, .I, .e] :=
  (Context.Holds.cut [.g, .I, .E, .f] [.G, .I, .e] (Context.Holds.rotate [.I, .E, .f, .E, .i, .g] [.g] ((n2077 D H).relator)))

theorem n2091 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -25, -50, -6, 0) [.G, .E, .G] [.g, .E, .g] :=
  ((((Context.Holds.replace [] [.G, .E, .G] (n4 D H)).symm).trans (Context.Holds.replace [.e] [] (n2080 D H))).trans (Context.Holds.replace [] [] (n1929 D H)))

theorem n2092 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 25, 50, 6, 0) [.g, .E, .g] [.G, .E, .G] :=
  ((n2091 D H).symm)

theorem n2093 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 25, 50, 6, 0) [.E, .G, .G] [.G, .G, .E] :=
  (((Context.Holds.replace [.E] [] (n14 D H)).symm).trans (Context.Holds.cut [.E, .g, .g] [.G, .G, .E] (Context.Holds.rotate [.g] [.E, .g, .g, .e, .g] ((n2092 D H).relator))))

theorem n2094 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -25, -50, -6, 0) [.G, .G, .E] [.E, .G, .G] :=
  ((n2093 D H).symm)

theorem n2097 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 25, 50, 6, 0) [.g, .e, .g] [.G, .e, .G] :=
  (Context.Holds.cut [.g, .e, .g] [.G, .e, .G] (Context.Holds.rotate [.g, .E, .g] [.g, .e, .g] ((n2092 D H).relator)))

theorem n2099 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -25, -50, -6, 0) [.G, .E, .G, .I] [.e, .I, .f] :=
  (Context.Holds.cut [.G, .E, .G, .I] [.e, .I, .f] (Context.Holds.rotate [.E] [.G, .E, .G, .I, .f, .i] ((n2080 D H).relator)))

theorem n2101 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -25, -50, -6, 0) [.d, .i, .g, .d] [.f, .i, .g] :=
  (((Context.Holds.replace [] [] (n1416 D H)).symm).trans (Context.Holds.cut [.i, .E, .G, .E] [.f, .i, .g] (Context.Holds.rotate [.E, .G, .E, .G, .I, .f] [.i] ((n2080 D H).relator))))

theorem n2102 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 25, 50, 6, 0) [.f, .i, .g, .e] [.i, .E, .G] :=
  (Context.Holds.cut [.f, .i, .g, .e] [.i, .E, .G] (Context.Holds.rotate [.I] [.f, .i, .g, .e, .g, .e] (((n2080 D H).relator).inv)))

theorem n2104 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -5, -10, -2, 0) [.g, .I, .e] [.G, .I, .E, .f] :=
  (((Context.Holds.replace [] [.I, .e] (n275 D H)).symm).trans (Context.Holds.replace [.G] [] (n2083 D H)))

theorem n2105 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 5, 10, 2, 0) [.G, .I, .E, .f] [.g, .I, .e] :=
  ((n2104 D H).symm)

theorem n2106 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -5, -10, -2, 0) [.f, .e, .i, .g] [.E, .i, .G] :=
  (((Context.Holds.replace [] [.g] (n2085 D H)).symm).trans (Context.Holds.replace [.E, .i, .G] [] (n11 D H)))

theorem n2110 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -27, -54, -6, 0) [.i, .g, .d] [.c, .i, .G] :=
  ((((Context.Holds.replace [] [.i, .g, .d] (n3 D H)).symm).trans (Context.Holds.replace [.d] [] (n2101 D H))).trans (Context.Holds.replace [] [] (n1871 D H)))

theorem n2111 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -15, -30, -6, 0) [.G, .d, .G] [.I, .c, .i] :=
  (((Context.Holds.replace [] [] (n1166 D H)).symm).trans (Context.Holds.cut [.g, .d, .g] [.I, .c, .i] (Context.Holds.rotate [.i] [.g, .d, .g, .I, .c] ((n2110 D H).relator))))

theorem n2112 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 15, 30, 6, 0) [.I, .c, .i] [.G, .d, .G] :=
  ((n2111 D H).symm)

theorem n2117 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -15, -30, -6, 0) [.G, .d, .G, .I] [.I, .c] :=
  (((Context.Holds.replace [] [.I] (n2112 D H)).symm).trans (Context.Holds.replace [.I, .c] [] (n8 D H)))

theorem n2122 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 16, 30, 7, 0) [.I, .c, .b] [.G, .b, .h, .E] :=
  ((((Context.Holds.replace [] [.b] (n2117 D H)).symm).trans (Context.Holds.replace [.G, .d] [] (n46 D H))).trans (Context.Holds.replace [.G] [.E] (n37 D H)))

theorem n2123 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -16, -30, -7, 0) [.G, .b, .h, .E] [.I, .c, .b] :=
  ((n2122 D H).symm)

theorem n2128 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -17, -34, -8, 0) [.b, .f, .h, .e] [.b, .e, .h] :=
  (((Context.Holds.replace [] [] (n1943 D H)).symm).trans (Context.Holds.cut [.c, .i, .G, .b] [.b, .e, .h] (Context.Holds.rotate [.G, .b, .h, .E, .b] [.c, .i] ((n2123 D H).relator))))

theorem n2132 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -17, -34, -8, 0) [.f, .h, .e] [.e, .h] :=
  ((((Context.Holds.replace [] [.f, .h, .e] (n1 D H)).symm).trans (Context.Holds.replace [.b] [] (n2128 D H))).trans (Context.Holds.replace [] [.e, .h] (n1 D H)))

theorem n2133 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 17, 34, 8, 0) [.e, .h, .E] [.f, .h] :=
  (((Context.Holds.replace [] [.E] (n2132 D H)).symm).trans (Context.Holds.replace [.f, .h] [] (n4 D H)))

theorem n2134 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -17, -34, -8, 0) [.h, .e] [.f, .e, .h] :=
  (((Context.Holds.replace [] [.h, .e] (n5 D H)).symm).trans (Context.Holds.replace [.f] [] (n2132 D H)))

theorem n2135 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 17, 34, 8, 0) [.f, .e, .h] [.h, .e] :=
  ((n2134 D H).symm)

theorem n2136 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -17, -34, -8, 0) [.h, .e, .h] [.f, .e] :=
  (Context.Holds.cut [.h, .e, .h] [.f, .e] (Context.Holds.rotate [.f] [.h, .e, .h, .E] ((n2132 D H).relator)))

theorem n2137 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -33, -66, -14, 0) [.c, .d] [.c, .d] :=
  ((((((((Context.Holds.replace [] [.h, .e, .h] (n2136 D H)).trans (Context.Holds.replace [] [.e, .h] (n2135 D H))).trans (Context.Holds.replace [.h] [.h] (n13 D H))).trans (Context.Holds.replace [] [.h] (n321 D H))).trans (Context.Holds.replace [.c, .d] [] (n7 D H))).symm).trans ((n2136 D H).mul (n2136 D H))).trans ((Context.Holds.replace [] [.e] (n2024 D H)).trans (Context.Holds.replace [] [] (n965 D H))))

theorem n2138 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -17, -34, -8, 0) [.h, .E, .f] [.E, .h] :=
  (Context.Holds.cut [.h, .E, .f] [.E, .h] (Context.Holds.rotate [.f, .h, .e] [.h, .E] ((n2132 D H).relator)))

theorem n2139 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -17, -34, -8, 0) [.E, .f, .h] [.h, .E] :=
  (Context.Holds.cut [.E, .f, .h] [.h, .E] (Context.Holds.rotate [.f, .h, .e, .h] [.E] ((n2132 D H).relator)))

theorem n2140 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 17, 34, 8, 0) [.h, .E, .h] [.E, .f] :=
  (Context.Holds.cut [.h, .E, .h] [.E, .f] (Context.Holds.rotate [.e] [.h, .E, .h, .f] (((n2132 D H).relator).inv)))

theorem n2141 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 14, 28, 6, 0) [.e, .h, .e] [.E, .f, .E, .h] :=
  ((((Context.Holds.replace [] [.e] (n2132 D H)).symm).trans (Context.Holds.replace [.f, .h] [] (n13 D H))).trans ((((Context.Holds.replace [.f] [] (n321 D H)).trans (Context.Holds.replace [] [.d, .h] (n495 D H))).trans (Context.Holds.replace [.c] [.h] (n25 D H))).trans (Context.Holds.replace [] [.h] (n2026 D H))))

theorem n2142 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -14, -28, -6, 0) [.E, .f, .E, .h] [.e, .h, .e] :=
  ((n2141 D H).symm)

theorem n2143 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 17, 34, 8, 0) [.E, .d, .h] [.f, .h, .c, .e] :=
  (((Context.Holds.replace [] [] (n325 D H)).symm).trans (((Context.Holds.replace [] [.c] (n2132 D H)).symm).trans (Context.Holds.replace [.f, .h] [] (n20 D H))))

theorem n2144 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -17, -34, -8, 0) [.f, .h, .c, .e] [.E, .d, .h] :=
  ((n2143 D H).symm)

theorem n2146 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -18, -36, -6, 0) [.c, .h, .G, .e] [.g, .e, .h] :=
  (((Context.Holds.replace [] [.e] (n1973 D H)).symm).trans (Context.Holds.replace [.g] [] (n2132 D H)))

theorem n2147 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -18, -36, -6, 0) [.G, .h, .G, .e] [.c, .e, .h] :=
  (((Context.Holds.replace [] [.e] (n1976 D H)).symm).trans (Context.Holds.replace [.c] [] (n2132 D H)))

theorem n2148 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 16, 32, 10, 0) [.e, .h, .G] [.f, .g, .h, .E] :=
  (((Context.Holds.replace [] [.G] (n2132 D H)).symm).trans (Context.Holds.replace [.f] [] (n1985 D H)))

theorem n2149 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -16, -32, -10, 0) [.f, .g, .h, .E] [.e, .h, .G] :=
  ((n2148 D H).symm)

theorem n2157 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -13, -26, -8, 0) [.d, .f, .h] [.E, .h, .E, .c] :=
  (((((Context.Holds.replace [.f] [] (n27 D H)).trans (Context.Holds.replace [] [.h] (n25 D H))).symm).trans (((Context.Holds.replace [] [.d] (n2133 D H)).symm).trans (Context.Holds.replace [.e] [] (n954 D H)))).trans ((Context.Holds.replace [] [.h, .e] (n20 D H)).trans (Context.Holds.replace [] [] (n680 D H))))

theorem n2158 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 13, 26, 8, 0) [.E, .h, .E, .c] [.d, .f, .h] :=
  ((n2157 D H).symm)

theorem n2166 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -20, -40, -6, 0) [.h, .e, .f] [.E, .c, .d, .h] :=
  ((((Context.Holds.replace [] [.f] (n2135 D H)).symm).trans (Context.Holds.replace [.f, .e] [] (n300 D H))).trans (Context.Holds.replace [] [.h] (n2024 D H)))

theorem n2167 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 20, 40, 6, 0) [.E, .c, .d, .h] [.h, .e, .f] :=
  ((n2166 D H).symm)

theorem n2168 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -14, -28, -10, 0) [.h, .c, .e] [.c, .e, .f, .h] :=
  ((((Context.Holds.replace [.h] [] (n20 D H)).symm).trans (((Context.Holds.replace [] [.c] (n2135 D H)).symm).trans (Context.Holds.replace [.f] [] (n325 D H)))).trans ((Context.Holds.replace [] [.h] (n952 D H)).trans (Context.Holds.replace [] [.h] (n2022 D H))))

theorem n2169 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 14, 28, 10, 0) [.c, .e, .f, .h] [.h, .c, .e] :=
  ((n2168 D H).symm)

theorem n2171 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 17, 34, 8, 0) [.E, .c, .g, .h] [.g, .h, .e] :=
  (((Context.Holds.replace [] [.h] (n483 D H)).symm).trans (Context.Holds.replace [.g] [] (n2135 D H)))

theorem n2186 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 17, 34, 9, 0) [.E, .b, .d] [.h, .E, .b, .f] :=
  (((Context.Holds.replace [.E] [] (n36 D H)).symm).trans (((Context.Holds.replace [] [.b] (n2138 D H)).symm).trans (Context.Holds.replace [.h, .E] [] (n40 D H))))

theorem n2187 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -17, -34, -9, 0) [.h, .E, .b, .f] [.E, .b, .d] :=
  ((n2186 D H).symm)

theorem n2197 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -28, -56, -10, 0) [.E, .g, .d, .h] [.g, .h, .E] :=
  (((Context.Holds.replace [] [.h] (n2039 D H)).symm).trans (((Context.Holds.replace [] [.h] (n487 D H)).symm).trans (Context.Holds.replace [.g] [] (n2139 D H))))

theorem n2207 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -16, -32, -10, 0) [.h, .g, .e] [.E, .G, .f, .h] :=
  ((((Context.Holds.replace [] [.e] (n1993 D H)).symm).trans (Context.Holds.replace [.G] [] (n2144 D H))).trans (Context.Holds.replace [] [.h] (n1176 D H)))

theorem n2208 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 16, 32, 10, 0) [.E, .G, .f, .h] [.h, .g, .e] :=
  ((n2207 D H).symm)

theorem n2210 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -16, -32, -10, 0) [.E, .h, .c, .e] [.G, .h, .G] :=
  ((((((Context.Holds.replace [.e] [.e] (n27 D H)).trans (Context.Holds.replace [] [.h, .e] (n945 D H))).trans (Context.Holds.replace [] [.e] (n957 D H))).symm).trans (Context.Holds.cut [.e, .h, .d, .e] [.c, .h, .f] (Context.Holds.rotate [.f, .h, .c] [.e, .h, .d, .e] ((n2144 D H).relator)))).trans ((Context.Holds.replace [.c] [] (n300 D H)).trans (Context.Holds.replace [] [] (n1976 D H))))

theorem n2212 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 22, 44, 10, 0) [.h, .E, .c, .h] [.c, .f, .E] :=
  ((Context.Holds.cut [.h, .E, .c, .h] [.d, .e, .f] (Context.Holds.rotate [.E, .d] [.h, .E, .c, .h, .f] (((n2144 D H).relator).inv))).trans (Context.Holds.replace [] [] (n2017 D H)))

theorem n2222 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 16, 32, 10, 0) [.e, .h, .G, .e] [.f, .g, .h] :=
  (((Context.Holds.replace [] [.e] (n2149 D H)).symm).trans (Context.Holds.replace [.f, .g, .h] [] (n10 D H)))

theorem n2223 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -17, -34, -8, 0) [.E, .g, .h, .E] [.c, .g, .h] :=
  ((Context.Holds.cut [.E, .g, .h, .E] [.h, .G, .f] (Context.Holds.rotate [.f, .g, .h] [.E, .g, .h, .E] ((n2149 D H).relator))).trans (Context.Holds.replace [] [] (n1980 D H)))

theorem n2230 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 12, 24, 10, 0) [.G, .h, .G, .d] [.e, .h, .e] :=
  ((((Context.Holds.replace [.c] [.d] (n300 D H)).trans (Context.Holds.replace [] [.d] (n1976 D H))).symm).trans (Context.Holds.cut [.c, .h, .f, .d] [.e, .h, .e] (Context.Holds.rotate [.E, .h, .E] [.c, .h, .f, .d] ((n2158 D H).relator))))

theorem n2240 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 17, 34, 8, 0) [.c, .g, .h, .E] [.e, .g, .h] :=
  (Context.Holds.cut [.c, .g, .h, .E] [.e, .g, .h] (Context.Holds.rotate [.E] [.c, .g, .h, .E, .h, .G] ((n2171 D H).relator)))

theorem n2241 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 16, 32, 10, 0) [.E, .h, .G, .E] [.f, .g, .h] :=
  ((Context.Holds.cut [.E, .h, .G, .E] [.h, .G, .c] (Context.Holds.rotate [.E, .c, .g, .h] [.E, .h, .G] ((n2171 D H).relator))).trans (Context.Holds.replace [] [] (n1982 D H)))

theorem n2246 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -28, -56, -10, 0) [.g, .d, .h] [.e, .g, .h, .E] :=
  (((Context.Holds.replace [] [.g, .d, .h] (n4 D H)).symm).trans (Context.Holds.replace [.e] [] (n2197 D H)))

theorem n2247 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 28, 56, 10, 0) [.e, .g, .h, .E] [.g, .d, .h] :=
  ((n2246 D H).symm)

theorem n2258 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 16, 32, 10, 0) [.G, .f, .h, .E] [.e, .h, .g] :=
  (Context.Holds.cut [.G, .f, .h, .E] [.e, .h, .g] (Context.Holds.rotate [.E] [.G, .f, .h, .E, .G, .h] ((n2208 D H).relator)))

theorem n2260 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 8, 16, 10, 0) [.h, .E, .G, .h] [.d, .e, .g] :=
  ((Context.Holds.cut [.h, .E, .G, .h] [.f, .g, .e] (Context.Holds.rotate [.E, .G, .f] [.h, .E, .G, .h] ((n2208 D H).relator))).trans (Context.Holds.replace [] [] (n1182 D H)))

theorem n2278 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 20, 40, 10, 0) [.E, .d, .G, .h] [.h, .e, .g] :=
  (((Context.Holds.replace [] [.h] (n949 D H)).symm).trans (Context.Holds.cut [.G, .f, .E, .h] [.h, .e, .g] (Context.Holds.rotate [.E, .h, .G, .E, .h] [.G, .f] ((n2241 D H).relator))))

theorem n2280 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -16, -32, -10, 0) [.g, .h, .e, .g] [.f, .E, .h] :=
  (Context.Holds.cut [.g, .h, .e, .g] [.f, .E, .h] (Context.Holds.rotate [.f] [.g, .h, .e, .g, .h, .e] (((n2241 D H).relator).inv)))

theorem n2283 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -12, -24, -10, 0) [.c, .h, .g, .E] [.G, .E, .h] :=
  (((Context.Holds.replace [] [] (n1667 D H)).symm).trans (Context.Holds.cut [.h, .e, .f, .g] [.G, .E, .h] (Context.Holds.rotate [.f, .g, .h, .e, .g] [.h, .e] (((n2241 D H).relator).inv))))

theorem n2290 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 20, 40, 10, 0) [.d, .G, .h, .G] [.e, .h, .e] :=
  (Context.Holds.cut [.d, .G, .h, .G] [.e, .h, .e] (Context.Holds.rotate [.E] [.d, .G, .h, .G, .E, .h] ((n2278 D H).relator)))

theorem n2292 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 12, 24, 10, 0) [.G, .E, .h, .e] [.c, .h, .g] :=
  (((Context.Holds.replace [] [.e] (n2283 D H)).symm).trans (Context.Holds.replace [.c, .h, .g] [] (n10 D H)))

end Tits.CentralCoverLifting.CompatibleGenerators.RemainingConjugations
