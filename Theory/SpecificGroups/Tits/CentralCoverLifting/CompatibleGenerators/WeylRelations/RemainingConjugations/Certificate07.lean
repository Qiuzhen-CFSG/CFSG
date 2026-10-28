module
public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.WeylRelations.RemainingConjugations.Certificate06
/-!
# Checked central word identities, block 8

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
theorem n2849 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -123, -238, -36, 0) [.f, .I, .G, .h] [.I, .h, .G] :=
  (Context.Holds.cut [.f, .I, .G, .h] [.I, .h, .G] (Context.Holds.rotate [.I, .G, .h, .g, .h, .i] [.f] ((n2846 D H).relator)))

theorem n2850 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 123, 238, 36, 0) [.G, .h, .g, .i] [.h, .i, .f] :=
  (Context.Holds.cut [.G, .h, .g, .i] [.h, .i, .f] (Context.Holds.rotate [.f, .I, .h] [.G, .h, .g, .i] (((n2846 D H).relator).inv)))

theorem n2891 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -7, -14, -8, 0) [.c, .d, .e, .i] [.h, .E, .i, .h] :=
  ((((Context.Holds.replace [] [.d, .i] (n20 D H)).trans (Context.Holds.replace [.c] [.i] (n945 D H))).symm).trans (Context.Holds.cut [.e, .c, .d, .i] [.h, .E, .i, .h] (Context.Holds.rotate [.c, .d, .i, .h, .I, .e, .h] [.e] ((n2610 D H).relator))))

theorem n2892 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 7, 14, 8, 0) [.h, .E, .i, .h] [.c, .d, .e, .i] :=
  ((n2891 D H).symm)

theorem n2897 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 3, 6, 2, 0) [.i, .h] [.d, .h, .i, .d] :=
  ((((Context.Holds.replace [.i, .h] [] (n11 D H)).symm).trans (Context.Holds.cut [.i, .h, .G, .g] [.h, .d, .i, .d] (Context.Holds.rotate [.h] [.i, .h, .G, .g, .d, .I, .d] ((n2633 D H).relator)))).trans (Context.Holds.replace [] [.i, .d] (n27 D H)))

theorem n2898 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -3, -6, -2, 0) [.d, .h, .i, .d] [.i, .h] :=
  ((n2897 D H).symm)

theorem n2899 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 3, 6, 2, 0) [.i, .d, .h] [.d, .h, .i] :=
  (((Context.Holds.replace [.i] [] (n27 D H)).symm).trans (((Context.Holds.replace [] [.d] (n2898 D H)).symm).trans (Context.Holds.replace [.d, .h, .i] [] (n3 D H))))

theorem n2900 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -3, -6, -2, 0) [.h, .i, .d] [.d, .i, .h] :=
  (((Context.Holds.replace [] [.h, .i, .d] (n3 D H)).symm).trans (Context.Holds.replace [.d] [] (n2898 D H)))

theorem n2902 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -3, -6, -2, 0) [.h, .I, .d] [.d, .I, .h] :=
  (Context.Holds.cut [.h, .I, .d] [.d, .I, .h] (Context.Holds.rotate [.d, .h, .i, .d] [.h, .I] ((n2898 D H).relator)))

theorem n2903 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 3, 6, 2, 0) [.h, .I, .h] [.d, .I, .d] :=
  (Context.Holds.cut [.h, .I, .h] [.d, .I, .d] (Context.Holds.rotate [.i, .d] [.h, .I, .h, .d] ((n2899 D H).relator)))

theorem n2904 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 3, 6, 2, 0) [.d, .i, .d] [.h, .i, .h] :=
  (Context.Holds.cut [.d, .i, .d] [.h, .i, .h] (Context.Holds.rotate [.i, .d, .h, .I, .h] [.d] ((n2899 D H).relator)))

theorem n2905 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -3, -6, -2, 0) [.h, .i, .h] [.d, .i, .d] :=
  ((n2904 D H).symm)

theorem n2910 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 125, 250, 38, 0) [.d, .I, .d, .e] [.I, .e, .f] :=
  (((Context.Holds.replace [] [.e] (n2903 D H)).symm).trans (n2760 D H))

theorem n2911 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 93, 186, 22, 0) [.d, .I, .E, .d] [.I, .E, .f] :=
  ((((Context.Holds.replace [] [.E] (n2903 D H)).trans (Context.Holds.replace [.d, .I] [] (n943 D H))).symm).trans (n2753 D H))

theorem n2912 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 116, 232, 36, 0) [.d, .I, .d, .G] [.I, .G, .f] :=
  (((Context.Holds.replace [] [.G] (n2903 D H)).symm).trans (n2750 D H))

theorem n2918 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 120, 240, 36, 0) [.I, .c, .f, .E] [.d, .I, .e] :=
  (((Context.Holds.replace [.I] [] (n2017 D H)).symm).trans (Context.Holds.cut [.I, .d, .e, .f] [.d, .I, .e] (Context.Holds.rotate [.d] [.I, .d, .e, .f, .E, .i] ((n2910 D H).relator))))

theorem n2919 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 118, 236, 36, 0) [.E, .E, .c, .f] [.i, .d, .I] :=
  ((((((Context.Holds.replace [] [.E] (n2017 D H)).trans (Context.Holds.replace [.c] [] (n885 D H))).trans (Context.Holds.replace [] [.E, .f] (n18 D H))).trans (Context.Holds.replace [.E] [.f] (n18 D H))).symm).trans (Context.Holds.cut [.d, .e, .f, .E] [.i, .d, .I] (Context.Holds.rotate [.d, .I] [.d, .e, .f, .E, .i] ((n2910 D H).relator))))

theorem n2929 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 92, 184, 20, 0) [.E, .c, .f, .i] [.e, .i, .d] :=
  (((Context.Holds.replace [] [.i] (n2018 D H)).symm).trans (Context.Holds.cut [.d, .f, .e, .i] [.e, .i, .d] (Context.Holds.rotate [.d, .I, .E] [.d, .f, .e, .i] ((n2911 D H).relator))))

theorem n2935 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 116, 232, 36, 0) [.I, .E, .G, .e] [.d, .I, .G] :=
  (((Context.Holds.replace [.I] [] (n520 D H)).symm).trans (Context.Holds.cut [.I, .d, .G, .f] [.d, .I, .G] (Context.Holds.rotate [.d] [.I, .d, .G, .f, .g, .i] ((n2912 D H).relator))))

theorem n2940 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -120, -240, -36, 0) [.d, .I, .E, .E] [.I, .c, .f] :=
  (((Context.Holds.replace [.d, .I] [] (n13 D H)).symm).trans (((Context.Holds.replace [] [.e] (n2918 D H)).symm).trans (Context.Holds.replace [.I, .c, .f] [] (n10 D H))))

theorem n2944 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 122, 244, 36, 0) [.c, .f, .I] [.I, .E, .E] :=
  ((((Context.Holds.replace [] [] (n1889 D H)).symm).trans (Context.Holds.cut [.d, .I, .c, .f] [.I, .e, .e] (Context.Holds.rotate [.I, .c, .f, .E, .E, .i] [.d] ((n2918 D H).relator)))).trans (Context.Holds.replace [.I] [] (n13 D H)))

theorem n2946 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 122, 244, 36, 0) [.E, .E, .i] [.i, .c, .f] :=
  ((((Context.Holds.replace [] [.i] (n13 D H)).symm).trans (Context.Holds.cut [.e, .e, .i] [.i, .f, .c] (Context.Holds.rotate [.c, .f, .I] [.e, .e, .i] ((n2944 D H).relator)))).trans (Context.Holds.replace [.i] [] (n495 D H)))

theorem n2947 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -122, -244, -36, 0) [.i, .c, .f] [.E, .E, .i] :=
  ((n2946 D H).symm)

theorem n2949 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 122, 244, 36, 0) [.f, .I] [.c, .I, .E, .E] :=
  (((Context.Holds.replace [] [.f, .I] (n2 D H)).symm).trans (Context.Holds.replace [.c] [] (n2944 D H)))

theorem n2950 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -122, -244, -36, 0) [.c, .I, .E, .E] [.f, .I] :=
  ((n2949 D H).symm)

theorem n2951 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 122, 244, 36, 0) [.f, .I, .E] [.c, .I, .e] :=
  (((Context.Holds.replace [] [.E] (n2950 D H)).symm).trans (Context.Holds.replace [.c, .I] [] (n274 D H)))

theorem n2952 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 122, 244, 36, 0) [.E, .i, .c] [.e, .i, .f] :=
  (Context.Holds.cut [.E, .i, .c] [.e, .i, .f] (Context.Holds.rotate [.f, .I, .E] [.E, .i, .c] ((n2951 D H).relator)))

theorem n2953 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -122, -244, -36, 0) [.e, .i, .f] [.E, .i, .c] :=
  ((n2952 D H).symm)

theorem n2954 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -122, -244, -36, 0) [.I, .E, .E, .i] [.c, .f] :=
  (((Context.Holds.replace [] [.i] (n2944 D H)).symm).trans (Context.Holds.replace [.c, .f] [] (n12 D H)))

theorem n2955 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 122, 244, 36, 0) [.E, .E, .i, .f] [.i, .c] :=
  (((Context.Holds.replace [] [.f] (n2947 D H)).symm).trans (Context.Holds.replace [.i, .c] [] (n5 D H)))

theorem n2956 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -122, -244, -36, 0) [.i, .f] [.E, .E, .i, .c] :=
  (((Context.Holds.replace [] [.i, .f] (n10 D H)).symm).trans (Context.Holds.replace [.E] [] (n2953 D H)))

theorem n2957 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 122, 244, 36, 0) [.E, .E, .i, .c] [.i, .f] :=
  ((n2956 D H).symm)

theorem n2961 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -99, -198, -34, 0) [.i, .d, .I, .g] [.E, .g, .e] :=
  (((Context.Holds.replace [] [.g] (n2919 D H)).symm).trans (Context.Holds.replace [.E] [] (n2074 D H)))

theorem n2963 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 118, 236, 36, 0) [.I, .E, .E, .c] [.d, .I, .f] :=
  (Context.Holds.cut [.I, .E, .E, .c] [.d, .I, .f] (Context.Holds.rotate [.E, .E, .c, .f, .i, .d] [.I] ((n2919 D H).relator)))

theorem n2964 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -118, -236, -36, 0) [.E, .E, .c, .i] [.f, .i, .d] :=
  (((((Context.Holds.replace [.c] [.i] (n13 D H)).trans (Context.Holds.replace [] [.E, .i] (n18 D H))).trans (Context.Holds.replace [.E] [.i] (n18 D H))).symm).trans (Context.Holds.cut [.c, .e, .e, .i] [.f, .i, .d] (Context.Holds.rotate [.i, .d, .I, .f] [.c, .e, .e] (((n2919 D H).relator).inv))))

theorem n2972 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 116, 232, 36, 0) [.d, .I, .E, .G] [.I, .G, .E] :=
  (Context.Holds.cut [.d, .I, .E, .G] [.I, .G, .E] (Context.Holds.rotate [.I, .E, .G, .e, .g, .i] [.d] ((n2935 D H).relator)))

theorem n2979 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -122, -236, -34, 0) [.c, .I, .e, .g] [.I, .G, .e] :=
  (((Context.Holds.replace [] [.g] (n2951 D H)).symm).trans (n2821 D H))

theorem n2980 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -115, -222, -32, 0) [.c, .I, .e, .G] [.I, .g, .e] :=
  (((Context.Holds.replace [] [.G] (n2951 D H)).symm).trans (n2816 D H))

theorem n2983 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 120, 248, 38, 0) [.d, .I, .I] [.i, .c, .i, .c] :=
  ((((((((((Context.Holds.replace [] [.E, .E, .i, .f] (n2955 D H)).trans (Context.Holds.replace [.i] [.E, .i, .f] (n18 D H))).trans (Context.Holds.replace [.i, .E] [.i, .f] (n18 D H))).trans (Context.Holds.replace [] [.i, .f] (n544 D H))).trans (Context.Holds.replace [] [.i, .f] (n1852 D H))).trans (Context.Holds.replace [.d, .f] [.f] (n15 D H))).trans (Context.Holds.replace [.d] [.f] (n2799 D H))).trans (Context.Holds.replace [.d, .I, .I] [] (n5 D H))).symm).trans ((n2955 D H).mul (n2955 D H)))

theorem n2984 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -120, -248, -38, 0) [.i, .c, .i, .c] [.d, .I, .I] :=
  ((n2983 D H).symm)

theorem n2988 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -99, -198, -34, 0) [.E, .G, .e, .i] [.G, .i, .d] :=
  (Context.Holds.cut [.E, .G, .e, .i] [.G, .i, .d] (Context.Holds.rotate [.i, .d, .I, .g] [.E, .G, .e] ((n2961 D H).relator)))

theorem n2992 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -113, -226, -34, 0) [.d, .I, .f, .g] [.I, .g, .d] :=
  (((Context.Holds.replace [] [.g] (n2963 D H)).symm).trans (Context.Holds.replace [.I] [] (n2059 D H)))

theorem n2995 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -122, -236, -34, 0) [.I, .d, .f, .g] [.c, .I, .G] :=
  (((Context.Holds.replace [.I] [] (n1186 D H)).symm).trans (Context.Holds.cut [.I, .e, .g, .E] [.c, .I, .G] (Context.Holds.rotate [.c] [.I, .e, .g, .E, .g, .i] ((n2979 D H).relator))))

theorem n2996 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -120, -232, -30, 0) [.G, .G, .d, .f] [.i, .c, .I] :=
  ((((((Context.Holds.replace [] [.g] (n1186 D H)).trans (Context.Holds.replace [.d, .f] [] (n14 D H))).trans (Context.Holds.replace [] [.G] (n2033 D H))).trans (Context.Holds.replace [.G] [] (n2033 D H))).symm).trans (Context.Holds.cut [.e, .g, .E, .g] [.i, .c, .I] (Context.Holds.rotate [.c, .I] [.e, .g, .E, .g, .i] ((n2979 D H).relator))))

theorem n3007 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -115, -222, -32, 0) [.G, .i, .c, .I] [.d, .f, .g] :=
  ((Context.Holds.cut [.G, .i, .c, .I] [.e, .g, .E] (Context.Holds.rotate [.c, .I, .e, .G, .E] [.G, .i] ((n2980 D H).relator))).trans (Context.Holds.replace [] [] (n1186 D H)))

theorem n3008 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -94, -180, -30, 0) [.i, .E, .E, .I] [.G, .G] :=
  ((((((Context.Holds.replace [] [.G, .i, .c, .I] (n3007 D H)).trans (Context.Holds.replace [.d, .f] [.i, .c, .I] (n6 D H))).trans (Context.Holds.replace [] [.I] (n1849 D H))).symm).trans ((n3007 D H).mul (n3007 D H))).trans ((((((Context.Holds.replace [.d] [.f, .g] (n525 D H)).trans (Context.Holds.replace [] [.g, .e, .f, .g] (n943 D H))).trans (Context.Holds.replace [.E] [.f, .g] (n2058 D H))).trans (Context.Holds.replace [] [.f, .g] (n490 D H))).trans (Context.Holds.replace [.g] [.g] (n5 D H))).trans (Context.Holds.replace [] [] (n14 D H))))

theorem n3009 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 94, 180, 30, 0) [.G, .G, .i] [.i, .E, .E] :=
  (((Context.Holds.replace [] [.i] (n3008 D H)).symm).trans (Context.Holds.replace [.i, .E, .E] [] (n12 D H)))

theorem n3010 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -94, -180, -30, 0) [.i, .E, .E] [.G, .G, .i] :=
  ((n3009 D H).symm)

theorem n3011 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -94, -180, -30, 0) [.E, .E, .I] [.I, .G, .G] :=
  (((Context.Holds.replace [] [.E, .E, .I] (n12 D H)).symm).trans (Context.Holds.replace [.I] [] (n3008 D H)))

theorem n3012 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 94, 180, 30, 0) [.I, .G, .G] [.E, .E, .I] :=
  ((n3011 D H).symm)

theorem n3013 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -94, -180, -30, 0) [.E, .I, .g] [.e, .I, .G] :=
  (Context.Holds.cut [.E, .I, .g] [.e, .I, .G] (Context.Holds.rotate [.i, .E] [.E, .I, .g, .g] ((n3008 D H).relator)))

theorem n3014 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 94, 180, 30, 0) [.e, .I, .G] [.E, .I, .g] :=
  ((n3013 D H).symm)

theorem n3015 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -94, -180, -30, 0) [.g, .i, .E] [.G, .i, .e] :=
  (Context.Holds.cut [.g, .i, .E] [.G, .i, .e] (Context.Holds.rotate [.i, .E, .E, .I, .g] [.g] ((n3008 D H).relator)))

theorem n3016 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 94, 180, 30, 0) [.G, .G, .i, .e] [.i, .E] :=
  (((Context.Holds.replace [] [.e] (n3010 D H)).symm).trans (Context.Holds.replace [.i, .E] [] (n10 D H)))

theorem n3017 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 94, 180, 30, 0) [.g, .i, .e] [.G, .i, .E] :=
  (((Context.Holds.replace [] [.i, .e] (n275 D H)).symm).trans (Context.Holds.replace [.G] [] (n3016 D H)))

theorem n3018 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 94, 180, 30, 0) [.e, .I, .g] [.E, .I, .G] :=
  (Context.Holds.cut [.e, .I, .g] [.E, .I, .G] (Context.Holds.rotate [.g, .i, .e] [.e, .I, .g] ((n3017 D H).relator)))

theorem n3020 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -94, -180, -30, 0) [.E, .E, .I, .g] [.I, .G] :=
  (((Context.Holds.replace [] [.g] (n3012 D H)).symm).trans (Context.Holds.replace [.I, .G] [] (n11 D H)))

theorem n3022 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 115, 222, 32, 0) [.d, .f, .g, .i] [.G, .i, .c] :=
  (((Context.Holds.replace [] [.i] (n1186 D H)).symm).trans (Context.Holds.cut [.e, .g, .E, .i] [.G, .i, .c] (Context.Holds.rotate [.I, .g] [.e, .g, .E, .i, .c] (((n2980 D H).relator).inv))))

theorem n3025 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -120, -248, -38, 0) [.c, .i, .c] [.I, .d, .I, .I] :=
  (((Context.Holds.replace [] [.c, .i, .c] (n12 D H)).symm).trans (Context.Holds.replace [.I] [] (n2984 D H)))

theorem n3026 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 120, 248, 38, 0) [.I, .d, .I, .I] [.c, .i, .c] :=
  ((n3025 D H).symm)

theorem n3027 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -120, -248, -38, 0) [.c, .i, .c, .i] [.I, .d, .I] :=
  (Context.Holds.cut [.c, .i, .c, .i] [.I, .d, .I] (Context.Holds.rotate [.i] [.c, .i, .c, .i, .i, .d] ((n2984 D H).relator)))

theorem n3034 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 120, 248, 38, 0) [.I, .c, .I, .c] [.i, .d, .i] :=
  (Context.Holds.cut [.I, .c, .I, .c] [.i, .d, .i] (Context.Holds.rotate [.d, .I] [.I, .c, .I, .c, .I] (((n2984 D H).relator).inv)))

theorem n3035 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 120, 248, 38, 0) [.c, .I, .c, .I] [.I, .I, .d] :=
  ((Context.Holds.cut [.c, .I, .c, .I] [.i, .i, .d] (Context.Holds.rotate [.d, .I, .I] [.c, .I, .c, .I] (((n2984 D H).relator).inv))).trans (Context.Holds.replace [] [.d] (n15 D H)))

theorem n3037 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 120, 248, 38, 0) [.c, .I, .d, .I] [.i, .c, .i] :=
  (Context.Holds.cut [.c, .I, .d, .I] [.i, .c, .i] (Context.Holds.rotate [.d, .I, .I, .c, .I] [.c, .I] (((n2984 D H).relator).inv)))

theorem n3038 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -113, -226, -34, 0) [.I, .f, .g] [.d, .I, .g, .d] :=
  (((Context.Holds.replace [] [.I, .f, .g] (n3 D H)).symm).trans (Context.Holds.replace [.d] [] (n2992 D H)))

theorem n3039 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 113, 226, 34, 0) [.d, .I, .g, .d] [.I, .f, .g] :=
  ((n3038 D H).symm)

theorem n3042 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -122, -236, -34, 0) [.G, .G, .f, .i] [.d, .i, .c] :=
  ((((Context.Holds.replace [.f] [.i] (n14 D H)).trans (Context.Holds.replace [] [.i] (n1201 D H))).symm).trans (Context.Holds.cut [.f, .g, .g, .i] [.d, .i, .c] (Context.Holds.rotate [.I, .d] [.f, .g, .g, .i, .c] ((n2995 D H).relator))))

theorem n3046 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -108, -208, -30, 0) [.f, .i, .c, .I] [.G, .G, .d] :=
  ((Context.Holds.cut [.f, .i, .c, .I] [.d, .g, .g] (Context.Holds.rotate [.G, .G, .d] [.f, .i, .c, .I] ((n2996 D H).relator))).trans ((Context.Holds.replace [.d] [] (n14 D H)).trans (Context.Holds.replace [] [] (n1162 D H))))

theorem n3056 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 93, 180, 30, 0) [.G, .G, .b] [.i, .E, .b, .G] :=
  (((Context.Holds.replace [] [.b] (n3008 D H)).symm).trans (Context.Holds.replace [.i, .E] [] (n51 D H)))

theorem n3057 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -93, -180, -30, 0) [.i, .E, .b, .G] [.G, .G, .b] :=
  ((n3056 D H).symm)

theorem n3058 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -93, -180, -30, 0) [.i, .E, .b] [.G, .G, .b, .g] :=
  (((Context.Holds.replace [] [.b] (n3016 D H)).symm).trans (Context.Holds.replace [.G, .G] [] (n283 D H)))

theorem n3059 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 93, 180, 30, 0) [.G, .G, .b, .g] [.i, .E, .b] :=
  ((n3058 D H).symm)

theorem n3067 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -122, -236, -34, 0) [.G, .f, .i, .c] [.g, .d, .i] :=
  (Context.Holds.cut [.G, .f, .i, .c] [.g, .d, .i] (Context.Holds.rotate [.G] [.G, .f, .i, .c, .I, .d] ((n3042 D H).relator)))

theorem n3069 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 122, 236, 34, 0) [.c, .I, .f, .g] [.I, .d, .G] :=
  (Context.Holds.cut [.c, .I, .f, .g] [.I, .d, .G] (Context.Holds.rotate [.d, .i] [.c, .I, .f, .g, .g] (((n3042 D H).relator).inv)))

theorem n3070 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -108, -208, -30, 0) [.c, .I, .d, .g] [.I, .f, .G] :=
  (Context.Holds.cut [.c, .I, .d, .g] [.I, .f, .G] (Context.Holds.rotate [.f, .i] [.c, .I, .d, .g, .g] ((n3046 D H).relator)))

theorem n3075 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 93, 180, 30, 0) [.g, .b, .e, .I] [.b, .G, .G] :=
  ((Context.Holds.cut [.g, .b, .e, .I] [.b, .g, .g] (Context.Holds.rotate [.G, .G, .b] [.g, .b, .e, .I] (((n3057 D H).relator).inv))).trans (Context.Holds.replace [.b] [] (n14 D H)))

theorem n3082 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 116, 232, 32, 0) [.E, .E, .i, .g] [.d, .i, .d, .G] :=
  (((((Context.Holds.replace [.i] [] (n2070 D H)).trans (Context.Holds.replace [] [.g] (n2947 D H))).symm).trans (Context.Holds.cut [.i, .e, .g, .e] [.h, .i, .h, .G] (Context.Holds.rotate [.e, .g, .h, .I, .h] [.i, .e, .g] ((n2635 D H).relator)))).trans (Context.Holds.replace [] [.G] (n2905 D H)))

theorem n3083 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -116, -232, -32, 0) [.d, .i, .d, .G] [.E, .E, .i, .g] :=
  ((n3082 D H).symm)

theorem n3096 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 89, 170, 28, 0) [.G, .G, .i, .h] [.d, .h, .i, .c] :=
  (((Context.Holds.replace [] [.h] (n3010 D H)).symm).trans (((Context.Holds.replace [] [.h] (n1849 D H)).symm).trans (Context.Holds.replace [.d] [] (n2658 D H))))

theorem n3097 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -89, -170, -28, 0) [.d, .h, .i, .c] [.G, .G, .i, .h] :=
  ((n3096 D H).symm)

theorem n3117 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -112, -216, -34, 0) [.f, .h, .I, .I] [.I, .f, .I, .h] :=
  ((((Context.Holds.replace [.f, .h] [] (n15 D H)).symm).trans (((Context.Holds.replace [] [.i] (n2659 D H)).symm).trans (Context.Holds.replace [.i] [] (n2717 D H)))).trans (Context.Holds.replace [] [.h] (n2802 D H)))

theorem n3118 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -19, -38, -8, 0) [.h, .E, .I, .c] [.e, .h, .I, .f] :=
  (((Context.Holds.replace [] [.c] (n2597 D H)).symm).trans (Context.Holds.replace [.e] [] (n2722 D H)))

theorem n3119 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -126, -252, -40, 0) [.h, .I, .f, .I] [.I, .I, .f, .h] :=
  (((Context.Holds.replace [] [.I] (n2722 D H)).symm).trans (Context.Holds.replace [.I] [] (n2660 D H)))

theorem n3128 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 109, 218, 32, 0) [.e, .i, .h, .i] [.h, .e, .I, .I] :=
  (((Context.Holds.replace [] [.i] (n2726 D H)).symm).trans (Context.Holds.replace [.h, .e] [] (n15 D H)))

theorem n3129 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -109, -218, -32, 0) [.h, .e, .I, .I] [.e, .i, .h, .i] :=
  ((n3128 D H).symm)

theorem n3139 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -103, -206, -28, 0) [.h, .I, .G, .E] [.I, .e, .g, .h] :=
  (((Context.Holds.replace [] [.E] (n2735 D H)).symm).trans (Context.Holds.replace [.I] [] (n2240 D H)))

theorem n3142 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 117, 234, 38, 0) [.G, .I, .E, .E] [.E, .G, .E, .I] :=
  ((((Context.Holds.replace [.G, .I] [] (n13 D H)).symm).trans (((Context.Holds.replace [] [.e] (n2087 D H)).symm).trans (Context.Holds.replace [.g] [] (n2743 D H)))).trans (((Context.Holds.replace [.g] [] (n2903 D H)).trans (Context.Holds.replace [] [] (n85 D H))).trans (Context.Holds.replace [] [.I] (n2068 D H))))

theorem n3158 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 124, 240, 38, 0) [.i, .G, .i, .e] [.E, .I, .g, .I] :=
  ((Context.Holds.cut [.i, .G, .i, .e] [.e, .I, .G, .I] (Context.Holds.rotate [.i, .E] [.i, .G, .i, .e, .i, .g] ((n2792 D H).relator))).trans (Context.Holds.replace [] [.I] (n3014 D H)))

theorem n3161 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 30, 60, 8, 0) [.e, .i, .g, .i] [.I, .g, .I, .e] :=
  (Context.Holds.cut [.e, .i, .g, .i] [.I, .g, .I, .e] (Context.Holds.rotate [.i, .E, .i, .G, .i] [.e, .i, .g] ((n2792 D H).relator)))

theorem n3170 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, -8, -2, 0) [.f, .j, .I, .I] [.j, .I, .I, .f] :=
  (((Context.Holds.replace [] [.I, .I] (n337 D H)).symm).trans (Context.Holds.replace [.j] [] (n2799 D H)))

theorem n3171 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 8, 2, 0) [.j, .I, .I, .f] [.f, .j, .I, .I] :=
  ((n3170 D H).symm)

theorem n3174 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 120, 248, 38, 0) [.I, .h, .G, .G] [.c, .d, .I, .h] :=
  ((((Context.Holds.replace [] [.G] (n2749 D H)).symm).trans (Context.Holds.replace [.h] [] (n2809 D H))).trans (((Context.Holds.replace [] [.I, .c] (n300 D H)).trans (Context.Holds.replace [] [] (n1696 D H))).trans (Context.Holds.replace [.c] [] (n2902 D H))))

theorem n3175 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -120, -248, -38, 0) [.c, .d, .I, .h] [.I, .h, .G, .G] :=
  ((n3174 D H).symm)

theorem n3178 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 119, 246, 40, 0) [.G, .i, .f, .h] [.c, .g, .h, .i] :=
  (((Context.Holds.replace [] [.h] (n2817 D H)).symm).trans (Context.Holds.replace [.c] [] (n2747 D H)))

theorem n3179 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -119, -246, -40, 0) [.c, .g, .h, .i] [.G, .i, .f, .h] :=
  ((n3178 D H).symm)

theorem n3191 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 246, 484, 74, 0) [.f, .I, .h, .I] [.I, .h, .I, .f] :=
  (((Context.Holds.replace [] [.I] (n2846 D H)).symm).trans (Context.Holds.replace [.I] [] (n2843 D H)))

theorem n3193 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 245, 482, 76, 0) [.I, .f, .g, .h] [.f, .h, .I, .g] :=
  (((Context.Holds.replace [.I] [] (n1982 D H)).symm).trans (((Context.Holds.replace [] [.c] (n2849 D H)).symm).trans (Context.Holds.replace [.f] [] (n2745 D H))))

theorem n3194 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -245, -482, -76, 0) [.f, .h, .I, .g] [.I, .f, .g, .h] :=
  ((n3193 D H).symm)

theorem n3195 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 246, 484, 74, 0) [.f, .i, .h, .i] [.i, .h, .i, .f] :=
  (((Context.Holds.replace [] [.i] (n2836 D H)).symm).trans (Context.Holds.replace [.i] [] (n2850 D H)))

theorem n3196 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -246, -484, -74, 0) [.i, .h, .i, .f] [.f, .i, .h, .i] :=
  ((n3195 D H).symm)

theorem n3225 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -1, -2, 2, 0) [.d, .i, .h, .E] [.h, .i, .E, .d] :=
  (((Context.Holds.replace [] [.E] (n2900 D H)).symm).trans (Context.Holds.replace [.h, .i] [] (n943 D H)))

theorem n3226 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 1, 2, -2, 0) [.h, .i, .E, .d] [.d, .i, .h, .E] :=
  ((n3225 D H).symm)

theorem n3227 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.d, .I, .I, .d] [.h, .I, .I, .h] :=
  ((((((Context.Holds.replace [] [.h, .i, .d] (n2900 D H)).trans (Context.Holds.replace [.d, .i] [.i, .d] (n7 D H))).trans (Context.Holds.replace [.d] [.d] (n15 D H))).symm).trans ((n2900 D H).mul (n2900 D H))).trans ((((Context.Holds.replace [.d, .i] [.i, .h] (n27 D H)).trans (Context.Holds.replace [.d] [.i, .h] (n2899 D H))).trans (Context.Holds.replace [] [.h, .i, .i, .h] (n3 D H))).trans (Context.Holds.replace [.h] [.h] (n15 D H))))

theorem n3228 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.h, .I, .I, .h] [.d, .I, .I, .d] :=
  ((n3227 D H).symm)

theorem n3263 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -97, -194, -22, 0) [.e, .i, .d, .e] [.E, .i, .E, .f] :=
  (((Context.Holds.replace [] [.e] (n2929 D H)).symm).trans (Context.Holds.replace [.E] [] (n2442 D H)))

theorem n3304 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 111, 222, 34, 0) [.f, .I, .g, .d] [.c, .I, .c, .g] :=
  (((Context.Holds.replace [] [.g, .d] (n2950 D H)).symm).trans (Context.Holds.replace [.c, .I] [] (n2072 D H)))

theorem n3314 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -116, -232, -36, 0) [.d, .I, .f, .I] [.I, .I, .d, .f] :=
  (((Context.Holds.replace [] [.I] (n2963 D H)).symm).trans (Context.Holds.replace [.I] [] (n1853 D H)))

theorem n3323 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 122, 260, 40, 0) [.d, .I, .I, .d] [.I, .f, .I, .f] :=
  ((((Context.Holds.replace [] [.d] (n2984 D H)).symm).trans (Context.Holds.replace [.i] [] (n1915 D H))).trans (Context.Holds.replace [] [.f] (n2802 D H)))

theorem n3337 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 96, 180, 30, 0) [.G, .G, .b, .I] [.b, .g, .i, .g] :=
  ((((Context.Holds.replace [] [.b] (n3010 D H)).trans (Context.Holds.replace [.G, .G] [] (n42 D H))).symm).trans (n595 D H))

theorem n3338 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -96, -180, -30, 0) [.b, .g, .i, .g] [.G, .G, .b, .I] :=
  ((n3337 D H).symm)

theorem n3341 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 92, 176, 30, 0) [.G, .G, .i, .g] [.c, .i, .G, .c] :=
  ((((Context.Holds.replace [] [.g] (n3010 D H)).symm).trans (n1369 D H)).trans (Context.Holds.replace [] [] (n1427 D H)))

theorem n3342 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -92, -176, -30, 0) [.c, .i, .G, .c] [.G, .G, .i, .g] :=
  ((n3341 D H).symm)

theorem n3354 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 4, 16, 6, 0) [.G, .i, .c, .h] [.d, .g, .h, .i] :=
  (((Context.Holds.replace [] [.h] (n3022 D H)).symm).trans (Context.Holds.replace [.d] [] (n2747 D H)))

theorem n3355 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -4, -16, -6, 0) [.d, .g, .h, .i] [.G, .i, .c, .h] :=
  ((n3354 D H).symm)

theorem n3361 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -118, -244, -38, 0) [.i, .d, .i, .f] [.I, .d, .f, .I] :=
  (((Context.Holds.replace [] [.f] (n3034 D H)).symm).trans (Context.Holds.replace [.I] [] (n1886 D H)))

theorem n3374 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 115, 222, 32, 0) [.g, .d, .i, .h] [.G, .h, .i, .c] :=
  (((Context.Holds.replace [] [.h] (n3067 D H)).symm).trans (Context.Holds.replace [.G] [] (n2658 D H)))

theorem n3378 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 112, 216, 30, 0) [.c, .I, .h, .g] [.d, .I, .h, .G] :=
  ((((Context.Holds.replace [] [.g] (n2655 D H)).symm).trans (Context.Holds.replace [.h] [] (n3069 D H))).trans (Context.Holds.replace [] [.G] (n2902 D H)))

theorem n3379 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -112, -216, -30, 0) [.d, .I, .h, .G] [.c, .I, .h, .g] :=
  ((n3378 D H).symm)

theorem n3380 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -110, -212, -30, 0) [.e, .I, .f, .g] [.E, .I, .f, .G] :=
  (((Context.Holds.replace [] [.g] (n1854 D H)).symm).trans (Context.Holds.replace [.E] [] (n3070 D H)))

theorem n3402 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -98, -180, -30, 0) [.E, .I, .E, .I] [.I, .G, .I, .G] :=
  ((((Context.Holds.replace [] [] (n588 D H)).symm).trans (((Context.Holds.replace [] [.b] (n3075 D H)).symm).trans (Context.Holds.replace [.g] [] (n352 D H)))).trans (Context.Holds.replace [] [] (n1491 D H)))

end Tits.CentralCoverLifting.CompatibleGenerators.RemainingConjugations
