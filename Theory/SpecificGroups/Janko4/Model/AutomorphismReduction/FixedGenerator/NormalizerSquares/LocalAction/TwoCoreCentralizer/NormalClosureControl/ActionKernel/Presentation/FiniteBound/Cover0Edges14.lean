module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.ActionKernel.Presentation.FiniteBound.Cover0Edges13

/-!
# The 693-coset cover of the fixed max2 presentation

The fixed words and transitions replay `source/special_scan.json`.
Tree edges are word extensions; 17 special edges have subgroup tails and
relations derived from the 29 published relators. Every remaining edge is
obtained by cancelling known paths in an original relator loop.
The untrusted producer uses GAP only to discover this finite witness.
-/

public section
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl.ActionKernel.Presentation.FiniteBound.Cover0
open Subgroup.CosetWordCertificate

set_option maxRecDepth 100000

theorem edge896 : Holds level0Subgroup PresentedGroup.of representative ⟨273, [(false, true)], 192⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨192, [(false, true)], 273⟩ :=
    edge272
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨192, [], 192⟩ :=
    (holds_refl 192)
  exact scanFacts hp hs (holds_relator 192 (level0Relator 0) (level0_relator 0))

theorem edge896Inv : Holds level0Subgroup PresentedGroup.of representative ⟨192, [(false, false)], 273⟩ :=
  holds_reverse edge896

theorem edge897 : Holds level0Subgroup PresentedGroup.of representative ⟨274, [(false, true)], 193⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨193, [(false, true)], 274⟩ :=
    edge273
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨193, [], 193⟩ :=
    (holds_refl 193)
  exact scanFacts hp hs (holds_relator 193 (level0Relator 0) (level0_relator 0))

theorem edge897Inv : Holds level0Subgroup PresentedGroup.of representative ⟨193, [(false, false)], 274⟩ :=
  holds_reverse edge897

theorem edge898 : Holds level0Subgroup PresentedGroup.of representative ⟨275, [(false, true)], 194⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨194, [(false, true)], 275⟩ :=
    edge274
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨194, [], 194⟩ :=
    (holds_refl 194)
  exact scanFacts hp hs (holds_relator 194 (level0Relator 0) (level0_relator 0))

theorem edge898Inv : Holds level0Subgroup PresentedGroup.of representative ⟨194, [(false, false)], 275⟩ :=
  holds_reverse edge898

theorem edge899 : Holds level0Subgroup PresentedGroup.of representative ⟨276, [(false, true)], 195⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨195, [(false, true)], 276⟩ :=
    edge275
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨195, [], 195⟩ :=
    (holds_refl 195)
  exact scanFacts hp hs (holds_relator 195 (level0Relator 0) (level0_relator 0))

theorem edge899Inv : Holds level0Subgroup PresentedGroup.of representative ⟨195, [(false, false)], 276⟩ :=
  holds_reverse edge899

theorem edge900 : Holds level0Subgroup PresentedGroup.of representative ⟨277, [(false, true)], 196⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨196, [(false, true)], 277⟩ :=
    edge276
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨196, [], 196⟩ :=
    (holds_refl 196)
  exact scanFacts hp hs (holds_relator 196 (level0Relator 0) (level0_relator 0))

theorem edge900Inv : Holds level0Subgroup PresentedGroup.of representative ⟨196, [(false, false)], 277⟩ :=
  holds_reverse edge900

theorem edge901 : Holds level0Subgroup PresentedGroup.of representative ⟨278, [(false, true)], 197⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨197, [(false, true)], 278⟩ :=
    edge277
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨197, [], 197⟩ :=
    (holds_refl 197)
  exact scanFacts hp hs (holds_relator 197 (level0Relator 0) (level0_relator 0))

theorem edge901Inv : Holds level0Subgroup PresentedGroup.of representative ⟨197, [(false, false)], 278⟩ :=
  holds_reverse edge901

theorem edge902 : Holds level0Subgroup PresentedGroup.of representative ⟨279, [(false, true)], 198⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨198, [(false, true)], 279⟩ :=
    edge278
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨198, [], 198⟩ :=
    (holds_refl 198)
  exact scanFacts hp hs (holds_relator 198 (level0Relator 0) (level0_relator 0))

theorem edge902Inv : Holds level0Subgroup PresentedGroup.of representative ⟨198, [(false, false)], 279⟩ :=
  holds_reverse edge902

theorem edge903 : Holds level0Subgroup PresentedGroup.of representative ⟨280, [(false, true)], 199⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨199, [(false, true)], 280⟩ :=
    edge279
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨199, [], 199⟩ :=
    (holds_refl 199)
  exact scanFacts hp hs (holds_relator 199 (level0Relator 0) (level0_relator 0))

theorem edge903Inv : Holds level0Subgroup PresentedGroup.of representative ⟨199, [(false, false)], 280⟩ :=
  holds_reverse edge903

theorem edge904 : Holds level0Subgroup PresentedGroup.of representative ⟨281, [(false, true)], 200⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨200, [(false, true)], 281⟩ :=
    edge280
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨200, [], 200⟩ :=
    (holds_refl 200)
  exact scanFacts hp hs (holds_relator 200 (level0Relator 0) (level0_relator 0))

theorem edge904Inv : Holds level0Subgroup PresentedGroup.of representative ⟨200, [(false, false)], 281⟩ :=
  holds_reverse edge904

theorem edge905 : Holds level0Subgroup PresentedGroup.of representative ⟨282, [(false, true)], 201⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨201, [(false, true)], 282⟩ :=
    edge281
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨201, [], 201⟩ :=
    (holds_refl 201)
  exact scanFacts hp hs (holds_relator 201 (level0Relator 0) (level0_relator 0))

theorem edge905Inv : Holds level0Subgroup PresentedGroup.of representative ⟨201, [(false, false)], 282⟩ :=
  holds_reverse edge905

theorem edge906 : Holds level0Subgroup PresentedGroup.of representative ⟨283, [(false, true)], 202⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨202, [(false, true)], 283⟩ :=
    edge282
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨202, [], 202⟩ :=
    (holds_refl 202)
  exact scanFacts hp hs (holds_relator 202 (level0Relator 0) (level0_relator 0))

theorem edge906Inv : Holds level0Subgroup PresentedGroup.of representative ⟨202, [(false, false)], 283⟩ :=
  holds_reverse edge906

theorem edge907 : Holds level0Subgroup PresentedGroup.of representative ⟨284, [(false, true)], 203⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨203, [(false, true)], 284⟩ :=
    edge283
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨203, [], 203⟩ :=
    (holds_refl 203)
  exact scanFacts hp hs (holds_relator 203 (level0Relator 0) (level0_relator 0))

theorem edge907Inv : Holds level0Subgroup PresentedGroup.of representative ⟨203, [(false, false)], 284⟩ :=
  holds_reverse edge907

theorem edge908 : Holds level0Subgroup PresentedGroup.of representative ⟨285, [(false, true)], 204⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨204, [(false, true)], 285⟩ :=
    edge284
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨204, [], 204⟩ :=
    (holds_refl 204)
  exact scanFacts hp hs (holds_relator 204 (level0Relator 0) (level0_relator 0))

theorem edge908Inv : Holds level0Subgroup PresentedGroup.of representative ⟨204, [(false, false)], 285⟩ :=
  holds_reverse edge908

theorem edge909 : Holds level0Subgroup PresentedGroup.of representative ⟨286, [(false, true)], 205⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨205, [(false, true)], 286⟩ :=
    edge285
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨205, [], 205⟩ :=
    (holds_refl 205)
  exact scanFacts hp hs (holds_relator 205 (level0Relator 0) (level0_relator 0))

theorem edge909Inv : Holds level0Subgroup PresentedGroup.of representative ⟨205, [(false, false)], 286⟩ :=
  holds_reverse edge909

theorem edge910 : Holds level0Subgroup PresentedGroup.of representative ⟨287, [(false, true)], 206⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨206, [(false, true)], 287⟩ :=
    edge286
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨206, [], 206⟩ :=
    (holds_refl 206)
  exact scanFacts hp hs (holds_relator 206 (level0Relator 0) (level0_relator 0))

theorem edge910Inv : Holds level0Subgroup PresentedGroup.of representative ⟨206, [(false, false)], 287⟩ :=
  holds_reverse edge910

theorem edge911 : Holds level0Subgroup PresentedGroup.of representative ⟨288, [(false, true)], 207⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨207, [(false, true)], 288⟩ :=
    edge287
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨207, [], 207⟩ :=
    (holds_refl 207)
  exact scanFacts hp hs (holds_relator 207 (level0Relator 0) (level0_relator 0))

theorem edge911Inv : Holds level0Subgroup PresentedGroup.of representative ⟨207, [(false, false)], 288⟩ :=
  holds_reverse edge911

theorem edge912 : Holds level0Subgroup PresentedGroup.of representative ⟨289, [(false, true)], 208⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨208, [(false, true)], 289⟩ :=
    edge288
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨208, [], 208⟩ :=
    (holds_refl 208)
  exact scanFacts hp hs (holds_relator 208 (level0Relator 0) (level0_relator 0))

theorem edge912Inv : Holds level0Subgroup PresentedGroup.of representative ⟨208, [(false, false)], 289⟩ :=
  holds_reverse edge912

theorem edge913 : Holds level0Subgroup PresentedGroup.of representative ⟨242, [(false, true)], 209⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨209, [(false, true)], 242⟩ :=
    edge699
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨209, [], 209⟩ :=
    (holds_refl 209)
  exact scanFacts hp hs (holds_relator 209 (level0Relator 0) (level0_relator 0))

theorem edge913Inv : Holds level0Subgroup PresentedGroup.of representative ⟨209, [(false, false)], 242⟩ :=
  holds_reverse edge913

theorem edge914 : Holds level0Subgroup PresentedGroup.of representative ⟨290, [(false, true)], 210⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨210, [(false, true)], 290⟩ :=
    edge289
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨210, [], 210⟩ :=
    (holds_refl 210)
  exact scanFacts hp hs (holds_relator 210 (level0Relator 0) (level0_relator 0))

theorem edge914Inv : Holds level0Subgroup PresentedGroup.of representative ⟨210, [(false, false)], 290⟩ :=
  holds_reverse edge914

theorem edge915 : Holds level0Subgroup PresentedGroup.of representative ⟨291, [(false, true)], 211⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨211, [(false, true)], 291⟩ :=
    edge290
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨211, [], 211⟩ :=
    (holds_refl 211)
  exact scanFacts hp hs (holds_relator 211 (level0Relator 0) (level0_relator 0))

theorem edge915Inv : Holds level0Subgroup PresentedGroup.of representative ⟨211, [(false, false)], 291⟩ :=
  holds_reverse edge915

theorem edge916 : Holds level0Subgroup PresentedGroup.of representative ⟨292, [(false, true)], 212⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨212, [(false, true)], 292⟩ :=
    edge291
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨212, [], 212⟩ :=
    (holds_refl 212)
  exact scanFacts hp hs (holds_relator 212 (level0Relator 0) (level0_relator 0))

theorem edge916Inv : Holds level0Subgroup PresentedGroup.of representative ⟨212, [(false, false)], 292⟩ :=
  holds_reverse edge916

theorem edge917 : Holds level0Subgroup PresentedGroup.of representative ⟨293, [(false, true)], 213⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨213, [(false, true)], 293⟩ :=
    edge292
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨213, [], 213⟩ :=
    (holds_refl 213)
  exact scanFacts hp hs (holds_relator 213 (level0Relator 0) (level0_relator 0))

theorem edge917Inv : Holds level0Subgroup PresentedGroup.of representative ⟨213, [(false, false)], 293⟩ :=
  holds_reverse edge917

theorem edge918 : Holds level0Subgroup PresentedGroup.of representative ⟨294, [(false, true)], 214⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨214, [(false, true)], 294⟩ :=
    edge293
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨214, [], 214⟩ :=
    (holds_refl 214)
  exact scanFacts hp hs (holds_relator 214 (level0Relator 0) (level0_relator 0))

theorem edge918Inv : Holds level0Subgroup PresentedGroup.of representative ⟨214, [(false, false)], 294⟩ :=
  holds_reverse edge918

theorem edge919 : Holds level0Subgroup PresentedGroup.of representative ⟨295, [(false, true)], 215⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨215, [(false, true)], 295⟩ :=
    edge294
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨215, [], 215⟩ :=
    (holds_refl 215)
  exact scanFacts hp hs (holds_relator 215 (level0Relator 0) (level0_relator 0))

theorem edge919Inv : Holds level0Subgroup PresentedGroup.of representative ⟨215, [(false, false)], 295⟩ :=
  holds_reverse edge919

theorem edge920 : Holds level0Subgroup PresentedGroup.of representative ⟨296, [(false, true)], 216⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨216, [(false, true)], 296⟩ :=
    edge295
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨216, [], 216⟩ :=
    (holds_refl 216)
  exact scanFacts hp hs (holds_relator 216 (level0Relator 0) (level0_relator 0))

theorem edge920Inv : Holds level0Subgroup PresentedGroup.of representative ⟨216, [(false, false)], 296⟩ :=
  holds_reverse edge920

theorem edge921 : Holds level0Subgroup PresentedGroup.of representative ⟨297, [(false, true)], 217⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨217, [(false, true)], 297⟩ :=
    edge296
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨217, [], 217⟩ :=
    (holds_refl 217)
  exact scanFacts hp hs (holds_relator 217 (level0Relator 0) (level0_relator 0))

theorem edge921Inv : Holds level0Subgroup PresentedGroup.of representative ⟨217, [(false, false)], 297⟩ :=
  holds_reverse edge921

theorem edge922 : Holds level0Subgroup PresentedGroup.of representative ⟨298, [(false, true)], 218⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨218, [(false, true)], 298⟩ :=
    edge297
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨218, [], 218⟩ :=
    (holds_refl 218)
  exact scanFacts hp hs (holds_relator 218 (level0Relator 0) (level0_relator 0))

theorem edge922Inv : Holds level0Subgroup PresentedGroup.of representative ⟨218, [(false, false)], 298⟩ :=
  holds_reverse edge922

theorem edge923 : Holds level0Subgroup PresentedGroup.of representative ⟨299, [(false, true)], 219⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨219, [(false, true)], 299⟩ :=
    edge298
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨219, [], 219⟩ :=
    (holds_refl 219)
  exact scanFacts hp hs (holds_relator 219 (level0Relator 0) (level0_relator 0))

theorem edge923Inv : Holds level0Subgroup PresentedGroup.of representative ⟨219, [(false, false)], 299⟩ :=
  holds_reverse edge923

theorem edge924 : Holds level0Subgroup PresentedGroup.of representative ⟨300, [(false, true)], 220⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨220, [(false, true)], 300⟩ :=
    edge299
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨220, [], 220⟩ :=
    (holds_refl 220)
  exact scanFacts hp hs (holds_relator 220 (level0Relator 0) (level0_relator 0))

theorem edge924Inv : Holds level0Subgroup PresentedGroup.of representative ⟨220, [(false, false)], 300⟩ :=
  holds_reverse edge924

theorem edge925 : Holds level0Subgroup PresentedGroup.of representative ⟨223, [(false, true)], 221⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨221, [(false, true)], 223⟩ :=
    edge700
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨221, [], 221⟩ :=
    (holds_refl 221)
  exact scanFacts hp hs (holds_relator 221 (level0Relator 0) (level0_relator 0))

theorem edge925Inv : Holds level0Subgroup PresentedGroup.of representative ⟨221, [(false, false)], 223⟩ :=
  holds_reverse edge925

theorem edge926 : Holds level0Subgroup PresentedGroup.of representative ⟨301, [(false, true)], 224⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨224, [(false, true)], 301⟩ :=
    edge300
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨224, [], 224⟩ :=
    (holds_refl 224)
  exact scanFacts hp hs (holds_relator 224 (level0Relator 0) (level0_relator 0))

theorem edge926Inv : Holds level0Subgroup PresentedGroup.of representative ⟨224, [(false, false)], 301⟩ :=
  holds_reverse edge926

theorem edge927 : Holds level0Subgroup PresentedGroup.of representative ⟨302, [(false, true)], 225⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨225, [(false, true)], 302⟩ :=
    edge301
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨225, [], 225⟩ :=
    (holds_refl 225)
  exact scanFacts hp hs (holds_relator 225 (level0Relator 0) (level0_relator 0))

theorem edge927Inv : Holds level0Subgroup PresentedGroup.of representative ⟨225, [(false, false)], 302⟩ :=
  holds_reverse edge927

theorem edge928 : Holds level0Subgroup PresentedGroup.of representative ⟨303, [(false, true)], 226⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨226, [(false, true)], 303⟩ :=
    edge302
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨226, [], 226⟩ :=
    (holds_refl 226)
  exact scanFacts hp hs (holds_relator 226 (level0Relator 0) (level0_relator 0))

theorem edge928Inv : Holds level0Subgroup PresentedGroup.of representative ⟨226, [(false, false)], 303⟩ :=
  holds_reverse edge928

theorem edge929 : Holds level0Subgroup PresentedGroup.of representative ⟨304, [(false, true)], 227⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨227, [(false, true)], 304⟩ :=
    edge303
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨227, [], 227⟩ :=
    (holds_refl 227)
  exact scanFacts hp hs (holds_relator 227 (level0Relator 0) (level0_relator 0))

theorem edge929Inv : Holds level0Subgroup PresentedGroup.of representative ⟨227, [(false, false)], 304⟩ :=
  holds_reverse edge929

theorem edge930 : Holds level0Subgroup PresentedGroup.of representative ⟨305, [(false, true)], 228⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨228, [(false, true)], 305⟩ :=
    edge304
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨228, [], 228⟩ :=
    (holds_refl 228)
  exact scanFacts hp hs (holds_relator 228 (level0Relator 0) (level0_relator 0))

theorem edge930Inv : Holds level0Subgroup PresentedGroup.of representative ⟨228, [(false, false)], 305⟩ :=
  holds_reverse edge930

theorem edge931 : Holds level0Subgroup PresentedGroup.of representative ⟨306, [(false, true)], 229⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨229, [(false, true)], 306⟩ :=
    edge305
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨229, [], 229⟩ :=
    (holds_refl 229)
  exact scanFacts hp hs (holds_relator 229 (level0Relator 0) (level0_relator 0))

theorem edge931Inv : Holds level0Subgroup PresentedGroup.of representative ⟨229, [(false, false)], 306⟩ :=
  holds_reverse edge931

theorem edge932 : Holds level0Subgroup PresentedGroup.of representative ⟨307, [(false, true)], 230⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨230, [(false, true)], 307⟩ :=
    edge306
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨230, [], 230⟩ :=
    (holds_refl 230)
  exact scanFacts hp hs (holds_relator 230 (level0Relator 0) (level0_relator 0))

theorem edge932Inv : Holds level0Subgroup PresentedGroup.of representative ⟨230, [(false, false)], 307⟩ :=
  holds_reverse edge932

theorem edge933 : Holds level0Subgroup PresentedGroup.of representative ⟨308, [(false, true)], 231⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨231, [(false, true)], 308⟩ :=
    edge307
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨231, [], 231⟩ :=
    (holds_refl 231)
  exact scanFacts hp hs (holds_relator 231 (level0Relator 0) (level0_relator 0))

theorem edge933Inv : Holds level0Subgroup PresentedGroup.of representative ⟨231, [(false, false)], 308⟩ :=
  holds_reverse edge933

theorem edge934 : Holds level0Subgroup PresentedGroup.of representative ⟨309, [(false, true)], 232⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨232, [(false, true)], 309⟩ :=
    edge308
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨232, [], 232⟩ :=
    (holds_refl 232)
  exact scanFacts hp hs (holds_relator 232 (level0Relator 0) (level0_relator 0))

theorem edge934Inv : Holds level0Subgroup PresentedGroup.of representative ⟨232, [(false, false)], 309⟩ :=
  holds_reverse edge934

theorem edge935 : Holds level0Subgroup PresentedGroup.of representative ⟨310, [(false, true)], 233⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨233, [(false, true)], 310⟩ :=
    edge309
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨233, [], 233⟩ :=
    (holds_refl 233)
  exact scanFacts hp hs (holds_relator 233 (level0Relator 0) (level0_relator 0))

theorem edge935Inv : Holds level0Subgroup PresentedGroup.of representative ⟨233, [(false, false)], 310⟩ :=
  holds_reverse edge935

theorem edge936 : Holds level0Subgroup PresentedGroup.of representative ⟨247, [(false, true)], 234⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨234, [(false, true)], 247⟩ :=
    edge701
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨234, [], 234⟩ :=
    (holds_refl 234)
  exact scanFacts hp hs (holds_relator 234 (level0Relator 0) (level0_relator 0))

theorem edge936Inv : Holds level0Subgroup PresentedGroup.of representative ⟨234, [(false, false)], 247⟩ :=
  holds_reverse edge936

theorem edge937 : Holds level0Subgroup PresentedGroup.of representative ⟨311, [(false, true)], 235⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨235, [(false, true)], 311⟩ :=
    edge310
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨235, [], 235⟩ :=
    (holds_refl 235)
  exact scanFacts hp hs (holds_relator 235 (level0Relator 0) (level0_relator 0))

theorem edge937Inv : Holds level0Subgroup PresentedGroup.of representative ⟨235, [(false, false)], 311⟩ :=
  holds_reverse edge937

theorem edge938 : Holds level0Subgroup PresentedGroup.of representative ⟨312, [(false, true)], 236⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨236, [(false, true)], 312⟩ :=
    edge311
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨236, [], 236⟩ :=
    (holds_refl 236)
  exact scanFacts hp hs (holds_relator 236 (level0Relator 0) (level0_relator 0))

theorem edge938Inv : Holds level0Subgroup PresentedGroup.of representative ⟨236, [(false, false)], 312⟩ :=
  holds_reverse edge938

theorem edge939 : Holds level0Subgroup PresentedGroup.of representative ⟨313, [(false, true)], 237⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨237, [(false, true)], 313⟩ :=
    edge312
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨237, [], 237⟩ :=
    (holds_refl 237)
  exact scanFacts hp hs (holds_relator 237 (level0Relator 0) (level0_relator 0))

theorem edge939Inv : Holds level0Subgroup PresentedGroup.of representative ⟨237, [(false, false)], 313⟩ :=
  holds_reverse edge939

theorem edge940 : Holds level0Subgroup PresentedGroup.of representative ⟨314, [(false, true)], 238⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨238, [(false, true)], 314⟩ :=
    edge313
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨238, [], 238⟩ :=
    (holds_refl 238)
  exact scanFacts hp hs (holds_relator 238 (level0Relator 0) (level0_relator 0))

theorem edge940Inv : Holds level0Subgroup PresentedGroup.of representative ⟨238, [(false, false)], 314⟩ :=
  holds_reverse edge940

theorem edge941 : Holds level0Subgroup PresentedGroup.of representative ⟨315, [(false, true)], 239⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨239, [(false, true)], 315⟩ :=
    edge314
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨239, [], 239⟩ :=
    (holds_refl 239)
  exact scanFacts hp hs (holds_relator 239 (level0Relator 0) (level0_relator 0))

theorem edge941Inv : Holds level0Subgroup PresentedGroup.of representative ⟨239, [(false, false)], 315⟩ :=
  holds_reverse edge941

theorem edge942 : Holds level0Subgroup PresentedGroup.of representative ⟨316, [(false, true)], 240⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨240, [(false, true)], 316⟩ :=
    edge315
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨240, [], 240⟩ :=
    (holds_refl 240)
  exact scanFacts hp hs (holds_relator 240 (level0Relator 0) (level0_relator 0))

theorem edge942Inv : Holds level0Subgroup PresentedGroup.of representative ⟨240, [(false, false)], 316⟩ :=
  holds_reverse edge942

theorem edge943 : Holds level0Subgroup PresentedGroup.of representative ⟨317, [(false, true)], 241⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨241, [(false, true)], 317⟩ :=
    edge316
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨241, [], 241⟩ :=
    (holds_refl 241)
  exact scanFacts hp hs (holds_relator 241 (level0Relator 0) (level0_relator 0))

theorem edge943Inv : Holds level0Subgroup PresentedGroup.of representative ⟨241, [(false, false)], 317⟩ :=
  holds_reverse edge943

theorem edge944 : Holds level0Subgroup PresentedGroup.of representative ⟨318, [(false, true)], 243⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨243, [(false, true)], 318⟩ :=
    edge317
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨243, [], 243⟩ :=
    (holds_refl 243)
  exact scanFacts hp hs (holds_relator 243 (level0Relator 0) (level0_relator 0))

theorem edge944Inv : Holds level0Subgroup PresentedGroup.of representative ⟨243, [(false, false)], 318⟩ :=
  holds_reverse edge944

theorem edge945 : Holds level0Subgroup PresentedGroup.of representative ⟨319, [(false, true)], 244⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨244, [(false, true)], 319⟩ :=
    edge318
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨244, [], 244⟩ :=
    (holds_refl 244)
  exact scanFacts hp hs (holds_relator 244 (level0Relator 0) (level0_relator 0))

theorem edge945Inv : Holds level0Subgroup PresentedGroup.of representative ⟨244, [(false, false)], 319⟩ :=
  holds_reverse edge945

theorem edge946 : Holds level0Subgroup PresentedGroup.of representative ⟨320, [(false, true)], 245⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨245, [(false, true)], 320⟩ :=
    edge319
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨245, [], 245⟩ :=
    (holds_refl 245)
  exact scanFacts hp hs (holds_relator 245 (level0Relator 0) (level0_relator 0))

theorem edge946Inv : Holds level0Subgroup PresentedGroup.of representative ⟨245, [(false, false)], 320⟩ :=
  holds_reverse edge946

theorem edge947 : Holds level0Subgroup PresentedGroup.of representative ⟨321, [(false, true)], 246⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨246, [(false, true)], 321⟩ :=
    edge320
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨246, [], 246⟩ :=
    (holds_refl 246)
  exact scanFacts hp hs (holds_relator 246 (level0Relator 0) (level0_relator 0))

theorem edge947Inv : Holds level0Subgroup PresentedGroup.of representative ⟨246, [(false, false)], 321⟩ :=
  holds_reverse edge947

theorem edge948 : Holds level0Subgroup PresentedGroup.of representative ⟨426, [(false, true)], 407⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨246, [(false, true), (true, false)], 426⟩ :=
    (appendFacts edge320 edge425)
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨407, [(true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false)], 246⟩ :=
    (appendFacts (appendFacts (appendFacts (appendFacts edge406Inv (appendFacts edge937 edge234Inv)) (appendFacts edge830 (appendFacts edge125Inv edge774))) (appendFacts (appendFacts edge67Inv (appendFacts edge744 edge35Inv)) (appendFacts edge728 (appendFacts edge721Inv edge24)))) (appendFacts (appendFacts (appendFacts edge34 (appendFacts edge46 edge66)) (appendFacts edge88 (appendFacts edge124 edge166))) (appendFacts (appendFacts edge233 (appendFacts edge701 edge246Inv)) (appendFacts (appendFacts edge837 edge799Inv) (appendFacts edge173 edge245)))))
  exact scanFacts hp hs (holds_relator 246 (level0Relator 2) (level0_relator 2))

theorem edge948Inv : Holds level0Subgroup PresentedGroup.of representative ⟨407, [(false, false)], 426⟩ :=
  holds_reverse edge948

theorem edge949 : Holds level0Subgroup PresentedGroup.of representative ⟨322, [(false, true)], 248⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨248, [(false, true)], 322⟩ :=
    edge321
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨248, [], 248⟩ :=
    (holds_refl 248)
  exact scanFacts hp hs (holds_relator 248 (level0Relator 0) (level0_relator 0))

theorem edge949Inv : Holds level0Subgroup PresentedGroup.of representative ⟨248, [(false, false)], 322⟩ :=
  holds_reverse edge949

theorem edge950 : Holds level0Subgroup PresentedGroup.of representative ⟨323, [(false, true)], 249⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨249, [(false, true)], 323⟩ :=
    edge322
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨249, [], 249⟩ :=
    (holds_refl 249)
  exact scanFacts hp hs (holds_relator 249 (level0Relator 0) (level0_relator 0))

theorem edge950Inv : Holds level0Subgroup PresentedGroup.of representative ⟨249, [(false, false)], 323⟩ :=
  holds_reverse edge950

theorem edge951 : Holds level0Subgroup PresentedGroup.of representative ⟨324, [(false, true)], 250⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨250, [(false, true)], 324⟩ :=
    edge323
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨250, [], 250⟩ :=
    (holds_refl 250)
  exact scanFacts hp hs (holds_relator 250 (level0Relator 0) (level0_relator 0))

theorem edge951Inv : Holds level0Subgroup PresentedGroup.of representative ⟨250, [(false, false)], 324⟩ :=
  holds_reverse edge951

theorem edge952 : Holds level0Subgroup PresentedGroup.of representative ⟨325, [(false, true)], 251⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨251, [(false, true)], 325⟩ :=
    edge324
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨251, [], 251⟩ :=
    (holds_refl 251)
  exact scanFacts hp hs (holds_relator 251 (level0Relator 0) (level0_relator 0))

theorem edge952Inv : Holds level0Subgroup PresentedGroup.of representative ⟨251, [(false, false)], 325⟩ :=
  holds_reverse edge952

theorem edge953 : Holds level0Subgroup PresentedGroup.of representative ⟨326, [(false, true)], 252⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨252, [(false, true)], 326⟩ :=
    edge325
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨252, [], 252⟩ :=
    (holds_refl 252)
  exact scanFacts hp hs (holds_relator 252 (level0Relator 0) (level0_relator 0))

theorem edge953Inv : Holds level0Subgroup PresentedGroup.of representative ⟨252, [(false, false)], 326⟩ :=
  holds_reverse edge953

theorem edge954 : Holds level0Subgroup PresentedGroup.of representative ⟨327, [(false, true)], 253⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨253, [(false, true)], 327⟩ :=
    edge326
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨253, [], 253⟩ :=
    (holds_refl 253)
  exact scanFacts hp hs (holds_relator 253 (level0Relator 0) (level0_relator 0))

theorem edge954Inv : Holds level0Subgroup PresentedGroup.of representative ⟨253, [(false, false)], 327⟩ :=
  holds_reverse edge954

theorem edge955 : Holds level0Subgroup PresentedGroup.of representative ⟨328, [(false, true)], 254⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨254, [(false, true)], 328⟩ :=
    edge327
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨254, [], 254⟩ :=
    (holds_refl 254)
  exact scanFacts hp hs (holds_relator 254 (level0Relator 0) (level0_relator 0))

theorem edge955Inv : Holds level0Subgroup PresentedGroup.of representative ⟨254, [(false, false)], 328⟩ :=
  holds_reverse edge955

theorem edge956 : Holds level0Subgroup PresentedGroup.of representative ⟨329, [(false, true)], 255⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨255, [(false, true)], 329⟩ :=
    edge328
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨255, [], 255⟩ :=
    (holds_refl 255)
  exact scanFacts hp hs (holds_relator 255 (level0Relator 0) (level0_relator 0))

theorem edge956Inv : Holds level0Subgroup PresentedGroup.of representative ⟨255, [(false, false)], 329⟩ :=
  holds_reverse edge956

theorem edge957 : Holds level0Subgroup PresentedGroup.of representative ⟨330, [(false, true)], 256⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨256, [(false, true)], 330⟩ :=
    edge329
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨256, [], 256⟩ :=
    (holds_refl 256)
  exact scanFacts hp hs (holds_relator 256 (level0Relator 0) (level0_relator 0))

theorem edge957Inv : Holds level0Subgroup PresentedGroup.of representative ⟨256, [(false, false)], 330⟩ :=
  holds_reverse edge957

theorem edge958 : Holds level0Subgroup PresentedGroup.of representative ⟨331, [(false, true)], 257⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨257, [(false, true)], 331⟩ :=
    edge330
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨257, [], 257⟩ :=
    (holds_refl 257)
  exact scanFacts hp hs (holds_relator 257 (level0Relator 0) (level0_relator 0))

theorem edge958Inv : Holds level0Subgroup PresentedGroup.of representative ⟨257, [(false, false)], 331⟩ :=
  holds_reverse edge958

theorem edge959 : Holds level0Subgroup PresentedGroup.of representative ⟨332, [(false, true)], 258⟩ := by
  have hp : Holds level0Subgroup PresentedGroup.of representative ⟨258, [(false, true)], 332⟩ :=
    edge331
  have hs : Holds level0Subgroup PresentedGroup.of representative ⟨258, [], 258⟩ :=
    (holds_refl 258)
  exact scanFacts hp hs (holds_relator 258 (level0Relator 0) (level0_relator 0))

theorem edge959Inv : Holds level0Subgroup PresentedGroup.of representative ⟨258, [(false, false)], 332⟩ :=
  holds_reverse edge959


end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl.ActionKernel.Presentation.FiniteBound.Cover0
