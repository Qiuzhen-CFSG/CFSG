module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.NormalizerCoverAssembly
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.Centralizer.ElementaryCover

/-!
# Discharging the ordinary input with the same native cover

The fixed-summand owner's shared C.2.8 theorem places the full normalizer of
the actual projected radical, with the whole module W retained. Apply that
theorem to the precise ordinary interface of the odd-normalizer assembly.
Its four native rows and embedded linear-five quotient are exactly those
already used to exclude the moved image of the original V.

Thus both branches use one uniform native cover, with no separate ordinary
source-exclusion callback. The cover and its actual embedded third local
remain with qt-model-j4-elementary-normalizer-cover, and its intrinsic
symmetry with qt-model-j4-large-center-radicals. The shared ordinary proof
belongs to qt-d-1222-natural-point-fixed-summand; final odd-normalizer
discharge remains with qt-d-1222-natural-odd-kernel-normalizer.

Source: Aschbacher--Smith C.3.5, 4.4.3 and Remark 4.4.2, as used in 11.2.1,
printed pp.150--151,619--623,766--767.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The shared full-W theorem supplies the ordinary input under precisely
the same uniform native cover used in the moved-inner branch. The covering
residual, relative normality and inclusion-compatible quotient are unchanged. -/
theorem ordinaryFullModuleExclusion_of_elementary_cover
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (C : Subgroup Janko4.Model) (eC : (C ⧸ pCore 2 C) ≃* PSL(5,ZMod 2))
    (hcover : NativeElementaryNormalizerCover C) : OrdinaryFullModuleExclusion D S := by
  intro H M B R W h hstrict hn hBL hc hVB e he _ _ K hK ek
  exact Normalizers.FixedSummand.Centralizer.c28_covering_jankoFour_false_of_elementary_cover
    C eC hcover D S h hstrict hn hBL hc hVB e he K hK ek

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
