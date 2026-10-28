module
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.LinearThree
public import Theory.GroupTheory.Amalgam.RankTwoTransport
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Recognition.Basic

/-!
# Original linear-three extension amalgams

Inside any automorphism overgroup of PSL₃(F), take the normalizers of the
two embedded root planes and their full intersection. Each endpoint contains
its original rank-one local through the same faithful inner embedding.
For |F| > 2 its SL₂ quotient makes that endpoint nonsolvable.

For |F| = 2, an endpoint actor preserves the corresponding parabolic and
therefore its diagram type. The binary diagram kernel is inner, even when
the ambient extension contains graph actors. Thus both full endpoints and
their entire overlap equal the base images. Restriction of the inner map
gives an amalgam isomorphism with both commuting squares; it does not
replace the overlap by a chosen Sylow subgroup.

This is the linear-three original-extension restriction in the mixed
solvability application of F.1.12 in 5.2.2. Recognition of a source pair in
these normalizers remains an input from the broad DGS original comparison.
Source: Aschbacher–Smith F.1.12, printed pp.263–264, and 5.2.2, p.647.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.GreenBook.LieModels.LinearThree.ExtensionAmalgam
open Matrix.PSL3.LinearThree Matrix.PSL3.LinearThree.OuterExtensions
open Matrix.PSL3.RootPlaneGeometry Theory.GroupTheory.AutomorphismExtensionBorel
variable (F : Type*) [Field F] [Finite F] [CharP F 2]
variable (E : Subgroup (MulAut PSL(3,F))) (hE : MulAut.innerSubgroup PSL(3,F) ≤ E)

/-- The actual root-plane normalizer in the chosen automorphism extension. -/
def endpoint (b : Bool) : Subgroup E :=
  normalizer (((rootPlane F b).map (innerEmbedding E hE)) : Set E)

/-- The full intersection, including its odd part. -/
def overlap : Subgroup E := endpoint F E hE true ⊓ endpoint F E hE false

def amalgam : RankTwoAmalgam (endpoint F E hE true) (overlap F E hE)
    (endpoint F E hE false) :=
  RankTwoAmalgam.ofSubgroups _ _ _ inf_le_left inf_le_right

/-- Each original parabolic embeds by the same inner map. -/
theorem base_parabolic_le_endpoint (b : Bool) :
    (parabolic F b).map (innerEmbedding E hE) ≤ endpoint F E hE b := by
  rw [← normalizer_rootPlane F b]
  exact (rootPlane F b).le_normalizer_map (innerEmbedding E hE)

/-- The embedded rank-one local belongs to that very endpoint. -/
theorem local_le_endpoint (b : Bool) : localIn F E hE b ≤ endpoint F E hE b := by
  apply le_trans (map_mono (show localFactor F b ≤ parabolic F b from ?_))
    (base_parabolic_le_endpoint F E hE b)
  cases b
  · change lineLocal F ≤ lineParabolic F
    rw [lineParabolic_eq_sup F]
    exact le_sup_left
  · change pointLocal F ≤ pointParabolic F
    rw [pointParabolic_eq_sup F]
    exact le_sup_left

/-- An actor preserving a binary root plane is inner, even in the full
outer extension: preservation of its parabolic rules out the graph coset. -/
theorem binary_endpoint_inner (hF : Nat.card F = 2) (b : Bool)
    (a : E) (ha : a ∈ endpoint F E hE b) :
    a.val ∈ MulAut.innerSubgroup PSL(3,F) := by
  have hr : (rootPlane F b).map a.val.toMonoidHom = rootPlane F b := by
    apply (mem_normalizer_rootIn_iff (rootPlane F b) E hE
      (by
        intro x y hxy
        apply componentEmbedding_injective F E hE
        exact Subtype.ext hxy) a).mp
    rwa [rootIn_eq_map]
  have hp : (parabolic F b).map a.val.toMonoidHom = parabolic F b := by
    rw [← normalizer_rootPlane F b, map_equiv_normalizer_eq, hr]
  have ht : MapsParabolicType F a.val b b := by
    refine ⟨1, ?_⟩
    rw [map_one]
    exact hp.trans (Subgroup.map_id _).symm
  have hi := (mapsParabolicType_self_iff_mem_linearField F (n := 1)
    (by decide) (by simpa using hF) a.val b).mp ht
  rwa [Matrix.PSL3.LinearThree.OuterExtensions.linearField_eq_inner_of_card_two F hF] at hi

/-- The complete binary endpoint is the original parabolic image. No
assumption that the entire extension acts trivially on the diagram is needed. -/
theorem binary_endpoint_eq (hF : Nat.card F = 2) (b : Bool) :
    endpoint F E hE b = (parabolic F b).map (innerEmbedding E hE) := by
  apply le_antisymm _ (base_parabolic_le_endpoint F E hE b)
  intro a ha
  obtain ⟨g,hg⟩ := binary_endpoint_inner F E hE hF b a ha
  have he : innerEmbedding E hE g = a := Subtype.ext hg
  refine ⟨g, ?_, he⟩
  have hn : g ∈ (normalizer (((rootPlane F b).map (innerEmbedding E hE)) : Set E)).comap
      (innerEmbedding E hE) := by
    change innerEmbedding E hE g ∈ endpoint F E hE b
    rwa [he]
  rw [comap_normalizer_eq_of_le_range (map_le_range _ _),
    comap_map_eq_self (by
      rw [(MonoidHom.ker_eq_bot_iff _).mpr (componentEmbedding_injective F E hE)]
      exact bot_le), normalizer_rootPlane F b] at hn
  exact hn

/-- The full binary overlap is transported by that same inner embedding. -/
theorem binary_overlap_eq (hF : Nat.card F = 2) :
    overlap F E hE = (borel F).map (innerEmbedding E hE) := by
  rw [overlap, binary_endpoint_eq F E hE hF true, binary_endpoint_eq F E hE hF false,
    ← Subgroup.map_inf _ _ _ (componentEmbedding_injective F E hE)]
  exact congrArg (Subgroup.map (innerEmbedding E hE)) (LinearThree.parabolic_intersection F)

/-- The original binary extension restricts to the ordinary flag amalgam,
with both commuting squares on the whole overlap. -/
def binaryIso (hF : Nat.card F = 2) :
    RankTwoAmalgam.Iso (LinearThree.amalgam F) (amalgam F E hE) := by
  have e := RankTwoAmalgam.ofSubgroupsMapIso (innerEmbedding E hE)
    (componentEmbedding_injective F E hE) (pointParabolic F) (borel F) (lineParabolic F)
    (LinearThree.borel_le_point F) (LinearThree.borel_le_line F)
  let t : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups ((pointParabolic F).map (innerEmbedding E hE))
        ((borel F).map (innerEmbedding E hE)) ((lineParabolic F).map (innerEmbedding E hE))
        (map_mono (LinearThree.borel_le_point F)) (map_mono (LinearThree.borel_le_line F)))
      (amalgam F E hE) :=
    { left := MulEquiv.subgroupCongr (binary_endpoint_eq F E hE hF true).symm
      middle := MulEquiv.subgroupCongr (binary_overlap_eq F E hE hF).symm
      right := MulEquiv.subgroupCongr (binary_endpoint_eq F E hE hF false).symm
      left_commutes := fun _ => rfl
      right_commutes := fun _ => rfl }
  exact e.trans t

/-- A nonbinary local SL₂ quotient obstructs solvability of its actual
root-plane normalizer in every automorphism extension. -/
theorem endpoint_not_solvable (hF : 2 < Nat.card F) (b : Bool) :
    ¬ Group.IsSolvable (endpoint F E hE b) := by
  intro hs
  let := hs
  let : Group.IsSolvable (localIn F E hE b) :=
    Group.isSolvable_of_isSolvable_injective
      (f := inclusion (local_le_endpoint F E hE b)) (inclusion_injective _)
  let e := localQuotientEquiv F E hE b
  let : Group.IsSolvable SL(2,F) :=
    Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
  let := Theory.SpecificGroups.SymplecticFour.NaturalExtension.model_perfect hF
  let := Theory.SpecificGroups.SymplecticFour.NaturalExtension.model_simple hF
  exact Group.IsPerfect.not_isSolvable SL(2,F) inferInstance

end CFSG.Quasithin.ChapterF.GreenBook.LieModels.LinearThree.ExtensionAmalgam
