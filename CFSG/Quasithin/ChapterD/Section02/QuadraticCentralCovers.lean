module
public import CFSG.Quasithin.ChapterD.Section02.QuadraticOrbit
public import Theory.Representation.BinaryOffender.Homogeneous.QuadraticCentralCovers

/-!
# Minimum-ratio actors preserve central covers

If a minimum-ratio quadratic actor moves a homogeneous cover, its image on
the orbit span has rank one. D.2.5 bounds the fixed codimension there by two.
Independence only in the central quotient already bounds this codimension
below by the dimension of the seed's central quotient. Thus a quotient of
dimension greater than two forces stability of the full original cover.

The detecting-actor consumers give the quadratic-ratio bound on the literal
faithful images of K join A acting on I and on its full normalizer orbit
span, retaining all covering kernels.
The Chapter14 consumer supplies the actors and natural quotient markings
from the original terminal component hypotheses.

Source: Aschbacher--Smith D.2.5, p.179, and14.6.22, p.1038.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace Representation.BinaryOffender.Homogeneous
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- D.2.5 excludes movement of a large faithful central quotient without
assuming that the covering kernel vanishes. -/
theorem IsIrrPlusWith.minimal_quadratic_stabilizes_central_cover
    {K T A : Subgroup G} {I : Submodule (ZMod 2) V}
    (hI : IsIrrPlusWith ρ K T I) (hAT : A ≤ T)
    (hA : A ∈ CFSG.Quasithin.ChapterD.RPlusBound ρ 2) (hq : IsQuadratic ρ A)
    (hf : Function.Injective (centralQuotientRepresentation ρ K I hI.isIrrPlus.choose))
    (hdim : 2 < Module.finrank (ZMod 2) (centralQuotient ρ K I)) :
    A ≤ subspaceStabilizer ρ I := by
  intro a ha
  apply (subspace_map_eq_iff ρ I a).mp
  by_contra hm
  let W := orbitSpan ρ A I
  have hW := orbitSpan_invariant ρ A I
  have hIW : I ≤ W := le_orbitSpan ρ A I
  have hdis := hI.isIrrPlus.disjoint_quotientImages ρ
    (hI.isIrrPlus.map_normalizer ρ (hI.normalizes (hAT ha))) (Ne.symm hm)
  have hif : I ⊓ (W ⊓ fixedSpace ρ A) ≤ I ⊓ fixedSpace ρ K := by
    intro v hv
    refine ⟨hv.1,?_⟩
    apply (Submodule.Quotient.mk_eq_zero _).mp
    apply Submodule.disjoint_def.mp hdis _ ⟨v,hv.1,rfl⟩
    exact ⟨ρ a v,⟨v,hv.1,rfl⟩,congrArg (fixedSpace ρ K).mkQ (hv.2.2 ⟨a,ha⟩)⟩
  have hn : ¬ W ≤ fixedSpace ρ A := by
    intro hh
    apply hI.isIrrPlus.not_le_fixedSpace ρ
    exact fun v hv => (hif ⟨hv,hIW hv,hh (hIW hv)⟩).2
  have hb := CFSG.Quasithin.ChapterD.RPlusBound.restricted ρ hA W hW hn
  have hcard := hI.quadratic_moving_cover_image_card ρ hAT hA.1.1 hq hf ha hm
  have hr : rank (restrictedSubgroup ρ W A) = 1 := by
    change Nat.log 2 (Nat.card (restrictedSubgroup ρ (orbitSpan ρ A I) A)) = 1
    rw [hcard]; decide
  have hc := (actionRatio_le_nat_iff _ hb.1 2).mp hb.2
  rw [hr,fixedCodim_restrictedSubgroup ρ W A hW] at hc
  have he := I.finrank_sup_add_finrank_inf_eq (W ⊓ fixedSpace ρ A)
  have hd := Submodule.finrank_mono (sup_le hIW (inf_le_left : W ⊓ fixedSpace ρ A ≤ W))
  have hi := Submodule.finrank_mono hif
  have hqdim := Submodule.finrank_quotient_add_finrank ((fixedSpace ρ K).comap I.subtype)
  have hk := Submodule.finrank_map_subtype_eq I ((fixedSpace ρ K).comap I.subtype)
  rw [Submodule.map_comap_subtype] at hk
  change Module.finrank (ZMod 2) (centralQuotient ρ K I) +
    Module.finrank (ZMod 2) ((fixedSpace ρ K).comap I.subtype) = Module.finrank (ZMod 2) I at hqdim
  omega

end Representation.BinaryOffender.Homogeneous

namespace CFSG.Quasithin.ChapterD
open Representation.BinaryOffender.Homogeneous
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- The actual image of the component and a detecting minimum-ratio actor
on the original central cover has quadratic ratio at most two. -/
theorem stable_central_cover_image_bound
    {K T A : Subgroup G} {I : Submodule (ZMod 2) V}
    (hI : IsIrrPlusWith ρ K T I) (hAT : A ≤ T)
    (hA : A ∈ RPlusBound ρ 2) (hq : IsQuadratic ρ A)
    (hf : Function.Injective (centralQuotientRepresentation ρ K I hI.isIrrPlus.choose))
    (hdim : 2 < Module.finrank (ZMod 2) (centralQuotient ρ K I))
    (hn : ¬ A ≤ centralizer (K : Set G)) :
    ∃ hD : K ⊔ A ≤ subspaceStabilizer ρ I,
      quadraticRatio (imageRepresentation (invariantSubspace ρ (K ⊔ A) I hD).toRepresentation) ≤ 2 := by
  have hs := hI.minimal_quadratic_stabilizes_central_cover ρ hAT hA hq hf hdim
  have hnI : ¬ I ≤ fixedSpace ρ A := by
    intro hh
    apply hn
    intro a ha
    apply centralizes_of_fixed_central_image ρ hI.isIrrPlus hf (hI.normalizes (hAT ha))
    intro v hv
    have hvf : ρ a v = v := hh hv ⟨a,ha⟩
    rw [hvf,sub_self]
    exact Submodule.zero_mem _
  have hb := RPlusBound.restricted ρ hA I hs hnI
  exact ⟨sup_le hI.invariant hs,quadraticRatio_image_invariantSubspace_le_two ρ (K ⊔ A) A I
    (sup_le hI.invariant hs) le_sup_right hb.1 hq hb.2⟩

/-- D.2.5 also bounds the actual component-normalizer orbit span, using the
same detecting actor. In the binary-three application this is the literal
pair of central covers; their fixed kernels need not be disjoint. -/
theorem central_cover_orbit_image_bound
    {K T A : Subgroup G} {I : Submodule (ZMod 2) V}
    (hI : IsIrrPlusWith ρ K T I) (hAT : A ≤ T)
    (hA : A ∈ RPlusBound ρ 2) (hq : IsQuadratic ρ A)
    (hf : Function.Injective (centralQuotientRepresentation ρ K I hI.isIrrPlus.choose))
    (hn : ¬ A ≤ centralizer (K : Set G)) :
    ∃ hD : K ⊔ A ≤ subspaceStabilizer ρ (orbitSpan ρ T I),
      quadraticRatio (imageRepresentation
        (invariantSubspace ρ (K ⊔ A) (orbitSpan ρ T I) hD).toRepresentation) ≤ 2 := by
  let W := orbitSpan ρ T I
  have hs : A ≤ subspaceStabilizer ρ W := hAT.trans (orbitSpan_invariant ρ T I)
  have hnW : ¬ W ≤ fixedSpace ρ A := by
    intro hh
    apply hn
    intro a ha
    apply centralizes_of_fixed_central_image ρ hI.isIrrPlus hf (hI.normalizes (hAT ha))
    intro v hv
    have hvf : ρ a v = v := hh (le_orbitSpan ρ T I hv) ⟨a,ha⟩
    rw [hvf,sub_self]
    exact Submodule.zero_mem _
  have hb := RPlusBound.restricted ρ hA W hs hnW
  have hD : K ⊔ A ≤ subspaceStabilizer ρ W :=
    sup_le (orbitSpan_component_invariant ρ hI.normalizes hI.isIrrPlus) hs
  exact ⟨hD,quadraticRatio_image_invariantSubspace_le_two ρ (K ⊔ A) A W hD
    le_sup_right hb.1 hq hb.2⟩

end CFSG.Quasithin.ChapterD
