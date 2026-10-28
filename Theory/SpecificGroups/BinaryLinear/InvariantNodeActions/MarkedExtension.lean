module

public import Theory.SpecificGroups.SymmetricEight.InvolutionActions
public import Theory.SpecificGroups.SymmetricEight.ComponentMarking.NormalizerAction

/-!
# A marked symmetric extension of a self-centralizing A₈

Conjugation on a normal subgroup K, followed by its supplied identification
with A₈ and the checked Aut(A₈) = S₈ action, gives a faithful permutation
representation when C_X(K) = 1. Its even preimage is exactly K. If K is
proper, an odd image together with the alternating image of K exhausts S₈.
The resulting equivalence restricts to the original marking, and agrees
with the existing normalizer representation.

This is the extension step in Aschbacher–Smith 13.8.25, printed pp.959–960
(PDF pp.976–977). The invariant-parabolic restriction is separate.
-/

@[expose] public section

open Subgroup Equiv
open Theory.SpecificGroups.SymmetricEight.Involutions

namespace BinaryLinear.InvariantNodeActions
variable {X : Type*} [Group X] (K : Subgroup X) [K.Normal]

/-- The eight-point action obtained from the given component marking. -/
noncomputable def permutationRepresentation (e : K ≃* alternatingGroup (Fin 8)) :
    X →* Perm (Fin 8) :=
  (automorphismPermutationEquiv e).toMonoidHom.comp MulAut.conjNormal

theorem permutationRepresentation_on_subgroup (e : K ≃* alternatingGroup (Fin 8))
    (x : K) : permutationRepresentation K e x = (e x).val := by
  change automorphismPermutationEquiv e (MulAut.conjNormal x.val) = _
  rw [MulAut.conjNormal_val, automorphismPermutationEquiv_inner]

theorem permutationRepresentation_eq_normalizerRepresentation
    (e : K ≃* alternatingGroup (Fin 8)) (x : X)
    (hx : x ∈ normalizer (K : Set X)) :
    permutationRepresentation K e x =
      Theory.SpecificGroups.SymmetricEight.ComponentMarking.normalizerRepresentation K e ⟨x, hx⟩ := by
  rfl

theorem permutationRepresentation_conj (e : K ≃* alternatingGroup (Fin 8))
    (x : X) (k : K) :
    (e (MulAut.conjNormal x k)).val =
      permutationRepresentation K e x * (e k).val * (permutationRepresentation K e x)⁻¹ :=
  automorphismPermutationEquiv_action e (MulAut.conjNormal x) k

theorem permutationRepresentation_injective (e : K ≃* alternatingGroup (Fin 8))
    (hc : centralizer (K : Set X) = ⊥) :
    Function.Injective (permutationRepresentation K e) :=
  (automorphismPermutationEquiv e).injective.comp
    (MulAut.conjNormal_injective_of_centralizer_eq_bot K hc)

theorem permutationRepresentation_mem_alternating (e : K ≃* alternatingGroup (Fin 8))
    (hc : centralizer (K : Set X) = ⊥) (x : X) :
    permutationRepresentation K e x ∈ alternatingGroup (Fin 8) ↔ x ∈ K := by
  rw [permutationRepresentation, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    automorphismPermutationEquiv_mem_alternating]
  change x ∈ (MulAut.innerSubgroup K).comap MulAut.conjNormal ↔ x ∈ K
  rw [MulAut.conjNormal_comap_innerSubgroup, hc, sup_bot_eq]

theorem permutationRepresentation_range (e : K ≃* alternatingGroup (Fin 8))
    (hc : centralizer (K : Set X) = ⊥) (hK : K ≠ ⊤) :
    (permutationRepresentation K e).range = ⊤ := by
  obtain ⟨x, hx⟩ : ∃ x : X, x ∉ K := by
    simpa only [ne_eq, Subgroup.eq_top_iff', not_forall] using hK
  have ha : alternatingGroup (Fin 8) ≤ (permutationRepresentation K e).range := by
    intro a ha
    refine ⟨e.symm ⟨a, ha⟩, ?_⟩
    rw [permutationRepresentation_on_subgroup, e.apply_symm_apply]
  have hx' : permutationRepresentation K e x ∉ alternatingGroup (Fin 8) :=
    fun h => hx ((permutationRepresentation_mem_alternating K e hc x).mp h)
  have hz : zpowers (permutationRepresentation K e x) ≤
      (permutationRepresentation K e).range :=
    zpowers_le.mpr ⟨x, rfl⟩
  exact top_unique (alternating_sup_zpowers_eq_top hx' ▸ sup_le ha hz)

/-- A proper self-centralizing normal A₈ extends to the whole symmetric group,
with the equivalence induced by conjugation. -/
noncomputable def symmetricExtension (e : K ≃* alternatingGroup (Fin 8))
    (hc : centralizer (K : Set X) = ⊥) (hK : K ≠ ⊤) : X ≃* Perm (Fin 8) :=
  MulEquiv.ofBijective (permutationRepresentation K e)
    ⟨permutationRepresentation_injective K e hc,
      MonoidHom.range_eq_top.mp (permutationRepresentation_range K e hc hK)⟩

theorem symmetricExtension_on_subgroup (e : K ≃* alternatingGroup (Fin 8))
    (hc : centralizer (K : Set X) = ⊥) (hK : K ≠ ⊤) (x : K) :
    symmetricExtension K e hc hK x = (e x).val :=
  permutationRepresentation_on_subgroup K e x

theorem symmetricExtension_map (e : K ≃* alternatingGroup (Fin 8))
    (hc : centralizer (K : Set X) = ⊥) (hK : K ≠ ⊤) :
    K.map (symmetricExtension K e hc hK).toMonoidHom = alternatingGroup (Fin 8) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (permutationRepresentation_mem_alternating K e hc y).mpr hy
  · intro hx
    refine ⟨e.symm ⟨x, hx⟩, (e.symm ⟨x, hx⟩).property, ?_⟩
    exact (symmetricExtension_on_subgroup K e hc hK _).trans
      (congrArg Subtype.val (e.apply_symm_apply ⟨x, hx⟩))

end BinaryLinear.InvariantNodeActions
