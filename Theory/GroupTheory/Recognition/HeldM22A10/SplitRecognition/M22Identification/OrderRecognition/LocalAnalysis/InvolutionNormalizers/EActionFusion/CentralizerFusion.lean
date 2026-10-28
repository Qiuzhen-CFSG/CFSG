module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.Interfaces
public import Theory.GroupTheory.InvolutionPairCentralInvolution

/-!
# Fusion from closure under involution centralizers

The normalizer of E is proper in the finite simple ambient group, and its
normal core is trivial. A conjugate of the marked involution therefore lies
outside that normalizer. If the normalizer contains the full centralizer of
each of its involutions, the dihedral common-involution argument fuses every
involution with this outside conjugate.

This supplies the consequence attributed to Thompson in Janko's argument
without a classification theorem. The closure condition is still an explicit
premise; proving it in the source cases is a separate obligation.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 2, Lemmas 6–7, pp.6–7. The elementary proof
also appears in this repository's A10Identification/Exhaustion development.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.M22Identification.CaseII
open LocalModelDichotomy
universe u
variable {G : Type u} [Group G] [Finite G] [IsSimpleGroup G]
  (D : LocalData G) (k : TwistedModel ≃* D.centralizer)

/-- Simplicity prevents the nontrivial proper elementary sixteen from being normal. -/
public theorem normalizer_E_ne_top : normalizer (E D k : Set G) ≠ ⊤ := by
  intro hN
  have hnormal : (E D k).Normal := normalizer_eq_top_iff.mp hN
  rcases hnormal.eq_bot_or_eq_top with h | h
  · have hc := E_card D k
    rw [h, Subgroup.card_bot] at hc
    norm_num at hc
  · have hc := Nat.card_le_card_of_injective
      (inclusion (show D.centralizer ≤ E D k by rw [h]; exact le_top))
      (inclusion_injective _)
    rw [D.centralizer_card, E_card] at hc
    omega

/-- The proper normalizer has trivial ambient normal core. -/
public theorem normalizer_E_normalCore :
    (normalizer (E D k : Set G)).normalCore = ⊥ := by
  rcases (inferInstance : (normalizer (E D k : Set G)).normalCore.Normal).eq_bot_or_eq_top
      with h | h
  · exact h
  · exact False.elim (normalizer_E_ne_top D k
      (top_unique (h ▸ (normalizer (E D k : Set G)).normalCore_le)))

omit [IsSimpleGroup G] in
private theorem conj_of_inside_outside (M : Subgroup G)
    (hC : ∀ t ∈ M, orderOf t = 2 → centralizer ({t} : Set G) ≤ M)
    {s t : G} (hsM : s ∈ M) (hs : orderOf s = 2)
    (htM : t ∉ M) (ht : orderOf t = 2) : IsConj s t := by
  by_contra hn
  obtain ⟨w, _, hw, hws, hwt⟩ :=
    Theory.GroupTheory.exists_central_involution_of_not_isConj s t hs ht hn
  have hwM : w ∈ M := hC s hsM hs (mem_centralizer_singleton_iff.mpr hws.eq)
  exact htM (hC w hwM hw (mem_centralizer_singleton_iff.mpr hwt.eq.symm))

/-- Full centralizer containment forces one ambient involution class. -/
public theorem involution_fusion_of_E_centralizer_closure
    (hC : ∀ t ∈ normalizer (E D k : Set G), orderOf t = 2 →
      centralizer ({t} : Set G) ≤ normalizer (E D k : Set G))
    (x : G) (hx : orderOf x = 2) : IsConj D.z x := by
  let M := normalizer (E D k : Set G)
  have hzE : D.z ∈ E D k := by
    rw [← into_z_zero D k, ← modelE_map D k]
    exact mem_map_of_mem _ (z_mem_modelE 0)
  have hzM : D.z ∈ M := (E D k).le_normalizer hzE
  have hncore : D.z ∉ M.normalCore := by
    rw [normalizer_E_normalCore D k, mem_bot]
    exact D.z_ne_one
  change ¬ ∀ g : G, g * D.z * g⁻¹ ∈ M at hncore
  push Not at hncore
  obtain ⟨g, hg⟩ := hncore
  have hgz : orderOf (g * D.z * g⁻¹) = 2 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, D.z_order]
  by_cases hxM : x ∈ M
  · exact (isConj_iff.mpr ⟨g, rfl⟩).trans
      (conj_of_inside_outside M hC hxM hx hg hgz).symm
  · exact conj_of_inside_outside M hC hzM D.z_order hxM hx

end Theory.GroupTheory.HeldM22A10.M22Identification.CaseII
