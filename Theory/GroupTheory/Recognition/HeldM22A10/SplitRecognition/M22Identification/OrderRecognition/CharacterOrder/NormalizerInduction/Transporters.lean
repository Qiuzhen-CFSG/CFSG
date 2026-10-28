module
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysisData
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.ExceptionalData
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.ModelPairCounts
public import Theory.Character.InductionSpecialSupport
public import Theory.GroupTheory.PGroup.CyclicInvolution

/-!
# Transporters of the five special normalizer classes

Each source representative has the distinguished involution as a power.
A transporter between two representatives must fix this involution, since
its image is the unique involution in the target cyclic subgroup. The whole
involution centralizer normalizes E. Conjugating on either side inside N(E)
therefore proves the special-set transporter condition for the union of the
five actual N(E)-classes, not just for roots inside a fixed centralizer.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 6, pp.10–12.
-/

open Subgroup
open scoped BigOperators
noncomputable section
attribute [local instance] Fintype.ofFinite
namespace Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder
open LocalModelDichotomy
universe u
variable {G : Type u} [Group G] [Finite G]
variable (D : LocalData G) (k : TwistedModel ≃* D.centralizer)

omit [Finite G] in
public theorem centralizer_le_E_normalizer :
    D.centralizer ≤ normalizer (CaseII.E D k : Set G) := by
  have hN : (SemidirectProduct.inl : BinaryFour →* TwistedModel).range.Normal := by
    rw [SemidirectProduct.range_inl_eq_ker_rightHom]
    infer_instance
  have h := (Subgroup.le_normalizer_map (H :=
    (SemidirectProduct.inl : BinaryFour →* TwistedModel).range) (CaseII.into D k))
  rw [Subgroup.normalizer_eq_top_iff.mpr hN, ← MonoidHom.range_eq_map] at h
  have hr : (CaseII.into D k).range = D.centralizer := by
    simp only [CaseII.into, MonoidHom.range_comp, k.toMonoidHom.range_eq_top_of_surjective k.surjective,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  simpa only [hr, CaseII.E, MonoidHom.range_comp] using h


@[expose] public def normalizerRepresentative (r : Fin 5) : normalizer (CaseII.E D k : Set G) :=
  ⟨CaseII.into D k (specialRepresentative r),
    centralizer_le_E_normalizer D k (k (specialRepresentative r)).property⟩

@[expose] public def normalizerSpecialSupport : Set (normalizer (CaseII.E D k : Set G)) :=
  {x | ∃ r, IsConj x (normalizerRepresentative D k r)}

private theorem representative_root (r : Fin 5) :
    D.z ∈ zpowers (CaseII.into D k (specialRepresentative r)) := by
  refine mem_zpowers_iff.mpr ⟨((![1, 3, 4, 2, 2] r : ℕ) : ℤ), ?_⟩
  rw [zpow_natCast, ← map_pow, specialRepresentative_power, CaseII.into_z_zero]

private theorem root_transporter (a b g : G)
    (ha : D.z ∈ zpowers a) (hb : D.z ∈ zpowers b)
    (hg : g⁻¹ * a * g = b) : g ∈ D.centralizer := by
  let e := MulAut.conj g⁻¹
  have he : e a = b := by simpa [e] using hg
  have het : e D.z ∈ zpowers b := by
    obtain ⟨n, hn⟩ := mem_zpowers_iff.mp ha
    refine mem_zpowers_iff.mpr ⟨n, ?_⟩
    rw [← he, ← map_zpow, hn]
  have horder : orderOf (e D.z) = 2 := (e.orderOf_eq _).trans D.z_order
  have ht' : orderOf (⟨D.z, hb⟩ : zpowers b) = 2 := by
    simpa only [← Subgroup.orderOf_coe] using D.z_order
  have het' : orderOf (⟨e D.z, het⟩ : zpowers b) = 2 := by
    simpa only [← Subgroup.orderOf_coe] using horder
  have heqt := congrArg Subtype.val (IsCyclic.eq_of_orderOf_eq_two het' ht')
  have hc : g⁻¹ * D.z * g = D.z := by simpa [e] using heqt
  apply mem_centralizer_singleton_iff.mpr
  have hh := congrArg (fun x : G => g * x) hc
  simpa only [← mul_assoc, mul_inv_cancel, one_mul] using hh.symm

public theorem normalizerSpecialSupport_transporters
    (a b : normalizer (CaseII.E D k : Set G))
    (ha : a ∈ normalizerSpecialSupport D k)
    (hb : b ∈ normalizerSpecialSupport D k)
    (g : G) (hg : g⁻¹ * (a : G) * g = (b : G)) :
    g ∈ normalizer (CaseII.E D k : Set G) := by
  obtain ⟨r, hr⟩ := ha
  obtain ⟨s, hs⟩ := hb
  obtain ⟨v, hv⟩ := isConj_iff.mp hr
  obtain ⟨w, hw⟩ := isConj_iff.mp hs
  have hv' : (v : G) * a * (v : G)⁻¹ = CaseII.into D k (specialRepresentative r) :=
    congrArg Subtype.val hv
  have hw' : (w : G) * b * (w : G)⁻¹ = CaseII.into D k (specialRepresentative s) :=
    congrArg Subtype.val hw
  have hq : ((v : G) * g * (w : G)⁻¹) ∈ D.centralizer := by
    apply root_transporter D _ _ _ (representative_root D k r) (representative_root D k s)
    rw [← hv', ← hw', mul_inv_rev, mul_inv_rev, inv_inv]
    calc
      _ = (w : G) * (g⁻¹ * (a : G) * g) * (w : G)⁻¹ := by group
      _ = _ := by rw [hg]
  have hN := centralizer_le_E_normalizer D k hq
  have he : g = (v : G)⁻¹ * ((v : G) * g * (w : G)⁻¹) * w := by group
  rw [he]
  exact mul_mem (mul_mem (inv_mem v.property) hN) w.property

end Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder
