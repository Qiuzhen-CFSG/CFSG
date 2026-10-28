module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Section
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Coordinates
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.SourceChecks
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# The central quotient in Held's noncentral centralizer argument

Here `C` is the actual ambient centralizer of mu, and `Q` is C/<mu>.
The centralizer of pi in C has order 64. Nonfusion of pi and mu prevents
a lift of an element of C_Q(pi) from conjugating pi to pi*mu: the latter
is already conjugate to mu in the given local group. Thus C_Q(pi) is
exactly the image of C_C(pi), of order 32.

This is the quotient setup on printed p.233 of D. Held, "A Characterization
of some multiply transitive permutation groups, I", Illinois J. Math. 13
(1969), 224--240, DOI 10.1215/ijm/1256053756, proof of Lemma 4.2.
It does not assert the later index-four subgroup or its recognition.
-/

open Subgroup
noncomputable section
namespace Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.CentralizerStructure
universe u
variable {G : Type u} [Group G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)

/-- The ambient centralizer, before either quotient is taken. -/
public abbrev C := centralizer ({D.a10NoncentralInvolution e} : Set G)

@[expose] public def mu : C D e :=
  ⟨D.a10NoncentralInvolution e, mem_centralizer_singleton_iff.mpr rfl⟩

@[expose] public def pi : C D e :=
  ⟨D.z, mem_centralizer_singleton_iff.mpr
    (mem_centralizer_singleton_iff.mp (D.a10NoncentralInvolution_mem e)).symm⟩

public theorem mu_order : orderOf (mu D e) = 2 :=
  (Subgroup.orderOf_mk _ _).trans (D.a10NoncentralInvolution_order e)

public theorem mu_mem_center : mu D e ∈ center (C D e) := by
  apply mem_center_iff.mpr
  intro x
  exact Subtype.ext (mem_centralizer_singleton_iff.mp x.property)

/-- The central subgroup divided out in the first, rather than the final, quotient. -/
@[expose] public def Z : Subgroup (C D e) := zpowers (mu D e)

public theorem Z_le_center : Z D e ≤ center (C D e) :=
  zpowers_le.mpr (mu_mem_center D e)

public instance Z_normal : (Z D e).Normal where
  conj_mem x hx g := by
    rw [mul_inv_eq_iff_eq_mul.mpr (mem_center_iff.mp (Z_le_center D e hx) g)]
    exact hx

public theorem Z_card : Nat.card (Z D e) = 2 :=
  (Nat.card_zpowers (mu D e)).trans (mu_order D e)

public abbrev Q := C D e ⧸ Z D e

@[expose] public def q : C D e →* Q D e := QuotientGroup.mk' (Z D e)

@[expose] public def p : Q D e := q D e (pi D e)

/-- The known centralizer before taking the quotient. -/
public abbrev P := centralizer ({pi D e} : Set (C D e))

public theorem P_card : Nat.card (P D e) = 64 := by
  let f : P D e ≃ ↥(D.centralizer ⊓ C D e) :=
    { toFun := fun x => ⟨x.1.1,
        ⟨mem_centralizer_singleton_iff.mpr
          (congrArg Subtype.val (mem_centralizer_singleton_iff.mp x.property)),
          x.1.property⟩⟩
      invFun := fun x => ⟨⟨x.1, x.property.2⟩,
        mem_centralizer_singleton_iff.mpr
          (Subtype.ext (mem_centralizer_singleton_iff.mp x.property.1))⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact (Nat.card_congr f).trans (Coordinates.ambient_intersection_card D e)

public theorem Z_le_P : Z D e ≤ P D e := by
  intro x hx
  exact mem_centralizer_singleton_iff.mpr
    (mem_center_iff.mp (Z_le_center D e hx) (pi D e)).symm

private theorem mem_Z_iff [Finite G] (x : C D e) :
    x ∈ Z D e ↔ x = 1 ∨ x = mu D e := by
  classical
  rw [Z, mem_zpowers_iff_mem_range_orderOf, mu_order]
  simp only [Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨k, hk, rfl⟩
    interval_cases k <;> simp
  · rintro (rfl | rfl)
    · exact ⟨0, by decide, pow_zero _⟩
    · exact ⟨1, by decide, pow_one _⟩

public theorem pi_mul_mu_isConj_mu [Finite G] :
    IsConj ((pi D e * mu D e : C D e) : G) (mu D e : G) := by
  let f := D.a10ModelEmbedding e
  have hlocal : Coordinates.taup⁻¹ * Coordinates.mu * Coordinates.taup =
      Coordinates.pi * Coordinates.mu := by decide +kernel
  have h : IsConj (f Coordinates.mu) (f (Coordinates.pi * Coordinates.mu)) :=
    isConj_iff.mpr ⟨f Coordinates.taup⁻¹, by
      simpa only [map_mul, map_inv, inv_inv] using congrArg f hlocal⟩
  simpa only [f, map_mul, Coordinates.pi, LocalData.a10ModelEmbedding_central,
    Coordinates.mu, LocalData.a10NoncentralInvolution, pi, mu, Subgroup.coe_mul] using h.symm

/-- Nonfusion is what prevents an extra centralizer coset in the central quotient. -/
public theorem centralizer_p_comap [Finite G]
    (hfusion : ¬ IsConj D.z (D.a10NoncentralInvolution e)) :
    (centralizer ({p D e} : Set (Q D e))).comap (q D e) = P D e := by
  ext x
  simp only [mem_comap, mem_centralizer_singleton_iff, p]
  constructor
  · intro h
    have hz : x * pi D e * x⁻¹ * (pi D e)⁻¹ ∈ Z D e := by
      apply (QuotientGroup.eq_one_iff _).mp
      change q D e (x * pi D e * x⁻¹ * (pi D e)⁻¹) = 1
      simp only [map_mul, map_inv]
      rw [h]
      group
    rcases (mem_Z_iff D e _).mp hz with htriv | htwist
    · have hc : x * pi D e * x⁻¹ = pi D e := mul_inv_eq_one.mp htriv
      exact mul_inv_eq_iff_eq_mul.mp hc
    · exfalso
      apply hfusion
      have hc : x * pi D e * x⁻¹ = pi D e * mu D e := by
        have hc := eq_mul_of_mul_inv_eq htwist
        exact hc.trans (mem_center_iff.mp (mu_mem_center D e) (pi D e)).symm
      have hconj : IsConj D.z ((pi D e * mu D e : C D e) : G) :=
        isConj_iff.mpr ⟨(x : G), congrArg Subtype.val hc⟩
      exact hconj.trans (pi_mul_mu_isConj_mu D e)
  · intro h
    simpa only [map_mul] using congrArg (q D e) h

public theorem centralizer_p_eq_map [Finite G]
    (hfusion : ¬ IsConj D.z (D.a10NoncentralInvolution e)) :
    centralizer ({p D e} : Set (Q D e)) = (P D e).map (q D e) := by
  rw [← centralizer_p_comap D e hfusion]
  exact (map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective (Z D e)) _).symm

public theorem centralizer_p_card [Finite G]
    (hfusion : ¬ IsConj D.z (D.a10NoncentralInvolution e)) :
    Nat.card (centralizer ({p D e} : Set (Q D e))) = 32 := by
  have hZ : Nat.card ((Z D e).subgroupOf (P D e)) = 2 :=
    (Nat.card_congr (subgroupOfEquivOfLe (Z_le_P D e)).toEquiv).trans (Z_card D e)
  have hindex : ((Z D e).subgroupOf (P D e)).index =
      Nat.card ((P D e).map (q D e)) := by
    simpa only [q, QuotientGroup.ker_mk', relIndex] using
      (relIndex_ker (K := P D e) (q D e))
  have h := ((Z D e).subgroupOf (P D e)).index_mul_card
  rw [hZ, P_card, hindex] at h
  rw [centralizer_p_eq_map D e hfusion]
  omega

end Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.CentralizerStructure
