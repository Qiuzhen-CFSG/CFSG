module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.TwoCoreSplitting.Counting.LinearCount.LocalAction
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.RankOne.LocalRecognition.Centralizers
public import BenderSuzuki.ZD.Recognition.MinimalReduction.Radical.Fusion

/-!
# The literal fixed-point degree for the Section 17 centralizer

Fusion control puts every coset fixed by u in the orbit of C_G(u).
The proved local-circle Frattini argument then replaces C_G(u) by its
actual distinguished closure. Orbit–stabilizer expresses the fixed-point
degree as the index of the original intersection with M. No fixed-point
cardinality or permutation-model identification is assumed.

Source: GLS4, Chapter 2, Corollary 7.13, Lemma 16.3(b), and (17D).
-/

noncomputable section
namespace BenderSuzuki.ZD.Section17
open Theory.GroupTheory PFAppendixIII PFchapter1section1 Subgroup
open scoped Pointwise
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

/-- The distinguished centralizer circle is transitive on the actual fixed
cosets of the original u. This uses the earlier local Frattini theorem. -/
public theorem fixedPoints_eq_circle_orbit
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    (d : TwoCoreLocalData Z M) :
    {beta : G ⧸ M | ((d.u : M) : G) • beta = beta} =
      MulAction.orbit (centralizerClosure Z ((d.u : M) : G))
        (QuotientGroup.mk 1 : G ⧸ M) := by
  let v : G := ((d.u : M) : G)
  have hvorder : orderOf v = 2 := by
    simpa only [v, Subgroup.orderOf_coe] using d.u_order
  have hv : IsInvolution v :=
    ⟨(orderOf_eq_prime_iff.mp hvorder).2, (orderOf_eq_prime_iff.mp hvorder).1⟩
  let F := centralizer ({v} : Set G)
  have hFM : ¬ F ≤ M := fun hc => d.t_not_mem
    (hc (mem_centralizer_singleton_iff.mpr d.commutes_t.symm.eq))
  have hfactor : (F : Set G) = (centralizerClosure Z v : Set G) * (F ⊓ M : Subgroup G) := by
    simpa only [localCircleIn_eq_closure, centralizerClosure, F] using
      localCircle_frattini_factorization h r F (r.involution_centralizer_ne_top h hv)
        hFM ⟨d.z, d.z_mem, mem_centralizer_singleton_iff.mpr d.commutes_z.symm.eq,
          d.z.property⟩
  let alpha : G ⧸ M := QuotientGroup.mk 1
  have hvfix : v • alpha = alpha := by
    change v ∈ MulAction.stabilizer G (QuotientGroup.mk 1 : G ⧸ M)
    rw [baseCoset_stabilizer]
    exact (d.u : M).property
  apply Set.Subset.antisymm
  · intro beta hbeta
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective beta
    have hgalpha : g • alpha = QuotientGroup.mk g := by
      change (QuotientGroup.mk (g * 1) : G ⧸ M) = QuotientGroup.mk g
      rw [mul_one]
    have hgfix : v • (g • alpha) = g • alpha := by
      rw [hgalpha]
      exact hbeta
    have hvconj : MulAut.conj g⁻¹ v ∈ M := by
      rw [← baseCoset_stabilizer M]
      apply MulAction.mem_stabilizer_iff.mpr
      change (g⁻¹ * v * (g⁻¹)⁻¹) • alpha = alpha
      rw [inv_inv]
      rw [mul_smul, mul_smul, hgfix, inv_smul_smul]
    obtain ⟨S, hSM, hf⟩ := r.fusion
    obtain ⟨m, hm⟩ := involution_fusion_in_subgroup S hSM hf hv
      (IsInvolution.map_of_injective hv (MulAut.conj g⁻¹).toMonoidHom
        (MulAut.conj g⁻¹).injective)
      (d.u : M).property hvconj (isConj_iff.mpr ⟨g⁻¹, rfl⟩)
    have hc : g * (m : G) ∈ centralizer ({v} : Set G) := by
      apply mem_centralizer_singleton_iff.mpr
      change (m : G) * v * (m : G)⁻¹ = g⁻¹ * v * (g⁻¹)⁻¹ at hm
      rw [inv_inv] at hm
      calc
        (g * (m : G)) * v = g * ((m : G) * v * (m : G)⁻¹) * m := by group
        _ = v * (g * (m : G)) := by rw [hm]; group
    change g * (m : G) ∈ (centralizer ({v} : Set G) : Set G) at hc
    rw [show (centralizer ({v} : Set G) : Set G) = _ from
      hfactor] at hc
    obtain ⟨l, hl, d, hd, he⟩ := hc
    change l * d = g * (m : G) at he
    have hmfix : (m : G) • alpha = alpha := by
      change (m : G) ∈ MulAction.stabilizer G (QuotientGroup.mk 1 : G ⧸ M)
      rw [baseCoset_stabilizer]
      exact m.property
    have hdfix : d • alpha = alpha := by
      change d ∈ MulAction.stabilizer G (QuotientGroup.mk 1 : G ⧸ M)
      rw [baseCoset_stabilizer]
      exact hd.2
    apply MulAction.mem_orbit_iff.mpr
    refine ⟨⟨l, hl⟩, ?_⟩
    change l • alpha = QuotientGroup.mk g
    calc
      l • alpha = (l * d) • alpha := by rw [mul_smul, hdfix]
      _ = (g * (m : G)) • alpha := by rw [he]
      _ = QuotientGroup.mk g := by
        rw [mul_smul, hmfix]
        exact hgalpha
  · intro beta hbeta
    obtain ⟨l, rfl⟩ := MulAction.mem_orbit_iff.mp hbeta
    change v • ((l : G) • alpha) = (l : G) • alpha
    have hc := mem_centralizer_singleton_iff.mp (centralizerClosure_le Z v l.property)
    rw [← mul_smul, ← hc, mul_smul, hvfix]


/-- The fixed-point degree is the index of the actual base stabilizer in
B°, before applying any of the four model alternatives. -/
public theorem fixedPoints_card_eq_circle_index
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    (d : TwoCoreLocalData Z M) :
    Nat.card {beta : G ⧸ M // ((d.u : M) : G) • beta = beta} =
      (M.comap (centralizerClosure Z ((d.u : M) : G)).subtype).index := by
  let B := centralizerClosure Z ((d.u : M) : G)
  let a : G ⧸ M := QuotientGroup.mk 1
  have hstab : MulAction.stabilizer B a = M.comap B.subtype := by
    ext x
    change (x : G) ∈ MulAction.stabilizer G (QuotientGroup.mk 1 : G ⧸ M) ↔ (x : G) ∈ M
    rw [baseCoset_stabilizer]
  calc
    _ = Nat.card (MulAction.orbit B a) :=
      Nat.card_congr (Equiv.setCongr (fixedPoints_eq_circle_orbit h r d))
    _ = (MulAction.stabilizer B a).index :=
      Nat.card_congr (MulAction.orbitEquivQuotientStabilizer B a)
    _ = _ := congrArg Subgroup.index hstab

/-- The rational number in (17D), with both centralizers relative to the
original two-point stabilizer. It is not an integral subgroup index. -/
@[expose] public def centralizerRatio (d : TwoCoreLocalData Z M) : ℚ :=
  (Nat.card (residualPairStabilizer M d.t ⊓
    centralizer ({((d.u : M) : G)} : Set G) : Subgroup G) : ℚ) /
  (Nat.card (residualPairStabilizer M d.t ⊓
    centralizer ({d.t * ((d.u : M) : G)} : Set G) : Subgroup G) : ℚ)

/-- The source ratio is strictly positive, since these are finite groups. -/
public theorem centralizerRatio_pos (d : TwoCoreLocalData Z M) :
    0 < centralizerRatio d := by
  unfold centralizerRatio
  exact div_pos (Nat.cast_pos.mpr Nat.card_pos) (Nat.cast_pos.mpr Nat.card_pos)

omit [Finite G] in
private theorem relative_centralizer_card_mul_index (D : Subgroup G) (v : G) :
    Nat.card (D ⊓ centralizer ({v} : Set G) : Subgroup G) *
      (centralizer ({v} : Set G)).relIndex D = Nat.card D := by
  have he := Nat.card_congr
    (subgroupOfEquivOfLe (H := D ⊓ centralizer ({v} : Set G)) (K := D) inf_le_left).toEquiv
  rw [inf_subgroupOf_left] at he
  rw [← he]
  exact (centralizer ({v} : Set G)).subgroupOf D |>.card_mul_index

/-- The centralizer-order ratio equals the reversed ratio of relative
indices. This is the orientation required when eliminating the two
incidence cardinalities in Lemma 17.1. -/
public theorem centralizerRatio_eq_index_ratio (d : TwoCoreLocalData Z M) :
    centralizerRatio d =
      ((centralizer ({d.t * ((d.u : M) : G)} : Set G)).relIndex
        (residualPairStabilizer M d.t) : ℚ) /
      ((centralizer ({((d.u : M) : G)} : Set G)).relIndex
        (residualPairStabilizer M d.t) : ℚ) := by
  let D := residualPairStabilizer M d.t
  have hu := relative_centralizer_card_mul_index D ((d.u : M) : G)
  have hv := relative_centralizer_card_mul_index D (d.t * ((d.u : M) : G))
  have hindex : (centralizer ({((d.u : M) : G)} : Set G)).relIndex D ≠ 0 := by
    intro he
    rw [he, mul_zero] at hu
    exact Nat.card_pos.ne' hu.symm
  unfold centralizerRatio
  apply (div_eq_div_iff (by exact_mod_cast
    (Nat.card_pos (α := (D ⊓ centralizer ({d.t * ((d.u : M) : G)} : Set G) : Subgroup G))).ne')
    (by exact_mod_cast hindex)).mpr
  exact_mod_cast hu.trans (by simpa only [mul_comm] using hv.symm)

end BenderSuzuki.ZD.Section17
