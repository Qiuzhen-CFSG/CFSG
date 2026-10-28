module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.ExtraspecialLocal.SourceData
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.Elementary
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.Reductions
public import BenderSuzuki.External.Huppert.IV.ResidualGenerators
public import Theory.GroupTheory.PrimeOrderLift

/-!
# Order-three generation and the extraspecial local residual

An exponent-three quotient with two-group kernel makes every odd-order
nonidentity element have order three. The coprime-order description of O²
therefore identifies it with θ. Cauchy's theorem applied to the central
inverse image gives nontriviality. The factorization M ∩ Mc = C_M(V)T and
Y = θ(M) then identify this residual with θ(M ∩ H).

The two-core of H lies in its specified Sylow subgroup, hence in M ∩ H.
Characteristic invariance of θ supplies the needed relative normalization.
The commutator lies in the intersection, a normal two-subgroup of Y₀,
and hence in O₂(Y₀). No ambient normality or abelianness is assumed.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.49(b) and the following calculation, printed p.1143.
-/

@[expose] public section

open Subgroup Stellmacher
open scoped commutatorElement

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.ExtraspecialLocal

variable {G : Type*} [Group G] [Finite G]

/-- Every element of order three belongs to the actual two-residual. -/
theorem theta_le_twoResidual (X : Subgroup G) : theta X ≤ twoResidualAmbient X := by
  apply (closure_le _).mpr
  rintro x ⟨hx, ho⟩
  refine ⟨⟨x, hx⟩, ?_, rfl⟩
  rw [Stellmacher.SectionThree.twoResidualSubgroup_eq_hktPResidual',
    BenderSuzuki.External.hktPResidual_eq_closure_coprime_orderOf]
  apply Subgroup.subset_closure
  change Nat.Coprime 2 (orderOf (⟨x, hx⟩ : X))
  rw [← Subgroup.orderOf_coe, ho]
  decide

/-- A two-group kernel and exponent-three image identify O²(X) with θ(X). -/
theorem twoResidual_eq_theta_of_exponent_three
    (X : Subgroup G) {K : Type*} [Group K] (f : X →* K)
    (hk : IsPGroup 2 f.ker) (he : ∀ x : X, f x ^ 3 = 1) :
    twoResidualAmbient X = theta X := by
  apply le_antisymm ?_ (theta_le_twoResidual X)
  change (twoResidualSubgroup X).map X.subtype ≤ theta X
  rw [map_le_iff_le_comap, Stellmacher.SectionThree.twoResidualSubgroup_eq_hktPResidual',
    BenderSuzuki.External.hktPResidual_eq_closure_coprime_orderOf, closure_le]
  intro x hx
  have ho : orderOf x ∣ 3 := by
    rw [← f.orderOf_map_eq_of_coprime_of_isPGroup_ker hk x hx]
    exact orderOf_dvd_of_pow_eq_one (he x)
  rcases (Nat.dvd_prime Nat.prime_three).mp ho with ho | ho
  · have hx1 := orderOf_eq_one_iff.mp ho
    simp [hx1]
  · exact Subgroup.subset_closure ⟨x.property, (Subgroup.orderOf_coe x).trans ho⟩

/-- The order-three generators of M ∩ H are exactly those in C_Y(V). -/
theorem theta_intersection_of_residual_bound
    (M H Y V : Subgroup G) (hYM : Y ≤ M) (hY : Y = theta M)
    (hCH : Y ⊓ centralizer (V : Set G) ≤ H)
    (hres : twoResidualAmbient (M ⊓ H) ≤ centralizer (V : Set G)) :
    theta (M ⊓ H) = theta (Y ⊓ centralizer (V : Set G)) := by
  apply le_antisymm
  · apply (closure_le _).mpr
    rintro x ⟨hx, ho⟩
    have hθ : x ∈ theta (M ⊓ H) := Subgroup.subset_closure ⟨hx, ho⟩
    apply Subgroup.subset_closure
    refine ⟨⟨?_, hres (theta_le_twoResidual _ hθ)⟩, ho⟩
    rw [hY]
    exact theta_mono inf_le_left hθ
  · apply theta_mono
    exact le_inf (inf_le_left.trans hYM) hCH

omit [Finite G] in
/-- Mutual normalization gives the intersection bound; its two-group property puts it in the relative core. -/
theorem commutator_core_le
    (H Q Y₀ : Subgroup G) (hYH : Y₀ ≤ H)
    (hHQ : H ≤ normalizer (Q : Set G))
    (hQY : Q ≤ normalizer (Y₀ : Set G)) (hp : IsPGroup 2 Q) :
    ⁅Q, Y₀⁆ ≤ Q ⊓ Y₀ ∧ ⁅Q, Y₀⁆ ≤ Y₀.pCoreIn 2 := by
  have hc : ⁅Q, Y₀⁆ ≤ Q ⊓ Y₀ := le_inf
    (le_normalizer_iff_commutator_le_left.mp (hYH.trans hHQ))
    (le_normalizer_iff_commutator_le_right.mp hQY)
  refine ⟨hc, hc.trans (le_pCoreIn_of_normalizes (hp.to_le inf_le_left) inf_le_right ?_)⟩
  apply le_normalizer_iff.mpr
  intro y hy x hx
  exact ⟨(hHQ (hYH hy) x).mp hx.1, Y₀.mul_mem (Y₀.mul_mem hy hx.2) (Y₀.inv_mem hy)⟩

/-- The generation identity for every subgroup of a group with exponent-three two-core quotient. -/
theorem residual_eq_theta_of_subgroup_exponent_three
    (X Y : Subgroup G) (hXY : X ≤ Y)
    (he : Monoid.exponent (Y ⧸ pCore 2 Y) = 3) :
    twoResidualAmbient X = theta X := by
  let f := (QuotientGroup.mk' (pCore 2 Y)).comp (inclusion hXY)
  apply twoResidual_eq_theta_of_exponent_three X f
  · change IsPGroup 2 ((QuotientGroup.mk' (pCore 2 Y)).ker.comap (inclusion hXY))
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_of_injective _ (inclusion_injective hXY)
  · intro x
    rw [← he]
    exact Monoid.pow_exponent_eq_one _

omit [Finite G] in
/-- The center of the genuine extraspecial quotient contributes a factor of three. -/
theorem three_dvd_card_twoCenter (Y : Subgroup G)
    [IsExtraspecial 3 (Y ⧸ pCore 2 Y)] : 3 ∣ Nat.card (twoCenter Y) := by
  let q := QuotientGroup.mk' (pCore 2 Y)
  let K := (center (Y ⧸ pCore 2 Y)).comap q
  have hm : K.map q = center (Y ⧸ pCore 2 Y) :=
    map_comap_eq_self (by intro z _; exact QuotientGroup.mk'_surjective _ z)
  have hd := card_map_dvd K q
  rw [hm, IsExtraspecial.center_order_p 3 (Y ⧸ pCore 2 Y)] at hd
  simpa only [twoCenter, card_map_of_injective Y.subtype_injective] using hd

/-- Cauchy supplies a nonidentity order-three generator. -/
theorem theta_ne_bot_of_three_dvd_card (X : Subgroup G) (h3 : 3 ∣ Nat.card X) :
    theta X ≠ ⊥ := by
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := X) 3 h3
  intro hbot
  have hmem : (x : G) ∈ theta X :=
    Subgroup.subset_closure ⟨x.property, (Subgroup.orderOf_coe x).trans hx⟩
  rw [hbot, mem_bot] at hmem
  have hx1 : x = 1 := Subtype.ext hmem
  simp [hx1] at hx

/-- The extraspecial center makes the centralizer residual nontrivial and identifies it with θ(M ∩ H). -/
theorem extraspecial_residual_generation
    (M H Y V : Subgroup G) (hYM : Y ≤ M) (hY : Y = theta M)
    [IsExtraspecial 3 (Y ⧸ pCore 2 Y)]
    (he : Monoid.exponent (Y ⧸ pCore 2 Y) = 3)
    (hcenter : Y ⊓ centralizer (V : Set G) = twoCenter Y)
    (hCH : Y ⊓ centralizer (V : Set G) ≤ H)
    (hres : twoResidualAmbient (M ⊓ H) ≤ centralizer (V : Set G)) :
    twoResidualAmbient (Y ⊓ centralizer (V : Set G)) ≠ ⊥ ∧
    twoResidualAmbient (Y ⊓ centralizer (V : Set G)) = theta (M ⊓ H) := by
  have heq := residual_eq_theta_of_subgroup_exponent_three
    (Y ⊓ centralizer (V : Set G)) Y inf_le_left he
  rw [heq]
  refine ⟨theta_ne_bot_of_three_dvd_card _ ?_,
    (theta_intersection_of_residual_bound M H Y V hYM hY hCH hres).symm⟩
  rw [hcenter]
  exact three_dvd_card_twoCenter Y

omit [Finite G] in
/-- The characteristic subgroup θ(M ∩ H) is normalized by O₂(H) when that core lies in M. -/
theorem commutator_theta_intersection_core_le
    (M H : Subgroup G) (hQM : H.pCoreIn 2 ≤ M) :
    ⁅H.pCoreIn 2, theta (M ⊓ H)⁆ ≤
      H.pCoreIn 2 ⊓ theta (M ⊓ H) ∧
    ⁅H.pCoreIn 2, theta (M ⊓ H)⁆ ≤ (theta (M ⊓ H)).pCoreIn 2 := by
  apply commutator_core_le H _ _ ((theta_le _).trans inf_le_right)
  · exact normalizer_le_normalizer_characteristic_image H (pCore 2 H) |>.trans' H.le_normalizer
  · exact (le_inf hQM (pCoreIn_le 2 H)).trans
      ((M ⊓ H).le_normalizer.trans (normalizer_le_normalizer_theta _))
  · exact isPGroup_pCoreIn 2 H

/-- Source 15.3.49(b) and the following commutator calculation, with the genuine earlier-source inputs explicit. -/
theorem extraspecial_local_algebra
    (M Mc H Y V : Subgroup G) (T : Sylow 2 G)
    (hYM : Y ≤ M) (h : ExtraspecialCase M Y V)
    (hM : M ≤ normalizer (V : Set G))
    (hTM : (T : Subgroup G) ≤ M) (hTH : (T : Subgroup G) ≤ H)
    (hH : H ≤ Mc) (hCH : Y ⊓ centralizer (V : Set G) ≤ H)
    (hfactor : ∀ x ∈ M ⊓ Mc,
      ∃ c ∈ M ⊓ centralizer (V : Set G), ∃ t ∈ (T : Subgroup G), c * t = x) :
    let Y₀ := twoResidualAmbient (Y ⊓ centralizer (V : Set G))
    Y₀ ≠ ⊥ ∧ Y₀ = theta (M ⊓ H) ∧
      Y₀ = theta (M ⊓ centralizer (V : Set G)) ∧
      twoResidualAmbient Y₀ = Y₀ ∧
      ⁅H.pCoreIn 2, Y₀⁆ ≤ H.pCoreIn 2 ⊓ Y₀ ∧
      ⁅H.pCoreIn 2, Y₀⁆ ≤ Y₀.pCoreIn 2 := by
  dsimp only
  let := h.extraspecial
  have hr := (lemma_15_3_49_1 M Mc H V T hM hTM hH hfactor).trans inf_le_right
  obtain ⟨hne, heq⟩ := extraspecial_residual_generation M H Y V hYM h.theta_eq
    h.quotient_exponent h.centralizer_eq hCH hr
  have hQT : H.pCoreIn 2 ≤ (T : Subgroup G) := by
    rintro x ⟨x, hx, rfl⟩
    exact pCore_isPGroup.le_sylow_of_normal (T.subtype hTH) hx
  have hc := commutator_theta_intersection_core_le M H (hQT.trans hTM)
  rw [← heq] at hc
  have hθ := residual_eq_theta_of_subgroup_exponent_three
    (Y ⊓ centralizer (V : Set G)) Y inf_le_left h.quotient_exponent
  refine ⟨hne, heq, ?_, ?_, hc⟩
  · rw [hθ]
    exact (theta_intersection_of_residual_bound M (centralizer (V : Set G)) Y V
      hYM h.theta_eq inf_le_right ((map_subtype_le _).trans inf_le_right)).symm
  · have hRY : twoResidualAmbient (Y ⊓ centralizer (V : Set G)) ≤ Y :=
      (map_subtype_le _).trans inf_le_left
    rw [residual_eq_theta_of_subgroup_exponent_three _ Y hRY h.quotient_exponent,
      hθ, theta_idempotent]

end CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.ExtraspecialLocal

end
