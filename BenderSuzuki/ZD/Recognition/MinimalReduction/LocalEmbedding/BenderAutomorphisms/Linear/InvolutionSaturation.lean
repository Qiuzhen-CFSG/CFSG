module

public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Linear.SemilinearCoverage
public import Theory.SpecificGroups.SL2.BorelSmallInvariant.Basic

/-!
# Involution-saturated two-subgroups of binary PSL₂ automorphisms

Let P be a Sylow two-subgroup of PSL₂(2ⁿ), and let B be a two-subgroup of
its actual automorphism group containing the inner image of P. If every
involution of B belongs to that image, then B equals the inner image.

In standard SL₂ coordinates, the upper root group has exponent two.
The involution hypothesis therefore forces B to preserve it. The checked
semilinear factorization and the upper triangular matrix decomposition
write each such automorphism as an inner upper-root element times an
automorphism preserving the opposite root group. No nonidentity inner
upper-root element preserves that opposite group, by a matrix-entry
calculation. Thus B's opposite-root stabilizer has no involutions and is
trivial by Cauchy's theorem. Finally, the characteristic-two quotient
isomorphism and Sylow conjugacy transport the assertion to arbitrary P.

This supplies the intrinsic linear-model step used in Aschbacher (1975),
Lemma 3.4, printed pp.94–96. The semilinear structure is GLS IV, Chapter 4,
Lemma 3.1(a), in `refs/KGroup/GLS4/Chapter4.tex`. The proof of the intrinsic
statement works over every finite field of characteristic two.
-/

open BenderSuzuki.Converse BenderSuzuki.PFAppendixIII
open scoped Pointwise
namespace BenderSuzuki.ZD.Linear.InvolutionSaturation
variable {K : Type*} [Field K] [CharP K 2]

private theorem conj_injective : Function.Injective (MulAut.conj : SL2 K →* _) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply (Subgroup.eq_bot_iff_forall _).mpr
  intro x hx
  have hc : x ∈ Subgroup.center (SL2 K) := by
    rw [Subgroup.mem_center_iff]
    intro y
    have he := congrArg (fun a : MulAut (SL2 K) => a y) hx
    change x * y * x⁻¹ = y at he
    exact ((mul_inv_eq_iff_eq_mul).mp he).symm
  simpa only [center_SL2_eq_bot, Subgroup.mem_bot] using hc

private def lowerRoot (K : Type*) [Field K] [CharP K 2] : Subgroup (SL2 K) :=
  (Unip K).map (MulAut.conj (weyl K)).toMonoidHom

private theorem mem_lowerRoot (x : SL2 K) :
    x ∈ lowerRoot K ↔ ∃ t : K, x = weyl K * uni t * weyl K := by
  constructor
  · rintro ⟨u, hu, he⟩
    obtain ⟨t, rfl⟩ := (mem_Unip_iff u).mp hu
    exact ⟨t, by simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, weyl_inv] using he.symm⟩
  · rintro ⟨t, rfl⟩
    exact ⟨uni t, (mem_Unip_iff _).mpr ⟨t, rfl⟩, by simp [MulAut.conj_apply, weyl_inv]⟩

private def lowerStabilizer (K : Type*) [Field K] [CharP K 2] : Subgroup (MulAut (SL2 K)) :=
  MulAction.stabilizer (MulAut (SL2 K)) (lowerRoot K)

private theorem mem_lowerStabilizer (a : MulAut (SL2 K)) :
    a ∈ lowerStabilizer K ↔ (lowerRoot K).map a.toMonoidHom = lowerRoot K := Iff.rfl

private theorem tor_field_mem_lowerStabilizer (d : Kˣ) (σ : K ≃+* K) :
    MulAut.conj (tor d) * sl2FieldAut σ ∈ lowerStabilizer K := by
  have calc_lower (t : K) :
      (MulAut.conj (tor d) * sl2FieldAut σ) (weyl K * uni t * weyl K) =
        weyl K * uni (((d⁻¹ : Kˣ) : K) ^ 2 * σ t) * weyl K := by
    simp only [MulAut.mul_apply, map_mul, sl2FieldAut_weyl, sl2FieldAut_uni,
      MulAut.conj_apply]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two, pow_two, mul_assoc, mul_comm]
  rw [mem_lowerStabilizer]
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨t, rfl⟩ := (mem_lowerRoot x).mp hx
    simp only [MulEquiv.coe_toMonoidHom]
    rw [calc_lower]
    exact (mem_lowerRoot _).mpr ⟨_, rfl⟩
  · intro x hx
    obtain ⟨t, rfl⟩ := (mem_lowerRoot x).mp hx
    refine ⟨weyl K * uni (σ.symm ((d : K) ^ 2 * t)) * weyl K,
      (mem_lowerRoot _).mpr ⟨_, rfl⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [calc_lower, σ.apply_symm_apply]
    congr 2
    simp [pow_two, mul_assoc]

private theorem inner_root_disjoint_lowerStabilizer :
    Disjoint ((Unip K).map MulAut.conj) (lowerStabilizer K) := by
  apply Subgroup.disjoint_def.mpr
  rintro a ⟨u, hu, rfl⟩ ha
  obtain ⟨t, rfl⟩ := (mem_Unip_iff u).mp hu
  have hm : MulAut.conj (uni t) (weyl K * uni (1 : K) * weyl K) ∈ lowerRoot K := by
    rw [← (mem_lowerStabilizer _).mp ha]
    exact Subgroup.mem_map_of_mem _ ((mem_lowerRoot _).mpr ⟨1, rfl⟩)
  obtain ⟨s, hs⟩ := (mem_lowerRoot _).mp hm
  have he := congrArg (fun x : SL2 K => x.val 0 1) hs
  have ht : t = 0 := by
    apply mul_self_eq_zero.mp
    simp [MulAut.conj_apply, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.adjugate_fin_two, CharTwo.neg_eq] at he
    simpa only [add_mul, one_mul, add_right_comm, CharTwo.add_self_eq_zero, zero_add] using he
  simp [ht, uni_zero]

omit [CharP K 2] in
private theorem unip_eq_upper : Unip K = Matrix.SpecialLinearGroup.upperUnipotent K := by
  ext g
  rw [mem_Unip_iff, Matrix.SpecialLinearGroup.mem_upperUnipotent]
  simp only [upper_transvection_eq_uni, eq_comm]

/-- Root preservation gives an upper-root times opposite-root-stabilizer factorization. -/
private theorem factor_of_preserves_root [Finite K] (a : MulAut (SL2 K))
    (hU : (Unip K).map a.toMonoidHom = Unip K) :
    ∃ (u : SL2 K) (c : MulAut (SL2 K)),
      u ∈ Unip K ∧ c ∈ lowerStabilizer K ∧ a = MulAut.conj u * c := by
  obtain ⟨g, b, hab, hbU, hbw⟩ := exists_root_weyl_normalization a
  obtain ⟨σ, rfl⟩ := eq_sl2FieldAut_of_rootParameter_mul b hbU hbw
    (rootParameter_mul b hbU hbw)
  have hg : g ∈ Borel K := by
    apply (mem_Borel_iff _).mpr
    apply (Matrix.SpecialLinearGroup.mem_rankOneBorel_iff g).mp
    apply Subgroup.mem_normalizer_iff.mpr
    intro x
    rw [← unip_eq_upper]
    have hmap : (Unip K).map (MulAut.conj g).toMonoidHom = Unip K := by
      have hf : a.toMonoidHom = (MulAut.conj g).toMonoidHom.comp
          (sl2FieldAut σ).toMonoidHom := by rw [hab]; rfl
      rw [hf, ← Subgroup.map_map, hbU] at hU
      exact hU
    constructor
    · intro hx
      have hm := Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hx
      rw [hmap] at hm
      exact hm
    · intro hx
      rw [← hmap] at hx
      obtain ⟨y, hy, he⟩ := hx
      exact (MulAut.conj g).injective he ▸ hy
  let d := Units.mk0 (g.val 0 0) (Borel_diag_ne_zero hg)
  let t := g.val 0 1 * g.val 0 0
  have hfac : g = uni t * tor d := by
    have h11 := Borel_lower_right hg
    have h10 := (mem_Borel_iff _).mp hg
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [d, t, Matrix.mul_apply, Fin.sum_univ_two, h10, h11, mul_assoc,
        mul_inv_cancel₀ (Borel_diag_ne_zero hg)]
  refine ⟨uni t, MulAut.conj (tor d) * sl2FieldAut σ,
    (mem_Unip_iff _).mpr ⟨t, rfl⟩, tor_field_mem_lowerStabilizer d σ, ?_⟩
  rw [hab, hfac, map_mul, mul_assoc]

/-- Saturation makes the inner root image invariant, hence preserves the actual root group. -/
private theorem root_preserved_of_involutions
    (B : Subgroup (MulAut (SL2 K)))
    (hUB : (Unip K).map MulAut.conj ≤ B)
    (hBI : ∀ b ∈ B, IsInvolution b → b ∈ (Unip K).map MulAut.conj)
    (a : MulAut (SL2 K)) (ha : a ∈ B) :
    (Unip K).map a.toMonoidHom = Unip K := by
  have hmem (b : MulAut (SL2 K)) (hb : b ∈ B) (u : SL2 K) (hu : u ∈ Unip K) :
      b u ∈ Unip K := by
    have hs : u ^ 2 = 1 := by
      obtain ⟨t, rfl⟩ := (mem_Unip_iff _).mp hu
      rw [pow_two, uni_mul_uni, CharTwo.add_self_eq_zero, uni_zero]
    have he : MulAut.conj (b u) = b * MulAut.conj u * b⁻¹ := by
      ext x
      simp [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv]
    have hbm : MulAut.conj (b u) ∈ B := by
      rw [he]
      exact B.mul_mem (B.mul_mem hb (hUB (Subgroup.mem_map_of_mem _ hu))) (B.inv_mem hb)
    have hinner : MulAut.conj (b u) ∈ (Unip K).map MulAut.conj := by
      by_cases h1 : MulAut.conj (b u) = 1
      · exact h1 ▸ ((Unip K).map MulAut.conj).one_mem
      · apply hBI _ hbm
        refine ⟨h1, ?_⟩
        rw [← map_pow, ← map_pow, hs, map_one, map_one]
    obtain ⟨v, hv, hvu⟩ := hinner
    exact conj_injective hvu ▸ hv
  apply le_antisymm
  · rintro _ ⟨u, hu, rfl⟩
    exact hmem a ha u hu
  · intro u hu
    exact ⟨a⁻¹ u, hmem a⁻¹ (B.inv_mem ha) u hu, a.apply_symm_apply u⟩

private theorem two_subgroup_eq_bot_of_no_involutions {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) (hH : IsPGroup 2 H)
    (hi : ∀ x ∈ H, ¬ IsInvolution x) : H = ⊥ := by
  apply (Subgroup.eq_bot_iff_forall _).mpr
  intro x hx
  by_contra hn
  have hd : 2 ∣ Nat.card H := (hH.dvd_orderOf (g := ⟨x, hx⟩)
    (fun he => hn (congrArg Subtype.val he))).trans (orderOf_dvd_natCard _)
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := H) 2 hd
  have hyG : orderOf (y : G) = 2 :=
    (orderOf_injective H.subtype H.subtype_injective y).trans hy
  exact hi y y.property ⟨(orderOf_eq_prime_iff.mp hyG).2, (orderOf_eq_prime_iff.mp hyG).1⟩

private theorem standard_saturation [Finite K] (B : Subgroup (MulAut (SL2 K)))
    (hB : IsPGroup 2 B) (hUB : (Unip K).map MulAut.conj ≤ B)
    (hBI : ∀ b ∈ B, IsInvolution b → b ∈ (Unip K).map MulAut.conj) :
    B ≤ (Unip K).map MulAut.conj := by
  have hC : B ⊓ lowerStabilizer K = ⊥ := by
    apply two_subgroup_eq_bot_of_no_involutions _ (hB.to_le inf_le_left)
    intro c hc hi
    exact hi.ne_one (Subgroup.disjoint_def.mp inner_root_disjoint_lowerStabilizer
      (hBI c hc.1 hi) hc.2)
  intro a ha
  obtain ⟨u, c, hu, hc, he⟩ := factor_of_preserves_root a
    (root_preserved_of_involutions B hUB hBI a ha)
  have hcB : c ∈ B := by
    have hh := B.mul_mem (B.inv_mem (hUB (Subgroup.mem_map_of_mem _ hu))) ha
    rw [he, inv_mul_cancel_left] at hh
    exact hh
  have hc1 : c = 1 := by
    apply Subgroup.mem_bot.mp
    rw [← hC]
    exact ⟨hcB, hc⟩
  rw [he, hc1, mul_one]
  exact Subgroup.mem_map_of_mem _ hu

/-- The quotient isomorphism followed by conjugation places the standard root group at P. -/
private theorem arbitrary_saturation [Finite K]
    (P : Sylow 2 (BenderSuzuki.MatrixGroups.PSL2MatrixGroup K))
    (B : Subgroup (MulAut (BenderSuzuki.MatrixGroups.PSL2MatrixGroup K)))
    (hB : IsPGroup 2 B)
    (hUB : (P : Subgroup _).map MulAut.conj ≤ B)
    (hBI : ∀ b ∈ B, IsInvolution b → b ∈ (P : Subgroup _).map MulAut.conj) :
    B ≤ (P : Subgroup _).map MulAut.conj := by
  let U := Matrix.SpecialLinearGroup.upperUnipotentSylow K 2
  let q := sl2QuotientEquiv K
  let P₀ := U.mapSurjective (f := q.toMonoidHom) q.surjective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq
    (BenderSuzuki.MatrixGroups.PSL2MatrixGroup K) P₀ P
  let e := q.trans (MulAut.conj g)
  have hP : (Unip K).map e.toMonoidHom = (P : Subgroup _) := by
    have hh := congrArg (fun S : Sylow 2 (BenderSuzuki.MatrixGroups.PSL2MatrixGroup K) =>
      (S : Subgroup (BenderSuzuki.MatrixGroups.PSL2MatrixGroup K))) hg
    change (P₀ : Subgroup _).map (MulAut.conj g).toMonoidHom = (P : Subgroup _) at hh
    change ((Matrix.SpecialLinearGroup.upperUnipotent K).map q.toMonoidHom).map
      (MulAut.conj g).toMonoidHom = (P : Subgroup _) at hh
    rw [← unip_eq_upper, Subgroup.map_map] at hh
    exact hh
  let E := MulAut.congr e
  let A := B.comap E.toMonoidHom
  have hA : IsPGroup 2 A := hB.comap_of_injective E.toMonoidHom E.injective
  have hUA : (Unip K).map MulAut.conj ≤ A := by
    rintro _ ⟨u, hu, rfl⟩
    change E (MulAut.conj u) ∈ B
    rw [show E (MulAut.conj u) = MulAut.conj (e u) from MulAut.congr_conj e u]
    apply hUB
    refine ⟨e u, ?_, rfl⟩
    rw [← hP]
    exact Subgroup.mem_map_of_mem e.toMonoidHom hu
  have hIA : ∀ a ∈ A, IsInvolution a → a ∈ (Unip K).map MulAut.conj := by
    intro a ha hi
    have hiE : IsInvolution (E a) := by
      refine ⟨fun h => hi.ne_one (E.injective (h.trans (map_one E).symm)), ?_⟩
      rw [← map_pow, hi.sq_eq_one, map_one]
    obtain ⟨x, hx, he⟩ := hBI (E a) ha hiE
    rw [← hP] at hx
    obtain ⟨u, hu, hux⟩ := hx
    refine ⟨u, hu, E.injective ?_⟩
    change E (MulAut.conj u) = E a
    rw [show E (MulAut.conj u) = MulAut.conj (e u) from MulAut.congr_conj e u]
    exact (congrArg MulAut.conj hux).trans he
  have hs := standard_saturation A hA hUA hIA
  intro b hb
  have hpre : E.symm b ∈ A := by
    change E (E.symm b) ∈ B
    rwa [E.apply_symm_apply]
  obtain ⟨u, hu, he⟩ := hs hpre
  refine ⟨e u, ?_, ?_⟩
  · rw [← hP]
    exact Subgroup.mem_map_of_mem e.toMonoidHom hu
  · have hh := congrArg E he
    rw [E.apply_symm_apply] at hh
    exact (MulAut.congr_conj e u).symm.trans hh

end BenderSuzuki.ZD.Linear.InvolutionSaturation

namespace BenderSuzuki.ZD.Linear
open BenderSuzuki.MatrixGroups
/-- A two-subgroup of the actual automorphism group of PSL₂(2ⁿ) containing the
inner image of a Sylow two-subgroup lies in that image if all its involutions do. -/
public theorem twoSubgroup_le_inner_sylow_of_involutions {n : ℕ} (_hn : 2 ≤ n) (P : Sylow 2 (PSL2BinaryMatrixGroup n))
    (B : Subgroup (MulAut (PSL2BinaryMatrixGroup n)))
    (hB : IsPGroup 2 B) (hUB : (P : Subgroup _).map MulAut.conj ≤ B)
    (hBI : ∀ b ∈ B, IsInvolution b → b ∈ (P : Subgroup _).map MulAut.conj) :
    B ≤ (P : Subgroup _).map MulAut.conj :=
  InvolutionSaturation.arbitrary_saturation P B hB hUB hBI
end BenderSuzuki.ZD.Linear
