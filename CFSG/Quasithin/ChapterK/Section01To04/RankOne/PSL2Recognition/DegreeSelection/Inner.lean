module

public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.PSL2Recognition.Preparation
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryRankOne
public import Theory.Representation.SL2.SylowFixedDimension
public import Theory.Representation.BinaryOffender.NormalizerTwoWeight

/-!
# The inner SL₂ actor in the Chapter K degree selection

A subgroup of a binary SL₂ Sylow satisfying the ratio-two inequality forces
that inequality for the entire Sylow. Maximize |A|² |C_V(A)| inside the Sylow:
supermodularity makes the largest maximizer invariant under the normalizer,
and the diagonal torus is transitive on the nonidentity root elements.
The known Sylow fixed-space dimension is the actual Schur degree. The
highest-weight orbit parameters then force binary dimension twice the field
degree. Cubicity is not needed for this inner-actor argument. The specified
layer marking transports the theorem to Chapter K's actual ambient action.
At odd field degree every two-subgroup lies in the layer, so the original
cubic-ratio hypothesis gives the exact dimension without a further premise.

Source: Guralnick–Malle, Classification of 2F-modules II, Proposition 4.1(1),
manuscript p.21, and Lemmas 2.1–2.2; Aschbacher–Smith, K.3.1, printed p.453.
-/

public section
open scoped MatrixGroups MonoidAlgebra
open Representation Representation.BinaryOffender Subgroup Matrix.SpecialLinearGroup
namespace CFSG.Quasithin.ChapterK.RankOne.DegreeSelection

section RootGroup
variable {K : Type*} [Field K] [Finite K] [CharP K 2]

omit [Finite K] [CharP K 2] in
private theorem diagonal_conj_upper (c : K) (hc : c ≠ 0) (t : K) :
    diag2 c hc * transvection (i := (0 : Fin 2)) (j := 1) zero_ne_one t *
        (diag2 c hc)⁻¹ = transvection zero_ne_one (c ^ 2 * t) := by
  rw [diag2_inv]
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diag2_coe', transvection_coe, Matrix.mul_apply, Fin.sum_univ_two,
      mul_inv_cancel₀ hc, inv_mul_cancel₀ hc, pow_two, mul_assoc, mul_comm, mul_left_comm]

omit [Finite K] [CharP K 2] in
private theorem diagonal_mem_normalizer (c : K) (hc : c ≠ 0) :
    diag2 c hc ∈ Subgroup.normalizer (upperUnipotent K : Set SL(2,K)) := by
  apply Subgroup.mem_normalizer_iff.mpr
  intro x
  constructor
  · intro hx
    obtain ⟨t, rfl⟩ := (mem_upperUnipotent K x).mp hx
    exact (mem_upperUnipotent K _).mpr ⟨c ^ 2 * t, (diagonal_conj_upper c hc t).symm⟩
  · intro hx
    obtain ⟨t, ht⟩ := (mem_upperUnipotent K _).mp hx
    have he : x = (diag2 c hc)⁻¹ * transvection zero_ne_one t * diag2 c hc := by
      rw [ht]
      group
    rw [he, diag2_inv]
    have hi := diagonal_conj_upper c⁻¹ (inv_ne_zero hc) t
    simp only [diag2_inv, inv_inv] at hi
    rw [hi]
    exact (mem_upperUnipotent K _).mpr ⟨_, rfl⟩

private theorem upper_normalizer_irreducible (M : Subgroup SL(2,K))
    (hMU : M ≤ upperUnipotent K) (hM : M ≠ ⊥)
    (hn : ∀ g ∈ Subgroup.normalizer (upperUnipotent K : Set SL(2,K)),
      M.map (MulAut.conj g).toMonoidHom ≤ M) : M = upperUnipotent K := by
  obtain ⟨x, hx, hx1⟩ := M.bot_or_exists_ne_one.resolve_left hM
  obtain ⟨a, ha⟩ := (mem_upperUnipotent K x).mp (hMU hx)
  have ha0 : a ≠ 0 := by
    intro h
    apply hx1
    rw [← ha, h, transvection_coeff_zero]
  apply le_antisymm hMU
  intro y hy
  obtain ⟨b, rfl⟩ := (mem_upperUnipotent K y).mp hy
  by_cases hb : b = 0
  · rw [hb, transvection_coeff_zero]
    exact M.one_mem
  · obtain ⟨c, hc⟩ := (frobeniusEquiv K 2).surjective (b / a)
    have hc2 : c ^ 2 = b / a := hc
    have hc0 : c ≠ 0 := by
      intro hz
      rw [hz, zero_pow (by decide)] at hc2
      exact (div_ne_zero hb ha0) hc2.symm
    have hm := hn (diag2 c hc0) (diagonal_mem_normalizer c hc0)
      (Subgroup.mem_map_of_mem (MulAut.conj (diag2 c hc0)).toMonoidHom hx)
    change diag2 c hc0 * x * (diag2 c hc0)⁻¹ ∈ M at hm
    rwa [← ha, diagonal_conj_upper, hc2, div_mul_cancel₀ _ ha0] at hm
end RootGroup

private theorem orbit_parameters_of_sylow_bound {s t a : ℕ}
    (hs : 0 < s) (ht : 0 < t) (ha : 0 < a)
    (hd : s * (2 ^ a) ^ t ≤ 2 * (s * t) + s) : a = 1 ∧ (t = 1 ∨ t = 2) := by
  have hpow (n : ℕ) (hn : 3 ≤ n) : 2 * n + 1 < 2 ^ n := by
    induction n, hn using Nat.le_induction with
    | base => norm_num
    | succ n hn ih => rw [pow_succ]; omega
  have ha1 : a = 1 := by
    by_contra h
    have ha2 : 2 ≤ a := by omega
    have hfour (n : ℕ) (hn : 0 < n) : 2 * n + 1 < 4 ^ n := by
      induction n, hn using Nat.le_induction with
      | base => norm_num
      | succ n hn ih => rw [pow_succ]; omega
    have hp := (hfour t ht).trans_le
      (Nat.pow_le_pow_left (by simpa using Nat.pow_le_pow_right (by decide : 0 < 2) ha2) t)
    have hm := Nat.mul_lt_mul_of_pos_left hp hs
    nlinarith
  refine ⟨ha1, ?_⟩
  rw [ha1, pow_one] at hd
  by_contra h
  have ht3 : 3 ≤ t := by omega
  have hm := Nat.mul_lt_mul_of_pos_left (hpow t ht3) hs
  nlinarith

variable {K V : Type*} [Field K] [Finite K] [CharP K 2]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (σ : Representation (ZMod 2) SL(2,K) V) [σ.IsIrreducible]

/-- An inner elementary ratio-two actor forces the natural/Hermitian degree,
without any assumed small-degree window or module-recognition conclusion. -/
theorem finrank_eq_twice_degree_of_inner_actor (hσ : ∃ g, σ g ≠ 1)
    {r : ℕ} (hr : 0 < r) (hc : Nat.card K = 2 ^ r)
    {A : Subgroup SL(2,K)} (hA : IsElementaryTwo A)
    (hd : fixedCodim σ A ≤ 2 * rank A) : Module.finrank (ZMod 2) V = 2 * r := by
  let : IsElementaryAbelian 2 A := hA.2
  obtain ⟨P, hAP⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq SL(2,K) P (upperUnipotentSylow K 2)
  let B := A.map (MulAut.conj g).toMonoidHom
  have hBU : B ≤ upperUnipotent K := by
    have hh := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hAP
    have he : P.toSubgroup.map (MulAut.conj g).toMonoidHom = upperUnipotent K :=
      congrArg Sylow.toSubgroup hg
    exact he ▸ hh
  have hB : IsElementaryTwo B := hA.map_conj g
  have hdB : fixedCodim σ B ≤ 2 * rank B := by
    simpa only [B, fixedCodim_map_conj, rank_map_conj] using hd
  have hcard := card_le_of_ratio_two_of_normalizer_irreducible σ (upperUnipotent K) B hBU hB hdB
    upper_normalizer_irreducible
  let s := Module.finrank (ZMod 2) (Module.End (ZMod 2)[SL(2,K)] σ.asModule)
  have hfix : Module.finrank (ZMod 2) (fixedSpace σ (upperUnipotent K)) = s :=
    Representation.SL2.finrank_sylow_invariants_eq_endField 2 σ (upperUnipotentSylow K 2)
  have hdim : Module.finrank (ZMod 2) V ≤ 2 * r + s := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V),
      Module.natCard_eq_pow_finrank (K := ZMod 2) (V := fixedSpace σ (upperUnipotent K)),
      Nat.card_zmod, card_upperUnipotent, hc, ← pow_mul, ← pow_add, hfix] at hcard
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hcard |>.trans (by omega)
  obtain ⟨hs, t, a, ht, ha, hrt, hv⟩ :=
    CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.exists_binary_orbit_parameters
      σ hσ r hr hc
  obtain ⟨rfl, ht1 | ht2⟩ := orbit_parameters_of_sylow_bound hs ht ha
    (by simpa only [hv, hrt] using hdim)
  · subst t
    simp only [pow_one, mul_one] at hv hrt
    omega
  · subst t
    norm_num at hv
    omega

end CFSG.Quasithin.ChapterK.RankOne.DegreeSelection

open scoped MatrixGroups
open Representation Representation.BinaryOffender Theory.GroupTheory Subgroup
namespace CFSG.Quasithin.ChapterK.RankOne.SourceHypotheses
universe u v
variable {G : Type u} {V : Type v} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}
  {K : Type*} [Field K] [Finite K] [CharP K 2]
  (h : SourceHypotheses ρ L) (e : L ≃* SL(2,K))

include h e

omit [Finite G] [FiniteDimensional (ZMod 2) V] [Finite K] [CharP K 2] in
private theorem matrix_action_nontrivial :
    ∃ g, ((ρ.comp L.subtype).comp e.symm.toMonoidHom) g ≠ 1 := by
  let g : SL(2,K) := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
  refine ⟨g, fun hg => ?_⟩
  have hf : Function.Injective ((ρ.comp L.subtype).comp e.symm.toMonoidHom) :=
    h.faithful.comp (L.subtype_injective.comp e.symm.injective)
  have hg1 : g = 1 := hf (hg.trans (map_one _).symm)
  have he := congrArg (fun a : SL(2,K) => a.val 0 1) hg1
  simp [g] at he

omit [Finite G] in
/-- The inner-actor branch has exactly the source degree, without cubicity
or any small-degree premise. All transport uses the specified layer marking. -/
theorem psl2_degree_eq_of_inner_actor {r : ℕ} (hr : 0 < r)
    (hc : Nat.card K = 2 ^ r) {A : Subgroup G} (hA : IsElementaryTwo A)
    (hAL : A ≤ L) (hd : fixedCodim ρ A ≤ 2 * rank A) :
    Module.finrank (ZMod 2) V = 2 * r := by
  let σ := (ρ.comp L.subtype).comp e.symm.toMonoidHom
  let : IsIrreducible σ :=
    (irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective
      (ρ.comp L.subtype)).mpr h.irreducible
  let B := (A.subgroupOf L).map e.toMonoidHom
  have he : B.map e.symm.toMonoidHom = A.subgroupOf L := by
    rw [map_map]
    simp
  let : IsElementaryAbelian 2 A := hA.2
  let : IsElementaryAbelian 2 (A.subgroupOf L) := IsElementaryAbelian.subgroupOf hAL
  have hB : IsElementaryTwo B := by
    refine ⟨?_, IsElementaryAbelian.map _⟩
    intro hz
    have hzero : A.subgroupOf L = ⊥ := by rw [← he, hz, Subgroup.map_bot]
    exact hA.1 (by rw [← map_subgroupOf_eq_of_le hAL, hzero, Subgroup.map_bot])
  have hrank : rank B = rank A := by
    rw [← rank_map_injective e.symm.toMonoidHom e.symm.injective, he,
      rank_subgroupOf hAL]
  have hfixed : fixedCodim σ B = fixedCodim ρ A := by
    calc
      fixedCodim σ B = fixedCodim (ρ.comp L.subtype) (A.subgroupOf L) := by
        unfold fixedCodim
        rw [fixedSpace_comp_map, he]
      _ = fixedCodim ρ A := fixedCodim_subgroupOf ρ hAL
  exact DegreeSelection.finrank_eq_twice_degree_of_inner_actor σ
    (h.matrix_action_nontrivial e) hr hc hB (by rwa [hfixed, hrank])

/-- At odd field degree every source actor is inner, so the exact dimension
is already determined. This includes r=3 without a triple-exclusion premise. -/
theorem psl2_degree_eq_of_odd {r : ℕ} (hr : 2 ≤ r)
    (hc : Nat.card K = 2 ^ r) (hodd : Odd r) :
    Module.finrank (ZMod 2) V = 2 * r := by
  obtain ⟨A, hA, _, hd, _⟩ := h.psl2_cubic_actor e hr hc
  let : IsElementaryAbelian 2 A := hA.2
  exact h.psl2_degree_eq_of_inner_actor e (by omega) hc hA
    (h.psl2_twoSubgroup_le_of_odd e hc hodd (IsElementaryAbelian.isPGroup 2 A)) hd

end CFSG.Quasithin.ChapterK.RankOne.SourceHypotheses
