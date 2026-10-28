module

public import Theory.SpecificGroups.PSL3.CubicBorel
public import Theory.SpecificGroups.PSL3.CartanActions.BorelQuotient
public import Theory.SpecificGroups.PSL3.CartanActions.NormalizerForm.BorelKernel
public import Theory.SpecificGroups.PSL3.CartanActions.ActorCoverage
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# The parameter restriction for an outer cubic linear actor

After conjugating a specified Sylow subgroup to the standard unitriangular
subgroup, a Sylow-preserving linear actor is upper triangular.  Its cube is
scalar on the projective group, so the three diagonal entries have a common
cube.  Dividing by one diagonal entry leaves cube roots of unity.  If the
field degree is divisible by three, then `9 ∣ |F| - 1`; every cube root in
`Fˣ` is itself a cube, so the determinant has a cube root and the actor is
inner.  This contradicts the supplied outer hypothesis.

Source: Aschbacher--Smith, proof of 15.3.38, printed pp.1135--1136.
-/

@[expose] public section

open scoped MatrixGroups
open Subgroup Matrix Matrix.PSL3.OuterSolvable
open Matrix.PSL3.LinearThree
open Matrix.PSL3.CartanActions
namespace Matrix.PSL3.CubicBorel

private theorem stable_congr {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (U : Subgroup G) (V : Subgroup H)
    (hUV : U.map e.toMonoidHom = V) (α : MulAut H)
    (hα : V.map α.toMonoidHom = V) :
    U.map (MulAut.congr e.symm α).toMonoidHom = U := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    have hm : α (e x) ∈ V := hα.le (Subgroup.mem_map_of_mem _
      (hUV ▸ Subgroup.mem_map_of_mem _ hx))
    rw [← hUV] at hm
    obtain ⟨y, hy, he⟩ := hm
    change e.symm (α (e x)) ∈ U
    change e y = α (e x) at he
    rw [← he, e.symm_apply_apply]
    exact hy
  · intro x hx
    have hm : e x ∈ V.map α.toMonoidHom := hα.symm ▸
      (hUV ▸ Subgroup.mem_map_of_mem _ hx)
    obtain ⟨y, hy, he⟩ := hm
    rw [← hUV] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    refine ⟨z, hz, ?_⟩
    change e.symm (α (e z)) = x
    change α (e z) = e x at he
    rw [he, e.symm_apply_apply]

private theorem scalar_of_trivial_action {F : Type*} [Field F]
    (g : GL (Fin 3) F) (hg : linearConj F g = 1) :
    ∃ a : Fˣ, GeneralLinearGroup.scalar (Fin 3) a = g := by
  have hs : linearConjSL F g = 1 :=
    Matrix.PSL3.CartanActions.ActorCoverage.centerAction_injective F
      (hg.trans (map_one _).symm)
  have hc (x : SL(3,F)) : g * SpecialLinearGroup.toGL x =
      SpecialLinearGroup.toGL x * g := by
    have he := congrArg SpecialLinearGroup.toGL (DFunLike.congr_fun hs x)
    rw [linearConjSL_toGL] at he
    exact mul_inv_eq_iff_eq_mul.mp he
  have hz : g ∈ center (GL (Fin 3) F) := by
    apply GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mpr
    apply Matrix.mem_range_scalar_of_commute_transvectionStruct
    intro t
    exact (congrArg Units.val (hc ⟨t.toMatrix, by simp⟩)).symm
  rwa [GeneralLinearGroup.center_eq_range_scalar] at hz

private theorem cube_root_of_cube_one {F : Type*} [Field F] [Finite F]
    (h9 : 9 ∣ Nat.card F - 1) (u : Fˣ) (hu : u ^ 3 = 1) :
    ∃ v : Fˣ, v ^ 3 = u := by
  let _ := Fintype.ofFinite F
  let _ := Classical.decEq Fˣ
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  have horder : orderOf g = Nat.card Fˣ :=
    orderOf_eq_card_of_forall_mem_zpowers hg
  have hprim : IsPrimitiveRoot g (Nat.card Fˣ) :=
    IsPrimitiveRoot.iff_orderOf.mpr horder
  have hmem := mem_zpowers_iff_mem_range_orderOf.mp (hg u)
  rw [Finset.mem_image] at hmem
  obtain ⟨k, hklt, hku⟩ := hmem
  have hpow : g ^ (3 * k) = 1 := by
    calc
      g ^ (3 * k) = g ^ (k * 3) := by rw [Nat.mul_comm]
      _ = (g ^ k) ^ 3 := by rw [pow_mul]
      _ = u ^ 3 := by rw [hku]
      _ = 1 := hu
  have hd : Nat.card Fˣ ∣ 3 * k :=
    (hprim.pow_eq_one_iff_dvd _).mp hpow
  have hcard : Nat.card Fˣ = Nat.card F - 1 := Nat.card_units F
  rw [hcard] at hd
  obtain ⟨m, hm⟩ := h9
  obtain ⟨t, ht⟩ := hd
  have ht' : 3 * k = 3 * (3 * (m * t)) := by
    calc
      3 * k = (Nat.card F - 1) * t := ht
      _ = (9 * m) * t := by rw [hm]
      _ = 3 * (3 * (m * t)) := by ring
  have hkdiv : k = 3 * (m * t) := Nat.mul_left_cancel (by decide) ht'
  refine ⟨g ^ (m * t), ?_⟩
  calc
    (g ^ (m * t)) ^ 3 = g ^ ((m * t) * 3) := (pow_mul g (m * t) 3).symm
    _ = g ^ (3 * (m * t)) := by rw [Nat.mul_comm]
    _ = g ^ k := by rw [hkdiv]
    _ = u := hku

private theorem upper_triangular_det_cube {F : Type*} [Field F] [Finite F]
    (g : GL (Fin 3) F)
    (hg : g.val 1 0 = 0 ∧ g.val 2 0 = 0 ∧ g.val 2 1 = 0)
    (hcube : linearConj F g ^ 3 = 1)
    (h9 : 9 ∣ Nat.card F - 1) :
    ∃ r : Fˣ, r ^ 3 = GeneralLinearGroup.det g := by
  have hdiag_ne (i : Fin 3) : g.val i i ≠ 0 := by
    have hn := (GeneralLinearGroup.det g).ne_zero
    change Matrix.det g.val ≠ 0 at hn
    rw [Matrix.det_fin_three] at hn
    simp only [hg.1, hg.2.1, hg.2.2, mul_zero, zero_mul, sub_zero, add_zero] at hn
    fin_cases i
    · exact (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hn).1).1
    · exact (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hn).1).2
    · exact (mul_ne_zero_iff.mp hn).2
  let a (i : Fin 3) : Fˣ := Units.mk0 (g.val i i) (hdiag_ne i)
  obtain ⟨s, hs⟩ := scalar_of_trivial_action (g ^ 3)
    (by rw [map_pow, hcube])
  have hacube (i : Fin 3) : a i ^ 3 = s := by
    apply Units.ext
    have hh := congrArg (fun m : GL (Fin 3) F => m.val i i) hs
    simp only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.diagonal_apply_eq] at hh
    have hdiag : (g ^ 3).val i i = g.val i i ^ 3 := by
      change (g.val ^ 3) i i = _
      fin_cases i <;>
        simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_three,
          hg.1, hg.2.1, hg.2.2]
    rw [hdiag] at hh
    simpa [a] using hh.symm
  let d : Fin 3 → Fˣ := fun i => a i * (a 2)⁻¹
  have hd (i : Fin 3) : d i ^ 3 = 1 := by
    simp only [d, mul_pow, inv_pow, hacube, mul_inv_cancel]
  have hdet : GeneralLinearGroup.det g =
      (a 0 * a 1 * a 2) := by
    apply Units.ext
    change Matrix.det g.val = _
    rw [Matrix.det_fin_three]
    simp only [hg.1, hg.2.1, hg.2.2, mul_zero, zero_mul, sub_zero, add_zero]
    simp [a]
  have hprod : (d 0 * d 1 * d 2) ^ 3 = 1 := by
    simp only [mul_pow, hd, one_mul]
  obtain ⟨v, hv⟩ := cube_root_of_cube_one h9 (d 0 * d 1 * d 2) hprod
  refine ⟨v * a 2, ?_⟩
  calc
    (v * a 2) ^ 3 = (d 0 * d 1 * d 2) * (a 2 ^ 3) := by rw [mul_pow, hv]
    _ = a 0 * a 1 * a 2 := by
      dsimp [d]
      simp [pow_succ, mul_comm, mul_left_comm, mul_assoc]
    _ = GeneralLinearGroup.det g := hdet.symm

private theorem scalar_action {F : Type*} [Field F] (a : Fˣ) :
    linearConj F (GeneralLinearGroup.scalar (Fin 3) a) = 1 := by
  ext y
  obtain ⟨x, rfl⟩ := Matrix.PSL3.projection_surjective F y
  change Matrix.PSL3.projection F
      (linearConjSL F (GeneralLinearGroup.scalar (Fin 3) a) x) =
    Matrix.PSL3.projection F x
  congr 1
  apply SpecialLinearGroup.toGL_injective
  rw [linearConjSL_toGL, GeneralLinearGroup.scalar_commute, mul_inv_cancel_right]

private theorem linearConj_congr {F : Type*} [Field F]
    (s : SL(3,F)) (g : GL (Fin 3) F) :
    MulAut.congr (MulAut.conj (Matrix.PSL3.projection F s)) (linearConj F g) =
      linearConj F (SpecialLinearGroup.toGL s * g * (SpecialLinearGroup.toGL s)⁻¹) := by
  rw [map_mul, map_mul, map_inv, linearConj_toGL]
  rfl

private theorem linearConj_inner_of_det_cube {F : Type*} [Field F]
    (g : GL (Fin 3) F) (hdet : ∃ r : Fˣ, r ^ 3 = GeneralLinearGroup.det g) :
    linearConj F g ∈ MulAut.innerSubgroup PSL(3,F) := by
  obtain ⟨r, hr⟩ := hdet
  let x : GL (Fin 3) F := GeneralLinearGroup.scalar (Fin 3) r⁻¹ * g
  have hx : GeneralLinearGroup.det x = 1 := by
    simp only [x, map_mul, GeneralLinearGroup.det_scalar, Fintype.card_fin,
      inv_pow, hr, inv_mul_cancel]
  let y : SL(3,F) := ⟨x.val, congrArg Units.val hx⟩
  refine ⟨Matrix.PSL3.projection F y, ?_⟩
  calc
    MulAut.conj (Matrix.PSL3.projection F y) =
        linearConj F (SpecialLinearGroup.toGL y) :=
      (linearConj_toGL F y).symm
    _ = linearConj F x := by
      congr 1
      exact Units.ext rfl
    _ = linearConj F (GeneralLinearGroup.scalar (Fin 3) r⁻¹) * linearConj F g := by
      change linearConj F (GeneralLinearGroup.scalar (Fin 3) r⁻¹ * g) = _
      rw [map_mul]
    _ = linearConj F g := by rw [scalar_action, one_mul]

variable {F : Type*} [Field F]

theorem three_not_dvd_parameter [Finite F] {n : ℕ} (hn : 0 < n) (he : Even n)
    (hF : Nat.card F = 2 ^ n) (P : Sylow 2 PSL(3,F))
    (a : GL (Fin 3) F)
    (hout : linearConj F a ∉ MulAut.innerSubgroup PSL(3,F))
    (ha3 : linearConj F a ^ 3 = 1)
    (haP : (P : Subgroup PSL(3,F)).map (linearConj F a).toMonoidHom = P) :
    ¬ 3 ∣ n := by
  intro h3n
  let _ := Fintype.ofFinite F
  have hc : ringChar F = 2 := FiniteField.even_card_iff_char_two.mpr (by
    rw [← Nat.card_eq_fintype_card, hF]
    exact Nat.mod_eq_zero_of_dvd (dvd_pow_self 2 (Nat.ne_of_gt hn)))
  let _ : CharP F 2 := ringChar.of_eq hc
  obtain ⟨s, hsU, _⟩ :=
    Matrix.PSL3.CartanActions.BorelQuotient.sylow_normalizer_conjugate F hn hF P
  obtain ⟨x, rfl⟩ := Matrix.PSL3.projection_surjective F s
  let c := MulAut.conj (Matrix.PSL3.projection F x)
  let m := SpecialLinearGroup.toGL x⁻¹ * a * (SpecialLinearGroup.toGL x⁻¹)⁻¹
  have hc_inv : c.symm = MulAut.conj (Matrix.PSL3.projection F x⁻¹) := by
    ext z
    simp [c, MulAut.inv_def]
  have hU : (unipotent F).map (linearConj F m).toMonoidHom = unipotent F := by
    have hm : linearConj F m = MulAut.congr c.symm (linearConj F a) := by
      rw [hc_inv]
      simpa [m] using (linearConj_congr (F := F) x⁻¹ a).symm
    rw [hm]
    exact stable_congr c _ _ hsU _ haP
  have htri := NormalizerForm.linearConj_upperTriangular F m hU
  have hdet9 : 9 ∣ Nat.card F - 1 := by
    rw [hF]
    obtain ⟨k, hk⟩ := h3n
    obtain ⟨j, hj⟩ := he
    have h2 : 2 ∣ k := by
      have h2' : 2 ∣ 3 * k := by
        refine ⟨j, ?_⟩
        omega
      exact Nat.Coprime.dvd_of_dvd_mul_left (by decide : Nat.Coprime 2 3) h2'
    obtain ⟨t, ht⟩ := h2
    subst n
    subst k
    have hpow : 3 * (2 * t) = 6 * t := by ring
    rw [hpow]
    have hb : 2 ^ 6 ≡ 1 [MOD 9] := by norm_num [Nat.ModEq]
    have hp := hb.pow t
    have hm : 1 ≡ 2 ^ (6 * t) [MOD 9] := by
      rw [← pow_mul] at hp
      simpa using hp.symm
    have hpos : 0 < 2 ^ (6 * t) := pow_pos (by decide) _
    exact (Nat.modEq_iff_dvd' (by omega)).mp hm
  have hinner_m := linearConj_inner_of_det_cube m
    (upper_triangular_det_cube m htri (by
      rw [show linearConj F m = MulAut.congr c.symm (linearConj F a) by
        rw [hc_inv]
        simpa [m] using (linearConj_congr (F := F) x⁻¹ a).symm]
      rw [← map_pow, ha3, map_one]) hdet9)
  apply hout
  have heq : linearConj F m = MulAut.congr c.symm (linearConj F a) := by
    rw [hc_inv]
    simpa [m] using (linearConj_congr (F := F) x⁻¹ a).symm
  obtain ⟨z, hz⟩ := hinner_m
  rw [heq] at hz
  refine ⟨c z, ?_⟩
  calc
    MulAut.conj (c z) = MulAut.congr c (MulAut.conj z) := by
      ext y
      simp [MulAut.congr_apply]
    _ = MulAut.congr c (MulAut.congr c.symm (linearConj F a)) := by rw [hz]
    _ = linearConj F a := by
      ext y
      simp [MulAut.congr_apply]

end Matrix.PSL3.CubicBorel
