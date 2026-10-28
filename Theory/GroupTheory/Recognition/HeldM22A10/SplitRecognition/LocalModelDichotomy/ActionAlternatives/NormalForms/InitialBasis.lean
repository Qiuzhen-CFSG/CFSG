module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.LocalModelDichotomy.ActionAlternatives.NormalForms.AdaptedBasis
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.LocalModelDichotomy.BinaryReduction
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring

/-!
# Janko's initial fixed and moved planes

For the actual binary complement action, the distinguished central involution
supplies a nonidentity globally fixed vector. Orbit counting shows that the
cubic fixes a plane. Its norm `v ↦ v * C v * C (C v)` is the projection onto
this plane. In the kernel of the norm, a nonidentity reflection-fixed vector
and its cubic translate give the second plane. Applying the norm proves that
the four chosen vectors are independent, hence form a genuine basis.

The reflection fixes the first vector and has one binary parameter on the
fixed plane. Its action on the moved plane follows from inversion of the
cubic. Here `C = ρ jankoC⁻¹`, respecting the source's right conjugation.
No matrix catalogue or coordinate witness is assumed.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 1, printed p.2,
DOI 10.1016/0021-8693(68)90002-1.
-/

namespace Theory.GroupTheory.HeldM22A10.LocalModelDichotomy
open Subgroup

private theorem square (v : BinaryFour) : v * v = 1 := by
  ext i
  exact (show ∀ x : ZMod 2, x + x = 0 by decide) (v.toAdd i)

private theorem mul_eq_one (v w : BinaryFour) : v * w = 1 ↔ v = w := by
  constructor
  · intro h
    have := congrArg (fun x => x * w) h
    simpa only [mul_assoc, square, mul_one, one_mul] using this
  · rintro rfl; exact square _

private theorem fixed_card (C : MulAut BinaryFour) (hc : C ^ 3 = 1) (hne : C ≠ 1)
    (z : BinaryFour) (hz : z ≠ 1) (hcz : C z = z) :
    Nat.card (FixedPoints.subgroup (zpowers C) BinaryFour) = 4 := by
  let F := FixedPoints.subgroup (zpowers C) BinaryFour
  have hD : Nat.card (zpowers C) = 3 := by
    rw [Nat.card_zpowers]; exact orderOf_eq_prime hc hne
  have hmod := (IsPGroup.of_card (p := 3) (G := zpowers C) (n := 1)
    (by simpa using hD)).card_modEq_card_fixedPoints BinaryFour
  change Nat.card BinaryFour % 3 = Nat.card F % 3 at hmod
  have hV : Nat.card BinaryFour = 16 := by rw [Nat.card_eq_fintype_card]; decide
  rw [hV] at hmod
  have hdiv : Nat.card F ∣ 16 := hV ▸ F.card_subgroup_dvd_card
  have hproper : Nat.card F ≠ 16 := by
    intro hh
    have htop : F = ⊤ := F.eq_top_of_card_eq (hh.trans hV.symm)
    apply hne
    apply MulEquiv.ext
    intro x
    have hx : x ∈ F := htop ▸ mem_top x
    exact hx ⟨C, mem_zpowers C⟩
  have hnotone : Nat.card F ≠ 1 := by
    intro hh
    have hbot : F = ⊥ := card_eq_one.mp hh
    have hzF : z ∈ F := fun q => smul_eq_self_of_mem_zpowers q.property hcz
    exact hz (mem_bot.mp (hbot ▸ hzF))
  have hmem := Nat.mem_divisors.mpr ⟨hdiv, by decide⟩
  have hdivs : (16 : ℕ).divisors = {1, 2, 4, 8, 16} := by decide
  rw [hdivs] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  change Nat.card F = 4
  omega

private theorem four_plane (F : Subgroup BinaryFour) (hF : Nat.card F = 4)
    (z : BinaryFour) (hzF : z ∈ F) (hz : z ≠ 1) :
    ∃ x ∈ F, x ≠ 1 ∧ x ≠ z ∧ ∀ y ∈ F, y = 1 ∨ y = z ∨ y = x ∨ y = z * x := by
  classical
  let : Fintype F := Fintype.ofFinite F
  let z' : F := ⟨z, hzF⟩
  have hz' : z' ≠ 1 := fun h => hz (congrArg Subtype.val h)
  have hcard : Fintype.card F = 4 := by rwa [← Nat.card_eq_fintype_card]
  obtain ⟨x, hx1, hxz⟩ : ∃ x : F, x ≠ 1 ∧ x ≠ z' := by
    by_contra! h
    have hsub : (Finset.univ : Finset F) ⊆ {1,z'} := by
      intro x _
      simp only [Finset.mem_insert, Finset.mem_singleton]
      exact or_iff_not_imp_left.mpr (h x)
    have := Finset.card_le_card hsub
    have hle := Finset.card_insert_le (1 : F) {z'}
    simp only [Finset.card_univ, hcard, Finset.card_singleton] at *
    omega
  have hzx1 : z' * x ≠ 1 := by
    intro h
    exact hxz (Subtype.ext ((mul_eq_one z x).mp (congrArg Subtype.val h)).symm)
  have hzxz : z' * x ≠ z' := by simpa using hx1
  have hzxx : z' * x ≠ x := by simpa using hz'
  have hset : ({1,z',x,z'*x} : Finset F) = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    simp [hcard, Ne.symm hx1, Ne.symm hxz,
      Ne.symm hz', Ne.symm hzx1, Ne.symm hzxz, Ne.symm hzxx]
  refine ⟨x, x.property, fun h => hx1 (Subtype.ext h),
    fun h => hxz (Subtype.ext h), ?_⟩
  intro y hy
  have h : (⟨y,hy⟩ : F) ∈ ({1,z',x,z'*x} : Finset F) := hset ▸ Finset.mem_univ _
  simp only [Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with h | h | h | h
  · exact Or.inl (congrArg Subtype.val h)
  · exact Or.inr (Or.inl (congrArg Subtype.val h))
  · exact Or.inr (Or.inr (Or.inl (congrArg Subtype.val h)))
  · exact Or.inr (Or.inr (Or.inr (congrArg Subtype.val h)))

private def cubicNorm (C : MulAut BinaryFour) : BinaryFour →* BinaryFour :=
  (MonoidHom.id BinaryFour * C.toMonoidHom) * (C * C).toMonoidHom

private theorem norm_apply (C : MulAut BinaryFour) (v : BinaryFour) :
    cubicNorm C v = v * C v * C (C v) := rfl

private theorem norm_c (C : MulAut BinaryFour) (hc : ∀ v, C (C (C v)) = v) (v : BinaryFour) :
    cubicNorm C (C v) = cubicNorm C v := by
  simp only [norm_apply, hc]; ac_rfl

private theorem norm_fixed (C : MulAut BinaryFour) {v : BinaryFour} (h : C v = v) :
    cubicNorm C v = v := by simp only [norm_apply, h, square, one_mul]

private theorem norm_d (C T : MulAut BinaryFour) (hc : ∀ v, C (C (C v)) = v)
    (hct : ∀ v, C (T v) = T (C (C v))) (v : BinaryFour) :
    cubicNorm C (T v) = T (cubicNorm C v) := by
  simp only [norm_apply, hct, hc, map_mul]
  ac_rfl

private theorem moved_fixed (C T : MulAut BinaryFour) (hc : ∀ v, C (C (C v)) = v)
    (ht : ∀ v, T (T v) = v) (hct : ∀ v, C (T v) = T (C (C v)))
    (hne : C ≠ 1) : ∃ y : BinaryFour, y ≠ 1 ∧ cubicNorm C y = 1 ∧ T y = y := by
  obtain ⟨v, hv⟩ : ∃ v, C v ≠ v := by
    by_contra! h
    exact hne (MulEquiv.ext h)
  let w := v * C v
  have hw : w ≠ 1 := fun h => hv ((mul_eq_one _ _).mp h).symm
  have hnw : cubicNorm C w = 1 := by
    change cubicNorm C (v * C v) = 1
    rw [map_mul, norm_c C hc, square]
  by_cases htw : T w = w
  · exact ⟨w, hw, hnw, htw⟩
  · refine ⟨w * T w, fun h => htw ((mul_eq_one _ _).mp h).symm, ?_, ?_⟩
    · rw [map_mul, norm_d C T hc hct, hnw, map_one, one_mul]
    · rw [map_mul, ht, mul_comm]

private def columnHom (w x y z : BinaryFour) : BinaryFour →* BinaryFour where
  toFun v := Multiplicative.ofAdd (fun i =>
    (v.toAdd 0) * w.toAdd i + (v.toAdd 1) * x.toAdd i +
      (v.toAdd 2) * y.toAdd i + (v.toAdd 3) * z.toAdd i)
  map_one' := by ext i; simp
  map_mul' v v' := by
    ext i
    change ((v.toAdd 0 + v'.toAdd 0) * w.toAdd i +
      (v.toAdd 1 + v'.toAdd 1) * x.toAdd i +
      (v.toAdd 2 + v'.toAdd 2) * y.toAdd i +
      (v.toAdd 3 + v'.toAdd 3) * z.toAdd i) =
      (v.toAdd 0 * w.toAdd i + v.toAdd 1 * x.toAdd i +
        v.toAdd 2 * y.toAdd i + v.toAdd 3 * z.toAdd i) +
      (v'.toAdd 0 * w.toAdd i + v'.toAdd 1 * x.toAdd i +
        v'.toAdd 2 * y.toAdd i + v'.toAdd 3 * z.toAdd i)
    ring

private theorem column_e (w x y z : BinaryFour) :
    columnHom w x y z (jankoUnit 0) = w ∧ columnHom w x y z (jankoUnit 1) = x ∧
    columnHom w x y z (jankoUnit 2) = y ∧ columnHom w x y z (jankoUnit 3) = z := by
  simp [columnHom, jankoUnit]

private theorem word : ∀ v : BinaryFour, v =
    (jankoUnit 0) ^ (v.toAdd 0).val * (jankoUnit 1) ^ (v.toAdd 1).val *
    (jankoUnit 2) ^ (v.toAdd 2).val * (jankoUnit 3) ^ (v.toAdd 3).val := by decide +kernel

private theorem column_word (w x y z v : BinaryFour) :
    columnHom w x y z v = w ^ (v.toAdd 0).val * x ^ (v.toAdd 1).val *
      y ^ (v.toAdd 2).val * z ^ (v.toAdd 3).val := by
  conv_lhs => rw [word v]
  obtain ⟨h0,h1,h2,h3⟩ := column_e w x y z
  simp only [map_mul, map_pow, h0, h1, h2, h3]

private theorem ext_basis (f g : BinaryFour →* BinaryFour)
    (h : ∀ i, f (jankoUnit i) = g (jankoUnit i)) : f = g := by
  apply MonoidHom.ext
  intro v
  conv_lhs => rw [word v]
  conv_rhs => rw [word v]
  simp only [map_mul, map_pow, h]

private theorem two_independent (x y : BinaryFour) (hx : x ≠ 1) (hy : y ≠ 1)
    (hxy : y ≠ x) (a b : ZMod 2) (h : x ^ a.val * y ^ b.val = 1) : a = 0 ∧ b = 0 := by
  fin_cases a <;> fin_cases b <;> simp_all [ZMod.val, mul_eq_one, eq_comm]
  rfl

private theorem column_injective (C : MulAut BinaryFour) (hc : ∀ v, C (C (C v)) = v)
    (z x y : BinaryFour) (hz : z ≠ 1) (hx : x ≠ 1) (hxz : x ≠ z)
    (hcz : C z = z) (hcx : C x = x) (hy : y ≠ 1) (hny : cubicNorm C y = 1) :
    Function.Injective (columnHom z x y (C y)) := by
  have hcy : C y ≠ 1 := fun h => hy (C.injective (h.trans (map_one C).symm))
  have hcyy : C y ≠ y := by
    intro h
    exact hy ((norm_fixed C h).symm.trans hny)
  rw [← MonoidHom.ker_eq_bot_iff]
  apply eq_bot_iff.mpr
  intro v hv
  change columnHom z x y (C y) v = 1 at hv
  have hn := congrArg (cubicNorm C) hv
  rw [column_word] at hv
  simp only [column_word, map_mul, map_pow, norm_fixed C hcz, norm_fixed C hcx,
    norm_c C hc, hny, one_pow, mul_one, map_one] at hn
  obtain ⟨h0,h1⟩ := two_independent z x hz hx hxz _ _ hn
  simp only [h0, h1, ZMod.val_zero, pow_zero, one_mul] at hv
  obtain ⟨h2,h3⟩ := two_independent y (C y) hy hcy hcyy _ _ hv
  apply mem_bot.mpr
  ext i
  fin_cases i <;> assumption

private def sourceCHom : BinaryFour →* BinaryFour where
  toFun := jankoSourceC
  map_one' := by decide +kernel
  map_mul' := by decide +kernel

private def sourceDHom (a : ZMod 2) : BinaryFour →* BinaryFour where
  toFun := jankoParameterD a
  map_one' := by revert a; decide +kernel
  map_mul' := by revert a; decide +kernel

private theorem sourceC_e : sourceCHom (jankoUnit 0) = jankoUnit 0 ∧
    sourceCHom (jankoUnit 1) = jankoUnit 1 ∧
    sourceCHom (jankoUnit 2) = jankoUnit 3 ∧
    sourceCHom (jankoUnit 3) = jankoUnit 2 * jankoUnit 3 := by decide +kernel

private theorem sourceD_e (a : ZMod 2) : sourceDHom a (jankoUnit 0) = jankoUnit 0 ∧
    sourceDHom a (jankoUnit 1) = (jankoUnit 0) ^ a.val * jankoUnit 1 ∧
    sourceDHom a (jankoUnit 2) = jankoUnit 2 ∧
    sourceDHom a (jankoUnit 3) = jankoUnit 2 * jankoUnit 3 := by revert a; decide +kernel

private theorem adaptedBasis_of_fixed (ρ : SymmetricFour →* MulAut BinaryFour)
    (hρ : Function.Injective ρ) (z : BinaryFour) (hz : z ≠ 1)
    (hfix : ∀ s, ρ s z = z) : Nonempty (JankoAdaptedBasis ρ) := by
  classical
  let C := ρ jankoC⁻¹
  let T := ρ jankoD
  have hc3 : C ^ 3 = 1 := by
    change (ρ jankoC⁻¹) ^ 3 = 1
    rw [← map_pow, show (jankoC⁻¹ : SymmetricFour) ^ 3 = 1 by decide +kernel, map_one]
  have hc (v) : C (C (C v)) = v := by
    have h := congrArg (fun f : MulAut BinaryFour => f v) hc3
    simpa only [pow_succ, pow_zero, one_mul, MulAut.mul_apply, MulAut.one_apply] using h
  have ht (v) : T (T v) = v := by
    change ρ jankoD (ρ jankoD v) = v
    rw [← MulAut.mul_apply, ← map_mul,
      show jankoD * jankoD = 1 by decide +kernel, map_one, MulAut.one_apply]
  have hct (v) : C (T v) = T (C (C v)) := by
    change ρ jankoC⁻¹ (ρ jankoD v) = ρ jankoD (ρ jankoC⁻¹ (ρ jankoC⁻¹ v))
    simp only [← MulAut.mul_apply, ← map_mul]
    congr 2
    decide +kernel
  have hne : C ≠ 1 := by
    intro h
    have he : jankoC⁻¹ = 1 := hρ (h.trans (map_one ρ).symm)
    exact (by decide +kernel : jankoC⁻¹ ≠ 1) he
  let F := FixedPoints.subgroup (zpowers C) BinaryFour
  have hmem (v) : v ∈ F ↔ C v = v := by
    constructor
    · intro h; exact h ⟨C, mem_zpowers C⟩
    · intro h q; exact smul_eq_self_of_mem_zpowers q.property h
  have hcz : C z = z := hfix _
  have htz : T z = z := hfix _
  have hF : Nat.card F = 4 := fixed_card C hc3 hne z hz hcz
  obtain ⟨x, hxF, hx1, hxz, hexhaust⟩ := four_plane F hF z ((hmem z).mpr hcz) hz
  have hcx : C x = x := (hmem x).mp hxF
  have htxF : T x ∈ F := (hmem _).mpr (by rw [hct, hcx, hcx])
  obtain ⟨a, htx⟩ : ∃ a : ZMod 2, T x = z ^ a.val * x := by
    rcases hexhaust (T x) htxF with h | h | h | h
    · exact False.elim (hx1 (T.injective (h.trans (map_one T).symm)))
    · exact False.elim (hxz (T.injective (h.trans htz.symm)))
    · exact ⟨0, by simpa using h⟩
    · exact ⟨1, by simpa only [show (1 : ZMod 2).val = 1 by decide, pow_one] using h⟩
  obtain ⟨y, hy1, hny, hty⟩ := moved_fixed C T hc ht hct hne
  have hccy : C (C y) = y * C y := ((mul_eq_one _ _).mp hny).symm
  have htcy : T (C y) = y * C y := by
    have h := congrArg T (hct y)
    rw [hty, ht, hccy] at h
    exact h
  let f := columnHom z x y (C y)
  have hinj : Function.Injective f := column_injective C hc z x y hz hx1 hxz hcz hcx hy1 hny
  let e : BinaryFour ≃* BinaryFour := MulEquiv.ofBijective f
    ⟨hinj, Finite.injective_iff_surjective.mp hinj⟩
  obtain ⟨e0,e1,e2,e3⟩ := column_e z x y (C y)
  obtain ⟨c0,c1,c2,c3⟩ := sourceC_e
  obtain ⟨d0,d1,d2,d3⟩ := sourceD_e a
  have heC : C.toMonoidHom.comp f = f.comp sourceCHom := by
    apply ext_basis
    intro i
    fin_cases i
    · change C (columnHom z x y (C y) (jankoUnit 0)) =
        columnHom z x y (C y) (sourceCHom (jankoUnit 0))
      rw [c0, e0, hcz]
    · change C (columnHom z x y (C y) (jankoUnit 1)) =
        columnHom z x y (C y) (sourceCHom (jankoUnit 1))
      rw [c1, e1, hcx]
    · change C (columnHom z x y (C y) (jankoUnit 2)) =
        columnHom z x y (C y) (sourceCHom (jankoUnit 2))
      rw [c2, e2, e3]
    · change C (columnHom z x y (C y) (jankoUnit 3)) =
        columnHom z x y (C y) (sourceCHom (jankoUnit 3))
      rw [c3, map_mul, e2, e3, hccy]
  have heT : T.toMonoidHom.comp f = f.comp (sourceDHom a) := by
    apply ext_basis
    intro i
    fin_cases i
    · change T (columnHom z x y (C y) (jankoUnit 0)) =
        columnHom z x y (C y) (sourceDHom a (jankoUnit 0))
      rw [d0, e0, htz]
    · change T (columnHom z x y (C y) (jankoUnit 1)) =
        columnHom z x y (C y) (sourceDHom a (jankoUnit 1))
      rw [d1, map_mul, map_pow, e0, e1, htx]
    · change T (columnHom z x y (C y) (jankoUnit 2)) =
        columnHom z x y (C y) (sourceDHom a (jankoUnit 2))
      rw [d2, e2, hty]
    · change T (columnHom z x y (C y) (jankoUnit 3)) =
        columnHom z x y (C y) (sourceDHom a (jankoUnit 3))
      rw [d3, map_mul, e2, e3, htcy]
  refine ⟨{ basis := e, alpha := a, action_c := ?_, action_d := ?_, fixed_a := ?_ }⟩
  · intro v; exact congrArg (fun h : BinaryFour →* BinaryFour => h v) heC
  · intro v; exact congrArg (fun h : BinaryFour →* BinaryFour => h v) heT
  · change ρ jankoA (columnHom z x y (C y) (jankoUnit 0)) =
      columnHom z x y (C y) (jankoUnit 0)
    rw [e0, hfix]

/-- Janko's initial fixed/moved-plane basis for the actual complement action.
The distinguished central involution supplies the first, globally fixed vector. -/
public theorem binaryAction_adaptedBasis
    {G : Type*} [Group G] [Finite G] (D : LocalData G)
    (K : Subgroup D.centralizer) (hK : D.kernel.IsComplement' K) :
    Nonempty (JankoAdaptedBasis (D.binaryAction K hK)) := by
  let zK : D.kernel := ⟨D.centralInvolution, D.centralInvolution_mem_kernel⟩
  let z := D.kernelBinaryEquiv zK
  have hz : z ≠ 1 := by
    intro h
    have he : zK = 1 := D.kernelBinaryEquiv.injective (h.trans (map_one _).symm)
    exact D.z_ne_one (congrArg (fun x : D.kernel => ((x : D.centralizer) : G)) he)
  apply adaptedBasis_of_fixed (D.binaryAction K hK) (D.binaryAction_injective K hK) z hz
  intro s
  change D.binaryAction K hK s (D.kernelBinaryEquiv zK) = D.kernelBinaryEquiv zK
  rw [D.binaryAction_apply_kernel]
  apply congrArg D.kernelBinaryEquiv
  apply Subtype.ext
  rw [D.complementAction_apply]
  change _ * D.centralInvolution * _ = D.centralInvolution
  rw [(Subgroup.mem_center_iff.mp D.centralInvolution_mem_center) _, mul_assoc,
    mul_inv_cancel, mul_one]

end Theory.GroupTheory.HeldM22A10.LocalModelDichotomy
