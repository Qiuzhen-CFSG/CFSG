module

public import Theory.SpecificGroups.PSL2.BinaryAutomorphismOrder
public import Theory.SpecificGroups.PSL2.ElementaryAutomorphisms.OuterInvolutions
public import Theory.SpecificGroups.PSL2.OuterSolvable.FieldAutomorphisms
public import Theory.GroupTheory.PrimeRankElementary
public import Theory.GroupTheory.QuasithinBasic

/-!
# The sharp binary SL₂ and PSL₂ automorphism two-rank bound

An elementary abelian subgroup of the inner automorphism group lifts faithfully
into PSL₂, whose two-part has order `2^n`. Otherwise choose an outer involution
in the elementary subgroup. The kernel of its projection to the actual outer
quotient lifts into that involution's fixed group. Semilinear coverage and
involutory field descent identify this fixed group with PSL₂ over GF(2^m),
where `n = 2*m`. The cyclic outer quotient gives an image of order at most two,
so the elementary subgroup has order at most `2^(m+1) ≤ 2^n`.

The descent includes `m = 1`, with fixed group PSL₂(2); no simplicity hypothesis
is imposed on this smaller group. Finite-field isomorphisms give the result over
every field of order `2^n`, and the genuine characteristic-two central quotient
`Theory.PSL2.sl2QuotientEquiv` transports the bound between SL₂ and PSL₂.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed p.356,
the rank-one automorphism rank in G.9.3 and its two-component argument, and the
swapped-factor argument of 16.3.9 on printed p.1180. The semilinear and fixed-group
inputs are the proved APIs for GLS4, Chapter 4, Lemmas 3.1(a) and 3.4(c).
-/

namespace Theory.PSL2.BinaryAutomorphismRank
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative

private theorem semilinear_coverage {F : Type*} [Field F] [Finite F] [CharP F 2]
    (a : MulAut (Group F)) :
    ∃ (g : Group F) (σ : F ≃+* F), a = MulAut.conj g * fieldAut σ :=
  BenderSuzuki.ZD.Linear.semilinear_coverage a

private theorem conj_injective {F : Type*} [Field F] [CharP F 2] :
    Function.Injective (MulAut.conj : Group F →* MulAut (Group F)) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  exact le_antisymm (fun g hg => psl2_conj_eq_one_implies g hg) bot_le

private theorem exists_inner_lift {F D : Type*} [Field F] [CharP F 2] [_root_.Group D]
    (f : D →* MulAut (Group F)) (hf : Function.Injective f)
    (hinner : ∀ d, f d ∈ inner F) :
    ∃ j : D →* Group F, Function.Injective j ∧ ∀ d, MulAut.conj (j d) = f d := by
  let e := MonoidHom.ofInjective (conj_injective (F := F))
  let u := f.codRestrict (inner F) hinner
  refine ⟨e.symm.toMonoidHom.comp u, ?_, ?_⟩
  · exact e.symm.injective.comp (fun x y h => hf (congrArg Subtype.val h))
  · intro d
    exact MonoidHom.apply_ofInjective_symm (conj_injective (F := F)) (u d)

private theorem outer_cyclic {F : Type*} [Field F] [Finite F] [CharP F 2] :
    IsCyclic (MulAut.Outer (Group F)) := by
  let q := QuotientGroup.mk' (MulAut.innerSubgroup (Group F))
  let f := q.comp (fieldAutHom (K := F))
  let : IsCyclic (F ≃+* F) := OuterSolvable.finiteFieldAut_isCyclic
  apply isCyclic_of_surjective f
  intro x
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (MulAut.innerSubgroup (Group F)) x
  obtain ⟨g, σ, rfl⟩ := semilinear_coverage a
  refine ⟨σ, ?_⟩
  have hg : q (MulAut.conj g) = 1 := (QuotientGroup.eq_one_iff _).mpr ⟨g, rfl⟩
  change q (fieldAut σ) = q (MulAut.conj g * fieldAut σ)
  rw [map_mul, hg, one_mul]

private theorem twoGroup_card_le {F D : Type*} [Field F] [Finite F] [CharP F 2]
    [_root_.Group D] [Finite D] {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2 ^ n)
    (hD : IsPGroup 2 D) (f : D →* Group F) (hf : Function.Injective f) :
    Nat.card D ≤ 2 ^ n := by
  obtain ⟨k, hk⟩ := hD.exists_card_eq
  have hG : Nat.card (Group F) = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
    rw [← Nat.card_congr (sl2QuotientEquiv F).toEquiv,
      BenderSuzuki.External.huppert614_card_specialLinearGroup, hF]
  have hdiv : Nat.card D ∣ 2 ^ n * ((2 ^ n) ^ 2 - 1) :=
    hG ▸ card_dvd_of_injective f hf
  have hodd : Odd ((2 ^ n) ^ 2 - 1) := by
    apply Nat.Even.sub_odd (by
      have := Nat.one_le_pow (n * 2) 2 (by omega)
      simpa [pow_mul] using this)
    · rw [← pow_mul]
      exact (Nat.even_pow' (by omega)).2 even_two
    · exact odd_one
  have hcop : Nat.Coprime (Nat.card D) ((2 ^ n) ^ 2 - 1) := by
    rw [hk]
    exact (Nat.coprime_two_left.mpr hodd).pow_left k
  exact Nat.le_of_dvd (by positivity) (hcop.dvd_of_dvd_mul_right hdiv)

private theorem lift_fixed {F : Type*} [Field F] [CharP F 2]
    (a : MulAut (Group F)) (g : Group F)
    (hcomm : a * MulAut.conj g = MulAut.conj g * a) : a g = g := by
  apply conj_injective
  calc
    MulAut.conj (a g) = a * MulAut.conj g * a⁻¹ := by
      ext x
      simp [MulAut.conj_apply]
    _ = MulAut.conj g := by rw [hcomm, mul_inv_cancel_right]

private theorem binary_elementary_card_le {n : ℕ} (hn : 2 ≤ n)
    (A : Subgroup (MulAut (BinaryGroup n))) [IsElementaryAbelian 2 A] :
    Nat.card A ≤ 2 ^ n := by
  classical
  have hAp := IsElementaryAbelian.isPGroup 2 A
  have hpow : ∀ a : A, a ^ 2 = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 A)
  by_cases hi : A ≤ inner (BinaryField n)
  · obtain ⟨j, hj, _⟩ := exists_inner_lift A.subtype A.subtype_injective
      (fun a => hi a.property)
    exact twoGroup_card_le (by omega) (GaloisField.card 2 n (by omega)) hAp j hj
  · obtain ⟨a, ha, haout⟩ : ∃ a ∈ A, a ∉ inner (BinaryField n) := by
      simpa only [SetLike.le_def, not_forall, exists_prop] using hi
    have ha2 : a ^ 2 = 1 := congrArg Subtype.val (hpow ⟨a, ha⟩)
    obtain ⟨g, σ, heq⟩ := semilinear_coverage a
    have haout' : ¬ ∃ b : BinaryGroup n, a = MulAut.conj b := by
      simpa only [mem_inner_iff] using haout
    obtain ⟨m, hm, hnm, ⟨e⟩⟩ :=
      outer_fixed_model_of_semilinear hn a ha2 g σ heq haout'
    let q := QuotientGroup.mk' (MulAut.innerSubgroup (BinaryGroup n))
    let f := q.comp A.subtype
    let v : f.ker →* MulAut (BinaryGroup n) := A.subtype.comp f.ker.subtype
    have hv : Function.Injective v := A.subtype_injective.comp f.ker.subtype_injective
    have hinner : ∀ x : f.ker, v x ∈ inner (BinaryField n) := by
      intro x
      exact (QuotientGroup.eq_one_iff _).mp x.property
    obtain ⟨j, hj, hjconj⟩ := exists_inner_lift v hv hinner
    have hjfixed (x : f.ker) : j x ∈ a.fixedSubgroup := by
      rw [MulAut.mem_fixedSubgroup]
      apply lift_fixed
      rw [hjconj]
      exact congrArg Subtype.val (mul_comm (⟨a, ha⟩ : A) x.val)
    let jf : f.ker →* a.fixedSubgroup := j.codRestrict a.fixedSubgroup hjfixed
    have hjf : Function.Injective jf := fun x y h => hj (congrArg Subtype.val h)
    have hker : Nat.card f.ker ≤ 2 ^ m :=
      twoGroup_card_le hm (GaloisField.card 2 m hm.ne')
        (hAp.to_subgroup f.ker) (e.toMonoidHom.comp jf) (e.injective.comp hjf)
    let : IsCyclic (MulAut.Outer (BinaryGroup n)) := outer_cyclic
    have hrange : Nat.card f.range ≤ 2 := by
      apply Nat.le_of_dvd (by decide)
      rw [← IsCyclic.exponent_eq_card]
      apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
      intro x
      obtain ⟨b, hb⟩ := x.property
      apply Subtype.ext
      change (x : MulAut.Outer (BinaryGroup n)) ^ 2 = 1
      rw [← hb, ← map_pow, hpow, map_one]
    calc
      Nat.card A = Nat.card f.ker * Nat.card f.range := by
        rw [← Subgroup.index_ker, f.ker.card_mul_index]
      _ ≤ 2 ^ m * 2 := Nat.mul_le_mul hker hrange
      _ = 2 ^ (m + 1) := (pow_succ 2 m).symm
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) (by omega)

private def sl2RingEquiv {F K : Type*} [Field F] [Field K] (e : F ≃+* K) :
    Matrix.SpecialLinearGroup (Fin 2) F ≃* Matrix.SpecialLinearGroup (Fin 2) K where
  toFun := Matrix.SpecialLinearGroup.map e.toRingHom
  invFun := Matrix.SpecialLinearGroup.map e.symm.toRingHom
  left_inv A := by ext i j; exact e.symm_apply_apply (A i j)
  right_inv A := by ext i j; exact e.apply_symm_apply (A i j)
  map_mul' := (Matrix.SpecialLinearGroup.map e.toRingHom).map_mul

/-- The sharp upper bound for the actual projective matrix group over any binary field. -/
public theorem psl2_automorphism_two_rank_le {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) :
    primeRank 2 (MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)) ≤ n := by
  let : Fintype F := Fintype.ofFinite F
  let : Fintype (BinaryField n) := Fintype.ofFinite _
  let eF : F ≃+* BinaryField n := FiniteField.ringEquivOfCardEq (by
    rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, hF,
      GaloisField.card 2 n (by omega)])
  let eG : Group F ≃* BinaryGroup n := (sl2QuotientEquiv F).symm.trans
    ((sl2RingEquiv eF).trans (sl2QuotientEquiv (BinaryField n)))
  rw [primeRank_equiv 2 (MulAut.congr eG)]
  apply (primeRank_le_iff_elementary_card_le _).mpr
  intro A hA
  let := hA
  exact binary_elementary_card_le hn A

/-- The sharp upper bound for SL₂, transported through its genuine binary central quotient. -/
public theorem sl2_automorphism_two_rank_le {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) :
    primeRank 2 (MulAut (Matrix.SpecialLinearGroup (Fin 2) F)) ≤ n := by
  rw [primeRank_equiv 2 (MulAut.congr (sl2QuotientEquiv F))]
  exact psl2_automorphism_two_rank_le hn hF

end Theory.PSL2.BinaryAutomorphismRank
