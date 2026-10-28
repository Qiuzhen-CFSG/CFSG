module

public import Theory.SpecificGroups.SU3.UnitaryTwoPerfectCentralizer
public import Theory.SpecificGroups.SU3.UnitaryTwoResidual
public import Theory.SpecificGroups.GL2.SylowNormalizedFive
public import Theory.SpecificGroups.PSL2.PrimeNormalExtension
public import Theory.GroupTheory.GeneralizedFitting.CentralizerQuotient
public import ABG.ChapterII.Section2.UnitaryCard

/-!
# The prime-five restriction in the unitary centralizer

The quotient of the actual GU₂(p) by its norm-one scalars is PGL₂(p).
Indeed the determinant kernel supplies a normal PSL₂(p) with trivial
centralizer, and the exact unitary and scalar orders make that subgroup
proper. Its faithful prime-field automorphism group identifies the quotient.

An SL₂(5) subgroup has precisely its own center in the scalar kernel.
It therefore projects to A₅. The full Sylow normalization survives the
quotient, and the prime PGL₂ theorem forces p = 5.

Source: Aschbacher–Smith C.5.12, printed p.163, using the A.3.12(9)
unitary centralizer model, and ABG II.2 Lemma 1(vi), article p.17.
-/

public noncomputable section
open Subgroup Matrix Theory.GroupTheory
open scoped MatrixGroups
namespace ABG

private def centerQuotientEquiv {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) : G ⧸ center G ≃* H ⧸ center H :=
  QuotientGroup.congr _ _ e (by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (centerCongr e ⟨y, hy⟩).property
    · intro hx
      exact ⟨e.symm x, (centerCongr e.symm ⟨x, hx⟩).property, e.apply_symm_apply x⟩)

/-- The actual scalar quotient of prime GU₂ is PGL₂ over the prime field. -/
theorem GU2_prime_projective_quotient
    (p : ℕ) [Fact p.Prime] (ho : Odd p) (hp : 3 < p) :
    ∃ f : GU2 p 1 one_ne_zero →* ProjGenLinGroup (Fin 2) (GaloisField p 1),
      Function.Surjective f ∧ f.ker = (GU2Scalar p 1 one_ne_zero).range := by
  let J := unitaryForm 2 p 1 one_ne_zero
  let D := J.unitaryDet.ker
  let eD : D ≃* SL(2, GaloisField p 1) :=
    J.unitaryDetKernelEquiv.trans (specialUnitaryTwo_equiv_sl2 p 1 ho one_ne_zero)
  have hF : Nat.card (GaloisField p 1) = p := by
    simpa using GaloisField.card p 1 one_ne_zero
  let : Group.IsPerfect SL(2, GaloisField p 1) :=
    GorensteinWalter.sl2_isPerfect_of_card_gt_three _ (hF.symm ▸ hp)
  let : IsSimpleGroup PSL(2, GaloisField p 1) :=
    ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
  let : Nontrivial SL(2, GaloisField p 1) :=
    Function.Surjective.nontrivial
      (GorensteinWalter.sl2ProjectiveProjection_surjective (GaloisField p 1))
  let : Group.IsPerfect D :=
    Group.IsPerfect.ofSurjective (f := eD.symm.toMonoidHom) eD.symm.surjective
  let : Nontrivial D := eD.nontrivial
  have hD : ¬ IsMulCommutative D := Group.IsPerfect.not_isMulCommutative D
  let Q := CentralizerQuotient D
  let q : GU2 p 1 one_ne_zero →* Q := centralizerQuotientMap D
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  let K := centralizerQuotientComponent D
  let : K.Normal := (inferInstance : D.Normal).map q hq
  let eK : K ≃* PSL(2, GaloisField p 1) :=
    (centralizerQuotientComponentEquiv D).symm.trans (centerQuotientEquiv eD)
  have hC : centralizer (K : Set Q) = ⊥ := centralizerQuotientComponent_centralizer D
  have hQcard : Nat.card Q = p * (p ^ 2 - 1) := by
    have hc : Nat.card (centralizer (D : Set (GU2 p 1 one_ne_zero))) = p + 1 := by
      simpa using GU2_noncommutative_centralizer_card p 1 one_ne_zero D hD
    have hmul := card_eq_card_quotient_mul_card_subgroup
      (centralizer (D : Set (GU2 p 1 one_ne_zero)))
    rw [GU2_card p 1 ho one_ne_zero, hc] at hmul
    simp only [pow_one] at hmul
    exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < p + 1) hmul.symm
  have hproper : K ≠ ⊤ := by
    intro he
    have hkcard : Nat.card K = Nat.card Q := by
      rw [he, Nat.card_congr (topEquiv (G := Q)).toEquiv]
    rw [Nat.card_congr eK.toEquiv] at hkcard
    have htwice := ProjectiveSpecialLinearGroup.psl2_card_twice
      (F := GaloisField p 1) (hF.symm ▸ ho)
    rw [hF, hkcard, ← hQcard] at htwice
    have hpos := Nat.card_pos (α := Q)
    omega
  obtain ⟨eQ, _⟩ := Theory.PSL2.exists_pgl_equiv_of_proper_normal_prime_psl
    K hC hproper (GaloisField p 1) hp hF eK
  refine ⟨eQ.toMonoidHom.comp q, eQ.surjective.comp hq, ?_⟩
  have hk : (eQ.toMonoidHom.comp q).ker = centralizer (D : Set (GU2 p 1 one_ne_zero)) := by
    ext x
    change eQ (q x) = 1 ↔ _
    rw [eQ.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff x
  rw [hk, GU2_centralizer_eq_scalar p 1 one_ne_zero D hD]

/-- The full-Sylow SL₂(5) exclusion in the actual unitary two-dimensional
centralizer, with no assumed quotient model. -/
theorem GU2_prime_eq_five_of_sylow_normalizes_sl2_five
    (p : ℕ) [Fact p.Prime] (ho : Odd p)
    (T : Sylow 2 (GU2 p 1 one_ne_zero))
    (B : Subgroup (GU2 p 1 one_ne_zero))
    (hB : Nonempty (B ≃* SL(2, ZMod 5)))
    (hTB : (T : Subgroup _) ≤ normalizer (B : Set (GU2 p 1 one_ne_zero))) : p = 5 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨eB⟩ := hB
  have hBcard : Nat.card B = 120 := by
    rw [Nat.card_congr eB.toEquiv, GorensteinWalter.sl2_card_formula]
    norm_num
  have hp : 3 < p := by
    have hd := B.card_subgroup_dvd_card
    rw [hBcard, GU2_card p 1 ho one_ne_zero] at hd
    simp only [pow_one] at hd
    have hp2 := (Fact.out : p.Prime).two_le
    have hpne2 : p ≠ 2 := fun he => ho.not_two_dvd_nat (he ▸ dvd_rfl)
    by_contra hh
    have he : p = 3 := by omega
    norm_num [he] at hd
  obtain ⟨f, hf, hk⟩ := GU2_prime_projective_quotient p ho hp
  let : Group.IsPerfect SL(2, ZMod 5) :=
    GorensteinWalter.sl2_isPerfect_of_card_gt_three (ZMod 5) (by norm_num)
  let : Group.IsPerfect B :=
    Group.IsPerfect.ofSurjective (f := eB.symm.toMonoidHom) eB.symm.surjective
  let : Nontrivial B := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  have hnB : ¬ IsMulCommutative B := Group.IsPerfect.not_isMulCommutative B
  let b := f.comp B.subtype
  have hbker : b.ker = center B := by
    ext x
    change f x.val = 1 ↔ _
    rw [← MonoidHom.mem_ker, hk, ← GU2_centralizer_eq_scalar p 1 one_ne_zero B hnB]
    rw [mem_centralizer_iff, mem_center_iff]
    constructor
    · intro h y
      exact Subtype.ext (h y y.property)
    · intro h y hy
      exact congrArg Subtype.val (h ⟨y, hy⟩)
  have hbrange : b.range = B.map f := by
    rw [MonoidHom.range_comp, B.range_subtype]
  let d : B.map f ≃* B ⧸ center B :=
    ((MulEquiv.subgroupCongr hbrange.symm).trans
      (QuotientGroup.quotientKerEquivRange b).symm).trans
      (QuotientGroup.quotientMulEquivOfEq hbker)
  obtain ⟨a⟩ := ProjectiveSpecialLinearGroup.equiv_alternatingGroup_five
  apply Theory.PSL2.pgl2_prime_eq_five_of_sylow_normalizes_alternating_five
    ho (by simpa using GaloisField.card p 1 one_ne_zero)
    (T.mapSurjective hf) (B.map f) ⟨((d.trans (centerQuotientEquiv eB)).trans a)⟩
  exact (map_mono hTB).trans (B.le_normalizer_map f)

end ABG
