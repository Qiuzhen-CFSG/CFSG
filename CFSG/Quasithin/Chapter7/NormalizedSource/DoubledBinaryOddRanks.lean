module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryOddWreath
public import Theory.SpecificGroups.G2.MultiplierOrdinary.OddTwoPrimary.OrthogonalMap
public import Theory.SpecificGroups.ClassicalUnitary.OddFourProjectiveRank
public import Theory.GroupTheory.PrimeRankCoprimeIndex
import all Theory.SpecificGroups.OddFourProjectiveRank

/-!
# The placed odd-model exclusions for the original binary-three residual

The whole doubled orbit has rank six inside the original component central
quotient. Every odd model in Theorem B has rank at most five: the existing
ternary bounds handle degree two and three, and the faithful determinant-one
four-space bounds retain the entire projective kernel in the other classical rows.

For odd-prime G₂, the actual orthogonal subgroup of odd index preserves
the second quaternion coordinate. Its action on this four-space is faithful:
products of vectors in the second coordinate fill the first coordinate, so
fixing the second coordinate pointwise fixes the whole octonion algebra.
The elementary sign-character bound therefore gives rank at most four.
The literal diagonal-kernel count also covers p = 3, whose index is 7371.

The Chapter12 application excludes the complete odd catalogue from the
placed branch with the same component, orbit and residual section. This
does not exclude the three remaining outer configurations.
Source: Aschbacher--Smith 4.4.12, 7.3.4 and 7.6.1, printed pp.622,699,702,
refs/quasithin.pdf. The quaternion coordinates and group orders retain the
ATLAS attribution and license in LICENSES/ATLAS.txt and
LICENSES/ATLAS-CITATION.cff. The proof-only import extends the existing
symplectic matrix embedding without changing its public boundary.
-/

open Subgroup Theory.GroupTheory Matrix
open scoped MatrixGroups IsMulCommutative
public noncomputable section
namespace CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryOddRanks
open Atlas.G2 Atlas.G2.MultiplierOrdinary
open OddQuadraticTorus.OrthogonalRankOne OddTwoPrimary.OrthogonalMap
variable {F : Type*} [Field F]

private def pairAction : Model F →* ((Mat F × Mat F) ≃ₗ[F] (Mat F × Mat F)) where
  toFun g := coordinates.symm.trans (g.val.trans coordinates)
  map_one' := by
    apply LinearEquiv.ext
    intro x
    change coordinates (coordinates.symm x) = x
    exact coordinates.apply_symm_apply x
  map_mul' g h := by
    apply LinearEquiv.ext
    intro x
    change coordinates (g.val (h.val (coordinates.symm x))) =
      coordinates (g.val (coordinates.symm (coordinates (h.val (coordinates.symm x)))))
    rw [LinearEquiv.symm_apply_apply]

private theorem pairAction_preserves (g : Model F) (x y : Mat F × Mat F) :
    pairAction g (pairMul x y) = pairMul (pairAction g x) (pairAction g y) := by
  have he := g.property (coordinates.symm x) (coordinates.symm y)
  have hxy : coordinates.symm (pairMul x y) =
      Atlas.SplitOctonion.mul (coordinates.symm x) (coordinates.symm y) := by
    apply coordinates.injective
    simp only [LinearEquiv.apply_symm_apply,coordinates_mul]
  change coordinates (g.val (coordinates.symm (pairMul x y))) = _
  rw [hxy,he,coordinates_mul]
  rfl

private theorem pairAction_injective : Function.Injective (pairAction (F:=F)) := by
  intro g h he
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  apply coordinates.injective
  have hh := congrArg (fun a => a (coordinates x)) he
  simpa only [pairAction,MonoidHom.coe_mk,OneHom.coe_mk,LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_apply] using hh

private theorem orthogonal_preserves_second (d : F) (hd : d ≠ 0)
    (g : (inclusion d hd).range) (X : Mat F) :
    (pairAction g.val (0,X)).1 = 0 := by
  obtain ⟨x,hx⟩ := g.property
  rw [←hx]
  change (pairAction (productHom x.left * outerHom d hd x.right) (0,X)).1 = 0
  rw [map_mul]
  have hc : x.right = 1 ∨ x.right = Multiplicative.ofAdd 1 := by
    exact (show ∀ c : OddTwoPrimary.C2, c=1 ∨ c=Multiplicative.ofAdd 1 from by decide) x.right
  have hz : twist d (0 : Mat F) = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [twist]
  rcases hc with hc | hc <;>
    simp [pairAction,productHom,octonionEquiv,pairEquiv,pairLinear,
      outerHom,hc,involutionHom_generator,outer,outerEquiv,pairTwist,hz]

private def secondAction (d : F) (hd : d ≠ 0) :
    Representation F (inclusion d hd).range (Mat F) where
  toFun g := (LinearMap.snd F (Mat F) (Mat F)).comp
    ((pairAction g.val).toLinearMap.comp (LinearMap.inr F (Mat F) (Mat F)))
  map_one' := by
    apply LinearMap.ext
    intro X
    change (pairAction (1 : Model F) (0,X)).2 = X
    rw [map_one]
    rfl
  map_mul' g h := by
    apply LinearMap.ext
    intro X
    have hh : pairAction h.val (0,X) = (0,(pairAction h.val (0,X)).2) :=
      Prod.ext (orthogonal_preserves_second d hd h X) rfl
    change (pairAction (g.val*h.val) (0,X)).2 =
      (pairAction g.val (0,(pairAction h.val (0,X)).2)).2
    rw [map_mul]
    change (pairAction g.val (pairAction h.val (0,X))).2 = _
    rw [hh]

private theorem secondAction_injective (d : F) (hd : d ≠ 0) :
    Function.Injective (secondAction d hd) := by
  apply (injective_iff_map_eq_one _).mpr
  intro g hg
  have hsecond (X : Mat F) : pairAction g.val (0,X) = (0,X) := by
    apply Prod.ext
    · exact orthogonal_preserves_second d hd g X
    · exact LinearMap.congr_fun hg X
  have hfirst (X : Mat F) : pairAction g.val (X,0) = (X,0) := by
    have he := pairAction_preserves g.val (0,-X) (0,1)
    rw [hsecond,hsecond] at he
    simpa only [pairMul,zero_mul,sub_neg_eq_add,bar_one,one_mul,mul_neg,
      zero_add,zero_sub,mul_zero,add_zero,neg_neg,show bar (0 : Mat F)=0 by ext i j; fin_cases i <;> fin_cases j <;> simp [bar]] using he
  apply Subtype.ext
  apply pairAction_injective
  change pairAction g.val = pairAction (1 : Model F)
  rw [map_one]
  apply LinearEquiv.ext
  rintro ⟨X,Y⟩
  have he : (X,Y) = (X,0) + (0,Y) := by simp
  rw [he,map_add,hfirst,hsecond]
  rfl

private theorem orthogonal_twoRank_le_four [Finite F] (h2 : (2 : F) ≠ 0)
    (d : F) (hd : d ≠ 0) : primeRank 2 (inclusion d hd).range ≤ 4 := by
  apply (primeRank_le_iff_elementary_card_le _).mpr
  intro E hE
  let : IsElementaryAbelian 2 E := hE
  have hb := Representation.elementary_card_le_pow_finrank_of_involutive
    ((secondAction d hd).comp E.subtype)
    ((secondAction_injective d hd).comp E.subtype_injective) h2
  simpa only [Mat,Module.finrank_matrix,Module.finrank_self,Fintype.card_fin,
    Nat.mul_one,Nat.reduceMul] using hb


private theorem prime_g2_twoRank_le_four {p : ℕ} [Fact p.Prime] (hp : 2 < p) :
    primeRank 2 (Model (ZMod p)) ≤ 4 := by
  obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare (F := ZMod p)
    (by rw [ZMod.ringChar_zmod_n]; omega)
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact ha ⟨0, by simp⟩
  let d := -a
  have hd : d ≠ 0 := neg_ne_zero.mpr ha0
  let H := (inclusion d hd).range
  have hindex : ¬ 2 ∣ H.index := by
    rw [← even_iff_two_dvd]
    apply Nat.not_even_iff_odd.mpr
    by_cases hp3 : 3 < p
    · exact OddTwoPrimary.odd_index_of_diagonal_kernel
        (F := ZMod p) (by simp [Nat.card_eq_fintype_card]) hp3
        (action d hd) (inclusion d hd)
        (inclusion_kernel d hd (by simpa [d] using ha))
    · have he : p = 3 := by omega
      subst p
      let j := inclusion d hd
      let z : (OddTwoPrimary.RankOne 3 × OddTwoPrimary.RankOne 3) ⋊[action d hd] OddTwoPrimary.C2 := SemidirectProduct.inl (-1,-1)
      have hz : z ≠ 1 := by
        intro h
        have h' := congrArg (fun x : (OddTwoPrimary.RankOne 3 × OddTwoPrimary.RankOne 3) ⋊[action d hd] OddTwoPrimary.C2 => x.left.1.val 0 0) h
        change (-1 : ZMod 3) = 1 at h'
        have hz : (2 : ZMod 3) = 0 := by linear_combination -h'
        have hh := (ZMod.natCast_eq_zero_iff 2 3).mp hz
        norm_num at hh
      have hk : Nat.card j.ker = 2 := by
        apply (Nat.card_eq_two_iff' (1 : j.ker)).mpr
        have hj := inclusion_kernel d hd (by simpa [d] using ha)
        refine ⟨⟨z,(hj z).mpr (Or.inr rfl)⟩,fun h => hz (congrArg Subtype.val h),?_⟩
        intro x hx
        rcases (hj x).mp x.property with h | h
        · exact (hx (Subtype.ext h)).elim
        · exact Subtype.ext h
      have hdom : Nat.card ((OddTwoPrimary.RankOne 3 × OddTwoPrimary.RankOne 3) ⋊[action d hd] OddTwoPrimary.C2) = 1152 := by
        rw [SemidirectProduct.card,Nat.card_prod,Atlas.card_sl_two]
        norm_num [OddTwoPrimary.C2,Nat.card_eq_fintype_card]
      have hr : Nat.card H = 576 := by
        have h := j.ker.card_mul_index
        rw [index_ker,hk,hdom] at h
        change 2 * Nat.card H = 1152 at h
        omega
      have hidx := H.card_mul_index
      rw [hr,Atlas.G2.card_Model] at hidx
      norm_num [Nat.card_eq_fintype_card] at hidx
      have hh : H.index = 7371 := by omega
      rw [hh]
      decide
  rw [← H.primeRank_eq_of_not_dvd_index hindex]
  apply orthogonal_twoRank_le_four _ d hd
  intro hz
  exact Nat.not_dvd_of_pos_of_lt (by decide) hp ((ZMod.natCast_eq_zero_iff 2 p).mp hz)

/-- The actual odd-prime G₂ model has two-rank at most four, including p = 3.
The odd-index quaternion-coordinate subgroup acts faithfully on its second coordinate. -/
theorem g2_odd_twoRank_le_four {Q : Type*} [Group Q] [Finite Q]
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hm : ClassificationModels.IsG2At Q p) :
    primeRank 2 Q ≤ 4 := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let := Fintype.ofFinite F
  let a : F ≃+* ZMod p := (ZMod.ringEquivOfPrime F hp
    (by simpa only [Nat.card_eq_fintype_card] using hF)).symm
  rw [primeRank_equiv 2 (e.trans (fieldEquiv a))]
  apply prime_g2_twoRank_le_four
  have hne : p ≠ 2 := by rintro rfl; norm_num at ho
  have := hp.two_le
  omega

/-- The same faithful four-space and full central quotient give the sharper
bound needed for the placed symplectic row. -/
theorem symplectic_odd_twoRank_le_five {Q : Type*} [Group Q] [Finite Q]
    {q : ℕ} (ho : Odd q) (hm : ClassicalGroup.IsPSp Q 2 q) : primeRank 2 Q ≤ 5 := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  have h2 : (2 : F) ≠ 0 :=
    Theory.SpecificGroups.OddThreeRank.two_ne_zero_of_odd_card (k:=1) ho (by simpa using hF)
  let r : GL (Fin 2 ⊕ Fin 2) F ≃* GL (Fin 4) F :=
    Units.mapEquiv (Matrix.reindexRingEquiv F finSumFinEquiv).toMulEquiv
  let ρ := r.toMonoidHom.comp Theory.SpecificGroups.SymplecticFour.OddProjectiveRank.toGL
  have hρ : Function.Injective ρ :=
    r.injective.comp Theory.SpecificGroups.SymplecticFour.OddProjectiveRank.toGL_injective
  have hdet (g : Theory.SpecificGroups.SymplecticFour.Sp F) :
      Matrix.GeneralLinearGroup.det (ρ g) = 1 := by
    apply Units.ext
    change Matrix.det (Matrix.reindex finSumFinEquiv finSumFinEquiv g.val) = 1
    rw [Matrix.det_reindex_self]
    exact SymplecticGroup.det_eq_one g.property
  rw [primeRank_equiv 2 e]
  exact Representation.ProjectiveFour.central_quotient_twoRank_le_five ρ hρ h2 hdet
    (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk'])

/-- The unitary parameter remains the fixed-field order, and the entire
kernel of the stored projective map is retained. -/
theorem unitary_odd_twoRank_le_five {Q : Type*} [Group Q] [Finite Q]
    {q : ℕ} (ho : Odd q) (hm : ClassicalGroup.IsPSU Q 4 q) : primeRank 2 Q ≤ 5 := by
  obtain ⟨F,_,_,J,hF,_,⟨e⟩⟩ := hm
  let : Finite (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_equiv Q e.toEquiv
  rw [primeRank_equiv 2 e]
  exact Theory.SpecificGroups.ClassicalUnitary.odd_four_projective_twoRank_le_five J
    (Theory.SpecificGroups.OddThreeRank.two_ne_zero_of_odd_card ho hF)

/-- The full center in the degree-four linear model also gives rank at most five. -/
theorem linear_odd_twoRank_le_five {Q : Type*} [Group Q] [Finite Q]
    {q : ℕ} (ho : Odd q) (hm : ClassicalGroup.IsPSL Q 4 q) : primeRank 2 Q ≤ 5 := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  rw [primeRank_equiv 2 e]
  exact Representation.ProjectiveFour.central_quotient_twoRank_le_five
    SpecialLinearGroup.toGL SpecialLinearGroup.toGL_injective
    (Theory.SpecificGroups.OddThreeRank.two_ne_zero_of_odd_card (k:=1) ho (by simpa using hF))
    SpecialLinearGroup.coeToGL_det (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
    (by rw [QuotientGroup.ker_mk'])

/-- All seven original odd Theorem B families are incompatible with the
whole binary doubled orbit's rank-six placement. -/
theorem odd_model_twoRank_le_five {Q : Type*} [Group Q] [Finite Q]
    (hm : ChapterA.Section02.IsTheoremBOddModel Q) : primeRank 2 Q ≤ 5 := by
  cases hm with
  | linear_two q ho hm =>
      exact (ChapterA.Section02.odd_psl_two_twoRank_le_two ho hm).trans (by decide)
  | linear_three p e hp ho he hm =>
      exact (ChapterA.Section02.odd_psl_three_twoRank_le_two ho.pow hm).trans (by decide)
  | unitary_three p e hp ho he hm =>
      exact (ChapterA.Section02.odd_psu_three_twoRank_le_two ho.pow hm).trans (by decide)
  | symplectic p hp ho hm => exact symplectic_odd_twoRank_le_five ho hm
  | g2 p hp ho hm => exact (g2_odd_twoRank_le_four hp ho hm).trans (by decide)
  | linear_four p hp hf hm =>
      have ho : Odd p := by
        obtain ⟨k,rfl⟩ := hf
        exact (even_two.pow_of_ne_zero (by positivity)).add_one
      exact linear_odd_twoRank_le_five ho hm
  | unitary_four p hp hf hm =>
      have ho : Odd p := by
        obtain ⟨k,hk⟩ := hf
        have hk0 : k ≠ 0 := by
          intro he
          simp only [he,pow_zero] at hk
          have := hp.two_le
          omega
        have he : Even (p+1) := hk.symm ▸ even_two.pow_of_ne_zero hk0
        exact Nat.not_even_iff_odd.mp (Nat.even_add_one.mp he)
      exact unitary_odd_twoRank_le_five ho hm

/-- The source rank-six lower bound excludes the complete odd catalogue. -/
theorem no_odd_model_of_rank_six {Q : Type*} [Group Q] [Finite Q]
    (hr : 6 ≤ primeRank 2 Q) : ¬ ChapterA.Section02.IsTheoremBOddModel Q := by
  intro hm
  have := odd_model_twoRank_le_five hm
  omega

end CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryOddRanks
