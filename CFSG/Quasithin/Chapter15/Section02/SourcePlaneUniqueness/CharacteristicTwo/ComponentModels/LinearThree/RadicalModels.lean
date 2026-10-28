module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.LinearThree.PartnerCollapse
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.Inputs
public import Theory.GroupTheory.CComponent.PairRadical
public import Theory.GroupTheory.SolvableRadical.NormalTwoExtension
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity
public import Theory.SpecificGroups.SL2.OddProjectiveNonsolvable

/-!
# The radical consequence of the source partner alternatives

The exact StructuralAlternatives of 15.2.12(2) give either Kc = K or a
two-group solvable radical. The invariant component has actual PSL₄(2)
or PSL₅(2) quotient. The moved row is the join of two distinct actual
C-components with simple rank-one two-core quotients. Their solvable
radical is a two-group by the component-pair kernel theorem.

The even-field parameter is at least four; nonsolvability of the
C-component excludes PSL₂(3) in the odd-prime row. No simplicity or
radical callback is retained. The binary consumer combines this with
the normal cubic factor obstruction to force Kc = K.

The earlier StructuralAlternatives premise retains producer
qt-e-152-plane-geometry; final discharge belongs to
qt-e-152-plane-uniqueness and qt-e-152-char2-component-models.
Source: Aschbacher--Smith, 15.2.12(2), 15.2.21(2), and proof of
15.2.23, printed pp.1111, 1114, and 1116; refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section02.PlaneUniquenessPreceding.LinearThree
variable {G : Type*} [Group G] [Finite G]

private theorem nonsolvable_core_quotient (A : Subgroup G) (hn : ¬ Group.IsSolvable A) :
    ¬ Group.IsSolvable (A ⧸ pCore 2 A) := by
  intro hs
  let := hs
  let : Group.IsNilpotent (pCore 2 A) := pCore_isPGroup.isNilpotent
  exact hn (Group.isSolvable_of_ker_le_range (pCore 2 A).subtype
    (QuotientGroup.mk' (pCore 2 A)) (by rw [QuotientGroup.ker_mk',range_subtype]))

private theorem rankOne_simple (A : Subgroup G) (hn : ¬ Group.IsSolvable A)
    (hm : (∃ n : ℕ, Even n ∧ ClassicalGroup.IsPSL (A ⧸ pCore 2 A) 2 (2^n)) ∨
      ∃ p : ℕ, p.Prime ∧ Odd p ∧ ClassicalGroup.IsPSL (A ⧸ pCore 2 A) 2 p) :
    IsSimpleGroup (A ⧸ pCore 2 A) := by
  rcases hm with ⟨n,he,F,hF,hfin,hcard,⟨e⟩⟩ | ⟨p,hp,ho,F,hF,hfin,hcard,⟨e⟩⟩
  · have hn0 : n ≠ 0 := by
      intro hz
      have hh : 1 < Nat.card F := Finite.one_lt_card
      simp only [hz,pow_zero] at hcard
      omega
    have hn2 : 2 ≤ n := by obtain ⟨k,hk⟩ := he; omega
    have hc : 4 ≤ Nat.card F := by
      rw [hcard]
      exact Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) hn2
    let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
      Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hc
    exact e.isSimpleGroup
  · have hns : ¬ Group.IsSolvable (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) := by
      intro hs
      let := hs
      exact nonsolvable_core_quotient A hn
        (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective)
    have hc := Matrix.ProjectiveSpecialLinearGroup.card_gt_three_of_odd_of_not_isSolvable
      (hcard ▸ ho) hns
    let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
      Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hc
    exact e.isSimpleGroup


variable {T : Sylow 2 G} {M Mc V H ZS I X : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)

include d in
/-- The literal proper alternatives in 15.2.12(2) have two-group radical. -/
theorem partner_radical_alternative
    (hc : ChosenGeometry.StructuralAlternatives T H Mc) :
    smallActionKc H Mc = smallActionK H ∨
      IsPGroup 2 (solvableRadical (smallActionKc H Mc)) := by
  rcases hc with he | ⟨_,hcomp,n,hn,hm,_⟩ |
    ⟨L,t,_,hcomp,ht,htn,he,_,hm⟩
  · exact Or.inl he
  · right
    obtain ⟨F,hF,hfin,hcard,⟨e⟩⟩ := hm
    let a := subgroupOfEquivOfLe hcomp.1
    let := hcomp.2.perfect
    let : Group.IsPerfect (smallActionKc H Mc) :=
      Group.IsPerfect.ofSurjective (f := a.toMonoidHom) a.surjective
    let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin n) F) :=
      Atlas.psl_simple_high_rank n (by omega)
    let : IsSimpleGroup ((smallActionKc H Mc) ⧸ pCore 2 (smallActionKc H Mc)) :=
      e.isSimpleGroup
    rw [radical_eq_core_of_perfect_simple_core_quotient]
    exact pCore_isPGroup
  · right
    have hTMc : (T : Subgroup G) ≤ Mc :=
      d.geometry.outside.1.1.2.trans d.geometry.in_partner
    let tM : Mc := ⟨t,hTMc ht⟩
    let A := L.subgroupOf Mc
    let B := A.map (MulAut.conj tM).toMonoidHom
    let a := subgroupOfEquivOfLe hcomp.1
    have hns : ¬ Group.IsSolvable L := by
      intro hs
      let := hs
      exact hcomp.2.not_isSolvable
        (Group.isSolvable_of_isSolvable_injective (f := a.toMonoidHom) a.injective)
    let : IsSimpleGroup (L ⧸ pCore 2 L) := rankOne_simple L hns hm
    let : IsSimpleGroup (A ⧸ pCore 2 A) :=
      (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).isSimpleGroup
    let b := (MulAut.conj tM).subgroupMap A
    let : IsSimpleGroup (B ⧸ pCore 2 B) :=
      (QuotientGroup.congr _ _ b (pCore_map_iso 2 b)).symm.isSimpleGroup
    have hmapB : B.map Mc.subtype = L.conjBy t := by
      change (A.map (MulAut.conj tM).toMonoidHom).map Mc.subtype = _
      rw [map_map]
      have hh : Mc.subtype.comp (MulAut.conj tM).toMonoidHom =
          (MulAut.conj t).toMonoidHom.comp Mc.subtype := by ext x; rfl
      rw [hh,← map_map,map_subgroupOf_eq_of_le hcomp.1]
      rfl
    have hne : A ≠ B := by
      intro h
      apply htn
      apply mem_normalizer_iff_map_conj_eq.mpr
      have hh := congrArg (map Mc.subtype) h
      rw [map_subgroupOf_eq_of_le hcomp.1,hmapB] at hh
      exact hh.symm
    have hr := radical_isTwoGroup_of_simple_core_pair A B hcomp.2
      (hcomp.2.map_equiv (MulAut.conj tM)) hne
    have hmap : (A ⊔ B).map Mc.subtype = smallActionKc H Mc := by
      rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hcomp.1,hmapB]
      exact he.symm
    let u : (A ⊔ B : Subgroup Mc) ≃* smallActionKc H Mc :=
      ((A ⊔ B).equivMapOfInjective Mc.subtype Mc.subtype_injective).trans
        (MulEquiv.subgroupCongr hmap)
    have hu := hr.map u.toMonoidHom
    rwa [map_solvableRadical_equiv u] at hu

include d in
/-- The literal 15.2.12(2) models force equality of the partner span and K
in the binary branch; the radical alternative is discharged here. -/
theorem Branch.binary_partner_eq_of_source_alternatives
    {F : Type} [Field F] [Finite F] (b : Branch M I X 1 F)
    (hI : PlaneEscapes Mc ZS I) (hout : ¬ X ≤ Mc)
    (hn : I ≤ normalizer (X : Set G))
    (hKcI : smallActionKc H Mc ≤ Mc ⊓ I)
    (hc : ChosenGeometry.StructuralAlternatives T H Mc) :
    smallActionK H = smallActionKc H Mc :=
  b.binary_partner_eq_of_radical_alternative d hI hout hn hKcI
    (partner_radical_alternative d hc)

include d in
/-- The original centralizer C_M(V) is three-prime from the literal
15.2.12(2) alternatives and the faithful NI action. -/
theorem Branch.binary_centralizer_threePrime_of_source_alternatives
    {F : Type} [Field F] [Finite F] (b : Branch M I X 1 F)
    (hI : PlaneEscapes Mc ZS I) (hout : ¬ X ≤ Mc)
    (f : (M ⊓ I : Subgroup G) →* Equiv.Perm (Fin 3))
    (hker : f.ker = (centralizer (V : Set G)).subgroupOf (M ⊓ I))
    (hKcI : smallActionKc H Mc ≤ Mc ⊓ I)
    (hc : ChosenGeometry.StructuralAlternatives T H Mc) :
    IsSmallActionThreePrime (M ⊓ centralizer (V : Set G)) :=
  b.binary_centralizer_threePrime_of_radical_alternative d hI hout f hker hKcI
    (partner_radical_alternative d hc)

end CFSG.Quasithin.Chapter15.Section02.PlaneUniquenessPreceding.LinearThree
