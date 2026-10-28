module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.ComponentRankOneJanko
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NonnormalOuterSource.FourModels.RemainingRows
public import Theory.SpecificGroups.PSL3.DefiningRank
public import Theory.SpecificGroups.SU3.OddDefiningRank
public import Theory.AtlasPort.ExceptionalIsomorphisms.SmallParameters

/-!
# The remaining linear models of the original rank-one component

The actual cubic-rank witnesses remove every nonlinear binary row and
every sporadic row except J1; condition (*) removes J1. Defining root
planes exclude PSL3(3) and PSU3(3). The original faithful binary-section
displacement excludes PSU3(5). The remaining binary PSL3 endpoint is
transported through its actual PSL2(7) equivalence. Thus Theorem C leaves
only odd PSL2 and PSL3(5) on the same selected component.

Downstream extensions carry out the PSL3(5) centralizer argument and the
PSL2 parameter restriction. The module contradiction and abelian point-span
conclusion require further source arguments.
Source: Aschbacher--Smith, proof of 12.6.26, printed p.833.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)
  (hz : z ≠ 1)
  (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
  (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
  (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
    Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
  {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
  (hn : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH H))
  (c : (D.fullSetup hZ T z).SelectedComponent H) (a : c.ActionMarking)


include hz hTV hTz hbound hH hn a in
/-- The original component cannot have an odd ternary degree-three model. -/
theorem SourceHypothesis.original_selectedComponent_not_ternaryThree
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L) :
    ¬ ClassicalGroup.IsPSL (Nonabelian.Setup.star H c.K) 3 3 ∧
      ¬ ClassicalGroup.IsPSU (Nonabelian.Setup.star H c.K) 3 3 := by
  have hr : primeRank 3 (Nonabelian.Setup.star H c.K) = 1 :=
    c.three_rank_eq_star.symm.trans
      (S.original_selectedComponent_rank_one D hZ z hz hTV hTz hbound hH hn c a hTI hns)
  constructor
  · rintro ⟨F,hfield,hfinite,hF,⟨e⟩⟩
    let := hfield
    let := hfinite
    let := Fintype.ofFinite F
    let : CharP F 3 := charP_of_card_eq_prime_pow (p := 3) (f := 1)
      (by simpa only [Nat.card_eq_fintype_card,pow_one] using hF)
    have hl := Matrix.PSL3.DefiningRank.two_mul_fieldExponent_le_primeRank F
      (p := 3) (e := 1) (by simpa using hF)
    rw [primeRank_equiv 3 e] at hr
    omega
  · rintro ⟨F,hfield,hfinite,J,hF,hconj,⟨e⟩⟩
    let := hfield
    let := hfinite
    have hl := BenderSuzuki.MatrixGroups.HermitianForm.OddDefiningRank.two_mul_fieldExponent_le_primeRank J
      (p := 3) (e := 1) (by decide) (by decide)
      (by simpa using hF) (by simpa using hconj)
    rw [primeRank_equiv 3 e] at hr
    omega

include hz hTV hTz hbound hH hn a in
/-- All odd unitary rows are excluded on the original component, also in rank one. -/
theorem SourceHypothesis.original_selectedComponent_not_oddUnitary
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) :
    ¬ ClassicalGroup.IsPSU (Nonabelian.Setup.star H c.K) 3 p := by
  intro he
  let B := Nonabelian.Setup.star H c.K
  let : IsSimpleGroup B := S.original_selectedComponent_simple D hZ z hz hTV hTz
    hbound hH hn c a hTI hns
  let := c.component.2
  have hc : center B = ⊥ := center_eq_bot_of_simple_perfect
  let e₀ : (B ⧸ center B) ≃* B :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
  rcases S.original_selectedComponent_oddUnitaryThree_quotient_parameter
    D hZ z hz hTV hTz hbound hns hH hn c a hp ho (he.of_mulEquiv e₀) with rfl | rfl
  · exact (S.original_selectedComponent_not_ternaryThree D hZ z hz hTV hTz
      hbound hH hn c a hTI hns).2 he
  · exact S.original_selectedComponent_not_projectiveUnitaryThreeFive D hZ z hz hTV hTz
      hbound hH hn c a hTI hns he

include hz hTV hTz hbound hH hn a in
/-- The full Theorem C inspection now leaves only the two stated linear possibilities. -/
theorem SourceHypothesis.original_rank_one_linear_models
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L) :
    let B := Nonabelian.Setup.star H c.K
    (∃ p n : ℕ, p.Prime ∧ Odd p ∧ n ≤ 2 ∧ ClassicalGroup.IsPSL B 2 (p^n)) ∨
      ClassicalGroup.IsPSL B 3 5 := by
  let B := Nonabelian.Setup.star H c.K
  let : IsSimpleGroup B := S.original_selectedComponent_simple D hZ z hz hTV hTz
    hbound hH hn c a hTI hns
  let := c.component.2
  have hr : primeRank 3 B = 1 := c.three_rank_eq_star.symm.trans
    (S.original_selectedComponent_rank_one D hZ z hz hTV hTz hbound hH hn c a hTI hns)
  have hs := (S.original_star_sqtk D hZ z hz hH).subgroup B
  have hm := ChapterA.Section02.theoremC_knownSimple (G := B) inferInstance
    (Group.IsPerfect.not_isMulCommutative B) hs.stronglyQuasithin hs.isKGroup
  cases hm with
  | alternating n hn8 he =>
      exact (S.original_selectedComponent_not_alternating D hZ z hz hTV hTz
        hbound hH hn c a hTI hns hn8 he).elim
  | odd hm =>
      cases hm with
      | linear_two p n hp ho hn2 he => exact Or.inl ⟨p,n,hp,ho,hn2,he⟩
      | linear_three p hp ho he =>
          have hc : center B = ⊥ := center_eq_bot_of_simple_perfect
          let e₀ : (B ⧸ center B) ≃* B :=
            (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
          rcases S.original_selectedComponent_oddLinearThree_quotient_parameter
            D hZ z hz hTV hTz hbound hns hH hn c a hp ho (he.of_mulEquiv e₀) with rfl | rfl
          · exact ((S.original_selectedComponent_not_ternaryThree D hZ z hz hTV hTz
              hbound hH hn c a hTI hns).1 he).elim
          · exact Or.inr he
      | unitary_three p hp ho he =>
          exact (S.original_selectedComponent_not_oddUnitary D hZ z hz hTV hTz
            hbound hH hn c a hTI hns hp ho he).elim
  | bender hm =>
      exact (S.original_selectedComponent_not_bender D hZ z hz hTV hTz
        hbound hH hn c a hTI hns hm).elim
  | rank_two f hm =>
      have hrows : (∃ n, 1 ≤ n ∧ ClassicalGroup.IsPSL B 3 (2^n)) ∨ 2 ≤ primeRank 3 B := by
        cases hm with
        | linear hn he => exact Or.inl ⟨f,hn,he⟩
        | symplectic hn he => exact ChapterA.SQTKStructure.NonnormalOuterSource.FourModels.rank_two_rows (.symplectic f hn he)
        | g2 hn he => exact ChapterA.SQTKStructure.NonnormalOuterSource.FourModels.rank_two_rows (.g2 f hn he)
        | triality hn he => exact ChapterA.SQTKStructure.NonnormalOuterSource.FourModels.rank_two_rows (.triality f hn he)
        | ree_f4 m _ _ he =>
            right
            rw [primeRank_equiv 3 he.some]
            exact ReeF4.CubicRank.model m
        | symplectic_derived _ he => exact ChapterA.SQTKStructure.NonnormalOuterSource.FourModels.rank_two_rows (.symplectic_derived he)
        | g2_derived _ he => exact ChapterA.SQTKStructure.NonnormalOuterSource.FourModels.rank_two_rows (.g2_derived he)
        | tits _ he => exact ChapterA.SQTKStructure.NonnormalOuterSource.FourModels.rank_two_rows (.tits he)
      rcases hrows with ⟨n,hn1,he⟩ | hlarge
      · by_cases hn2 : 2 ≤ n
        · exact (S.original_selectedComponent_not_binaryLinear D hZ z hz hTV hTz
            hbound hns hH hn c a hn2 he).elim
        · have hn : n = 1 := by omega
          obtain ⟨F,hfield,hfinite,hF,⟨e⟩⟩ := he
          let := hfield
          let := hfinite
          let := Fintype.ofFinite F
          let eF : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
            simpa only [←Nat.card_eq_fintype_card,Nat.card_zmod,hn,pow_one] using hF)
          let : Fact (Nat.Prime 7) := ⟨by decide⟩
          refine Or.inl ⟨7,1,by decide,by decide,by decide,ZMod 7,
            inferInstance,inferInstance,by simp,?_⟩
          exact ⟨(e.trans (Atlas.fieldEquivPSL 3 eF)).trans
            Atlas.Comparisons.Exceptional.psl2SevenEquivPsl3Two.symm⟩
      · omega
  | linear_binary n hn he =>
      have hl := ChapterA.SQTKStructure.NonnormalOuterSource.FourModels.binary_linear_three_rank n hn he
      omega
  | sporadic hm =>
      rcases hm with ⟨name,hne,⟨e⟩⟩ | he
      · let : Finite name.Carrier := Finite.of_equiv B e.toEquiv
        have hl := ChapterA.SQTKStructure.NonnormalOuterSource.FourModels.sporadic_three_rank name hne
        rw [primeRank_equiv 3 e] at hr
        omega
      · exact (S.original_selectedComponent_not_jankoOne D hZ z hz hTV hTz
          hbound hH hn c a hTI hns he).elim

end CFSG.Quasithin.Chapter12.Section06
