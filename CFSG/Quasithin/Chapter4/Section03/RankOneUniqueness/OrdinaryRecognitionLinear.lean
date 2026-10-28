module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OrdinaryRecognitionMathieu
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.BinaryLinear.Source
public import Theory.Representation.SL2.PerfectCoreQuotientDegree
public import Theory.Representation.GeneralLinearNatural
public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.OddCharacteristicExclusion

public import Theory.Alternating.PrimeRank
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8

/-!
# Excluding the higher binary linear and alternating ordinary carriers

The literal image of L in a central-quotient model of K preserves L/O₂(L).
A nontrivial binary representation of this perfect image therefore has
an irreducible section of dimension at least 2n. In dimensions four and
five this forces n = 2. The full-Sylow local A₅ section exclusion then
rules out both higher binary linear rows, including all central covers.
The same degree bound excludes PSL₃(2). Alternating eight is the actual
PSL₄(2) carrier, while smaller alternating groups contradict the original
moved module's lower bound of three on the quotient two-rank.

Every exclusion is applied to the original SourceConfiguration and its
unchanged local quotient; no placement or field comparison is assumed.
Source: Aschbacher--Smith C.3.1(2,10), printed pp.149--151, and the
rank-one row selection in 4.3.6, printed p.614; E.2.13(4) supplies the
binary representation degree bound. Final exhaustion remains with
qt-d-1222-rankone-ordinary-symplectic-marking.
-/

public section
open Subgroup Theory.GroupTheory ClassicalGroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.SourceConfiguration
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The same original local quotient bounds every faithful binary linear model. -/
theorem ordinary_binary_linear_degree_bound (c : SourceConfiguration T L)
    (ho : IsComponent c.H c.K) {n d : ℕ} (hn : 1 < n)
    (hpsl : IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (e : (c.K ⧸ center c.K) ≃* SL(d,ZMod 2)) : 2 * n ≤ d := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center c.K))
  let B := c.ordinaryLocal.map f
  obtain ⟨a⟩ := c.ordinary_model_local_quotient_equiv ho e
  obtain ⟨F,_,_,hF,⟨b⟩⟩ := hpsl.of_mulEquiv a.symm
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  let b' := b.trans (Theory.PSL2.sl2QuotientEquiv F).symm
  let := c.ordinaryLocal_perfect
  let : Group.IsPerfect B := Group.IsPerfect.map f
  have hB : B ≠ ⊥ := by
    intro he
    have hs : Group.IsSolvable B := he ▸ inferInstanceAs (Group.IsSolvable (⊥ : Subgroup SL(d,ZMod 2)))
    let := hs
    let j : (c.ordinaryLocal.map (QuotientGroup.mk' (center c.K))) →* B :=
      (e.toMonoidHom.comp (c.ordinaryLocal.map (QuotientGroup.mk' (center c.K))).subtype).codRestrict B (by
        rintro ⟨x,⟨l,hl,rfl⟩⟩
        exact ⟨l,hl,rfl⟩)
    exact c.ordinary_quotient_local_nonsolvable ho
      (Group.isSolvable_of_isSolvable_injective (f := j) (by
        intro x y hh
        exact Subtype.ext (e.injective (congrArg Subtype.val hh))))
  let : Nontrivial B := B.nontrivial_iff_ne_bot.mpr hB
  let ρ := (Representation.specialLinearNatural (k := ZMod 2) d).comp B.subtype
  have hi : Function.Injective ρ := (Representation.specialLinearNatural_injective d).comp B.subtype_injective
  obtain ⟨x,hx⟩ := exists_ne (1 : B)
  have hnt : ∃ x, ρ x ≠ 1 := ⟨x,fun he => hx (hi (he.trans ρ.map_one.symm))⟩
  simpa only [Module.finrank_fin_fun] using
    Representation.SL2.perfect_core_quotient_finrank_bound b' ρ hnt (by omega) hF

private theorem binaryLinearCoordinates {A : Type*} [Group A] {d : ℕ}
    (hd : 0 < d) (hm : IsPSL A d 2) : Nonempty (A ≃* SL(d,ZMod 2)) := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  let k : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    simpa only [←Nat.card_eq_fintype_card,Nat.card_zmod] using hF)
  exact ⟨((e.trans (Atlas.fieldEquivPSL d k)).trans
    (BinaryLinear.OuterCyclic.projectiveEquivLinear hd)).trans
      (BinaryLinear.OuterCyclic.slEquivLinear d).symm⟩

/-- Both higher binary linear quotient rows are impossible for the original local pair. -/
theorem ordinary_no_higher_binary_linear (c : SourceConfiguration T L)
    (D : Chapter12.Section02.ChosenModule T L V) (ho : IsComponent c.H c.K)
    {n : ℕ} (hn : 1 < n) (hpsl : IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    {d : ℕ} (hd : d = 4 ∨ d = 5) (hm : IsPSL (c.K ⧸ center c.K) d 2) : False := by
  have hb := c.ordinary_binary_linear_degree_bound ho hn hpsl
    (binaryLinearCoordinates (by rcases hd with rfl | rfl <;> decide) hm).some
  have hn2 : n = 2 := by rcases hd with rfl | rfl <;> omega
  let e := MulEquiv.refl (c.K ⧸ center c.K)
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center c.K))
  obtain ⟨P,_,hl,_⟩ := c.ordinary_model_local_data D ho e
  obtain ⟨a⟩ := c.ordinary_model_local_quotient_equiv ho e
  obtain ⟨F,_,_,hF,⟨b⟩⟩ := hpsl.of_mulEquiv a.symm
  have hF4 : Nat.card F = 4 := by simpa [hn2] using hF
  obtain ⟨k⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF4
  exact ChapterA.Section03.SourceEmbeddings.FiveLocalFF.BinaryLinear.not_section_binary_linear
    (P.mapSurjective (f := f) (e.surjective.comp (QuotientGroup.mk'_surjective _)))
    (c.ordinaryLocal.map f) hl (b.trans k) hd hm

/-- The binary endpoint of the degree-three row violates the original field degree. -/
theorem ordinary_no_pslThree_binary (c : SourceConfiguration T L)
    (ho : IsComponent c.H c.K) {n : ℕ} (hn : 1 < n)
    (hpsl : IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hm : IsPSL (c.K ⧸ center c.K) 3 2) : False := by
  have h := c.ordinary_binary_linear_degree_bound ho hn hpsl
    (binaryLinearCoordinates (by decide) hm).some
  omega

/-- All alternating quotient carriers of Theorem C are excluded, including A₈. -/
theorem ordinary_no_alternating (c : SourceConfiguration T L)
    (D : Chapter12.Section02.ChosenModule T L V) (ho : IsComponent c.H c.K)
    {n : ℕ} (hn : 1 < n) (hpsl : IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    {d : ℕ} (hd : d ≤ 8) (e : (c.K ⧸ center c.K) ≃* alternatingGroup (Fin d)) : False := by
  by_cases h8 : d = 8
  · subst d
    exact c.ordinary_no_higher_binary_linear D ho hn hpsl (Or.inl rfl)
      ⟨ZMod 2,inferInstance,inferInstance,by simp,
        ⟨e.trans Atlas.Comparisons.Exceptional.alt8EquivPSL4Two⟩⟩
  · have hr := c.c28.ordinary_quotient_twoRank_ge_three c.K ho
    rw [primeRank_congr 2 e,
      (GLS3.Chapter5.PRank.alternating_hasPRank_two d).primeRank_eq Nat.prime_two] at hr
    omega

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.SourceConfiguration