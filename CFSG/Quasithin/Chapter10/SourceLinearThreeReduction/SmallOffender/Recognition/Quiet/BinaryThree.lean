module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Recognition.Quiet.FullBound
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Recognition.Quiet.MovedBound

/-!
# Recognition of every quiet binary-three small offender

No size bound or irreducible marking is assumed. Semisimplicity and the
checked small-order classification leave a center-free TI moved factor of
order at least 512. The fully moved case has already been excluded. In the
separated case, fixed-space geometry normalizes every small moved offender.
A noncommuting conjugate pair would force moved-factor order at most 64.
Thus all those conjugates commute; point control places them in the original
maximal local subgroup, and the full-module commutator contradicts the
original configuration.

This proves the natural marking on the literal moved central quotient,
full/local equality, crossed centralization and w≥2. The final adapter uses
contained reselection in the original survivor consumer. Other quiet-family
markings remain with qt-d-10-nona5-small-offender. HalfSylowUniqueAt retains
producer qt-d-10-nona5-half-sylow-unique and its final discharge by
qt-d-10-nona5-point-control; this adapter is still conditional on those inputs.
Source: Aschbacher--Smith 10.1.1--2 and 10.2.10--12, pp.741--742,753--755.
-/

public noncomputable section
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.SmallOffender.Recognition
open Subgroup Theory.GroupTheory Representation
open Chapter3.Section02 ChapterE ChapterI.Section06To08 PointControl.Selection
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

theorem no_large_quiet_binary_three
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) {g : G}
    (c : Configuration T D g)
    (hJ : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (hNL : normalizer (L : Set G) ≤ D.maximalLocal)
    (e : (L ⧸ pCore 2 L) ≃* BinaryLinearThree.Group)
    (hlarge : 512 ≤ Nat.card (⁅D.fullModule,L⁆ : Subgroup G)) : False := by
  have hz := quiet_moved_fixed_eq_bot D c.many c.minimal c.nonnormal hJ
  have hthree : 3 ∣ Nat.card (L ⧸ pCore 2 L) := by
    rw [Nat.card_congr e.toEquiv,Matrix.PSL3Two.card_SL]
    decide
  have hti := quiet_moved_ti_of_three D c hJ hNL hthree
  have hcross : ∀ {t : G}, t ∈ (T : Subgroup G) → t ∉ normalizer (L : Set G) →
      (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G) :=
    fun ht htn => quiet_binary_three_crossed D c hJ hNL e ht htn
  have hsize : 8 < (centralizer (L : Set G)).relIndex ⁅D.fullModule,L⁆ := by
    rw [←inf_relIndex_left,hz,relIndex_bot_left]
    omega
  let ctx : FixedSpaces.Context D :=
    ⟨c.many,c.minimal,c.nonnormal,c.notA5,c.pointCentralizers,
      fun _ ht htn => hcross ht htn,hsize⟩
  have hgeometry := FixedSpaces.fixedSpaceGeometry_of_normalizer D ctx hNL
  obtain ⟨t,ht,htn⟩ := SetLike.not_le_iff_exists.mp c.nonnormal
  apply c.noncommuting
  apply source_a5_small_conjugates_commute_of_moved_factor D c.nonnormal ht
    (hcross ht htn) 2 ?_ g c.small
  intro x hx hs
  have hc : ⁅⁅D.fullModule,L⁆,(⁅D.fullModule,L⁆).map (MulAut.conj x).toMonoidHom⁆ = ⊥ := by
    by_contra hnc
    have hd : Disjoint ⁅D.fullModule,L⁆ ((⁅D.fullModule,L⁆).map (MulAut.conj x).toMonoidHom) :=
      disjoint_iff.mpr (FixedSpaces.moved_inf_conjugate_eq_bot D c.nonnormal t ht
        (hcross ht htn) c.pointCentralizers hNL hx)
    have hb := moved_ti_binary_three_card_le_sixtyfour D c.nonnormal hti hz e hd hnc hs
      (hgeometry x hx hs).1
    omega
  have hp := le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hc)
  refine ⟨?_,hp⟩
  obtain ⟨w,hw,hw1⟩ := (⁅D.fullModule,L⁆ : Subgroup G).bot_or_exists_ne_one.resolve_left
    (source_full_moved_ne_bot D)
  exact (hp.trans (centralizer_le (Set.singleton_subset_iff.mpr hw))).trans
    (c.pointCentralizers w hw hw1)

theorem natural_of_quiet_binary_three
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) {g : G}
    (c : Configuration T D g)
    (hJ : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (hNL : normalizer (L : Set G) ≤ D.maximalLocal)
    (e : (L ⧸ pCore 2 L) ≃* BinaryLinearThree.Group) :
    BinaryThreeNatural D := by
  rcases quiet_binary_three_natural_or_large_ti D c hJ hNL e with hnat | hlarge
  · exact hnat
  · exact (no_large_quiet_binary_three D c hJ hNL e hlarge.1).elim

theorem survivor_of_quiet_binary_three
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) {g : G}
    (c : Configuration T D g)
    (hJ : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (hNL : normalizer (L : Set G) ≤ D.maximalLocal)
    (e : (L ⧸ pCore 2 L) ≃* BinaryLinearThree.Group) :
    Nonempty (SourceLinearThreeGeometry T D) ∧
      2 ≤ globalW D.fullModule (T : Subgroup G) := by
  have hnat := natural_of_quiet_binary_three D c hJ hNL e
  obtain ⟨f,⟨s⟩⟩ := hnat
  let m : SourceLinearThreeGeometry T D := {
    full_eq_local := ModuleChoice.full_eq_local_of_binaryThreeNatural D c.nonnormal ⟨f,⟨s⟩⟩
    quotient := f
    natural := s
    crossed := fun _ ht htn => binary_three_crossed_of_marking D ⟨f,⟨s⟩⟩ ht htn }
  refine ⟨⟨m⟩,?_⟩
  have hk : 2 ≤ subgroupCorank (D.fullModule.map (MulAut.conj g).toMonoidHom)
      (D.fullModule.map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal) := by
    by_contra hn
    exact natural_small_corank_false_of_normalizer D c m hNL (by omega)
  rw [c.attained]
  exact_mod_cast hk

theorem nonnormalSmallOffender_of_quiet_component_rows_and_halfSylow
    (hhalf : PointControl.HalfSylowUniqueAt T)
    (hquiet : ∀ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L) (g : G),
      Configuration T D g →
      Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G) →
      ∃ E : FundamentalSetup KnownSimple.IsKnownSimple T L,
        E.fullModule ≤ D.fullModule ∧
        (Nonempty ((L ⧸ pCore 2 L) ≃* BinaryLinearThree.Group) ∨
          RankOneNatural E ∨ NaturalDualRow E ∨ FourNaturalRow E ∨
          OrthogonalFourMinusRow E ∨ SuzukiNaturalRow E)) :
    SourceNonnormalSmallOffenderAt T := by
  apply nonnormalSmallOffender_of_quiet_marked_rows_and_halfSylow hhalf
  intro L D g c hJ
  obtain ⟨E,hE,hrow⟩ := hquiet L D g c hJ
  refine ⟨E,hE,?_⟩
  rcases hrow with he | hrow
  · obtain ⟨e⟩ := he
    obtain ⟨he,cE⟩ := c.reselect E hE
    have hthree : 3 ∣ Nat.card (L ⧸ pCore 2 L) := by
      rw [Nat.card_congr e.toEquiv,Matrix.PSL3Two.card_SL]
      decide
    have hJE : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤
        centralizer (E.moduleSubgroup : Set G) :=
      (ModuleChoice.full_thompson_centralizes_of_local_three D c.nonnormal hthree hJ).trans
        (centralizer_le ((le_componentOrbit _ _).trans hE))
    exact Or.inl (natural_of_quiet_binary_three E cE hJE
      (PointControl.component_normalizer_le_of_halfSylowUnique E cE.nonnormal
        (hhalf cE.many L E cE.nonnormal cE.notA5)) e)
  · exact Or.inr hrow

end CFSG.Quasithin.Chapter10.SmallOffender.Recognition
