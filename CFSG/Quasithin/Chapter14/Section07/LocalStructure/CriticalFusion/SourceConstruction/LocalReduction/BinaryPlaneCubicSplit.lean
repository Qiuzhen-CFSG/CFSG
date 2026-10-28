module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.BinaryPlaneSimpleFactors
public import Theory.GroupTheory.RankTwoSectionNineSplit
public import Theory.Alternating.FivePairOuterTwo
public import Theory.SpecificGroups.Alternating.FiveLocalGeometry.CubicNormalizer
public import Theory.SpecificGroups.PSL3Two.Automorphisms.OuterOrder
public import Theory.SpecificGroups.PSL3Two.PairedGraphInputs

/-!
# The original nine-group and its two cubic projections

The selected S₃/A₅/L₃(2) Thompson factor has trivial center and two-group
outer action. Each model contains an actual S₃ subgroup and has three-part
of order three. Applying A.1.31 to inverse images under the original
I₀ → I₀/C_{I₀}(V_I) map bounds elementary three-subgroups of its centralizer.
The actual faithful nine therefore splits as its intersections with the
factor and its centralizer; both intersections have order three.

The lifted original point cubic remains cubic under this exact map.
If the point residual were contained in the factor or centralized it,
the split nine would normalize that residual, contradicting the original
construction. Two-perfectness then shows that the point cubic meets both
factors trivially. Multiplication supplies the actual two projections,
and both restrictions to that same cubic are injective.

The final application retains the original Y, I₀, reciprocal plane,
point span, quotient and nonnormalization conclusions. It proves source
case (c), excluding cases (a) and (b). The doubled-S₃ orbit exclusion,
T-normalization and terminal projection contradiction are still needed,
as are the guarded specialization and later local reductions through 14.7.52.

Source: Aschbacher–Smith, proof of 14.7.32, printed pp.1058–1059,
using A.1.31(1), refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
universe u
variable {Q : Type u} [Group Q] [Finite Q]

private theorem center_trivial_of_equiv {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (hz : center B = ⊥) : center A = ⊥ := by
  apply eq_bot_iff.mpr
  intro a ha
  have hh := (centerCongr e ⟨a,ha⟩).property
  change e a ∈ center B at hh
  rw [hz,mem_bot] at hh
  exact e.map_eq_one_iff.mp hh

private theorem symmetric_outer_two : IsPGroup 2 (MulAut.Outer (Equiv.Perm (Fin 3))) := by
  intro x
  obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective (MulAut.innerSubgroup (Equiv.Perm (Fin 3))) x
  obtain ⟨k,rfl⟩ := NormalSymmetricThreePairRank.symmetricThree_aut_inner a
  refine ⟨0,?_⟩
  simp only [pow_zero,pow_one]
  exact (QuotientGroup.eq_one_iff _).mpr ⟨k,rfl⟩

/-- The three selected models have trivial center, two-group outer action,
three-part of order three, and a genuine embedded S₃. -/
theorem small_thompson_factor_geometry (A : Subgroup Q)
    (hm : Nonempty (A ≃* Equiv.Perm (Fin 3)) ∨
      Nonempty (A ≃* alternatingGroup (Fin 5)) ∨
      Nonempty (A ≃* Matrix.PSL3Two.PSL)) :
    center A = ⊥ ∧ ¬ 9 ∣ Nat.card A ∧ IsPGroup 2 (MulAut.Outer A) ∧
      ∃ j : Equiv.Perm (Fin 3) →* A, Function.Injective j := by
  rcases hm with he | he | he
  · obtain ⟨e⟩ := he
    have hz : center (Equiv.Perm (Fin 3)) = ⊥ := by
      apply eq_bot_iff.mpr
      intro x hx
      exact NormalSymmetricThreePairRank.symmetricThree_center_trivial x (mem_center_iff.mp hx)
    refine ⟨center_trivial_of_equiv e hz,?_,
      symmetric_outer_two.of_equiv (MulAut.outerCongr e).symm,
      e.symm.toMonoidHom,e.symm.injective⟩
    rw [Nat.card_congr e.toEquiv,Nat.card_perm,Nat.card_fin]
    decide
  · obtain ⟨e⟩ := he
    have hc : Nat.card A = 60 := by
      rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup,Nat.card_fin]
      decide
    obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' 3 (by rw [hc]; decide : 3 ∣ Nat.card A)
    obtain ⟨s⟩ := alternatingGroup.FiveLocalGeometry.cubic_normalizer_equiv e (zpowers a)
      (by rw [Nat.card_zpowers,ha])
    refine ⟨center_trivial_of_equiv e (alternatingGroup.center_eq_bot (by simp)),?_,
      Theory.AlternatingFive.outer_isPGroup_two.of_equiv (MulAut.outerCongr e).symm,
      (normalizer (zpowers a : Set A)).subtype.comp s.symm.toMonoidHom,
      (normalizer (zpowers a : Set A)).subtype_injective.comp s.symm.injective⟩
    rw [hc]; decide
  · obtain ⟨e⟩ := he
    let f : A ≃* Matrix.PSL3Two.SL := e.trans Matrix.PSL3Two.equiv.symm
    let S := Matrix.PSL3Two.MarkedAutomorphisms.diagram.fixedSubgroup
    let s : S ≃* Equiv.Perm (Fin 3) := Matrix.PSL3Two.PairedGraphInputs.fixedEquivSymmetricThree
    refine ⟨center_trivial_of_equiv f Matrix.PSL3Two.center_eq_bot,?_,
      Matrix.PSL3Two.Automorphisms.outer_sl_isTwoGroup.of_equiv (MulAut.outerCongr f).symm,
      f.symm.toMonoidHom.comp (S.subtype.comp s.symm.toMonoidHom),
      f.symm.injective.comp (S.subtype_injective.comp s.symm.injective)⟩
    rw [Nat.card_congr f.toEquiv,Matrix.PSL3Two.card_SL]
    decide

/-- Split the faithful nine in the literal action quotient along the selected
Thompson factor and its centralizer. Both intersections have order three. -/
theorem reduced_thompson_factor_nine_split
    {D : Type*} [Group D] [Finite D]
    (q : D →* Q) (hq : Function.Surjective q) (hr : primeRank 3 D ≤ 2)
    (P A : Subgroup Q) [IsElementaryAbelian 3 P]
    (hP : Nat.card P = 9) (hn : P ≤ normalizer (A : Set Q))
    (hm : Nonempty (A ≃* Equiv.Perm (Fin 3)) ∨
      A.Normal ∧ (Nonempty (A ≃* alternatingGroup (Fin 5)) ∨
        Nonempty (A ≃* Matrix.PSL3Two.PSL))) :
    P = (P ⊓ A) ⊔ (P ⊓ centralizer (A : Set Q)) ∧
      Nat.card (P ⊓ A : Subgroup Q) = 3 ∧
      Nat.card (P ⊓ centralizer (A : Set Q) : Subgroup Q) = 3 ∧
      Disjoint (P ⊓ A) (P ⊓ centralizer (A : Set Q)) := by
  obtain ⟨hz,hcard,ho,j,hj⟩ := small_thompson_factor_geometry A
    (hm.imp id fun hh => hh.2)
  exact elementary_nine_split_at_small_factor q hq hr P A hP hn hz hcard ho j hj


/-- The actual nine splits into two cubics, and the marked point cubic
projects faithfully to each. All subgroups and projections use the given
ambient carrier and its literal multiplication map. -/
@[expose] def CubicFactorSplit (P A L B : Subgroup Q) : Prop :=
  P = (P ⊓ A) ⊔ (P ⊓ centralizer (A : Set Q)) ∧
    Nat.card (P ⊓ A : Subgroup Q) = 3 ∧
    Nat.card (P ⊓ centralizer (A : Set Q) : Subgroup Q) = 3 ∧
    Disjoint (P ⊓ A) (P ⊓ centralizer (A : Set Q)) ∧
    Nat.card B = 3 ∧ ¬ L ≤ A ∧ ¬ L ≤ centralizer (A : Set Q) ∧
    Disjoint B A ∧ Disjoint B (centralizer (A : Set Q)) ∧
    ∃ hBP : B ≤ P,
      ∃ e : (P ⊓ A : Subgroup Q) × (P ⊓ centralizer (A : Set Q) : Subgroup Q) ≃* P,
        (∀ a c, (e (a,c) : Q) = (a : Q) * (c : Q)) ∧
        Function.Injective ((MonoidHom.fst _ _).comp
          (e.symm.toMonoidHom.comp (inclusion hBP))) ∧
        Function.Injective ((MonoidHom.snd _ _).comp
          (e.symm.toMonoidHom.comp (inclusion hBP)))

/-- A literal cubic supplement supplies the split and faithful projections in its action image. -/
theorem cubic_factor_split_of_lift
    {D : Type*} [Group D] [Finite D]
    (q : D →* Q) (hq : Function.Surjective q) (hr : primeRank 3 D ≤ 2)
    (E N : Subgroup D) [IsElementaryAbelian 3 E]
    (x : D) (hx : orderOf x = 3) (hxE : zpowers x ≤ E)
    (hg : zpowers x ⊔ N.pCoreIn 2 = N) (hpN : IsPPerfect 2 N)
    (hne : N.map q ≠ ⊥) (hc : Nat.card (E.map q) = 9)
    (A : Subgroup Q) (hNA : N.map q ≤ normalizer (A : Set Q))
    (hEA : E.map q ≤ normalizer (A : Set Q))
    (hnot : ¬ E.map q ≤ normalizer (N.map q : Set Q))
    (hm : Nonempty (A ≃* Equiv.Perm (Fin 3)) ∨
      A.Normal ∧ (Nonempty (A ≃* alternatingGroup (Fin 5)) ∨
        Nonempty (A ≃* Matrix.PSL3Two.PSL))) :
    CubicFactorSplit (E.map q) A (N.map q) ((zpowers x).map q) := by
  let : IsElementaryAbelian 3 (E.map q) := IsElementaryAbelian.map q
  obtain ⟨hs,hcA,hcC,hd⟩ := reduced_thompson_factor_nine_split q hq hr (E.map q) A hc hEA hm
  have hxq : q x ≠ 1 := cubic_image_ne_one_of_twoPerfect q N hpN x hg hne
  have ho : orderOf (q x) = 3 := orderOf_eq_prime
    (by rw [←map_pow,←hx,pow_orderOf_eq_one,map_one]) hxq
  have hBcard : Nat.card ((zpowers x).map q) = 3 := by
    rw [MonoidHom.map_zpowers,Nat.card_zpowers,ho]
  have hBP : (zpowers x).map q ≤ E.map q := map_mono hxE
  have hgen : (zpowers x).map q ⊔ (N.pCoreIn 2).map q = N.map q := by
    rw [←Subgroup.map_sup,hg]
  have hp : IsPPerfect 2 (N.map q) := hpN.of_surjective (q.subgroupMap N)
    (q.subgroupMap_surjective N)
  obtain ⟨hnA,hnC,hdA,hdC⟩ := cubic_disjoint_factors_of_nine_not_normalizing
    (E.map q) A (N.map q) ((zpowers x).map q) ((N.pCoreIn 2).map q)
    hs hcA hcC hBcard hBP hgen hp ((isPGroup_pCoreIn 2 N).map q) hNA hnot
  refine ⟨hs,hcA,hcC,hd,hBcard,hnA,hnC,hdA,hdC,hBP,?_⟩
  exact exists_faithful_projections_of_split_disjoint (E.map q) (E.map q ⊓ A)
    (E.map q ⊓ centralizer (A : Set Q)) ((zpowers x).map q) hs hd
    (inf_le_right.trans (le_centralizer_iff.mpr inf_le_right)) hBP
    (hdA.mono_right inf_le_right) (hdC.mono_right inf_le_right)

open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter13.Section08.Components Swapped Swapped.LinearTwo ModuleAlternatives
open Chapter15.Section03.AbelianAmalgam
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Representation Representation.BinaryOffender Stellmacher
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The same original Y and I₀ supply both actual cubic factors. The point
cubic projects faithfully onto both, excluding source cases (a) and (b). -/
theorem local_nonnormal_component_weakClosure_cubic_split
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I K : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hKI : K ≤ I) (hK : (K.subgroupOf I).IsCComponent)
    (hnormal : ¬ (K.subgroupOf I).Normal) :
    ∃ c : CriticalPath (L := L) F, c.RankSelection ∧ c.Uα ≤ F.Ri L 1 ∧
      Nat.card (star F c.Uα) = 2 ∧
      let P := F.Vi 1 ⊔ c.Zα
      let J := F.Li L 1 ⊔ (T : Subgroup G)
      let R := F.H.pCoreIn 2 ⊔ conjugateSpanBy c.Uα J
      let Y := (F.H.pCoreIn 2 ⊔ c.Qα) ⊔ R
      let I₀ := J ⊔ Y
      let W₀ := ChapterE.indexedWeakClosure V R 0
      IsElementaryAbelian 2 P ∧ Nat.card P = 4 ∧ P ≤ F.U ⊓ c.Uα ∧
      R ≤ (T : Subgroup G) ∧ J ≤ normalizer (R : Set G) ∧
      R ≤ normalizer (P : Set G) ∧ Chapter1.IsSylowIn 2 R Y ∧
      Y ⊓ centralizer (P : Set G) = Y.pCoreIn 2 ∧
      Nonempty (Y ⧸ pCore 2 Y ≃* Equiv.Perm (Fin 3)) ∧
      V ≤ W₀ ∧ W₀ ≤ R ∧ I₀ ≤ normalizer (W₀ : Set G) ∧
      IsTwoLocal (normalizer (W₀ : Set G)) ∧ normalizer (W₀ : Set G) ≠ ⊤ ∧
      I₀ = J ⊔ c.Qα ∧ HasCharacteristicTwo I₀ ∧
      IsSQTK KnownSimple.IsKnownSimple I₀ ∧
      IsPReduced 2 ((conjugateSpanBy (F.Vi 1) I₀).subgroupOf I₀) ∧
      P ≤ conjugateSpanBy (F.Vi 1) I₀ ∧ conjugateSpanBy (F.Vi 1) I₀ ≤ W₀ ∧
      ⁅conjugateSpanBy (F.Vi 1) I₀,elementaryAbelianMaxJ (T : Subgroup G)⁆ ≠ ⊥ ∧
      letI : ((conjugateSpanBy (F.Vi 1) I₀).subgroupOf I₀).Normal :=
        normal_subgroupOf_of_le_normalizer (le_normalizer_conjugateSpanBy _ _)
      let q := QuotientGroup.mk'
        (centralizer ((conjugateSpanBy (F.Vi 1) I₀).subgroupOf I₀ : Set I₀))
      (elementaryAbelianMaxJ (⊤ : Subgroup I₀)).map q ≠ ⊥ ∧
      ¬ (((F.Li L 1).subgroupOf I₀).map q).IsSubnormal ∧
        ((F.Li L 1).subgroupOf I₀).map q ≠ ⊥ ∧
        ¬ F.H.pCoreIn 2 ⊔ c.Qα ≤ normalizer (F.Li L 1 : Set G) ∧
        ¬ F.H.pCoreIn 2 ⊔ c.Qα ≤ normalizer (L : Set G) ∧
        Y ≤ normalizer ((pResidual 2 (F.Li L 1 ⊓ centralizer (P : Set G) : Subgroup G)).map
          (F.Li L 1 ⊓ centralizer (P : Set G)).subtype : Set G) ∧
        let RY := (pResidual 2 (F.Li L 1 ⊓ centralizer (P : Set G) : Subgroup G)).map
          (F.Li L 1 ⊓ centralizer (P : Set G)).subtype
        RY ⊔ (F.Li L 1).pCoreIn 2=F.Li L 1 ∧
          ∃ l : F.H, (l:G) ∈ RY ∧ orderOf (l:G)=3 ∧
            zpowers (l:G) ⊔ (F.Li L 1).pCoreIn 2=F.Li L 1 ∧
            ∃ y ∈ F.H.pCoreIn 2 ⊔ c.Qα, orderOf y = 3 ∧ Commute (l : G) y ∧
              IsElementaryAbelian 3 (zpowers y ⊔ zpowers (l : G) : Subgroup G) ∧
              Nat.card (zpowers y ⊔ zpowers (l : G) : Subgroup G) = 9 ∧
              Nat.card (((zpowers y ⊔ zpowers (l : G)).subgroupOf I₀).map q) = 9 ∧
              J ⊔ (zpowers y ⊔ zpowers (l : G)) = I₀ ∧
              ¬ ((zpowers y ⊔ zpowers (l : G)).subgroupOf I₀).map q ≤
                normalizer (((F.Li L 1).subgroupOf I₀).map q : Set _) ∧
              ∃ A : Subgroup _, A ≤ (elementaryAbelianMaxJ (⊤ : Subgroup I₀)).map q ∧
                (A.subgroupOf ((elementaryAbelianMaxJ (⊤ : Subgroup I₀)).map q)).Normal ∧
                A.IsSubnormal ∧
                (Nonempty (A ≃* Equiv.Perm (Fin 3)) ∨
                  A.Normal ∧ (Nonempty (A ≃* alternatingGroup (Fin 5)) ∨
                    Nonempty (A ≃* Matrix.PSL3Two.PSL))) ∧
                pResidual 2 (I₀ ⧸ centralizer
                  ((conjugateSpanBy (F.Vi 1) I₀).subgroupOf I₀ : Set I₀)) ≤ normalizer (A : Set _) ∧
                ((F.Li L 1).subgroupOf I₀).map q ≤ normalizer (A : Set _) ∧
                ((zpowers y ⊔ zpowers (l : G)).subgroupOf I₀).map q ≤
                  normalizer (A : Set _) ∧
                CubicFactorSplit (((zpowers y ⊔ zpowers (l : G)).subgroupOf I₀).map q) A
                  (((F.Li L 1).subgroupOf I₀).map q) (((zpowers (l : G)).subgroupOf I₀).map q) := by
  obtain ⟨c,hs,hR,ha,hE,hfour,hplane,hRT,hJR,hRN,hSylow,hcore,he,hVW,hWR,hIW,
    hlocal,hproper,hIeq,hcharI,hsqtk,hred,hPVI,hVIW,hmove,hJplus,hsub,hne,hYn,hescape,hres,hgen,
    l,hl,hl3,hlgen,y,hy,hy3,hly,hE9,hcard,hplus,hIgen,hplusNot,
    A,hAJ,hAn,hAsub,hmodel,hresA,hLA,hPA⟩ :=
    local_nonnormal_component_weakClosure_factors d h hab structural previous
      faithful earlier I K hI hKI hK hnormal
  let J := F.Li L 1 ⊔ (T : Subgroup G)
  let R := F.H.pCoreIn 2 ⊔ conjugateSpanBy c.Uα J
  let Y := (F.H.pCoreIn 2 ⊔ c.Qα) ⊔ R
  let I₀ := J ⊔ Y
  let W := conjugateSpanBy (F.Vi 1) I₀
  let : (W.subgroupOf I₀).Normal := normal_subgroupOf_of_le_normalizer
    (le_normalizer_conjugateSpanBy _ _)
  let q := QuotientGroup.mk' (centralizer (W.subgroupOf I₀ : Set I₀))
  let E := zpowers y ⊔ zpowers (l : G)
  let Eplus := (E.subgroupOf I₀).map q
  let Bplus := ((zpowers (l : G)).subgroupOf I₀).map q
  let D := (F.Li L 1).subgroupOf I₀
  let Dplus := D.map q
  refine ⟨c,hs,hR,ha,hE,hfour,hplane,hRT,hJR,hRN,hSylow,hcore,he,hVW,hWR,hIW,
    hlocal,hproper,hIeq,hcharI,hsqtk,hred,hPVI,hVIW,hmove,hJplus,hsub,hne,hYn,hescape,hres,hgen,
    l,hl,hl3,hlgen,y,hy,hy3,hly,hE9,hcard,hplus,hIgen,hplusNot,
    A,hAJ,hAn,hAsub,hmodel,hresA,hLA,hPA,?_⟩
  let : IsElementaryAbelian 3 E := hE9
  have hEI : E ≤ I₀ := le_sup_right.trans_eq hIgen
  let : IsElementaryAbelian 3 (E.subgroupOf I₀) := IsElementaryAbelian.subgroupOf hEI
  have hLI : F.Li L 1 ≤ I₀ := le_sup_left.trans le_sup_left
  have hpowL : zpowers (l : G) ≤ F.Li L 1 := le_sup_left.trans_eq hlgen
  have hlI : (l : G) ∈ I₀ := hLI (hpowL (mem_zpowers _))
  let lI : I₀ := ⟨l,hlI⟩
  have hpow : (zpowers (l : G)).subgroupOf I₀ = zpowers lI := by
    apply map_injective I₀.subtype_injective
    rw [map_subgroupOf_eq_of_le (hpowL.trans hLI),MonoidHom.map_zpowers]
    rfl
  have hgenD : zpowers lI ⊔ D.pCoreIn 2 = D := by
    rw [show D = (F.Li L 1).subgroupOf I₀ from rfl,
      pCoreIn_subgroupOf 2 _ I₀ hLI,←hpow,
      ←subgroupOf_sup (hpowL.trans hLI) ((pCoreIn_le 2 _).trans hLI),hlgen]
  have hpD : IsPPerfect 2 D :=
    (show IsPPerfect 2 (F.Li L 1) from isPPerfect_embedded_pResidual 2 _).of_surjective
      (subgroupOfEquivOfLe hLI).symm.toMonoidHom (subgroupOfEquivOfLe hLI).symm.surjective
  have hxE : zpowers lI ≤ E.subgroupOf I₀ := by
    rw [←hpow]
    exact comap_mono le_sup_right
  have ht := cubic_factor_split_of_lift q (QuotientGroup.mk'_surjective _)
    (hsqtk.stronglyQuasithin 3 (by decide) (by decide))
    (E.subgroupOf I₀) D lI ((I₀.orderOf_coe lI).symm.trans hl3) hxE hgenD hpD
    hne hplus A hLA hPA hplusNot hmodel
  simpa only [←hpow] using ht

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
