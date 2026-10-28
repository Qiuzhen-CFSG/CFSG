module
public import Theory.GroupTheory.CComponent.ExternalPrimeSelection
public import Theory.GroupAction.SubgroupPerfectFixedCover
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockMSCoreComplete
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryTorus
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.SourceOrbits
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete
public import CFSG.Quasithin.ChapterA.Section03.SourceComponents.Generation

/-!
# Selecting the original nonblock secondary component

The original torus of order 2ⁿ−1 acts faithfully on the root and trivially
on K₂/O₂(K₂). Coprime fixed-point lifting supplies a commuting pair of
prime-order elements, one in K₂ and one outside the root centralizer.
The source component-layer theorem places K₂ in that layer. The rank-two
bound then forces a prime-divisible component to contain all of K₂:
a proper normal intersection lies in O₂(K₂), and would leave a disjoint
elementary plane acting on the component. The same argument for conjugates
makes the selected component normal in the original root normalizer.

The original marked parabolics give K=⟨L,K₂⟩, so T cannot normalize K₂;
the selected component therefore properly contains it. The actual
SecondarySourceData constructor now uses this chosen component, retaining
the original subgroup inclusions and normalQuotientAction.

The MS witness and simultaneous parabolic/Sylow markings remain earlier
inputs. Quotient quasisimplicity, the 4.3.14 radical-normalizer/core bounds,
and the terminal representation contradiction are still owned by
qt-d-1222-rankone-uniqueness-nonblock. This proves component selection
conditionally on the earlier MS geometry, not the final nonblock exclusion.
Source: Aschbacher--Smith, original 4.3.12(1)--13, p.617; 1.2.1--2,
pp.504--505; A.1.27, p.26, for the rank obstruction.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {c : SourceConfiguration T L} {n : ℕ} {d : MSData c n}

private theorem quotient_sqtk {X : Type*} [Group X] [Finite X]
    (h : IsSQTK KnownSimple.IsKnownSimple X) :
    IsSQTK KnownSimple.IsKnownSimple (X ⧸ pCore 2 X) := by
  refine ⟨?_,h.isKGroup.quotient _⟩
  intro p hp ho
  let : Fact p.Prime := ⟨hp⟩
  exact (primeRank_quotient_le_of_isTwoGroup p ho (pCore 2 X) pCore_isPGroup).trans
    (h.stronglyQuasithin p hp ho)

private theorem layer_eq_residual {X : Type*} [Group X] [Finite X]
    (h : IsSQTK KnownSimple.IsKnownSimple X) :
    cComponentLayer X = solvableResidual X :=
  Chapter1.Section02.proposition_1_2_1_one_of_A_3_9
    (fun _Y _ _ hY hO =>
      ChapterA.Section03.SourceComponents.generation
        (fun Z _ _ => ChapterA.Section02.theoremA_knownSimple (G := Z))
        (ChapterA.Section03.SourceComponents.source_model_inputs_of_theoremC
          (fun Z _ _ => ChapterA.Section02.theoremC_knownSimple (G := Z))) hY hO)
    (quotient_sqtk h)

/-- The actual root torus selects a normal component containing the complete
secondary residual, including its two-core. -/
theorem RootCoordinates.exists_secondary_normal_component (m : RootCoordinates d)
    (hn : 1 < n) (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L) :
    ∃ B : Subgroup (rootNormalizer c), B.IsCComponent ∧ B.Normal ∧
      secondary c ≤ B.map (rootNormalizer c).subtype ∧
      B.map (rootNormalizer c).subtype ≤ Subgroup.centralizer (root c : Set G) := by
  classical
  let N := rootNormalizer c
  let C := (centralizer (root c : Set G)).subgroupOf N
  let : C.Normal := normal_subgroupOf_of_le_normalizer
    (normalizer_le_normalizer_centralizer (root c))
  have hSN : secondary c ≤ N :=
    secondary_centralizes_root.trans (Subgroup.centralizer_le_normalizer _)
  let S := (secondary c).subgroupOf N
  let eS : S ≃* secondary c := subgroupOfEquivOfLe hSN
  let : Group.IsPerfect (secondary c) := by
    change Group.IsPerfect ((solvableResidual (rootCentralizer c)).map (rootCentralizer c).subtype)
    exact Group.IsPerfect.map _
  let : Group.IsPerfect S := Group.IsPerfect.ofSurjective
    (f := eS.symm.toMonoidHom) eS.symm.surjective
  have hF : 3 < Nat.card d.field.Carrier := by
    rw [d.field.card_eq,d.degree_eq]
    have hh := Nat.pow_le_pow_right (by decide : 0 < 2) (show 2 ≤ n by omega)
    norm_num at hh
    omega
  let : IsSimpleGroup PSL(2,d.field.Carrier) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hF
  let : IsSimpleGroup SL(2,d.field.Carrier) := (Theory.PSL2.sl2QuotientEquiv d.field.Carrier).isSimpleGroup
  let : IsSimpleGroup (secondary c ⧸ pCore 2 (secondary c)) := (m.secondaryCoreEquiv hn).isSimpleGroup
  let : IsSimpleGroup (S ⧸ pCore 2 S) :=
    (QuotientGroup.congr _ _ eS (pCore_map_iso 2 eS)).isSimpleGroup
  have hSC : S ≤ C := comap_mono secondary_centralizes_root
  have hN := EndgameSieve.rootNormalizer_sqtk c D h
  have hSlayer : S.subgroupOf C ≤ cComponentLayer C := by
    let e := subgroupOfEquivOfLe hSC
    let : Group.IsPerfect (S.subgroupOf C) := Group.IsPerfect.ofSurjective
      (f := e.symm.toMonoidHom) e.symm.surjective
    rw [layer_eq_residual (hN.subgroup C)]
    exact le_solvableResidual_of_isPerfect _
  have hq : 2 < 2 ^ n :=
    (show 2 = 2 ^ 1 by decide).trans_lt (Nat.pow_lt_pow_right (by decide) hn)
  obtain ⟨p,hp,hd⟩ := Nat.exists_prime_and_dvd (by omega : 2 ^ n - 1 ≠ 1)
  let : Fact p.Prime := ⟨hp⟩
  have hodd : Odd (2 ^ n - 1) := by
    rw [Nat.odd_iff]
    have hmod := Nat.mod_eq_zero_of_dvd (dvd_pow_self 2 (by omega : n ≠ 0))
    omega
  have hpo : Odd p := hodd.of_dvd_nat hd
  have hdQ : p ∣ Nat.card (secondary c ⧸ pCore 2 (secondary c)) := by
    rw [Nat.card_congr (m.secondaryCoreEquiv hn).toEquiv,
      BenderSuzuki.External.huppert614_card_specialLinearGroup,d.field.card_eq,d.degree_eq]
    exact dvd_mul_of_dvd_right (hd.trans (Nat.sub_one_dvd_pow_sub_one (2 ^ n) 2)) _
  have hdS : p ∣ Nat.card S := by
    rw [Nat.card_congr eS.toEquiv]
    exact hdQ.trans (card_dvd_of_surjective (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _))
  have hdE : p ∣ Nat.card (cComponentLayer C) := by
    have hdiv := card_dvd_of_le hSlayer
    rw [Nat.card_congr (subgroupOfEquivOfLe hSC).toEquiv] at hdiv
    exact hdS.trans hdiv
  obtain ⟨Y,_,hY,hYK,hYN,hfaith,_,hmove,_⟩ := m.exists_moving_root_torus hn
  have hYS : Y ≤ normalizer (secondary c : Set G) :=
    (le_inf (hYK.trans (map_subtype_le _)) hYN).trans original_root_normalizer_normalizes_secondary
  have hcop : Nat.Coprime (Nat.card Y) (Nat.card (pCore 2 (secondary c))) := by
    obtain ⟨j,hj⟩ := (pCore_isPGroup (p := 2) (G := secondary c)).exists_card_eq
    rw [hY,hj]
    exact hodd.coprime_two_right.pow_right j
  let : Group.IsNilpotent (pCore 2 (secondary c)) := pCore_isPGroup.isNilpotent
  have hsurj := centralizer_quotient_surjective_of_solvable_coprime (secondary c) Y
    (pCore 2 (secondary c)) hYS inferInstance hcop hmove
  have hdFix : p ∣ Nat.card (secondary c ⊓ centralizer (Y : Set G) : Subgroup G) :=
    hdQ.trans (card_dvd_of_surjective _ hsurj)
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' p hdFix
  obtain ⟨y,hy⟩ := exists_prime_orderOf_dvd_card' p (hY ▸ hd)
  let aN : N := ⟨a,hSN a.property.1⟩
  let yN : N := ⟨y,hYN y.property⟩
  have haN : orderOf aN = p := (orderOf_injective N.subtype N.subtype_injective aN).symm.trans
    ((orderOf_injective (secondary c ⊓ centralizer (Y : Set G) : Subgroup G).subtype
      (secondary c ⊓ centralizer (Y : Set G) : Subgroup G).subtype_injective a).trans ha)
  have hyN : orderOf yN = p := (orderOf_injective N.subtype N.subtype_injective yN).symm.trans
    ((orderOf_injective Y.subtype Y.subtype_injective y).trans hy)
  have hyC : yN ∉ C := by
    intro hyC
    have hy1 : (y : G) = 1 := mem_bot.mp (hfaith ▸ ⟨y.property,hyC⟩)
    have hy1' : y = 1 := Subtype.ext hy1
    rw [hy1',orderOf_one] at hy
    exact hp.ne_one hy.symm
  have hay : Commute aN yN := by
    apply Subtype.ext
    exact (mem_centralizer_iff.mp a.property.2 y y.property).symm
  obtain ⟨B,hBC,hB,hSB,hBn⟩ := ExternalPrimeSelection.normal_component_of_external_prime
    hpo C S hSC hdE (hN.stronglyQuasithin p hp hpo) yN hyN hyC
    aN a.property.1 haN hay
    (fun B hB => Chapter1.Section02.proposition_1_2_1_three_orbit_source (quotient_sqtk hN) hB)
  have hBN : B.IsCComponent := by
    have hh := hB.map_subtype (inferInstance : C.Normal).isSubnormal
    rwa [map_subgroupOf_eq_of_le hBC] at hh
  refine ⟨B,hBN,hBn,?_,?_⟩
  · have hh := map_mono (f := N.subtype) hSB
    rwa [map_subgroupOf_eq_of_le hSN] at hh
  · rintro x ⟨b,hb,rfl⟩
    exact hBC hb

open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open Matrix.PSL3.LinearThree

/-- The source component selected from the original MS and parabolic geometry. -/
noncomputable def MSData.sourceComponent (d : MSData c n) (hn : 1 < n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hL : (L.subgroupOf (K c)).map (linearThreeActor d.model) = lineLocalSL d.field.Carrier)
    (hSL : ((S c ⊓ L).subgroupOf (K c)).map (linearThreeActor d.model) = unipotentSL d.field.Carrier) :
    Subgroup (rootNormalizer c) :=
  ((Classical.choice (d.rootCoordinates_of_marked_parabolic hL hSL)).exists_secondary_normal_component
    hn D h).choose

/-- The chosen source component is normal, properly contains K₂, and
centralizes the actual root. Properness uses the original generation K=⟨L,K₂⟩. -/
theorem MSData.sourceComponent_spec (d : MSData c n) (hn : 1 < n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hL : (L.subgroupOf (K c)).map (linearThreeActor d.model) = lineLocalSL d.field.Carrier)
    (hSL : ((S c ⊓ L).subgroupOf (K c)).map (linearThreeActor d.model) = unipotentSL d.field.Carrier) :
    let B := d.sourceComponent hn D h hL hSL
    B.IsCComponent ∧ B.Normal ∧
      secondary c < B.map (rootNormalizer c).subtype ∧
      B.map (rootNormalizer c).subtype ≤ Subgroup.centralizer (root c : Set G) := by
  let m := Classical.choice (d.rootCoordinates_of_marked_parabolic hL hSL)
  obtain ⟨hB,hBn,hsec,hcent⟩ := (m.exists_secondary_normal_component hn D h).choose_spec
  refine ⟨hB,hBn,?_,hcent⟩
  exact secondary_lt_component_of_generation D (m.original_sup_secondary hn D hL.ge)
    _ hBn hsec

/-- The actual component selection discharges the component, normality and
containment premises of the secondary-source constructor. The remaining
4.3.12--14 bounds and quotient quasisimplicity stay explicit for this owner. -/
theorem MSData.exists_secondarySourceData_of_sourceComponent
    (d : MSData c n) (hn : 1 < n) (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hL : (L.subgroupOf (K c)).map (linearThreeActor d.model) = lineLocalSL d.field.Carrier)
    (hSL : ((S c ⊓ L).subgroupOf (K c)).map (linearThreeActor d.model) = unipotentSL d.field.Carrier)
    (hBq : IsQuasisimple (d.sourceComponent hn D h hL hSL ⧸
      pCore 2 (d.sourceComponent hn D h hL hSL)))
    (henlarged : ((d.sourceComponent hn D h hL hSL).map (rootNormalizer c).subtype ⊔
      (T : Subgroup G)).pCoreIn 2 ≤ R₂ c)
    (hnorm : normalizer (R₂ c : Set G) ≤ c.H ⊓ normalizer (secondary c : Set G))
    (henlarges : secondary c < ((d.sourceComponent hn D h hL hSL).map
      (rootNormalizer c).subtype).pCoreIn 2 ⊔ secondary c) :
    ∃ s : SecondarySourceData c n,
      s.component = d.sourceComponent hn D h hL hSL ∧ s.torus ≤ K c ∧
      Q c ⊓ Subgroup.centralizer (s.torus : Set G) = ⊥ ∧
      ((Q c).subgroupOf (rootNormalizer c)).map s.action ⊔
        ⁅((R₂ c).subgroupOf (rootNormalizer c)).map s.action,
          ((secondary c).subgroupOf (rootNormalizer c)).map s.action⁆ =
        ((R₂ c).subgroupOf (rootNormalizer c)).map s.action := by
  obtain ⟨hB,hBn,hsec,_⟩ := d.sourceComponent_spec hn D h hL hSL
  exact d.exists_secondarySourceData_of_marked_parabolic hn D hL hSL
    (d.sourceComponent hn D h hL hSL) hB hBn hBq hsec.le
    (d.joinCore_eq hn) henlarged hnorm henlarges

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
