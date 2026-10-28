module

public import CFSG.Quasithin.Chapter15.Section04.LocalIdentification.ComponentRecognition
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.Quotient
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Residual
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.OffenderTransfer
public import CFSG.Quasithin.ChapterF.Section06.Elementary.Rigidity.Local
public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.SourceTheorems
public import CFSG.Quasithin.ChapterA.Section01
public import Theory.GroupTheory.SpecificGroups.SLTwoPermThree
public import FeitThompson.FinalTheorem

/-!
# Source 15.4.21: equal cores use solvable FF structure

The argument retains the equal-core branch. Equal
embedded local two-cores are the ambient two-core, so the action quotient
has a cyclic Sylow two-subgroup. Transfer and the Odd Order Theorem make
that quotient solvable. B.1.8 then expresses its actual offender subgroup
as a product of SL₂(2)'s. Both factor images lie in its abelian derived
subgroup, so the cross-commutator lies in O₂(I). Residual characteristicness
lifts this to normality. For unequal cores the existing complete FF/F.6.18
comparison gives the same commutator bound.

The literal d.J = J(T) remains an earlier-source identity; its existing
producer is qt-15-04-local-setup. The other unproved inputs are universal
F.6.18 (qt-f-06) and corrected B.5.1/adequate B.5.6
(qt-b05-quasisimple, qt-b05-general-classification). The final endgame also
retains source 1.1.5 through the existing qt-1-01 producer.
No normality, recognition, Baumann or unequal-core premise is added.

Source: Aschbacher–Smith, 15.4.21, printed pp.1164–1165; B.1.8, p.70.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
open CFSG.Quasithin
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison

namespace CFSG.Quasithin.Chapter15.Section04.SourceRecognition.TwoCore
universe u v

private theorem solvable_of_cyclic_sylow_two
    {H : Type u} [Group H] [Finite H] (P : Sylow 2 H) (hP : IsCyclic P) :
    Group.IsSolvable H := by
  by_cases heven : 2 ∣ Nat.card H
  · obtain ⟨N, hN, hodd, hquot⟩ := ChapterA.lemma_A_1_38 P
      ((Nat.minFac_eq_two_iff _).mpr heven) hP
    let : N.Normal := hN
    let : Group.IsSolvable N := odd_order_theorem N (Nat.coprime_two_left.mp hodd)
    let := hquot.isNilpotent
    exact (Group.isSolvable_iff_subgroup_quotient N).mpr ⟨inferInstance, inferInstance⟩
  · exact odd_order_theorem H
      (Nat.not_even_iff_odd.mp (fun h => heven (even_iff_two_dvd.mp h)))

/-- Equal embedded local cores make the actual action quotient solvable.
There is no use of the classification lists in this branch. -/
theorem quotient_solvable_of_equal_cores
    {H : Type u} [Group H] [Finite H] (A B : Subgroup H)
    (triple : ChapterF.IsGoldschmidtTriple A B)
    (heq : (pCore 2 A).map A.subtype = (pCore 2 B).map B.subtype) :
    Group.IsSolvable (H ⧸ pCore 2 H) := by
  let C := (pCore 2 A).map A.subtype
  have hn : C.Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_unique
    rw [← triple.generated]
    refine sup_le triple.left_core_normalized ?_
    change B ≤ normalizer (((pCore 2 A).map A.subtype) : Set H)
    rw [heq]
    exact triple.symm.left_core_normalized
  have hCQ : C ≤ pCore 2 H := le_sSup ⟨hn, pCore_isPGroup.map A.subtype⟩
  have hQA : pCore 2 H ≤ A := triple.twoCore_isGreatest.1.1.trans inf_le_left
  have hQC : pCore 2 H ≤ C := by
    rw [← map_subgroupOf_eq_of_le hQA]
    exact map_mono (show (pCore 2 H).subgroupOf A ≤ pCore 2 A from
      le_sSup ⟨inferInstance, pCore_isPGroup.comap_subtype⟩)
  have hC : C = pCore 2 H := le_antisymm hCQ hQC
  obtain ⟨P, hP⟩ := triple.intersection_sylow
  let S := P.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H))
  have hcard : Nat.card S = 2 := by
    change Nat.card ((P : Subgroup H).map (QuotientGroup.mk' (pCore 2 H))) = 2
    rw [← relIndex_ker, QuotientGroup.ker_mk', ← hP, ← hC]
    exact triple.left_core_index
  have hd : Nat.card S ∣ 2 := by rw [hcard]
  exact solvable_of_cyclic_sylow_two S (isCyclic_of_card_dvd_prime hd)

/-- Solvable FF structure makes the derived subgroup of the literal offender
actor abelian; the equivalence comes from the proved B.1.8. -/
theorem offender_derived_abelian_of_solvable
    {D : Type u} [Group D] [Finite D]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V)
    (hsolv : Group.IsSolvable D) (hcore : pCore 2 D = ⊥)
    (hfaith : Function.Injective ρ) (hff : IsFFModule ρ) :
    IsMulCommutative (_root_.commutator (offenderSubgroup ρ)) := by
  obtain ⟨d⟩ := ChapterB.solvableFFStructure_nonempty ρ hsolv hcore hfaith hff
  obtain ⟨eSL⟩ := SLTwoPermThree.sl2Two_equiv_perm_three
  let e : offenderSubgroup ρ ≃* (Fin d.count → Equiv.Perm (Fin 3)) :=
    d.groupProduct.symm.trans (MulEquiv.piCongrRight fun i => (d.factorModel i).trans eSL)
  let alt := alternatingGroup (Fin 3)
  let : IsMulCommutative alt := alternatingGroup.isMulCommutative_of_card_le_three (by simp)
  let f (i : Fin d.count) : offenderSubgroup ρ →* Equiv.Perm (Fin 3) := {
    toFun x := e x i
    map_one' := congrFun e.map_one i
    map_mul' x y := congrFun (e.map_mul x y) i }
  have hmap (i : Fin d.count) :
      (_root_.commutator (offenderSubgroup ρ)).map (f i) ≤ alt := by
    rw [_root_.commutator_def, map_commutator]
    exact (commutator_mono le_top le_top).trans alternatingGroup.commutator_perm_le
  refine ⟨⟨fun x y => ?_⟩⟩
  apply Subtype.ext
  apply e.injective
  funext i
  change f i ((x : offenderSubgroup ρ) * y) = f i ((y : offenderSubgroup ρ) * x)
  rw [map_mul, map_mul]
  exact setLike_mul_comm (hmap i (mem_map_of_mem (f i) x.property))
    (hmap i (mem_map_of_mem (f i) y.property))

/-- The source commutator identities and actual Thompson image suffice in the
solvable branch. No whole-quotient identification is needed. -/
theorem cross_le_core_of_solvable
    {H : Type u} [Group H] [Finite H]
    (P : Sylow 2 H) (Z Y₁ Y₂ : Subgroup H)
    [IsElementaryAbelian 2 (moduleClosure Z)]
    (hC : centralizer (Z : Set H) = (P : Subgroup H))
    (hF : generalizedFitting H = pCore 2 H)
    (h₁ : Y₁ = ⁅Y₁, Stellmacher.elementaryAbelianMaxJ (P : Subgroup H)⁆)
    (h₂ : Y₂ = ⁅Y₂, Stellmacher.elementaryAbelianMaxJ (P : Subgroup H)⁆)
    (hZY : ⁅Z, Y₁⁆ ≠ ⊥)
    (hJ : (Stellmacher.elementaryAbelianMaxJ (P : Subgroup H)).map coreProjection ≤
      offenderGroup P Z hC)
    (hsolv : Group.IsSolvable (coreQuotient H)) : ⁅Y₂, Y₁⁆ ≤ pCore 2 H := by
  let N := offenderGroup P Z hC
  let : IsMulCommutative (_root_.commutator N) :=
    offender_derived_abelian_of_solvable (quotientAction P Z hC) hsolv
      coreQuotient_twoCore (quotientAction_injective P Z hC)
      (quotientAction_isFFModule P Z hC Y₁ hF h₁ hZY)
  have hmet : ⁅⁅N, N⁆, ⁅N, N⁆⁆ = ⊥ := by
    have he := congrArg (Subgroup.map N.subtype)
      (commutator_self_eq_bot_iff.mpr
        (inferInstance : IsMulCommutative (_root_.commutator N)))
    simpa only [map_commutator, map_subtype_commutator, Subgroup.map_bot] using he
  have hder (Y : Subgroup H)
      (hy : Y = ⁅Y, Stellmacher.elementaryAbelianMaxJ (P : Subgroup H)⁆) :
      Y.map coreProjection ≤ ⁅N, N⁆ := by
    have hn := factor_image_le_offenderGroup P Z hC Y hy hJ
    rw [hy, map_commutator]
    exact commutator_mono hn hJ
  have hm : (⁅Y₂, Y₁⁆).map (coreProjection (H := H)) = ⊥ := by
    apply le_bot_iff.mp
    rw [map_commutator, ← hmet]
    exact commutator_mono (hder Y₂ h₂) (hder Y₁ h₁)
  simpa only [coreProjection, QuotientGroup.ker_mk'] using
    (Subgroup.map_eq_bot_iff _).mp hm

/-- A generic two-core branch for the literal Goldschmidt triple. Equal cores
are handled by solvable FF theory; unequal cores use existing recognition. -/
theorem normal_factors_of_goldschmidt
    {H : Type u} [Group H] [Finite H] {K : GroupClass.{u}}
    (source618 : F618Universal K)
    (sourceB : FFAlternatives.ProjectiveLine.AdequateCompleteClassificationInput.{u,u} K)
    (hH : IsSQTK K H) (A B : Subgroup H)
    (triple : ChapterF.IsGoldschmidtTriple A B)
    (P : Sylow 2 H) (Z Y₁ Y₂ : Subgroup H)
    [IsElementaryAbelian 2 (moduleClosure Z)]
    (hC : centralizer (Z : Set H) = (P : Subgroup H))
    (hF : generalizedFitting H = pCore 2 H)
    (hgen : Y₁ ⊔ Y₂ ⊔ (P : Subgroup H) = ⊤)
    (h₁ : Y₁ = ⁅Y₁, Stellmacher.elementaryAbelianMaxJ (P : Subgroup H)⁆)
    (h₂ : Y₂ = ⁅Y₂, Stellmacher.elementaryAbelianMaxJ (P : Subgroup H)⁆)
    (hZY : ⁅Z, Y₁⁆ ≠ ⊥)
    (hJ : (Stellmacher.elementaryAbelianMaxJ (P : Subgroup H)).map coreProjection ≤
      offenderGroup P Z hC)
    (hp₁ : IsPPerfect 2 Y₁) (hp₂ : IsPPerfect 2 Y₂)
    (hn₁ : (P : Subgroup H) ≤ normalizer (Y₁ : Set H))
    (hn₂ : (P : Subgroup H) ≤ normalizer (Y₂ : Set H)) :
    Y₁.Normal ∧ Y₂.Normal := by
  have hc : ⁅Y₂, Y₁⁆ ≤ pCore 2 H := by
    by_cases heq : (pCore 2 A).map A.subtype = (pCore 2 B).map B.subtype
    · exact cross_le_core_of_solvable P Z Y₁ Y₂ hC hF h₁ h₂ hZY hJ
        (quotient_solvable_of_equal_cores A B triple heq)
    · obtain ⟨e⟩ := symmetricThreeProduct_quotient_of_goldschmidt source618 sourceB
        hH A B triple heq P Z Y₁ Y₂ hC hF hgen h₁ h₂ hZY hJ
      let := symmetricThreeProduct_derived_abelian
      let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
      have hk : q.ker = pCore 2 H := by
        ext x
        change e (QuotientGroup.mk' (pCore 2 H) x) = 1 ↔ x ∈ pCore 2 H
        rw [← e.map_one, e.injective.eq_iff]
        exact QuotientGroup.eq_one_iff x
      exact hk ▸ factor_commutator_le_kernel q Y₁ Y₂
        (Stellmacher.elementaryAbelianMaxJ (P : Subgroup H)) h₁ h₂
  have hQ : pCore 2 H ≤ (P : Subgroup H) := pCore_isPGroup.le_sylow_of_normal P
  have h₂₁ := (normalizes_factor_of_commutator_le (pCore 2 H) Y₁ Y₂
    pCore_isPGroup hp₁ (hQ.trans hn₁) hc).2
  have h₁₂ := (normalizes_factor_of_commutator_le (pCore 2 H) Y₂ Y₁
    pCore_isPGroup hp₂ (hQ.trans hn₂) (by rw [commutator_comm]; exact hc)).2
  constructor
  · apply normalizer_eq_top_iff.mp
    apply top_unique
    rw [← hgen]
    exact sup_le (sup_le Y₁.le_normalizer h₂₁) hn₁
  · apply normalizer_eq_top_iff.mp
    apply top_unique
    rw [← hgen]
    exact sup_le (sup_le h₁₂ Y₂.le_normalizer) hn₂

open CFSG.Quasithin.Chapter15.Section04.Source

/-- The actual source pair, with generation and both normal factors.
The source identity for d.J is retained explicitly for its existing producer. -/
theorem source_lemma_15_4_21
    {G : Type u} [Group G] [Finite G] {d : Geometry G}
    (h : LocalData d) (hG : IsSimpleQTKE CFSG.KnownSimple.IsKnownSimple G)
    (source618 : F618Universal.{u} CFSG.KnownSimple.IsKnownSimple)
    (sourceB : FFAlternatives.ProjectiveLine.AdequateCompleteClassificationInput.{u,u}
      CFSG.KnownSimple.IsKnownSimple)
    (hJsource : d.J = ChapterB.thompsonJ (d.T : Subgroup G) 0)
    (i j : Bool) (hF : generalizedFitting (d.I i j) = pCore 2 (d.I i j)) :
    ((d.X i).subgroupOf (d.I i j)).Normal ∧
      ((d.Y j).subgroupOf (d.I i j)).Normal ∧
      d.I i j = (d.X i ⊔ d.Y j) ⊔ d.T₀ := by
  let I := d.I i j
  let P := h.sylow i j
  let Z := d.Z.subgroupOf I
  let U := (d.X i).subgroupOf I
  let W := (d.Y j).subgroupOf I
  have hZI : d.Z ≤ I := h.Z_le.trans (d.T₀_le_I i j)
  have hUI : d.X i ≤ I := d.X_le_I i j
  have hWI : d.Y j ≤ I := d.Y_le_I i j
  have hPT : (P : Subgroup I).map I.subtype ≤ (d.T : Subgroup G) := by
    rw [h.sylow_image]
    exact d.T₀_le_T
  have hP : (P : Subgroup I) = d.T₀.subgroupOf I := by
    apply Subgroup.map_injective I.subtype_injective
    rw [h.sylow_image, map_subgroupOf_eq_of_le (d.T₀_le_I i j)]
  have hC : centralizer (Z : Set I) = (P : Subgroup I) :=
    centralizer_seed_subgroupOf I (d.T : Subgroup G) d.Z P d.T.isPGroup'
      hPT hZI h.centralizer_Z
  let : IsElementaryAbelian 2 d.Z := h.Z_elementary
  let : IsElementaryAbelian 2 Z := IsElementaryAbelian.subgroupOf hZI
  let := moduleClosure_elementary P Z hC hF
  have hJambient : d.J = Stellmacher.elementaryAbelianMaxJ (d.T : Subgroup G) :=
    hJsource.trans (ChapterB.thompsonJ_zero _)
  have hJT : (Stellmacher.elementaryAbelianMaxJ (P : Subgroup I)).map I.subtype = d.J := by
    rw [hJambient]
    apply thompson_sylow_image I (d.T : Subgroup G) P hPT
    rw [h.sylow_image, ← hJambient]
    exact h.J_le
  have hU : U = ⁅U, Stellmacher.elementaryAbelianMaxJ (P : Subgroup I)⁆ :=
    factor_commutator_subgroupOf I (d.X i) d.J _ hUI hJT (h.X_commutator i).symm
  have hW : W = ⁅W, Stellmacher.elementaryAbelianMaxJ (P : Subgroup I)⁆ :=
    factor_commutator_subgroupOf I (d.Y j) d.J _ hWI hJT (h.Y_commutator j).symm
  have hZU : ⁅Z, U⁆ ≠ ⊥ := by
    apply seed_factor_commutator_ne_bot_subgroupOf I d.Z (d.X i) hZI hUI
    intro hb
    apply h.X_outside i
    have hc := le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hb)
    rw [h.centralizer_Z] at hc
    exact hc.trans h.T_normalizes_Y
  have hJ : (Stellmacher.elementaryAbelianMaxJ (P : Subgroup I)).map coreProjection ≤
      offenderGroup P Z hC := by
    apply Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.thompson_image_le_offender
      (P : Subgroup I) (moduleClosure Z)
      ((moduleClosure_le_twoCore P Z hC hF).trans (pCore_isPGroup.le_sylow_of_normal P))
      coreProjection
      ((QuotientGroup.ker_mk' _).trans (moduleClosure_centralizer P Z hC).symm)
      (quotientAction P Z hC)
    exact quotientAction_apply P Z hC
  have hgen : U ⊔ W ⊔ (P : Subgroup I) = ⊤ := by
    rw [hP, ← subgroupOf_sup hUI hWI,
      ← subgroupOf_sup (sup_le hUI hWI) (d.T₀_le_I i j),
      ← d.I_eq_join i j, subgroupOf_self]
  have hpU : IsPPerfect 2 U := (h.X_perfect i).of_surjective
    (subgroupOfEquivOfLe hUI).symm.toMonoidHom (subgroupOfEquivOfLe hUI).symm.surjective
  have hpW : IsPPerfect 2 W := (h.Y_perfect j).of_surjective
    (subgroupOfEquivOfLe hWI).symm.toMonoidHom (subgroupOfEquivOfLe hWI).symm.surjective
  have hnU : (P : Subgroup I) ≤ normalizer (U : Set I) := by
    rw [← subgroupOf_normalizer_eq hUI, hP]
    exact subgroupOf_mono I (h.X_normalized i)
  have hnW : (P : Subgroup I) ≤ normalizer (W : Set I) := by
    rw [← subgroupOf_normalizer_eq hWI, hP]
    exact subgroupOf_mono I (h.Y_normalized j)
  obtain ⟨hUn, hWn⟩ := normal_factors_of_goldschmidt source618 sourceB
    (h.I_sqtk hG i j) ((d.G₁ i).subgroupOf I) ((d.G₂ j).subgroupOf I)
    (Chapter15.Section04.SourceRecognition.Source.source_triple h i j)
    P Z U W hC hF hgen hU hW hZU hJ hpU hpW hnU hnW
  exact ⟨hUn, hWn, d.I_eq_join i j⟩

/-- Actual application to the source assembly: the original two-core premise
is now discharged, leaving only genuine earlier-source inputs. -/
theorem source_endgame
    {G : Type u} [Group G] [Finite G] {d : Geometry G}
    (h : LocalData d) (hG : IsSimpleQTKE CFSG.KnownSimple.IsKnownSimple G)
    (source618 : F618Universal.{u} CFSG.KnownSimple.IsKnownSimple)
    (sourceB : FFAlternatives.ProjectiveLine.AdequateCompleteClassificationInput.{u,u}
      CFSG.KnownSimple.IsKnownSimple)
    (source115 : Chapter15.Section04.SourceRecognition.Source.Earlier115 (G := G))
    (hJsource : d.J = ChapterB.thompsonJ (d.T : Subgroup G) 0) : False :=
  Chapter15.Section04.SourceRecognition.Source.false_of_source_twoCore_branch
    h hG source618 source115 (fun i j hF =>
      (source_lemma_15_4_21 h hG source618 sourceB hJsource i j hF).1)

end CFSG.Quasithin.Chapter15.Section04.SourceRecognition.TwoCore

