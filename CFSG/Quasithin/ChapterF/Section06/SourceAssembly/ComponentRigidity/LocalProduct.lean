module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentRigidity
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Solvable.MinimalParabolic.IndexThree
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Solvable.Source.Selection
public import Theory.GroupTheory.TwoPerfectOrderTwelve
public import Theory.GroupTheory.PResidual.SylowSupplement

/-!
# The actual C(G,T) reduction in Goldschmidt rigidity

For the original normal X containing only the first local residual, the
subgroup Y = Q2 L1 has its literal Q2 as a Sylow subgroup of index three,
and its embedded two-residual is exactly L1. F.6.12 supplies the genuine
characteristic-subgroup obstruction. Unless L1 is cubic, Y satisfies the
solvable minimal-parabolic hypotheses; the proved C.1.29 specialization
makes its residual an A3-block. A faithful four-coset action identifies
that residual with A4.

Thus all the C(G,T) work in F.6.13 is discharged on the original subgroup
maps. Excluding the A4 alternative is the separate F.6.5/F.1.12 amalgam
geometry step. Source: Aschbacher--Smith F.6.13, printed p.307.
-/

public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.ChapterF.SourceAssembly
variable {G : Type*} [Group G] [Finite G] {G₁ G₂ : Subgroup G}

theorem normal_subgroup_local_product_setup
    (h : IsGoldschmidtTriple G₁ G₂) (X : Subgroup G) [X.Normal]
    (h₁ : (pResidual 2 G₁).map G₁.subtype ≤ X)
    (h₂ : ¬ (pResidual 2 G₂).map G₂.subtype ≤ X) :
    let Q := (pCore 2 G₂).map G₂.subtype
    let L := (pResidual 2 G₁).map G₁.subtype
    let Y := Q ⊔ L
    (pResidual 2 Y).map Y.subtype = L ∧
      ∃ S : Sylow 2 Y, (S : Subgroup Y).map Y.subtype = Q ∧
        (S : Subgroup Y).index = 3 := by
  classical
  dsimp only
  let Q := (pCore 2 G₂).map G₂.subtype
  let L := (pResidual 2 G₁).map G₁.subtype
  let Y := Q ⊔ L
  let T := G₁ ⊓ G₂
  have hQT : Q ≤ T := by
    simpa only [inf_comm G₂ G₁] using h.symm.local_twoCore_le_intersection
  have hQL : Q ≤ normalizer (L : Set G) := hQT.trans h.intersection_normalizes_left_residual
  have hLperfect : IsPPerfect 2 L := (isPPerfect_pResidual 2).of_surjective
    (G₁.subtype.subgroupMap (pResidual 2 G₁)) (G₁.subtype.subgroupMap_surjective _)
  have hres : (pResidual 2 Y).map Y.subtype = L := by
    change (pResidual 2 (Q ⊔ L : Subgroup G)).map (Q ⊔ L).subtype = L
    rw [sup_comm Q L]
    exact embedded_pResidual_join_pGroup L Q hLperfect (pCore_isPGroup.map G₂.subtype) hQL
  refine ⟨hres, ?_⟩
  obtain ⟨_, _, P, hP⟩ := normal_subgroup_rigidity_setup h X h₁ h₂
  change (P : Subgroup (X ⊔ Q : Subgroup G)).map (X ⊔ Q).subtype = Q at hP
  have hY : Y ≤ X ⊔ Q := sup_le le_sup_right (h₁.trans le_sup_left)
  let Y' := Y.subgroupOf (X ⊔ Q)
  have hPY : (P : Subgroup (X ⊔ Q : Subgroup G)) ≤ Y' := by
    intro x hx
    exact (le_sup_left : Q ≤ Y) (hP.le (mem_map_of_mem (X ⊔ Q).subtype hx))
  let S' := P.subtype hPY
  let e : Y' ≃* Y := subgroupOfEquivOfLe hY
  let S := S'.mapSurjective (f := e.toMonoidHom) e.surjective
  have hS : (S : Subgroup Y).map Y.subtype = Q := by
    change (((P : Subgroup (X ⊔ Q : Subgroup G)).subgroupOf Y').map e.toMonoidHom).map Y.subtype = Q
    rw [map_map]
    change ((P : Subgroup (X ⊔ Q : Subgroup G)).subgroupOf Y').map
      ((X ⊔ Q).subtype.comp Y'.subtype) = Q
    rw [← map_map, map_subgroupOf_eq_of_le hPY, hP]
  refine ⟨S, hS, ?_⟩
  have hYG₁ : Y ≤ G₁ := sup_le (hQT.trans inf_le_left) (map_subtype_le _)
  have hindexT : T.relIndex G₁ = 3 := by
    change ((G₁ ⊓ G₂).subgroupOf G₁).index = 3
    obtain ⟨R, hR⟩ := h.intersection_sylow
    have hRG : (R : Subgroup G) ≤ G₁ := hR.symm.le.trans inf_le_left
    have hh := SymmetricThreeTwoCore.sylow_index_three h.quotient_left.some (R.subtype hRG)
    simpa only [Sylow.coe_subtype, ← hR] using hh
  have hindexQ : Q.relIndex G₁ = 6 := by
    have hh := relIndex_mul_relIndex Q T G₁ hQT inf_le_left
    have htwo : Q.relIndex T = 2 := by
      simpa only [inf_comm G₂ G₁] using h.symm.left_core_index
    rw [htwo, hindexT] at hh
    exact hh.symm
  have hSindex : (S : Subgroup Y).index = Q.relIndex Y := by
    rw [← hS, relIndex, subgroupOf, comap_map_eq_self_of_injective Y.subtype_injective]
  have hdiv : (S : Subgroup Y).index ∣ 6 := by
    rw [hSindex, ← hindexQ]
    exact ⟨Y.relIndex G₁, (relIndex_mul_relIndex Q Y G₁ le_sup_left hYG₁).symm⟩
  have hne : (S : Subgroup Y).index ≠ 1 := by
    intro he
    have hYQ : Y = Q := by
      have hh := congrArg (Subgroup.map Y.subtype) (index_eq_one.mp he)
      simpa only [hS, ← MonoidHom.range_eq_map, range_subtype] using hh.symm
    have hLp : IsPGroup 2 L := (pCore_isPGroup.map G₂.subtype).to_le
      (show L ≤ Q by rw [← hYQ]; exact le_sup_right)
    have hbot : L = ⊥ := by
      have hf := hLperfect.hom_eq_one_of_isPGroup hLp (MonoidHom.id L)
      apply eq_bot_iff.mpr
      intro x hx
      exact congrArg Subtype.val (congrArg (fun f : L →* L => f ⟨x, hx⟩) hf)
    have hp : IsPGroup 3 L := hbot ▸ IsPGroup.of_bot
    have hc := local_residual_card_three_of_isThreeGroup h hp
    change Nat.card L = 3 at hc
    rw [hbot, Nat.card_unique] at hc
    omega
  have hodd := S.not_dvd_index
  have hle := Nat.le_of_dvd (by decide : 0 < 6) hdiv
  interval_cases hs : (S : Subgroup Y).index <;> norm_num [hs] at *
end CFSG.Quasithin.ChapterF.SourceAssembly

namespace CFSG.Quasithin.ChapterF.SourceAssembly
open Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G] {G₁ G₂ : Subgroup G}

omit [Finite G] in
private theorem characteristic_map_equiv {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (D : Subgroup A) [D.Characteristic] :
    (D.map e.toMonoidHom).Characteristic := by
  apply characteristic_iff_le_comap.mpr
  rintro a x ⟨y, hy, rfl⟩
  refine ⟨(MulAut.congr e.symm a) y,
    characteristic_iff_le_comap.mp inferInstance (MulAut.congr e.symm a) hy, ?_⟩
  exact e.apply_symm_apply _

theorem local_product_characteristic_obstruction
    (h : IsGoldschmidtTriple G₁ G₂) (hcore : pCore 2 G = ⊥)
    (S : Sylow 2 ((pCore 2 G₂).map G₂.subtype ⊔
      (pResidual 2 G₁).map G₁.subtype : Subgroup G))
    (hS : (S : Subgroup ((pCore 2 G₂).map G₂.subtype ⊔
      (pResidual 2 G₁).map G₁.subtype : Subgroup G)).map
        ((pCore 2 G₂).map G₂.subtype ⊔ (pResidual 2 G₁).map G₁.subtype).subtype =
          (pCore 2 G₂).map G₂.subtype) :
    ∀ K : Subgroup S, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (S : Subgroup ((pCore 2 G₂).map G₂.subtype ⊔
        (pResidual 2 G₁).map G₁.subtype : Subgroup G)).subtype).Normal := by
  let Q := (pCore 2 G₂).map G₂.subtype
  let L := (pResidual 2 G₁).map G₁.subtype
  let Y := Q ⊔ L
  let e : S ≃* Q := (equivMapOfInjective (S : Subgroup Y)
    Y.subtype Y.subtype_injective).trans (MulEquiv.subgroupCongr hS)
  intro K hK hne hN
  let : K.Characteristic := hK
  let D := (K.map (S : Subgroup Y).subtype).map Y.subtype
  have hDQ : D ≤ Q := (map_mono (f := Y.subtype) (map_subtype_le K)).trans_eq hS
  have hmap : (K.map e.toMonoidHom).map Q.subtype = D := by
    dsimp only [D]
    rw [map_map, map_map]
    rfl
  have hDe : D.subgroupOf Q = K.map e.toMonoidHom := by
    rw [← hmap, subgroupOf, comap_map_eq_self_of_injective Q.subtype_injective]
  have hchar : (D.subgroupOf Q).Characteristic := by
    rw [hDe]
    exact characteristic_map_equiv e K
  have hn : (D.subgroupOf Y).Normal := by
    change ((K.map (S : Subgroup Y).subtype).map Y.subtype).subgroupOf Y |>.Normal
    simpa only [subgroupOf, comap_map_eq_self_of_injective Y.subtype_injective] using hN
  have hbot := h.right_characteristic_subgroup_eq_bot hcore D hDQ hchar hn
  have hKe : K.map e.toMonoidHom = ⊥ := by
    rw [← hDe, hbot, bot_subgroupOf]
  exact hne ((map_injective e.injective) (hKe.trans (Subgroup.map_bot _).symm))
end CFSG.Quasithin.ChapterF.SourceAssembly

namespace CFSG.Quasithin.ChapterF.SourceAssembly
open Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G] {G₁ G₂ : Subgroup G}

theorem normal_subgroup_noncubic_local_product
    (h : IsGoldschmidtTriple G₁ G₂) (hcore : pCore 2 G = ⊥)
    (X : Subgroup G) [X.Normal]
    (h₁ : (pResidual 2 G₁).map G₁.subtype ≤ X)
    (h₂ : ¬ (pResidual 2 G₂).map G₂.subtype ≤ X)
    (hnc : Nat.card ((pResidual 2 G₁).map G₁.subtype) ≠ 3) :
    let Q := (pCore 2 G₂).map G₂.subtype
    let L := (pResidual 2 G₁).map G₁.subtype
    let Y := Q ⊔ L
    ∃ S : Sylow 2 Y, (S : Subgroup Y).map Y.subtype = Q ∧
      (S : Subgroup Y).index = 3 ∧ Stellmacher.SectionTwo.Hypotheses Y ∧
      IsElementaryAbelian 2 (pCore 2 (pResidual 2 Y)) ∧
      Nat.card (pCore 2 (pResidual 2 Y)) = 4 ∧
      Nat.card (pResidual 2 Y ⧸ pCore 2 (pResidual 2 Y)) = 3 ∧
      ChapterC.IsBlock (pResidual 2 Y) ∧ ChapterC.IsAlternatingBlock (pResidual 2 Y) 3 := by
  classical
  dsimp only
  let Q := (pCore 2 G₂).map G₂.subtype
  let L := (pResidual 2 G₁).map G₁.subtype
  let Y := Q ⊔ L
  obtain ⟨hres, S, hS, hi⟩ := normal_subgroup_local_product_setup h X h₁ h₂
  change (pResidual 2 Y).map Y.subtype = L at hres
  change (S : Subgroup Y).map Y.subtype = Q at hS
  have hP := local_product_characteristic_obstruction h hcore S hS
  have hSne : (S : Subgroup Y) ≠ ⊥ := by
    intro he
    have hc := (S : Subgroup Y).index_mul_card
    rw [hi, he, Nat.card_unique, mul_one] at hc
    have hp : IsPGroup 3 Y := IsPGroup.of_card (n := 1) (by simpa using hc.symm)
    have hLp : IsPGroup 3 L := hres ▸ (hp.to_subgroup (pResidual 2 Y)).map Y.subtype
    exact hnc (local_residual_card_three_of_isThreeGroup h hLp)
  have hnS : ¬ (S : Subgroup Y).Normal := by
    intro hn
    let : Nontrivial S := (nontrivial_iff_ne_bot _).mpr hSne
    have hh := hP ⊤ inferInstance top_ne_bot
    apply hh
    simpa only [← MonoidHom.range_eq_map, range_subtype] using hn
  have hproper : pCore 2 Y < (S : Subgroup Y) := lt_of_le_of_ne
    (pCore_isPGroup.le_sylow_of_normal S) (fun he => hnS (he ▸ inferInstance))
  obtain ⟨e⟩ := sylow_index_three_core_quotient S hi hproper
  have hf : generalizedFitting Y = pCore 2 Y := by
    by_contra hf
    have hcard : Nat.card (pResidual 2 Y) = 3 := by
      rw [SymmetricThreeTwoCore.residual_eq_oddCore e hf]
      exact SymmetricThreeTwoCore.oddCore_card_of_not_characteristic_two e hf
    apply hnc
    change Nat.card L = 3
    rw [← hres, Nat.card_congr
      (equivMapOfInjective (pResidual 2 Y) Y.subtype Y.subtype_injective).symm.toEquiv]
    exact hcard
  have hcent : centralizer (pCore 2 Y : Set Y) ≤ pCore 2 Y := by
    rw [← hf]
    exact centralizer_generalizedFitting_le Y
  have hs : SectionTwo.Hypotheses Y :=
    ChapterC.RankOne.Solvable.sectionTwoHypotheses_of_proper_subgroup
      (SymmetricThreeTwoCore.solvable e) hcent (S : Subgroup Y)
      (lt_top_iff_ne_top.mpr (fun he => by have hh := index_eq_one.mpr he; omega))
  exact ⟨S, hS, hi, hs, ChapterC.RankOne.Solvable.MinimalParabolic.index_three_residual hs S hi hP⟩
end CFSG.Quasithin.ChapterF.SourceAssembly

namespace CFSG.Quasithin.ChapterF.SourceAssembly
open Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G] {G₁ G₂ : Subgroup G}

theorem normal_subgroup_left_residual_cubic_or_alternating_four
    (h : IsGoldschmidtTriple G₁ G₂) (hcore : pCore 2 G = ⊥)
    (X : Subgroup G) [X.Normal]
    (h₁ : (pResidual 2 G₁).map G₁.subtype ≤ X)
    (h₂ : ¬ (pResidual 2 G₂).map G₂.subtype ≤ X) :
    Nonempty (((pResidual 2 G₁).map G₁.subtype) ≃* Multiplicative (ZMod 3)) ∨
      Nonempty (((pResidual 2 G₁).map G₁.subtype) ≃* alternatingGroup (Fin 4)) := by
  classical
  by_cases hcard : Nat.card ((pResidual 2 G₁).map G₁.subtype) = 3
  · exact Or.inl ⟨mulEquivOfPrimeCardEq hcard (by simp)⟩
  let Y := (pCore 2 G₂).map G₂.subtype ⊔ (pResidual 2 G₁).map G₁.subtype
  obtain ⟨_, _, _, _, _, hc, hq, _, _⟩ :=
    normal_subgroup_noncubic_local_product h hcore X h₁ h₂ hcard
  have hRcard : Nat.card (pResidual 2 Y) = 12 := by
    have hh := (pCore 2 (pResidual 2 Y)).index_mul_card
    change Nat.card (pResidual 2 Y ⧸ pCore 2 (pResidual 2 Y)) * _ = _ at hh
    rw [hc, hq] at hh
    exact hh.symm
  obtain ⟨e⟩ := alternatingFour_of_twoPerfect_card_twelve (isPPerfect_pResidual 2) hRcard
  have he := (normal_subgroup_local_product_setup h X h₁ h₂).1
  let r : pResidual 2 Y ≃* ((pResidual 2 G₁).map G₁.subtype) :=
    (equivMapOfInjective (pResidual 2 Y) Y.subtype Y.subtype_injective).trans
      (MulEquiv.subgroupCongr he)
  exact Or.inr ⟨r.symm.trans e⟩
end CFSG.Quasithin.ChapterF.SourceAssembly
