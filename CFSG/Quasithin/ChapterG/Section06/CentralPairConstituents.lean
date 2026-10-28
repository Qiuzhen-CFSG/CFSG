module
public import CFSG.Quasithin.ChapterG.Section06.Source
public import Theory.Representation.NormalConstituentKernel
public import Theory.Representation.BinaryOffender.ActionImage
public import Theory.SpecificGroups.BinaryLinear.SmallCubicRank
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.Models
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity
public import Theory.GroupTheory.Commutator.PerfectLocalReduction
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.SpecificGroups.SymmetricFourSolvable

/-!
# The central rank-one models for a constituent of a simple pair

A component of three-rank at most one rules out GL₄(2), GL₅(2) and the
symmetric central-model rows: their components have three-rank at least two.
Perfectness excludes GL₂(2), leaving the marked natural GL₃(2) action.

For a normal pair of simple components in a faithful irreducible ambient
action, at least one component acts nontrivially on every constituent.
Its nontrivial image is isomorphic to the original simple component, so the
rank bound survives passage to the faithful image. The surviving image is
simple GL₃(2). Distinct commuting components cannot have the same nontrivial
image, hence exactly one acts fully and the other trivially. The literal
subgroup images and the intertwining model are retained.

Source: Aschbacher–Smith G.6.4, printed pp.345–346; component calculus in
A.3.3; the exchanged constituent branch of 15.2.27(2), printed p.1119.
-/

public section
open Subgroup Theory.GroupTheory Representation
open BinaryLinear.OuterCyclic Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterG.Section06
variable {G W : Type*} [Group G] [Finite G] [AddCommGroup W] [Module (ZMod 2) W]

private instance (n : ℕ) : Finite (LinearGroup n) :=
  Finite.of_injective (fun g : LinearGroup n => (g : (Fin n → ZMod 2) → (Fin n → ZMod 2))) DFunLike.coe_injective

private theorem symmetric_component_rank {n : ℕ} (hn : 6 ≤ n)
    (D : Subgroup (Equiv.Perm (Fin n))) (hD : IsComponent _ D) :
    2 ≤ primeRank 3 D := by
  let : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  let : IsQuasisimple (alternatingGroup (Fin n)) := {
    toIsPerfect := ⟨commutator_alternatingGroup_eq_top (by simpa using (show 5 ≤ n by omega))⟩
    simple := by
      let : IsSimpleGroup (alternatingGroup (Fin n)) :=
        alternatingGroup.isSimpleGroup (by simpa using (show 5 ≤ n by omega))
      exact ((QuotientGroup.quotientMulEquivOfEq
        (alternatingGroup.center_eq_bot (by simpa using (show 4 ≤ n by omega)))).trans
          QuotientGroup.quotientBot).isSimpleGroup }
  let := hD.2
  have hA : IsComponent (Equiv.Perm (Fin n)) (alternatingGroup (Fin n)) :=
    ⟨(inferInstance : (alternatingGroup (Fin n)).Normal).isSubnormal,inferInstance⟩
  have he : D = alternatingGroup (Fin n) := hD.eq_of_le hA
    (le_of_isPerfect_of_index_eq_two D _ (alternatingGroup.index_eq_two))
  rw [he]
  exact alternatingGroup.TwoThreeCycles.two_le_primeRank hn

private theorem linear_component_top {n : ℕ} (hn : 3 ≤ n)
    (D : Subgroup (LinearGroup n)) (hD : IsComponent _ D) : D = ⊤ := by
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2)) :=
    Atlas.psl_simple_high_rank n hn
  let : IsSimpleGroup (LinearGroup n) :=
    (projectiveEquivLinear (by omega : 0 < n)).symm.isSimpleGroup
  have hnt : Nontrivial D := by
    let := hD.2
    let : IsSimpleGroup (D ⧸ center D) := IsQuasisimple.simple
    exact (QuotientGroup.mk'_surjective (center D)).nontrivial
  exact (hD.1.eq_bot_or_top_of_isSimpleGroup inferInstance).resolve_left
    ((nontrivial_iff_ne_bot _).mp hnt)

/-- A component of three-rank at most one leaves only the binary natural three-space. -/
theorem central_model_natural_three_of_component
    (ρ : Representation (ZMod 2) G W) (hm : CentralModel ρ)
    (D : Subgroup G) (hD : IsComponent G D) (hr : primeRank 3 D ≤ 1) :
    HasModelOn ρ ⊤ ⊤ (binaryLinearAction 3) := by
  rcases hm with ⟨n,hn,hn5,hmodel⟩ | hsix | hseven | hcore
  · obtain ⟨eK,eW,hstable,haction⟩ := hmodel
    let e : G ≃* LinearGroup n := topEquiv.symm.trans eK
    let D' := D.map e.toMonoidHom
    have hD' : IsComponent (LinearGroup n) D' := hD.map_equiv e
    have hr' : primeRank 3 D' ≤ 1 := by
      rw [←primeRank_equiv 3 (D.equivMapOfInjective e.toMonoidHom e.injective)]
      exact hr
    by_cases hn2 : n = 2
    · subst n
      let s := BinaryLinear.SmallParabolicLevi.linearTwoEquivSymmetricThree
      let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
      let : Group.IsSolvable (Equiv.Perm (Fin 3)) :=
        Group.isSolvable_of_isSolvable_injective
          (Equiv.Perm.viaEmbeddingHom_injective (Fin.castLEEmb (by decide : 3 ≤ 4)))
      let : Group.IsSolvable (LinearGroup 2) :=
        Group.isSolvable_of_isSolvable_injective (f := s.toMonoidHom) s.injective
      let := hD'.2
      let : IsSimpleGroup (D' ⧸ center D') := IsQuasisimple.simple
      let : Nontrivial D' := (QuotientGroup.mk'_surjective (center D')).nontrivial
      exact (Group.IsPerfect.not_isSolvable D' inferInstance).elim
    have ht := linear_component_top (by omega : 3 ≤ n) D' hD'
    have hrG : primeRank 3 (LinearGroup n) ≤ 1 := by
      rw [ht,primeRank_equiv 3 topEquiv] at hr'
      exact hr'
    have hn3 : n = 3 := by
      by_contra hn3
      have hd : n = 4 ∨ n = 5 := by omega
      have hl := BinaryLinear.SmallCubicRank.four_or_five hd
      rw [primeRank_equiv 3 (slEquivLinear n)] at hl
      omega
    subst n
    exact ⟨eK,eW,hstable,haction⟩
  all_goals
    exfalso
    first | obtain ⟨eK,_,_,_⟩ := hsix | obtain ⟨eK,_,_,_⟩ := hseven | obtain ⟨eK,_,_,_⟩ := hcore
    let e := topEquiv.symm.trans eK
    have hl := symmetric_component_rank (by decide) (D.map e.toMonoidHom) (hD.map_equiv e)
    rw [←primeRank_equiv 3 (D.equivMapOfInjective e.toMonoidHom e.injective)] at hl
    omega
end CFSG.Quasithin.ChapterG.Section06

namespace CFSG.Quasithin.ChapterG.Section06
variable {G W : Type*} [Group G] [Finite G] [AddCommGroup W] [Module (ZMod 2) W]

private theorem component_nontrivial {X : Type*} [Group X]
    (D : Subgroup X) (hD : IsComponent X D) : Nontrivial D := by
  let := hD.2
  let : IsSimpleGroup (D ⧸ center D) := IsQuasisimple.simple
  exact (QuotientGroup.mk'_surjective (center D)).nontrivial

private theorem simple_map_equiv {X Y : Type*} [Group X] [Group Y]
    (f : X →* Y) (D : Subgroup X) [IsSimpleGroup D] (hne : D.map f ≠ ⊥) :
    Nonempty (D ≃* D.map f) := by
  let g := f.subgroupMap D
  have hi : Function.Injective g := by
    apply g.ker_eq_bot_iff.mp
    apply g.normal_ker.eq_bot_or_eq_top.resolve_right
    intro ht
    have hg : g = 1 := g.ker_eq_top_iff.mp ht
    have he : D.map f = ⊥ := by
      apply _root_.eq_bot_iff.mpr
      intro d hd
      obtain ⟨a,ha⟩ := f.subgroupMap_surjective D ⟨d,hd⟩
      have hh : g a = 1 := by rw [hg]; rfl
      rw [ha] at hh
      exact congrArg Subtype.val hh
    exact hne he
  exact ⟨MulEquiv.ofBijective g ⟨hi,f.subgroupMap_surjective D⟩⟩

private theorem simple_component_top {X : Type*} [Group X] [IsSimpleGroup X]
    (D : Subgroup X) (hD : IsComponent X D) : D = ⊤ :=
  (hD.1.eq_bot_or_top_of_isSimpleGroup inferInstance).resolve_left
    ((nontrivial_iff_ne_bot _).mp (component_nontrivial D hD))

/-- A normal simple pair acts on a central-model constituent through exactly one full GL₃(2) factor. -/
theorem normal_pair_constituent_natural_three
    (ρ : Representation (ZMod 2) G W) [IsIrreducible ρ] (hf : Function.Injective ρ)
    (I : Subgroup G) (C : Subrepresentation (ρ.comp I.subtype))
    [IsIrreducible C.toRepresentation]
    (A B : Subgroup G) (hA : IsComponent G A) (hB : IsComponent G B)
    [IsSimpleGroup A] [IsSimpleGroup B] [(A ⊔ B).Normal]
    (hne : A ≠ B) (hAI : A ≤ I) (hBI : B ≤ I)
    (hrA : primeRank 3 A ≤ 1) (hrB : primeRank 3 B ≤ 1)
    (hm : CentralModel (imageRepresentation C.toRepresentation)) :
    HasModelOn (imageRepresentation C.toRepresentation) ⊤ ⊤ (binaryLinearAction 3) ∧
      (((A.subgroupOf I).map (actionHom C.toRepresentation) = ⊤ ∧
        (B.subgroupOf I).map (actionHom C.toRepresentation) = ⊥) ∨
       ((A.subgroupOf I).map (actionHom C.toRepresentation) = ⊥ ∧
        (B.subgroupOf I).map (actionHom C.toRepresentation) = ⊤)) := by
  let τ := C.toRepresentation
  let q := actionHom τ
  have hq : Function.Surjective q := τ.asGroupHom.rangeRestrict_surjective
  let A' := A.subgroupOf I
  let B' := B.subgroupOf I
  have hA' := hA.subgroupOf hAI
  have hB' := hB.subgroupOf hBI
  let : IsSimpleGroup A' := (subgroupOfEquivOfLe hAI).isSimpleGroup
  let : IsSimpleGroup B' := (subgroupOfEquivOfLe hBI).isSimpleGroup
  have hrA' : primeRank 3 A' ≤ 1 := by
    rw [primeRank_equiv 3 (subgroupOfEquivOfLe hAI)]
    exact hrA
  have hrB' : primeRank 3 B' ≤ 1 := by
    rw [primeRank_equiv 3 (subgroupOfEquivOfLe hBI)]
    exact hrB
  have hpair : ¬ (A'.map q = ⊥ ∧ B'.map q = ⊥) := by
    rintro ⟨ha,hb⟩
    have hnot := normal_subgroup_not_le_constituent_kernel ρ hf I C (A ⊔ B)
      (sup_le hAI hBI) (fun ht => (nontrivial_iff_ne_bot A).mp inferInstance
        (bot_unique (le_sup_left.trans ht.le)))
    apply hnot
    rw [subgroupOf_sup hAI hBI]
    apply sup_le
    all_goals
      intro g hg
      have he : q g = 1 := mem_bot.mp (by
        first | rw [←ha]; exact mem_map_of_mem q hg | rw [←hb]; exact mem_map_of_mem q hg)
      change τ g = 1
      change imageRepresentation τ (q g) = 1
      rw [he,map_one]
  have hm3 : HasModelOn (imageRepresentation τ) ⊤ ⊤ (binaryLinearAction 3) := by
    by_cases ha : A'.map q = ⊥
    · have hb : B'.map q ≠ ⊥ := fun hb => hpair ⟨ha,hb⟩
      obtain ⟨e⟩ := simple_map_equiv q B' hb
      exact central_model_natural_three_of_component _ hm _
        ((hB'.map_surjective q hq).resolve_left hb)
        (by rw [←primeRank_equiv 3 e]; exact hrB')
    · obtain ⟨e⟩ := simple_map_equiv q A' ha
      exact central_model_natural_three_of_component _ hm _
        ((hA'.map_surjective q hq).resolve_left ha)
        (by rw [←primeRank_equiv 3 e]; exact hrA')
  refine ⟨hm3,?_⟩
  obtain ⟨eK,_,_,_⟩ := hm3
  let e := topEquiv.symm.trans eK
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) :=
    Atlas.psl_simple_high_rank 3 (by decide)
  let : IsSimpleGroup (BinaryLinear.OuterCyclic.LinearGroup 3) :=
    (BinaryLinear.OuterCyclic.projectiveEquivLinear (by decide : 0 < 3)).symm.isSimpleGroup
  let : IsSimpleGroup (actionImage τ) := e.isSimpleGroup
  have hne' : A' ≠ B' := by
    intro hh
    apply hne
    have hh' := congrArg (Subgroup.map I.subtype) hh
    change (A.subgroupOf I).map I.subtype = (B.subgroupOf I).map I.subtype at hh'
    simpa only [map_subgroupOf_eq_of_le hAI,map_subgroupOf_eq_of_le hBI] using hh'
  by_cases ha : A'.map q = ⊥
  · exact Or.inr ⟨ha,simple_component_top _
      ((hB'.map_surjective q hq).resolve_left (fun hb => hpair ⟨ha,hb⟩))⟩
  · have haT := simple_component_top _ ((hA'.map_surjective q hq).resolve_left ha)
    refine Or.inl ⟨haT,?_⟩
    by_contra hb
    have hbT := simple_component_top _ ((hB'.map_surjective q hq).resolve_left hb)
    exact hne' (hA'.eq_of_map_eq hB' q (haT.trans hbT.symm) ha)
end CFSG.Quasithin.ChapterG.Section06
