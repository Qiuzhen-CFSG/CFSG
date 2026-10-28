module
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.OffenderSubgroup
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.RankOneComparison
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.Geometry
public import Theory.Representation.BinaryOffender.CubicQuotient
public import Theory.Representation.BinaryOddDisplacement.PrimeDivisibility
public import Theory.ElementaryAbelian.Basic
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.Actions
public import Theory.AtlasPort.LinearGroups.SL2Order
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.Order
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.BinaryThree
public import Theory.Representation.BinaryOffender.MovedDimension
public import Theory.Representation.BinaryOffender.AmbientSectionTransport
public import Theory.Representation.BinaryPermutation.FiveCentralExtension.OuterCompatibility
public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.Glauberman.BlockConstruction.PairRecognition.Model
public import Theory.Representation.SL2NaturalOffenders.Semilinear
public import Theory.Quasithin.NormalTwoQuotient
public import Theory.GroupTheory.PrimeRankInvolutionLift
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.DefiningSylow
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.MovedSection
public import Mathlib.GroupTheory.Nilpotent
/-!
# The source odd-component rows of B.5.6

Apply the complete adequate classification to the actual offender subgroup
of the reduced action. A normal component and three-rank one identify its
quasisimple factor. For the source three-row list, a commuting fixed-free
cubic excludes the cyclic and marked deleted-permutation A₅ rows. In the
order-168 row it excludes an odd-dimensional single natural module, so the
whole moved module consists of the two binary natural copies under one
literal component identification. Failure of Irr⁺ supplies a second route
to the same doubled conclusion.

The A₅ marking is on the actual central quotient; a dimension-only A₅
hypothesis would also allow the natural SL₂(4) module and would be false.
All subgroup inclusions and the original ambient action are retained.

Source: Aschbacher--Smith B.5.6 and 13.7.4(1), printed pp.104--106 and938.
-/

public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section07.PlusAction.OddFFRows
open ChapterB.SourceInduction ChapterB.QuasisimpleSource
open ChapterB.SourceInduction.ComponentReduction.PreliminaryActions
variable {D V : Type*} [Group D] [Finite D]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) D V)

/-- Adequate B.5 on the actual normal offender subgroup, retaining the
literal component and its full central-quotient action. -/
theorem component_rankOne_rows
    (hfaith : Function.Injective ρ) (hcore : pCore 2 D = ⊥)
    (cover : SQTKQuotient KnownSimple.IsKnownSimple D)
    {C : Subgroup D} [C.Normal] [IsQuasisimple C]
    (hCN : C ≤ offenderSubgroup ρ) (hr : primeRank 3 D ≤ 1) :
    ∃ c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
        (ρ.comp (offenderSubgroup ρ).subtype) (C.subgroupOf (offenderSubgroup ρ)),
      RankOneActionCase (ρ.comp (offenderSubgroup ρ).subtype)
        (C.subgroupOf (offenderSubgroup ρ)) c.sectionData := by
  let N := offenderSubgroup ρ
  let C' := C.subgroupOf N
  let : IsQuasisimple C' := IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hCN).symm
  let : C'.Normal := inferInstance
  have hC : IsComponent N C' := ⟨(inferInstance : C'.Normal).isSubnormal, inferInstance⟩
  let : IsSimpleGroup (C' ⧸ center C') := IsQuasisimple.simple
  let : Nontrivial C' := (QuotientGroup.mk'_surjective (center C')).nontrivial
  let : Nontrivial N := C'.subtype_injective.nontrivial
  have hrN : primeRank 3 N ≤ 1 :=
    (_root_.primeRank_le_of_injective 3 N.subtype N.subtype_injective).trans hr
  rcases (offenderSubgroup_adequateAlternative ρ hfaith hcore cover).at_three_rank_le_one hrN with hq | hs
  · obtain ⟨hq, ⟨c⟩⟩ := hq
    have hF : IsComponent N (generalizedFitting N) :=
      ⟨(inferInstance : (generalizedFitting N).Normal).isSubnormal, hq⟩
    have he : C' = generalizedFitting N :=
      hC.eq_of_le hF (component_le_generalizedFitting N C' hC)
    change ∃ c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
        (ρ.comp N.subtype) C', RankOneActionCase (ρ.comp N.subtype) C' c.sectionData
    rw [he]
    exact ⟨c, c.rank_one_action hrN⟩
  · obtain ⟨c⟩ := hs
    let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
    let : Group.IsSolvable (Equiv.Perm (Fin 3)) :=
      Group.isSolvable_of_isSolvable_injective
        (Equiv.Perm.viaEmbeddingHom_injective (Fin.castLEEmb (by decide : 3 ≤ 4)))
    let : Group.IsSolvable N := Group.isSolvable_of_surjective
      (f := c.equiv.symm.toMonoidHom) c.equiv.symm.surjective
    exact (Group.IsPerfect.not_isSolvable C' inferInstance).elim
end CFSG.Quasithin.Chapter13.Section07.PlusAction.OddFFRows


open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section07.PlusAction.OddFFRows
open ChapterB.QuasisimpleSource
variable {G V : Type*} [Group G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- A commuting cubic acts on the literal moved section and its literal central quotient. -/
theorem central_quotient_even {D : Type*} [Group D] (j : D →* G) {L : Subgroup D}
    (s : MovedSection (ρ.comp j) L)
    (hspace : s.space.toSubmodule = ⊤)
    (z : G) (hz : z ^ 3 = 1)
    (hcomm : ∀ l : L, z * j l = j l * z)
    (hfix : ∀ v, ρ z v = v → v = 0) :
    Even (Module.finrank (ZMod 2) (s.space.toSubmodule ⧸ s.central.toSubmodule)) := by
  let U := s.space.toSubmodule
  have stable (g : G) (w : U) : ρ g w ∈ U := by
    change ρ g w ∈ s.space.toSubmodule
    rw [hspace]
    trivial
  let τ : Representation (ZMod 2) (zpowers z) U := {
    toFun g := {
      toFun w := ⟨ρ g w, stable g w⟩
      map_add' a b := Subtype.ext ((ρ g).map_add a b)
      map_smul' a b := Subtype.ext ((ρ g).map_smul a b) }
    map_one' := by ext w; simp
    map_mul' g h := by ext w; simp [map_mul, Module.End.mul_apply] }
  have hgcomm (g : zpowers z) (l : L) : (g : G) * j l = j l * g := by
    let C := centralizer ((L.map j) : Set G)
    have hzC : z ∈ C := by
      rintro _ ⟨a,ha,rfl⟩
      exact (hcomm ⟨a,ha⟩).symm
    have hgC : (g : G) ∈ C := zpowers_le.mpr hzC g.property
    exact (hgC _ (mem_map_of_mem j l.property)).symm
  let N : Subrepresentation τ := {
    toSubmodule := s.central.toSubmodule
    apply_mem_toSubmodule := by
      intro g w hw
      rw [s.central_eq] at hw ⊢
      intro l
      apply Subtype.ext
      change ρ (j l) (ρ g w) = ρ g w
      rw [← Module.End.mul_apply, ← map_mul, ← hgcomm]
      rw [map_mul, Module.End.mul_apply]
      exact congrArg (ρ g) (congrArg Subtype.val (hw l)) }
  let f : τ.IntertwiningMap N.quotientRepresentation :=
    ⟨N.toSubmodule.mkQ, fun _ => rfl⟩
  have hz' : (⟨z,mem_zpowers z⟩ : zpowers z) ^ 3 = 1 := Subtype.ext hz
  exact even_finrank_of_fixedFree_cubic_quotient τ N.quotientRepresentation f N.toSubmodule.mkQ_surjective
    ⟨z,mem_zpowers z⟩ hz' (fun v hv => Subtype.ext (hfix v (congrArg Subtype.val hv)))
end CFSG.Quasithin.Chapter13.Section07.PlusAction.OddFFRows


open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section07.PlusAction.OddFFRows
open ChapterB.QuasisimpleSource

private theorem not_slTwo_card168 (F : BinaryField)
    (hc : Nat.card (Matrix.SpecialLinearGroup (Fin 2) F.Carrier) = 168) : False := by
  rw [Atlas.card_sl_two] at hc
  let q := Nat.card F.Carrier
  change q * (q ^ 2 - 1) = 168 at hc
  have hq : 2 ≤ q := Finite.one_lt_card
  have hq6 : q < 6 := by
    by_contra hn
    have h6 : 6 ≤ q := by omega
    have hs : 36 ≤ q ^ 2 := by simpa using Nat.pow_le_pow_left h6 2
    have hp : 6 * 35 ≤ q * (q ^ 2 - 1) := Nat.mul_le_mul h6 (by omega)
    omega
  interval_cases q <;> norm_num at hc

private theorem slThree_card168_degree (F : BinaryField) (ho : Odd F.degree)
    (hc : Nat.card (Matrix.SpecialLinearGroup (Fin 3) F.Carrier) = 168) :
    F.degree = 1 := by
  have hd := (Matrix.PSL3.LinearThree.unipotentSL F.Carrier).card_subgroup_dvd_card
  rw [Matrix.PSL3.LinearThree.card_unipotentSL, F.card_eq, hc, ← pow_mul] at hd
  have hbound : F.degree < 3 := by
    by_contra hn
    have hp : 2 ^ 9 ∣ 168 :=
      (Nat.pow_dvd_pow 2 (show 9 ≤ F.degree * 3 by omega)).trans hd
    norm_num at hp
  have hp := F.degree_pos
  obtain ⟨k,hk⟩ := ho
  omega
end CFSG.Quasithin.Chapter13.Section07.PlusAction.OddFFRows

namespace CFSG.Quasithin.Chapter13.Section07.PlusAction.OddFFRows
open ChapterB.QuasisimpleSource ChapterB.SourceInduction
open ChapterB.SourceInduction.ComponentReduction.PreliminaryActions
variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- The actual order-168 component and a commuting fixed-free cubic select
both natural copies, with the original component inclusion retained. -/
theorem doubleThree_of_commuting_cubic {E : Subgroup G} {C : Subgroup E}
    [C.Normal] [IsQuasisimple C]
    (hfaith : Function.Injective ρ) (hcore : pCore 2 E = ⊥)
    (cover : SQTKQuotient KnownSimple.IsKnownSimple E)
    (hCN : C ≤ offenderSubgroup (ρ.comp E.subtype)) (hr : primeRank 3 E ≤ 1)
    (hwhole : moved (ρ.comp E.subtype) C = ⊤) (hcard : Nat.card C = 168)
    (z : G) (hz : z ^ 3 = 1)
    (hcomm : ∀ c : C, z * (c : G) = (c : G) * z)
    (hfix : ∀ v, ρ z v = v → v = 0) :
    Nonempty (ActionEquiv ((ρ.comp E.subtype).comp C.subtype)
      (repeated (linearNatural BinaryField.two 3) 2)) := by
  let σ := ρ.comp E.subtype
  let N := offenderSubgroup σ
  let L := C.subgroupOf N
  obtain ⟨c,hc⟩ := component_rankOne_rows σ
    (hfaith.comp E.subtype_injective) hcore cover hCN hr
  let s := c.sectionData
  have hspace : s.space.toSubmodule = ⊤ := by
    rw [s.space_eq]
    change subspaceCommutator (σ.comp N.subtype) ⊤ L = ⊤
    rw [subspaceCommutator_comp_map, map_subgroupOf_eq_of_le hCN]
    exact hwhole
  have hcardL : Nat.card L = 168 :=
    (Nat.card_congr (subgroupOfEquivOfLe hCN).toEquiv).trans hcard
  have heven := central_quotient_even ρ (E.subtype.comp N.subtype) s hspace z hz
    (fun l => hcomm ((subgroupOfEquivOfLe hCN) l)) hfix
  cases hc with
  | irreducible _ _ _ hi _ =>
    cases hi with
    | linearTwo F _ e _ _ =>
      exact False.elim (not_slTwo_card168 F
        ((Nat.card_congr e.groupEquiv.toEquiv).symm.trans hcardL))
    | linearThree F ho _ e _ =>
      have hd : Module.finrank (ZMod 2) F.Carrier = F.degree := by
        have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F.Carrier)
        rw [Nat.card_zmod,F.card_eq] at hh
        exact (Nat.pow_right_injective (by decide : 1 < 2) hh).symm
      have hdim : Module.finrank (ZMod 2) (Fin 3 → F.Carrier) = 3 * F.degree := by
        simp [Module.finrank_pi_fintype, hd]
      have hq := e.linearEquiv.finrank_eq.trans hdim
      have he : Even (3 * F.degree) := hq ▸ heven
      exact False.elim ((Nat.not_odd_iff_even.mpr he) ((by decide : Odd 3).mul ho))
    | symmetricFive e _ _ =>
      have hh : Nat.card L = 60 := by
        rw [Nat.card_congr e.subgroupEquiv.toEquiv,nat_card_alternatingGroup]
        norm_num [Nat.factorial]
      omega
  | doubleThree F ho _ e _ _ =>
    have hd := slThree_card168_degree F ho
      ((Nat.card_congr e.groupEquiv.toEquiv).symm.trans hcardL)
    let q := ExtensionConsequences.degreeOneRepeatedEquiv F hd 3 2
    let b : V ≃ₗ[ZMod 2] s.space.toSubmodule :=
      Submodule.topEquiv.symm.trans (LinearEquiv.ofEq _ _ hspace.symm)
    let j : C ≃* L := (subgroupOfEquivOfLe hCN).symm
    refine ⟨⟨j.trans (e.groupEquiv.trans q.groupEquiv),
      b.trans (e.linearEquiv.trans q.linearEquiv),?_⟩⟩
    intro g v
    change q.linearEquiv (e.linearEquiv (b (ρ (g : G) v))) =
      repeated (linearNatural BinaryField.two 3) 2
        (q.groupEquiv (e.groupEquiv (j g)))
        (q.linearEquiv (e.linearEquiv (b v)))
    have hb : b (ρ (g : G) v) = s.space.toRepresentation (j g : N) (b v) := by
      apply Subtype.ext
      rfl
    rw [hb]
    exact (congrArg q.linearEquiv (e.intertwines (j g) (b v))).trans
      (q.intertwines (e.groupEquiv (j g)) (e.linearEquiv (b v)))
/-- Failure of Irr⁺ selects the two natural binary copies on the literal component. -/
theorem doubleThree_of_not_irrPlus {E : Subgroup G} {C : Subgroup E}
    [C.Normal] [IsQuasisimple C]
    (hfaith : Function.Injective ρ) (hcore : pCore 2 E = ⊥)
    (cover : SQTKQuotient KnownSimple.IsKnownSimple E)
    (hCN : C ≤ offenderSubgroup (ρ.comp E.subtype)) (hr : primeRank 3 E ≤ 1)
    (hwhole : moved (ρ.comp E.subtype) C = ⊤) (hcard : Nat.card C = 168)
    (hnot : ¬ IsIrrPlus (ρ.comp E.subtype) C ⊤) :
    Nonempty (ActionEquiv ((ρ.comp E.subtype).comp C.subtype)
      (repeated (linearNatural BinaryField.two 3) 2)) := by
  let σ := ρ.comp E.subtype
  let N := offenderSubgroup σ
  let L := C.subgroupOf N
  obtain ⟨c,hc⟩ := component_rankOne_rows σ
    (hfaith.comp E.subtype_injective) hcore cover hCN hr
  let s := c.sectionData
  have hspace : s.space.toSubmodule = ⊤ := by
    rw [s.space_eq]
    change subspaceCommutator (σ.comp N.subtype) ⊤ L = ⊤
    rw [subspaceCommutator_comp_map, map_subgroupOf_eq_of_le hCN]
    exact hwhole
  have hcardL : Nat.card L = 168 :=
    (Nat.card_congr (subgroupOfEquivOfLe hCN).toEquiv).trans hcard
  cases hc with
  | irreducible hi _ _ _ _ =>
    have hi' : IsIrrPlus (σ.comp N.subtype) L ⊤ := hspace ▸ hi
    exact False.elim (hnot ((IsIrrPlus.subgroupOf_iff σ C N hCN ⊤).mp hi'))
  | doubleThree F ho _ e _ _ =>
    have hd := slThree_card168_degree F ho
      ((Nat.card_congr e.groupEquiv.toEquiv).symm.trans hcardL)
    let q := ExtensionConsequences.degreeOneRepeatedEquiv F hd 3 2
    let b : V ≃ₗ[ZMod 2] s.space.toSubmodule :=
      Submodule.topEquiv.symm.trans (LinearEquiv.ofEq _ _ hspace.symm)
    let j : C ≃* L := (subgroupOfEquivOfLe hCN).symm
    refine ⟨⟨j.trans (e.groupEquiv.trans q.groupEquiv),
      b.trans (e.linearEquiv.trans q.linearEquiv),?_⟩⟩
    intro g v
    change q.linearEquiv (e.linearEquiv (b (ρ (g : G) v))) =
      repeated (linearNatural BinaryField.two 3) 2
        (q.groupEquiv (e.groupEquiv (j g)))
        (q.linearEquiv (e.linearEquiv (b v)))
    have hb : b (ρ (g : G) v) = s.space.toRepresentation (j g : N) (b v) := by
      apply Subtype.ext
      rfl
    rw [hb]
    exact (congrArg q.linearEquiv (e.intertwines (j g) (b v))).trans
      (q.intertwines (e.groupEquiv (j g)) (e.linearEquiv (b v)))
end CFSG.Quasithin.Chapter13.Section07.PlusAction.OddFFRows

public section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section07.PlusAction.OddFFRows
open ChapterB.QuasisimpleSource ChapterB.SourceInduction
open ChapterB.Glauberman.BlockConstruction

private theorem naturalFive_commuting_eq_id
    (f : BinaryPermutation.natural (Fin 5) →ₗ[ZMod 2] BinaryPermutation.natural (Fin 5))
    (hf : ∀ g ∈ alternatingGroup (Fin 5), ∀ v,
      f (BinaryPermutation.naturalRepresentation (Fin 5) g v) =
        BinaryPermutation.naturalRepresentation (Fin 5) g (f v))
    (hi : Function.Injective f) : ∀ v, f v = v := by
  have hodd : Odd (Fintype.card (Fin 5)) := by decide
  let e := BinaryPermutation.coreEquivNatural (Fin 5) hodd
  let F := e.symm.toLinearMap.comp (f.comp e.toLinearMap)
  have hF : ∀ v, F v = v := by
    apply BinaryPermutation.FiveCentralExtension.core_commuting_eq_id F
    · intro g hg v
      apply e.injective
      simp only [F, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
      rw [BinaryPermutation.coreEquivNatural_equivariant, hf g hg,
        BinaryPermutation.coreEquivNatural_equivariant]
      change _ = BinaryPermutation.naturalRepresentation (Fin 5) g (e (e.symm (f (e v))))
      rw [LinearEquiv.apply_symm_apply]
    · exact e.symm.injective.comp (hi.comp e.injective)
  intro v
  have hh := congrArg e (hF (e.symm v))
  simpa only [F, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] using hh

variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

omit [FiniteDimensional (ZMod 2) V] in
/-- The deleted-permutation module has no commuting fixed-free invertible operator. -/
theorem not_naturalFive_of_commuting_fixedFree_operator
    {D : Type*} [Group D] (σ : Representation (ZMod 2) D V)
    (e : ActionEquiv σ (alternatingNatural 5))
    (f : V →ₗ[ZMod 2] V) (hfi : Function.Injective f)
    (hcomm : ∀ c v, f (σ c v) = σ c (f v))
    (hfix : ∀ v, f v = v → v = 0) : False := by
  let F := e.linearEquiv.toLinearMap.comp (f.comp e.linearEquiv.symm.toLinearMap)
  have hF : ∀ v, F v = v := by
    apply naturalFive_commuting_eq_id F
    · intro g hg v
      obtain ⟨c,hc⟩ := e.groupEquiv.surjective ⟨g,hg⟩
      have hg' : (e.groupEquiv c : Equiv.Perm (Fin 5)) = g := congrArg Subtype.val hc
      rw [← hg']
      obtain ⟨w,rfl⟩ := e.linearEquiv.surjective v
      change e.linearEquiv (f (e.linearEquiv.symm
        (alternatingNatural 5 (e.groupEquiv c) (e.linearEquiv w)))) = _
      rw [← e.intertwines c w, LinearEquiv.symm_apply_apply, hcomm, e.intertwines]
      simp only [F, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
      rfl
    · exact e.linearEquiv.injective.comp (hfi.comp e.linearEquiv.symm.injective)
  have hid : ∀ v, f v = v := by
    intro v
    apply e.linearEquiv.injective
    simpa only [F, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
      using hF (e.linearEquiv v)
  have hzero : ∀ v : V, v = 0 := fun v => hfix v (hid v)
  have hdim : Module.finrank (ZMod 2) V = 4 := by
    rw [e.linearEquiv.finrank_eq, BinaryPermutation.finrank_natural_odd (Fin 5) (by decide)]
    rfl
  have : Subsingleton V := ⟨fun a b => (hzero a).trans (hzero b).symm⟩
  have hh := Module.finrank_zero_of_subsingleton (R := ZMod 2) (M := V)
  omega

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
/-- A fixed-free cubic on the full moved module descends to its marked central quotient. -/
theorem not_alternatingFive_central_quotient_of_commuting_cubic
    {D : Type*} [Group D] (j : D →* G) {L : Subgroup D}
    (s : MovedSection (ρ.comp j) L) (hspace : s.space.toSubmodule = ⊤)
    (e : ActionEquiv (s.action.comp L.subtype) (alternatingNatural 5))
    (z : G) (hz : z ^ 3 = 1)
    (hcomm : ∀ l : L, z * j l = j l * z)
    (hfix : ∀ v, ρ z v = v → v = 0) : False := by
  let U := s.space.toSubmodule
  have stable (g : G) (w : U) : ρ g w ∈ U := by
    change ρ g w ∈ s.space.toSubmodule
    rw [hspace]
    trivial
  let τ : Representation (ZMod 2) (zpowers z) U := {
    toFun g := {
      toFun w := ⟨ρ g w, stable g w⟩
      map_add' a b := Subtype.ext ((ρ g).map_add a b)
      map_smul' a b := Subtype.ext ((ρ g).map_smul a b) }
    map_one' := by ext w; simp
    map_mul' g h := by ext w; simp [map_mul, Module.End.mul_apply] }
  have hgcomm (g : zpowers z) (l : L) : (g : G) * j l = j l * g := by
    let C := centralizer ((L.map j) : Set G)
    have hzC : z ∈ C := by
      rintro _ ⟨a,ha,rfl⟩
      exact (hcomm ⟨a,ha⟩).symm
    have hgC : (g : G) ∈ C := zpowers_le.mpr hzC g.property
    exact (hgC _ (mem_map_of_mem j l.property)).symm
  let N : Subrepresentation τ := {
    toSubmodule := s.central.toSubmodule
    apply_mem_toSubmodule := by
      intro g w hw
      rw [s.central_eq] at hw ⊢
      intro l
      apply Subtype.ext
      change ρ (j l) (ρ g w) = ρ g w
      rw [← Module.End.mul_apply, ← map_mul, ← hgcomm]
      rw [map_mul, Module.End.mul_apply]
      exact congrArg (ρ g) (congrArg Subtype.val (hw l)) }
  let f : τ.IntertwiningMap N.quotientRepresentation :=
    ⟨N.toSubmodule.mkQ, fun _ => rfl⟩
  let t : zpowers z := ⟨z,mem_zpowers z⟩
  have ht : t ^ 3 = 1 := Subtype.ext hz
  have hfixed : ∀ w, N.quotientRepresentation t w = w → w = 0 := by
    intro w hw
    obtain ⟨v,hv,rfl⟩ := Representation.QuadraticFourGroup.exists_cubic_fixed_lift
      f N.toSubmodule.mkQ_surjective ht hw
    have hv0 : v = 0 := Subtype.ext (hfix v (congrArg Subtype.val hv))
    rw [hv0,map_zero]
  apply not_naturalFive_of_commuting_fixedFree_operator (s.action.comp L.subtype) e
    (N.quotientRepresentation t) (N.quotientRepresentation.apply_bijective t).1 _ hfixed
  intro l w
  obtain ⟨v,rfl⟩ := N.toSubmodule.mkQ_surjective w
  change N.toSubmodule.mkQ (τ t (s.space.toRepresentation l v)) =
    s.central.toSubmodule.mkQ (s.space.toRepresentation l (τ t v))
  apply congrArg s.central.toSubmodule.mkQ
  apply Subtype.ext
  change ρ z (ρ (j l) v) = ρ (j l) (ρ z v)
  rw [← Module.End.mul_apply,←map_mul,hcomm,map_mul,Module.End.mul_apply]

private theorem symmetricThree_commuting_eq_id
    {D : Type*} [Group D] [Finite D]
    (σ : Representation (ZMod 2) D V) (e : D ≃* Equiv.Perm (Fin 3))
    (hf : Function.Injective σ) (hd : Module.finrank (ZMod 2) V = 2)
    (f : V →ₗ[ZMod 2] V) (hfi : Function.Injective f)
    (hc : ∀ g v, f (σ g v) = σ g (f v)) : ∀ v, f v = v := by
  let t := e.symm (Equiv.swap 0 1)
  let u := e.symm (Equiv.swap 1 2)
  have ht : t * t = 1 := by apply e.injective; simp [t]
  have hu : u * u = 1 := by apply e.injective; simp [u]
  have htn : t ≠ 1 := by
    intro hh
    have hh' := congrArg e hh
    have hn : (Equiv.swap 0 1 : Equiv.Perm (Fin 3)) ≠ 1 := by decide
    apply hn
    simp [t] at hh'
  have hun : u ≠ 1 := by
    intro hh
    have hh' := congrArg e hh
    have hn : (Equiv.swap 1 2 : Equiv.Perm (Fin 3)) ≠ 1 := by decide
    apply hn
    simp [u] at hh'
  have htu : t ≠ u := by
    intro hh
    have hh' := congrArg e hh
    have hn : (Equiv.swap 0 1 : Equiv.Perm (Fin 3)) ≠ Equiv.swap 1 2 := by decide
    apply hn
    simpa [t,u] using hh'
  obtain ⟨a,b,hb⟩ := PairRecognition.exists_natural_model σ hf hd t u ht hu htn hun htu
  let F : (Fin 2 → ZMod 2) →+ (Fin 2 → ZMod 2) :=
    (b.toLinearMap.comp (f.comp b.symm.toLinearMap)).toAddMonoidHom
  obtain ⟨c,hc'⟩ := Representation.SL2NaturalOffenders.centralizer_scalar F (by
    intro g v
    obtain ⟨h,rfl⟩ := a.surjective g
    obtain ⟨w,rfl⟩ := b.surjective v
    change b (f (b.symm (Representation.specialLinearNatural 2 (a h) (b w)))) =
      Representation.specialLinearNatural 2 (a h) (F (b w))
    rw [← hb h w, LinearEquiv.symm_apply_apply, hc, hb]
    change _ = Representation.specialLinearNatural 2 (a h) (b (f (b.symm (b w))))
    rw [LinearEquiv.symm_apply_apply])
  have hc1 : c = 1 := by
    have hc01 : c = 0 ∨ c = 1 := by exact (show ∀ x : ZMod 2, x = 0 ∨ x = 1 by decide) c
    rcases hc01 with hz | ho
    · have hinj : Function.Injective F := b.injective.comp (hfi.comp b.symm.injective)
      have : (1 : Fin 2 → ZMod 2) = 0 := hinj (by simp [hc',hz])
      have hh := congrFun this 0
      norm_num at hh
    · exact ho
  intro v
  apply b.injective
  have hh := hc' (b v)
  change b (f (b.symm (b v))) = c • b v at hh
  simpa only [LinearEquiv.symm_apply_apply, hc1, one_smul] using hh

/-- The cyclic component row cannot coexist with the source's commuting fixed-free cubic. -/
theorem not_cyclicThree_of_commuting_fixedFree {E : Subgroup G} {C : Subgroup E}
    [C.Normal] (hfaith : Function.Injective ρ) (hcore : pCore 2 E = ⊥)
    (cover : SQTKQuotient KnownSimple.IsKnownSimple E)
    (hCN : C ≤ offenderSubgroup (ρ.comp E.subtype)) (hr : primeRank 3 E ≤ 1)
    (hquot : IsPGroup 2 (E ⧸ C)) (hcard : Nat.card C = 3)
    (hwhole : moved (ρ.comp E.subtype) C = ⊤)
    (z : G) (hcomm : ∀ x : E, z * x = x * z)
    (hfix : ∀ v, ρ z v = v → v = 0) : False := by
  let σ := ρ.comp E.subtype
  let N := offenderSubgroup σ
  let : IsCyclic C := isCyclic_of_prime_card hcard
  let : Group.IsSolvable C := inferInstance
  let : Group.IsSolvable (E ⧸ C) := @IsNilpotent.to_isSolvable _ _ hquot.isNilpotent
  let : Group.IsSolvable E := (Group.isSolvable_iff_subgroup_quotient C).mpr ⟨inferInstance,inferInstance⟩
  let : Group.IsSolvable N := inferInstance
  let hCpos : Nontrivial C := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let : Nontrivial N := (inclusion_injective hCN).nontrivial
  have hfaithN := hfaith.comp (E.subtype_injective.comp N.subtype_injective)
  have hrN : primeRank 3 N ≤ 1 :=
    (_root_.primeRank_le_of_injective 3 N.subtype N.subtype_injective).trans hr
  rcases (offenderSubgroup_adequateAlternative σ (hfaith.comp E.subtype_injective)
    hcore cover).at_three_rank_le_one hrN with hq | hs
  · let : IsQuasisimple (generalizedFitting N) := hq.1
    let : IsSimpleGroup (generalizedFitting N ⧸ center (generalizedFitting N)) := IsQuasisimple.simple
    let : Nontrivial (generalizedFitting N) :=
      (QuotientGroup.mk'_surjective (center (generalizedFitting N))).nontrivial
    exact Group.IsPerfect.not_isSolvable (generalizedFitting N) inferInstance
  · obtain ⟨c⟩ := hs
    have hmoveN : moved (σ.comp N.subtype) ⊤ = ⊤ := by
      change subspaceCommutator (σ.comp N.subtype) ⊤ ⊤ = ⊤
      rw [subspaceCommutator_comp_map]
      have ht : (⊤ : Subgroup N).map N.subtype = N := by
        rw [← MonoidHom.range_eq_map]
        exact range_subtype N
      rw [ht]
      apply top_unique
      calc
        ⊤ = moved σ C := hwhole.symm
        _ ≤ moved σ N := by
          unfold moved subspaceCommutator
          apply Submodule.span_mono
          rintro _ ⟨g,hg,v,hv,rfl⟩
          exact ⟨g,hCN hg,v,hv,rfl⟩
    have hd : Module.finrank (ZMod 2) V = 2 := by
      have hh := c.dimension
      rw [hmoveN] at hh
      simpa using hh
    have hid : ∀ v, ρ z v = v := symmetricThree_commuting_eq_id
      (ρ.comp (E.subtype.comp N.subtype)) c.equiv hfaithN hd (ρ z)
      (ρ.apply_bijective z).1 (by
        intro g v
        change ρ z (ρ (g : G) v) = ρ (g : G) (ρ z v)
        rw [← Module.End.mul_apply, ← map_mul, hcomm, map_mul, Module.End.mul_apply])
    have hzero : ∀ v : V, v = 0 := fun v => hfix v (hid v)
    have : Subsingleton V := ⟨fun a b => (hzero a).trans (hzero b).symm⟩
    have hh := Module.finrank_zero_of_subsingleton (R := ZMod 2) (M := V)
    omega
end CFSG.Quasithin.Chapter13.Section07.PlusAction.OddFFRows

namespace CFSG.Quasithin.Chapter13.Section07.PlusAction.OddFFRows
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open ChapterB.QuasisimpleSource ChapterB.SourceInduction

private theorem three_rank_le_one_of_card {D : Type*} [Group D] [Finite D]
    (hc : Nat.card D = 3 ∨ Nat.card D = 60 ∨ Nat.card D = 168) : primeRank 3 D ≤ 1 := by
  obtain ⟨P,hP,hPc⟩ := exists_elementaryAbelian_card_primeRank (G := D) (p := 3)
  have hd : 3 ^ primeRank 3 D ∣ Nat.card D := hPc ▸ P.card_subgroup_dvd_card
  by_contra hn
  have h9 : 9 ∣ Nat.card D := (Nat.pow_dvd_pow 3 (show 2 ≤ primeRank 3 D by omega)).trans hd
  rcases hc with hc | hc | hc <;> norm_num [hc] at h9

variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- The actual three-row component catalogue, its literal A₅ central-quotient
mark, and the commuting cubic select the doubled PSL₃(2) action. -/
theorem three_row_doubleThree_of_commuting_cubic {E : Subgroup G} {C : Subgroup E}
    [C.Normal] (hfaith : Function.Injective ρ) (hcore : pCore 2 E = ⊥)
    (cover : SQTKQuotient KnownSimple.IsKnownSimple E)
    (hCN : C ≤ offenderSubgroup (ρ.comp E.subtype))
    (hquot : IsPGroup 2 (E ⧸ C))
    (hcases : Nat.card C = 3 ∨ Nonempty (C ≃* alternatingGroup (Fin 5)) ∨
      Nonempty (C ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)))
    (hwhole : moved (ρ.comp E.subtype) C = ⊤)
    (hA5 : Nat.card C = 60 → Nonempty (ActionEquiv
      ((MovedSection.ofNormal (ρ.comp E.subtype) C).action.comp C.subtype)
      (alternatingNatural 5)))
    (z : G) (hz : z ^ 3 = 1)
    (hcomm : ∀ x : E, z * (x : G) = (x : G) * z)
    (hfix : ∀ v, ρ z v = v → v = 0) :
    Nonempty (ActionEquiv ((ρ.comp E.subtype).comp C.subtype)
      (repeated (linearNatural BinaryField.two 3) 2)) := by
  have hcard : Nat.card C = 3 ∨ Nat.card C = 60 ∨ Nat.card C = 168 := by
    rcases hcases with h3 | ha | hl
    · exact Or.inl h3
    · obtain ⟨e⟩ := ha
      apply Or.inr; apply Or.inl
      rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup]
      norm_num [Nat.factorial]
    · obtain ⟨e⟩ := hl
      apply Or.inr; apply Or.inr
      rw [Nat.card_congr e.toEquiv,Matrix.PSL3.LinearThree.DefiningSylow.card_specialLinear]
      norm_num
  have hr : primeRank 3 E ≤ 1 :=
    (primeRank_le_of_normal_two_quotient C hquot 3 (by decide)).trans
      (three_rank_le_one_of_card hcard)
  rcases hcases with h3 | ha | hl
  · exact False.elim (not_cyclicThree_of_commuting_fixedFree ρ hfaith hcore cover hCN hr
      hquot h3 hwhole z hcomm hfix)
  · obtain ⟨e⟩ := ha
    have h60 : Nat.card C = 60 := by
      rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup]
      norm_num [Nat.factorial]
    obtain ⟨a⟩ := hA5 h60
    let s := MovedSection.ofNormal (ρ.comp E.subtype) C
    have hspace : s.space.toSubmodule = ⊤ := s.space_eq.trans hwhole
    exact False.elim (not_alternatingFive_central_quotient_of_commuting_cubic ρ E.subtype
      s hspace a z hz (fun c => hcomm c) hfix)
  · obtain ⟨e⟩ := hl
    let : IsQuasisimple C := IsQuasisimple.of_mulEquiv e.symm
    have h168 : Nat.card C = 168 := by
      rw [Nat.card_congr e.toEquiv,Matrix.PSL3.LinearThree.DefiningSylow.card_specialLinear]
      norm_num
    exact doubleThree_of_commuting_cubic ρ hfaith hcore cover hCN hr hwhole h168 z hz
      (fun c => hcomm c) hfix
end CFSG.Quasithin.Chapter13.Section07.PlusAction.OddFFRows

namespace CFSG.Quasithin.Chapter13.Section07.PlusAction.OddFFRows
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open ChapterB.QuasisimpleSource ChapterB.SourceInduction
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- The row extraction retains the ambient component, rather than replacing
its inclusion by an unrelated actor isomorphism. -/
theorem ambient_three_row_doubleThree_of_commuting_cubic
    {E C : Subgroup G} [C.Normal] (hCE : C ≤ E)
    (hfaith : Function.Injective ρ) (hcore : pCore 2 E = ⊥)
    (cover : SQTKQuotient KnownSimple.IsKnownSimple E)
    (hCN : C.subgroupOf E ≤ offenderSubgroup (ρ.comp E.subtype))
    (hquot : IsPGroup 2 (E ⧸ C.subgroupOf E))
    (hcases : Nat.card C = 3 ∨ Nonempty (C ≃* alternatingGroup (Fin 5)) ∨
      Nonempty (C ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)))
    (hwhole : moved ρ C = ⊤)
    (hA5 : Nat.card C = 60 → Nonempty (ActionEquiv
      ((MovedSection.ofNormal (ρ.comp E.subtype) (C.subgroupOf E)).action.comp
        (C.subgroupOf E).subtype) (alternatingNatural 5)))
    (z : G) (hz : z ^ 3 = 1)
    (hcomm : ∀ x : E, z * (x : G) = (x : G) * z)
    (hfix : ∀ v, ρ z v = v → v = 0) :
    Nonempty (ActionEquiv (ρ.comp C.subtype)
      (repeated (linearNatural BinaryField.two 3) 2)) := by
  let e := subgroupOfEquivOfLe hCE
  have hcases' : Nat.card (C.subgroupOf E) = 3 ∨
      Nonempty (C.subgroupOf E ≃* alternatingGroup (Fin 5)) ∨
      Nonempty (C.subgroupOf E ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) := by
    rcases hcases with h3 | ha | hl
    · exact Or.inl ((Nat.card_congr e.toEquiv).trans h3)
    · obtain ⟨a⟩ := ha
      exact Or.inr (Or.inl ⟨e.trans a⟩)
    · obtain ⟨a⟩ := hl
      exact Or.inr (Or.inr ⟨e.trans a⟩)
  have hm : moved (ρ.comp E.subtype) (C.subgroupOf E) = ⊤ := by
    change subspaceCommutator (ρ.comp E.subtype) ⊤ (C.subgroupOf E) = ⊤
    rw [subspaceCommutator_comp_map,map_subgroupOf_eq_of_le hCE]
    exact hwhole
  obtain ⟨a⟩ := three_row_doubleThree_of_commuting_cubic ρ hfaith hcore cover hCN hquot
    hcases' hm (fun hc => hA5 ((Nat.card_congr e.toEquiv).symm.trans hc)) z hz hcomm hfix
  refine ⟨⟨e.symm.trans a.groupEquiv,a.linearEquiv,?_⟩⟩
  intro c v
  exact a.intertwines (e.symm c) v
end CFSG.Quasithin.Chapter13.Section07.PlusAction.OddFFRows
