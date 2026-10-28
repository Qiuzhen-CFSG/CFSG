module
public import CFSG.Quasithin.ChapterC.Section04.ConstrainedAction
public import CFSG.Quasithin.ChapterC.Section04.ConstrainedG2Normality
public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.SourceLocalQuotient
public import Theory.GroupTheory.GeneralizedFitting.PerfectCoreTwoImages
public import Theory.GroupTheory.PerfectSimpleImageKernel
public import Theory.AtlasPort.LinearGroups.G2.EvenThreeRank
public import Theory.AtlasPort.LinearGroups.G2.BinaryDerivedSimplicity

/-!
# Binary rank-two exclusions for the original unitary pushing-up pair

The unitary seed has three-rank at least two. If it is normal in the
local subgroup, its nontrivial action on an escaping component has a
solvable kernel. Its simple two-core quotient forces that kernel to be
a two-group, so the three-rank survives in the actual action image.

The proved local normalizer bounds for binary symplectic and G₂ groups
then exclude these rows, both for ordinary components and for the
literal constrained star quotient. No component normality, inner action
or new local-classification hypothesis is assumed.

The original 4.2.12–13 intersection residual is the consumer; this is a
partial row exclusion, not the Rudvalis recognition or uniqueness theorem.
Source: Aschbacher–Smith C.3.5, C.4.5–8, pp.150,152–154, and 4.2.12–13,
pp.610–612.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.HypothesisC28
open Chapter1.RadicalExclusions.ModelReduction
variable {G : Type*} [Group G] [Finite G] {H M L R V : Subgroup G}
local notation "D" => commutator (Atlas.G2.Model (ZMod 2))

/-- The original unitary quotient contributes an elementary nine to its cover. -/
theorem unitary_seed_threeRank (e : L ⧸ pCore 2 L ≃* D) : 2 ≤ primeRank 3 L := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hr : 2 ≤ primeRank 3 (L ⧸ pCore 2 L) := by
    rw [primeRank_congr 3 e]
    exact Atlas.G2.EvenThreeRank.two_le_primeRank_derived
  exact hr.trans (primeRank_quotient_le_of_isTwoGroup 3 (by decide) _ pCore_isPGroup)

/-- The full source span retains the unitary seed’s three-rank. -/
theorem unitary_span_threeRank (e : L ⧸ pCore 2 L ≃* D) :
    2 ≤ primeRank 3 (conjugateSpanBy L M) :=
  (unitary_seed_threeRank e).trans (primeRank_mono 3 (le_conjugateSpanBy L M))

/-- The literal component action of the normal unitary seed retains three-rank two. -/
theorem unitary_constrained_action_threeRank
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (hn : (L.subgroupOf M).Normal) (e : L ⧸ pCore 2 L ≃* D)
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ M.subgroupOf H) :
    2 ≤ primeRank 3 (coreCentralActorImage K ((conjugateSpanBy L M).subgroupOf H)) := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  let : IsSimpleGroup D := Atlas.G2.isSimple_commutator_binary
  let : IsSimpleGroup (L ⧸ pCore 2 L) := e.isSimpleGroup
  have hspan : conjugateSpanBy L M = L := le_antisymm
    (conjugateSpanBy_le le_rfl ((normal_subgroupOf_iff_le_normalizer h.component_le).mp hn))
    (le_conjugateSpanBy _ _)
  let := h.component.perfect
  let : Group.IsPerfect L := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe h.component_le).toMonoidHom)
    (subgroupOfEquivOfLe h.component_le).surjective
  let A := L.subgroupOf H
  let N := normalizer (K : Set H)
  let B := coreCentralActorImage K A
  have hLH : L ≤ H := h.component_le.trans h.local_le
  have hAN : A ≤ N := by
    simpa only [hspan] using h.constrained_span_normalizes_intrinsic K hK hq
  let ex := (subgroupOfEquivOfLe hLH).symm.trans (subgroupOfEquivOfLe hAN).symm
  let a : L →* B := ((normalizerCoreCentralAction K).subgroupMap (A.subgroupOf N)).comp ex.toMonoidHom
  have ha : Function.Surjective a :=
    ((normalizerCoreCentralAction K).subgroupMap_surjective _).comp ex.surjective
  have hb : B ≠ ⊥ := by
    simpa only [hspan] using h.constrained_span_action_nontrivial K hK hq hout
  have hne : a ≠ 1 := by
    intro he
    apply hb
    apply eq_bot_iff.mpr
    intro b hb
    obtain ⟨x,hx⟩ := ha ⟨b,hb⟩
    exact congrArg Subtype.val (hx.symm.trans (DFunLike.congr_fun he x))
  let q := QuotientGroup.mk' (pCore 2 L)
  let : Group.IsSolvable q.ker := by
    rw [QuotientGroup.ker_mk']
    let : Group.IsNilpotent (pCore 2 L) := pCore_isPGroup.isNilpotent
    infer_instance
  let : Group.IsSolvable a.ker := solvable_ker_of_nontrivial_hom_of_simple_quotient
    q (QuotientGroup.mk'_surjective _) a hne
  rw [hspan]
  exact (unitary_seed_threeRank e).trans
    (PerfectCoreTwoExtension.odd_rank_le_of_solvable_kernel (by decide : Odd 3) a)

/-- Binary symplectic ordinary components cannot contain this source span. -/
theorem no_unitary_ordinary_sp4
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (a : L ⧸ pCore 2 L ≃* D) (K : Subgroup H) (hK : IsComponent H K)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : K ⧸ center K ≃* Theory.SpecificGroups.SymplecticFour.Sp F) : False := by
  have hl := unitary_span_threeRank (M := M) a
  have hu := h.ordinary_span_primeRank_le_one_of_sp4 K hK e (by decide : Odd 3)
  omega

/-- Binary G₂ ordinary components in the simple range are excluded. -/
theorem no_unitary_ordinary_g2
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (a : L ⧸ pCore 2 L ≃* D) (K : Subgroup H) (hK : IsComponent H K)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : K ⧸ center K ≃* Atlas.G2.Model F) (hF : 2 < Nat.card F) : False := by
  have hl := unitary_span_threeRank (M := M) a
  have hu := h.ordinary_span_primeRank_le_one_of_g2 K hK e hF (by decide : Odd 3)
  omega

/-- The literal constrained symplectic star row is excluded. -/
theorem no_unitary_constrained_sp4
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (hn : (L.subgroupOf M).Normal) (a : L ⧸ pCore 2 L ≃* D)
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ M.subgroupOf H) (hf : generalizedFitting K = pCore 2 K)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : starImage (K.map H.subtype) R (K.map H.subtype) ≃*
      Theory.SpecificGroups.SymplecticFour.Sp F) (hF : 4 ≤ Nat.card F) : False := by
  have hl := h.unitary_constrained_action_threeRank hn a K hK hq hout
  have hu := h.constrained_symplectic_span_rank_le_one K hK hq hout hf e hF (by decide : Odd 3)
  omega

/-- The literal constrained G₂ star row is excluded. -/
theorem no_unitary_constrained_g2
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (hn : (L.subgroupOf M).Normal) (a : L ⧸ pCore 2 L ≃* D)
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ M.subgroupOf H) (hf : generalizedFitting K = pCore 2 K)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : starImage (K.map H.subtype) R (K.map H.subtype) ≃* Atlas.G2.Model F)
    (hF : 4 ≤ Nat.card F) : False := by
  have hl := h.unitary_constrained_action_threeRank hn a K hK hq hout
  have hu := h.constrained_g2_span_rank_le_one K hK hq hout hf e hF (by decide : Odd 3)
  omega
end CFSG.Quasithin.ChapterC.HypothesisC28
