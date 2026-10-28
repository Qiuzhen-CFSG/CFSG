module

public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed.OmegaStructure
public import Theory.GroupTheory.PResidual.PrimeToAction

/-!
# The binary fixed kernel and the actual moved four-group

Over the field of order two, the generalized-Fitting actor in the original
local quotient has order three. Its literal conjugation image on localV
has the same kernel as actorProjection, hence also has order three.
Coprime splitting on the elementary group localV shows that the moved
subgroup has trivial actor-fixed subgroup. The original natural quotient
therefore identifies the moved subgroup itself as a four-group. Over a
Baumann-fixed base, Campbell V is this group and the omega core splits as
V times the central omega subgroup, with trivial intersection.

Source: Campbell, *Pushing up in Finite Groups* (1979), II.4.3(i), printed
p.25, applied to Aschbacher–Smith C.1.17's actual actor and moved subgroup.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.GlaubermanNiles
variable {B H : Type*} [Group B] [Group H] [Finite H] {e : B →* H}
  {F : Type} [Field F] [Finite F] [CharP F 2]

theorem NaturalModel.actor_conjugation_image_card_three (m : NaturalModel e F)
    (hF : Nat.card F = 2) :
    Nat.card ((localV e).normalizerMonoidHom.comp
      (inclusion (le_normalizer_of_normal : actorLift e ≤ normalizer (localV e : Set H)))).range = 3 := by
  let hn : actorLift e ≤ normalizer (localV e : Set H) := le_normalizer_of_normal
  let f := (localV e).normalizerMonoidHom.comp (inclusion hn)
  have hk : f.ker = (localKernel e).subgroupOf (actorLift e) := by
    ext a
    change f a = 1 ↔ (a : H) ∈ localKernel e
    constructor
    · intro ha v hv
      have hh := congrArg (fun b : MulAut (localV e) => (b ⟨v,hv⟩ : H)) ha
      change (a : H)*v*(a : H)⁻¹ = v at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    · intro ha
      ext v
      change (a : H)*(v : H)*(a : H)⁻¹ = v
      rw [←ha v v.property,mul_inv_cancel_right]
  have hp : (actorProjection e).ker = (localKernel e).subgroupOf (actorLift e) := by
    ext a
    change actorProjection e a = 1 ↔ (a : H) ∈ localKernel e
    constructor
    · intro ha
      exact (QuotientGroup.eq_one_iff (a : H)).mp (congrArg Subtype.val ha)
    · intro ha
      apply Subtype.ext
      exact (QuotientGroup.eq_one_iff (a : H)).mpr ha
  have hs : Function.Surjective (actorProjection e) := by
    intro a
    obtain ⟨g,hg⟩ := QuotientGroup.mk'_surjective (localKernel e) (a : LocalStar e)
    have hm : g ∈ actorLift e := by change QuotientGroup.mk' (localKernel e) g ∈ generalizedFitting (LocalStar e); rw [hg]; exact a.property
    exact ⟨⟨g,hm⟩,Subtype.ext hg⟩
  change Nat.card f.range = 3
  rw [←index_ker,hk,←hp,index_ker,MonoidHom.range_eq_top.mpr hs,card_top]
  exact m.actor_card_of_field_card_two e hF

theorem InLocalClass.movedFixed_eq_bot_of_field_card_two (h : InLocalClass e) (m : NaturalModel e F)
    (hF : Nat.card F = 2) : movedFixed e = ⊥ := by
  let : IsElementaryAbelian 2 (localV e) := h.localV_elementary
  let hn : actorLift e ≤ normalizer (localV e : Set H) := le_normalizer_of_normal
  have hc : Nat.Coprime
      (Nat.card ((localV e).normalizerMonoidHom.comp (inclusion hn)).range) (Nat.card (localV e)) := by
    rw [NaturalModel.actor_conjugation_image_card_three m hF]
    obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 (localV e)).exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  have hd := (commutator_centralizer_decomposition_of_coprime_image (localV e) (actorLift e) hn hc).2
  apply eq_bot_iff.mpr
  intro w hw
  have he : (w : H) = 1 := by
    apply mem_bot.mp
    rw [←hd]
    exact ⟨w.property,moved_le_localV e w.property,hw⟩
  exact show w = 1 from Subtype.ext he

theorem InLocalClass.moved_card_four_of_field_card_two (h : InLocalClass e) (m : NaturalModel e F)
    (hF : Nat.card F = 2) : Nat.card (moved e) = 4 := by
  have hc := m.module_card e
  change (movedFixed e).index = Nat.card F^2 at hc
  rw [InLocalClass.movedFixed_eq_bot_of_field_card_two h m hF,index_bot,hF] at hc
  exact hc

variable [Finite B]
theorem InLocalClass.campbellV_four_and_omegaCore_split (h : InLocalClass e) (hB : IsBaumannFixed B)
    (m : NaturalModel e F) (hF : Nat.card F = 2) :
    Nat.card (Campbell.V H) = 4 ∧
      Disjoint (Campbell.V H) (omegaCenter H) ∧
      omegaOneCenterAmbient (pCore 2 H) = Campbell.V H ⊔ omegaCenter H := by
  refine ⟨?_,?_,h.omegaCore_eq_campbellV_sup_omegaCenter hB m⟩
  · rw [h.campbellV_eq_moved hB m]
    exact InLocalClass.moved_card_four_of_field_card_two h m hF
  · rw [h.campbellV_eq_moved hB m]
    apply Subgroup.disjoint_def.mpr
    intro x hx hz
    have hc : x ∈ center H := ((h.omegaCore_inf_center).symm.le hz).2
    have hm : (⟨x,hx⟩ : moved e) ∈ movedFixed e := by
      rw [h.movedFixed_eq_center hB m]
      exact hc
    rw [InLocalClass.movedFixed_eq_bot_of_field_card_two h m hF,mem_bot] at hm
    exact congrArg Subtype.val hm
end CFSG.Quasithin.ChapterC.GlaubermanNiles
