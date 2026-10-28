module

public import Theory.GroupTheory.Amalgam.NormalSubamalgam
public import Theory.GroupTheory.Amalgam.AutomorphismGroup
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# The faithful marked action of an overlap on a normal base

A common overlap acts by conjugation on both local intersections with a normal
subgroup. The restrictions commute with both inclusion maps. If those local
intersections generate the normal subgroup and the overlap supplements it,
the action is injective: an element in its kernel centralizes the normal base,
and its normal closure lies in the original faithful overlap.

This is the faithful local action needed for the normalizer and extension
argument of Goldschmidt, *Automorphisms of trivalent graphs* (1980), (2.8)
and (3.2), printed pp.381 and 386--387.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace Subgroup
variable {G : Type*} [Group G]

/-- No nonidentity element of the original overlap centralizes the whole
normal supplement when the overlap has trivial ambient core. -/
theorem centralizer_inf_eq_bot_of_normal_supplement (N T : Subgroup G) [N.Normal]
    (hgen : N ⊔ T = ⊤) (hcore : T.normalCore = ⊥) :
    centralizer (N : Set G) ⊓ T = ⊥ := by
  let K := centralizer (N : Set G) ⊓ T
  have hn : N ≤ normalizer (K : Set G) := by
    intro n hn
    rw [mem_normalizer_iff]
    intro k
    constructor
    · intro hk
      have hc := (mem_centralizer_iff.mp hk.1 n hn)
      simpa only [hc, mul_assoc, mul_inv_cancel, mul_one] using hk
    · intro hk
      have hc := (mem_centralizer_iff.mp hk.1 n⁻¹ (N.inv_mem hn))
      have he : n⁻¹ * (n * k * n⁻¹) * n = n * k * n⁻¹ := by
        simpa only [inv_inv, mul_assoc, inv_mul_cancel, mul_one] using
          congrArg (fun x : G => x*n) hc
      have he' : k = n * k * n⁻¹ := by simpa only [inv_mul_cancel_left, mul_assoc, inv_mul_cancel, mul_one] using he
      exact he' ▸ hk
  have hc := normalClosure_le_of_normal_supplement N T K hgen hn inf_le_right
  have hbot : normalClosure (K : Set G) = ⊥ :=
    le_bot_iff.mp (hcore ▸ normal_le_normalCore.mpr hc)
  exact le_bot_iff.mp (le_normalClosure.trans hbot.le)

/-- The overlap acts faithfully by conjugation on a normal supplement. -/
theorem normal_supplement_conjugation_injective (N T : Subgroup G) [N.Normal]
    (hgen : N ⊔ T = ⊤) (hcore : T.normalCore = ⊥) :
    Function.Injective ((MulAut.conjNormal : G →* MulAut N).comp T.subtype) := by
  apply ((MulAut.conjNormal : G →* MulAut N).comp T.subtype).ker_eq_bot_iff.mp
  apply le_bot_iff.mp
  intro t ht
  have he : (MulAut.conjNormal (t : G) : MulAut N) = 1 := ht
  have hc : (t : G) ∈ centralizer (N : Set G) := by
    rw [mem_centralizer_iff]
    intro n hn
    have he' := congrArg (fun e : MulAut N => ((e ⟨n,hn⟩ : N) : G)) he
    change (t : G)*n*(t : G)⁻¹=n at he'
    have hh := congrArg (fun z : G => z*(t : G)) he'
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using hh.symm
  have hb := (centralizer_inf_eq_bot_of_normal_supplement N T hgen hcore).le ⟨hc,t.2⟩
  exact Subgroup.mem_bot.mpr (Subtype.ext (Subgroup.mem_bot.mp hb))

end Subgroup



namespace Theory.GroupTheory.RankTwoAmalgam
variable {G : Type*} [Group G]

/-- Restriction to both endpoints preserves the two inclusion squares. -/
def pairRestriction (A B : Subgroup G) (e : MulAut G)
    (ha : A.map e.toMonoidHom = A) (hb : B.map e.toMonoidHom = B) :
    Iso (ofSubgroups A (A ⊓ B) B inf_le_left inf_le_right)
      (ofSubgroups A (A ⊓ B) B inf_le_left inf_le_right) where
  left := (e.subgroupMap A).trans (MulEquiv.subgroupCongr ha)
  right := (e.subgroupMap B).trans (MulEquiv.subgroupCongr hb)
  middle := (e.subgroupMap (A ⊓ B)).trans (MulEquiv.subgroupCongr (by
    rw [Subgroup.map_inf _ _ _ e.injective]
    change A.map e.toMonoidHom ⊓ B.map e.toMonoidHom = A ⊓ B
    rw [ha, hb]))
  left_commutes _ := rfl
  right_commutes _ := rfl

/-- Generation makes restriction to the marked local pair faithful. -/
theorem pairRestriction_eq_iff (A B : Subgroup G) (hgen : A ⊔ B = ⊤)
    (e f : MulAut G) (ha : A.map e.toMonoidHom = A) (hb : B.map e.toMonoidHom = B)
    (ha' : A.map f.toMonoidHom = A) (hb' : B.map f.toMonoidHom = B) :
    pairRestriction A B e ha hb = pairRestriction A B f ha' hb' ↔ e = f := by
  constructor
  · intro he
    have hA : A ≤ e.toMonoidHom.eqLocus f.toMonoidHom := by
      intro a ha
      exact congrArg (fun z => ((z.left ⟨a,ha⟩ : A) : G)) he
    have hB : B ≤ e.toMonoidHom.eqLocus f.toMonoidHom := by
      intro b hb
      exact congrArg (fun z => ((z.right ⟨b,hb⟩ : B) : G)) he
    have hh := hgen ▸ sup_le hA hB
    ext g
    exact hh (show g ∈ (⊤ : Subgroup G) from trivial)
  · rintro rfl
    rfl

end Theory.GroupTheory.RankTwoAmalgam



namespace Subgroup
variable {G : Type*} [Group G]

/-- An element of a local group preserves its intersection with a normal base. -/
theorem subgroupOf_map_conjNormal (N A : Subgroup G) [N.Normal] (t : G) (ht : t ∈ A) :
    (A.subgroupOf N).map (MulAut.conjNormal t).toMonoidHom = A.subgroupOf N := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    change t * (y : G) * t⁻¹ ∈ A
    exact A.mul_mem (A.mul_mem ht hy) (A.inv_mem ht)
  · intro hx
    refine ⟨(MulAut.conjNormal t).symm x, ?_, (MulAut.conjNormal t).apply_symm_apply x⟩
    change (((MulAut.conjNormal t).symm x : N) : G) ∈ A
    rw [MulAut.conjNormal_symm_apply]
    exact A.mul_mem (A.mul_mem (A.inv_mem ht) hx) ht

end Subgroup

namespace Theory.GroupTheory.RankTwoAmalgam
variable {G : Type*} [Group G]
/-- The literal common overlap acts by compatible conjugation on the normal base. -/
def normalOverlapAction (N A B : Subgroup G) [N.Normal] :
    ↥(A ⊓ B) →* Iso
      (ofSubgroups (A.subgroupOf N) (A.subgroupOf N ⊓ B.subgroupOf N)
        (B.subgroupOf N) inf_le_left inf_le_right)
      (ofSubgroups (A.subgroupOf N) (A.subgroupOf N ⊓ B.subgroupOf N)
        (B.subgroupOf N) inf_le_left inf_le_right) where
  toFun t := pairRestriction (A.subgroupOf N) (B.subgroupOf N)
    (MulAut.conjNormal (t : G)) (subgroupOf_map_conjNormal N A t t.2.1)
    (subgroupOf_map_conjNormal N B t t.2.2)
  map_one' := by
    apply Iso.ext <;> apply MulEquiv.ext <;> intro x <;> apply Subtype.ext
    all_goals
      change MulAut.conjNormal (1 : G) (x : N) = (x : N)
      simp only [map_one, MulAut.one_apply]
  map_mul' t u := by
    apply Iso.ext <;> apply MulEquiv.ext <;> intro x <;> apply Subtype.ext
    all_goals
      change MulAut.conjNormal ((t : G) * (u : G)) (x : N) =
        MulAut.conjNormal (t : G) (MulAut.conjNormal (u : G) (x : N))
      rw [map_mul, MulAut.mul_apply]

/-- A faithful generated normal base detects each element of the original overlap. -/
theorem normalOverlapAction_injective (N A B : Subgroup G) [N.Normal]
    (hgen : N ⊔ (A ⊓ B) = ⊤) (hcore : (A ⊓ B).normalCore = ⊥)
    (hNgen : A.subgroupOf N ⊔ B.subgroupOf N = ⊤) :
    Function.Injective (normalOverlapAction N A B) := by
  intro t u he
  apply Subgroup.normal_supplement_conjugation_injective N (A ⊓ B) hgen hcore
  exact (pairRestriction_eq_iff _ _ hNgen _ _ _ _ _ _).mp he
end Theory.GroupTheory.RankTwoAmalgam
