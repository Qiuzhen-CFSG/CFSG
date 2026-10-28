module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.SixteenPointPolarity

/-!
# Separating two original point-core hyperplanes

Nondegeneracy of the actual binary polarity distinguishes the hyperplanes
cut out by distinct points. Their equal order supplies an element of either
hyperplane outside the other, inside the same original elementary sixteen.
These are the kernel corrections needed for simultaneous orthogonal lifts.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}

/-- Distinct original points admit a kernel element in the second point
core and outside the first, with no choice of new coordinates or kernel. -/
theorem TypeAt.sixteen_point_core_separator (h : TypeAt z V)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hA : Nat.card A=16)
    (hpure : ∀ x∈A,x≠1 → IsConj x z)
    (hpoints : ∀ x∈A,x≠1 →
      Nat.card (A⊓(involutionCentralizer x).pCoreIn 2:Subgroup G)=8)
    (x y : G) (hx : x∈A) (hy : y∈A) (hx1 : x≠1) (hy1 : y≠1) (hxy : x≠y) :
    ∃ a∈A, a∈(involutionCentralizer y).pCoreIn 2 ∧
      a∉(involutionCentralizer x).pCoreIn 2 := by
  by_contra! hn
  have hle : A⊓(involutionCentralizer y).pCoreIn 2 ≤
      A⊓(involutionCentralizer x).pCoreIn 2 := fun a ha => ⟨ha.1,hn a ha.1 ha.2⟩
  have hE := eq_of_le_of_card_ge hle (by
    rw [hpoints x hx hx1,hpoints y hy hy1])
  obtain ⟨B,_,hN,_,hker⟩ := h.sixteen_point_core_form A hA hpure hpoints
  let X : Additive A := Additive.ofMul ⟨x,hx⟩
  let Y : Additive A := Additive.ofMul ⟨y,hy⟩
  have hX : (⟨x,hx⟩:A)≠1 := fun he => hx1 (congrArg Subtype.val he)
  have hY : (⟨y,hy⟩:A)≠1 := fun he => hy1 (congrArg Subtype.val he)
  have heval (v : Additive A) : B X v=B Y v := by
    have hz : B X v=0 ↔ B Y v=0 := by
      change B (Additive.ofMul (⟨x,hx⟩:A)) (Additive.ofMul v.toMul)=0 ↔
        B (Additive.ofMul (⟨y,hy⟩:A)) (Additive.ofMul v.toMul)=0
      rw [hker ⟨x,hx⟩ hX v.toMul,hker ⟨y,hy⟩ hY v.toMul]
      constructor
      · intro hv
        have hm : (v.toMul:G)∈A⊓(involutionCentralizer x).pCoreIn 2 := ⟨v.toMul.property,hv⟩
        rw [←hE] at hm
        exact hm.2
      · intro hv
        exact (hle ⟨v.toMul.property,hv⟩).2
    have bit : ∀ a b : ZMod 2,(a=0 ↔ b=0) → a=b := by decide +kernel
    exact bit _ _ hz
  have hzero : X-Y=0 := hN.1 _ (fun v => by
    change (B (X-Y)) v=0
    rw [map_sub,LinearMap.sub_apply,heval v,sub_self])
  have heq : X=Y := sub_eq_zero.mp hzero
  exact hxy (congrArg (fun a : Additive A => (a.toMul:G)) heq)

end CFSG.Quasithin.HigmanSims
