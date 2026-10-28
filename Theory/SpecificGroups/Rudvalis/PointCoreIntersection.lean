module
public import Theory.SpecificGroups.Rudvalis.Model.InvolutionCentralizers.Representatives
public import Theory.GroupTheory.PCoreIntersectionFivePoint

/-!
# The ambient two-core intersection of a Rudvalis point stabilizer

For a central-class involution z and a subgroup C whose point stabilizer
has order 12288, restrict the literal map C_Ru(z) → S₅ to C_C(z).
The restricted kernel is C ∩ O₂(C_Ru(z)), with the same inclusion into
Ru. The only possible kernel/image orders are (2048,6), (1024,12) and
(512,24). This uses the native involution-centralizer marking and its
proved two-core order; it assumes no full Sylow placement for C.

Chapter13's original odd-actor component supplies the point-stabilizer
order. Selecting the order-twelve image needs the subsequent module and
quaternion geometry. The natural-action parabolic quotient is a different
map and does not identify this intersection merely by its kernel order.
Source: Aschbacher--Smith 4.2.13, printed pp.611--612.
-/

public section
namespace Rudvalis
open Subgroup Theory.GroupTheory

/-- Restrict the ambient involution-centralizer quotient, retaining its
literal intersection kernel and all possible image orders. -/
theorem point_core_intersection_quotient (C : Subgroup Model) (z : Model)
    (hclass : IsConj z (b ^ 2))
    (hP : Nat.card ((centralizer ({z} : Set Model)).subgroupOf C) = 12288) :
      let D := centralizer ({z} : Set Model)
      let P := D.subgroupOf C
      ∃ q : D →* Equiv.Perm (Fin 5),
        Function.Surjective q ∧ q.ker = pCore 2 D ∧
        let i : P →* D := {
          toFun := fun x => ⟨x.val.val,x.property⟩
          map_one' := rfl
          map_mul' := fun _ _ => rfl }
        let r := q.comp i
        r.ker = ((D.pCoreIn 2).subgroupOf C).subgroupOf P ∧
        r.ker.map (C.subtype.comp P.subtype) = C ⊓ D.pCoreIn 2 ∧
        ((Nat.card r.ker = 2048 ∧ Nat.card r.range = 6) ∨
          (Nat.card r.ker = 1024 ∧ Nat.card r.range = 12) ∨
          (Nat.card r.ker = 512 ∧ Nat.card r.range = 24)) := by
  let D := centralizer ({z} : Set Model)
  let P := D.subgroupOf C
  have hQ : Nat.card (pCore 2 D) = 2048 := InvolutionCentralizers.first_core_card hclass
  let a := Rudvalis.InvolutionCentralizers.firstQuotientEquiv hclass
  let q : D →* Equiv.Perm (Fin 5) :=
    a.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 D))
  have hq : Function.Surjective q := a.surjective.comp (QuotientGroup.mk'_surjective _)
  have hqk : q.ker = pCore 2 D := by
    ext x
    change a (QuotientGroup.mk' (pCore 2 D) x) = 1 ↔ _
    rw [←map_one a,a.injective.eq_iff]
    exact QuotientGroup.eq_one_iff x
  let i : P →* D := {
    toFun := fun x => ⟨x.val.val,x.property⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  have hi : Function.Injective i := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun t : D => (t : Model)) h
  obtain ⟨hk,hmap,hsizes⟩ := fivePoint_core_restriction_sizes i hi a hQ hP
  let r := q.comp i
  refine ⟨q,hq,hqk,?_,?_,hsizes⟩
  · change r.ker = ((D.pCoreIn 2).subgroupOf C).subgroupOf P
    ext x
    change r x = 1 ↔ (x.val.val : Model) ∈ D.pCoreIn 2
    change i x ∈ q.ker ↔ _
    rw [hqk]
    constructor
    · intro hx
      exact ⟨i x,hx,rfl⟩
    · rintro ⟨y,hy,he⟩
      have hyx : y = i x := Subtype.ext he
      exact hyx ▸ hy
  · change r.ker.map (C.subtype.comp P.subtype) = C ⊓ D.pCoreIn 2
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      refine ⟨y.val.property,?_⟩
      have hy' : i y ∈ pCore 2 D := by
        change y ∈ (pCore 2 D).comap i
        rw [←hk]
        exact hy
      exact ⟨i y,hy',rfl⟩
    · rintro ⟨hxC,y,hy,rfl⟩
      let x : P := ⟨⟨(y : Model),hxC⟩,y.property⟩
      refine ⟨x,?_,rfl⟩
      change q (i x) = 1
      change i x ∈ q.ker
      rw [hqk]
      exact hy

end Rudvalis
