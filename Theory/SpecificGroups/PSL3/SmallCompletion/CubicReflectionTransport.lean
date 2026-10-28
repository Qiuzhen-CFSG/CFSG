module

public import Theory.SpecificGroups.PSL3.SmallCompletion.CubicReflectionMarking
public import Theory.SpecificGroups.PSL3.BorelTwoParabolics

/-!
# Standard reflection marking on original subgroup carriers

The native marking is transported through an existing two-parabolic
isomorphism. The original ambient group, both literal subgroups and the
specified three elements are retained.
-/

public noncomputable section
open Subgroup Matrix
open scoped MatrixGroups
namespace Matrix.PSL3.SmallCompletion
open Matrix.PSL3.LinearThree
variable {G F : Type*} [Group G] [Field F] [Finite F] [CharP F 2]

/-- Correct an existing parabolic marking so the same two original
cubic inverters become the exact native simple reflections. -/
theorem exists_original_reflection_marking (hF : Nat.card F=4)
    (P Q : Subgroup G) (e : (P⊔Q:Subgroup G)≃*PSL(3,F))
    (hP : (P.subgroupOf (P⊔Q)).map e.toMonoidHom=pointParabolic F)
    (hQ : (Q.subgroupOf (P⊔Q)).map e.toMonoidHom=lineParabolic F)
    (t r s : G) (ht : t∈P⊓Q) (ht3 : orderOf t=3)
    (hr : r∈P) (hs : s∈Q) (hrout : r∉P⊓Q) (hsout : s∉P⊓Q)
    (hrt : r*t*r⁻¹=t⁻¹) (hst : s*t*s⁻¹=t⁻¹) :
    ∃ f : (P⊔Q:Subgroup G)≃*PSL(3,F),
      (P.subgroupOf (P⊔Q)).map f.toMonoidHom=pointParabolic F ∧
      (Q.subgroupOf (P⊔Q)).map f.toMonoidHom=lineParabolic F ∧
      f ⟨r,mem_sup_left hr⟩=reflection F false ∧
      f ⟨s,mem_sup_right hs⟩=reflection F true := by
  let K := P⊔Q
  let t₀ : K := ⟨t,mem_sup_left ht.1⟩
  let r₀ : K := ⟨r,mem_sup_left hr⟩
  let s₀ : K := ⟨s,mem_sup_right hs⟩
  have hJ : ((P⊓Q).subgroupOf K).map e.toMonoidHom=borel F := by
    change ((P.subgroupOf K)⊓(Q.subgroupOf K)).map e.toMonoidHom=borel F
    rw [Subgroup.map_inf _ _ _ e.injective,hP,hQ,projective_parabolics_inf]
  have htb : e t₀∈borel F := hJ ▸ mem_map_of_mem e.toMonoidHom ht
  have ht₀3 : orderOf (e t₀)=3 := (e.orderOf_eq t₀).trans ((orderOf_coe t₀).symm.trans ht3)
  have hrp : e r₀∈pointParabolic F := hP ▸ mem_map_of_mem e.toMonoidHom hr
  have hsq : e s₀∈lineParabolic F := hQ ▸ mem_map_of_mem e.toMonoidHom hs
  have hrb : e r₀∉borel F := by
    intro hh
    rw [←hJ] at hh
    exact hrout ((mem_map_iff_mem (f:=e.toMonoidHom) e.injective).mp hh)
  have hsb : e s₀∉borel F := by
    intro hh
    rw [←hJ] at hh
    exact hsout ((mem_map_iff_mem (f:=e.toMonoidHom) e.injective).mp hh)
  have hrti : e r₀*e t₀*(e r₀)⁻¹=(e t₀)⁻¹ := by
    rw [←map_inv,←map_mul,←map_mul,←map_inv]
    exact congrArg e (Subtype.ext hrt)
  have hsti : e s₀*e t₀*(e s₀)⁻¹=(e t₀)⁻¹ := by
    rw [←map_inv,←map_mul,←map_mul,←map_inv]
    exact congrArg e (Subtype.ext hst)
  obtain ⟨a,har,has,haP,haQ,_⟩ := exists_cubic_reflection_pair_marking F hF
    (e t₀) (e r₀) (e s₀) htb ht₀3 hrp hsq hrb hsb hrti hsti
  refine ⟨e.trans a,?_,?_,har,has⟩
  · change (P.subgroupOf K).map (a.toMonoidHom.comp e.toMonoidHom)=_
    rw [←Subgroup.map_map,hP,haP]
  · change (Q.subgroupOf K).map (a.toMonoidHom.comp e.toMonoidHom)=_
    rw [←Subgroup.map_map,hQ,haQ]

end Matrix.PSL3.SmallCompletion
