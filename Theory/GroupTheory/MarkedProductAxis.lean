module
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# Quotient maps onto marked product axes

If a subgroup has exactly one full axis as its image in a marked product,
projection onto that coordinate is surjective and has the original
quotient kernel restricted to the subgroup. The construction retains the
actual quotient and its chosen product marking.

Source application: the factor-centralizer extensions in Aschbacher–Smith
10.2.1, pp.742–743.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G K X Z : Type*} [Group G] [Group K] [Group X] [Group Z]

/-- The literal first coordinate of an original subgroup's marked quotient image. -/
@[expose] def markedAxisProjection (q : G →* K) (Y : Subgroup K)
    (e : Y ≃* X × Z) (P : Subgroup G) (hP : P.map q ≤ Y) : P →* X :=
  (MonoidHom.fst X Z).comp (e.toMonoidHom.comp
    ((q.comp P.subtype).codRestrict Y (fun g => hP (mem_map_of_mem q g.property))))

set_option backward.isDefEq.respectTransparency false in
theorem markedAxisProjection_surjective_ker (q : G →* K) (Y : Subgroup K)
    (e : Y ≃* X × Z) (P : Subgroup G)
    (hP : P.map q = ((⊤ : Subgroup X).prod (⊥ : Subgroup Z)).map
      (Y.subtype.comp e.symm.toMonoidHom)) :
    ∃ f : P →* X, Function.Surjective f ∧
      f.ker = q.ker.subgroupOf P ∧
      ∀ g : P, f g = (e ⟨q (g:G), by
        have hg := mem_map_of_mem q g.property
        rw [hP] at hg
        obtain ⟨v,_,hv⟩ := hg
        exact hv ▸ (e.symm v).property⟩).1 := by
  have hPY : P.map q ≤ Y := by
    rw [hP]
    rintro _ ⟨v,_,rfl⟩
    exact (e.symm v).property
  let f := markedAxisProjection q Y e P hPY
  have hsecond (g : P) : (e ⟨q (g:G),hPY (mem_map_of_mem q g.property)⟩).2 = 1 := by
    have hg := mem_map_of_mem q g.property
    rw [hP] at hg
    obtain ⟨v,hv,hvg⟩ := hg
    have hvg' : e.symm v = ⟨q (g:G),hPY (mem_map_of_mem q g.property)⟩ := Subtype.ext hvg
    rw [←hvg',e.apply_symm_apply]
    exact hv.2
  refine ⟨f,?_,?_,fun _ => rfl⟩
  · intro x
    have hx : (Y.subtype.comp e.symm.toMonoidHom) (x,1) ∈ P.map q := by
      rw [hP]
      exact mem_map_of_mem _ ⟨mem_top _,one_mem _⟩
    obtain ⟨g,hg,hgx⟩ := hx
    refine ⟨⟨g,hg⟩,?_⟩
    change (e ⟨q g,hPY (mem_map_of_mem q hg)⟩).1 = x
    have he : (⟨q g,hPY (mem_map_of_mem q hg)⟩ : Y) = e.symm (x,1) := Subtype.ext hgx
    rw [he,e.apply_symm_apply]
  · ext g
    constructor
    · intro hg
      have he : e (⟨q (g:G),hPY (mem_map_of_mem q g.property)⟩ : Y) = 1 :=
        Prod.ext hg (hsecond g)
      have hz : (⟨q (g:G),hPY (mem_map_of_mem q g.property)⟩ : Y) = 1 :=
        e.injective (he.trans e.map_one.symm)
      exact congrArg Y.subtype hz
    · intro hg
      change (e ⟨q (g:G),hPY (mem_map_of_mem q g.property)⟩).1 = 1
      have hz : (⟨q (g:G),hPY (mem_map_of_mem q g.property)⟩ : Y) = 1 :=
        Subtype.ext hg
      rw [hz,e.map_one]
      rfl
end Theory.GroupTheory
