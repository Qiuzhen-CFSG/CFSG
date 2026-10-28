module
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Algebra.Group.Prod

/-!
# Automorphisms of a centerless product

Surjective images of the two commuting factors generate each target factor.
Their intersection is central, hence trivial. Direct indecomposability forces
each target to come from a single source factor, so an automorphism fixes or
swaps the two factors. No finiteness assumption is needed.

This is the centerless two-factor instance of Aschbacher--Smith A.1.15,
used in the proof of 1.3.8, printed p.514.
-/
public section
open Subgroup
namespace Theory.GroupTheory.CenterlessDirectFactors
variable {A B C : Type*} [Group A] [Group B] [Group C]

private theorem range_choice
    (f : A × B →* C) (hf : Function.Surjective f) (hz : center C = ⊥)
    (hi : ∀ U V : Subgroup C, Disjoint U V → ⁅U,V⁆ = ⊥ → U ⊔ V = ⊤ →
      U = ⊥ ∨ V = ⊥) :
    (∀ a, f (a,1) = 1) ∨ (∀ b, f (1,b) = 1) := by
  let U := (f.comp (MonoidHom.inl A B)).range
  let V := (f.comp (MonoidHom.inr A B)).range
  have hc : U ≤ centralizer (V : Set C) := by
    rintro _ ⟨a,rfl⟩ _ ⟨b,rfl⟩
    change f (1,b) * f (a,1) = f (a,1) * f (1,b)
    rw [← map_mul, ← map_mul]
    simp
  have hg : U ⊔ V = ⊤ := by
    apply top_unique
    intro c _
    obtain ⟨⟨a,b⟩,rfl⟩ := hf c
    have he : f (a,b) = f (a,1) * f (1,b) := by
      rw [← map_mul]; simp
    rw [he]
    exact mul_mem ((show U ≤ U ⊔ V from le_sup_left) (show f (a,1) ∈ U from ⟨a,rfl⟩))
      ((show V ≤ U ⊔ V from le_sup_right) (show f (1,b) ∈ V from ⟨b,rfl⟩))
  have hd : Disjoint U V := by
    apply disjoint_def.mpr
    intro x hxU hxV
    have hle : U ⊔ V ≤ centralizer ({x} : Set C) := by
      apply sup_le
      · intro y hy
        apply mem_centralizer_singleton_iff.mpr
        exact (hc hy x hxV).symm
      · intro y hy
        apply mem_centralizer_singleton_iff.mpr
        exact hc hxU y hy
    have hxc : x ∈ center C := by
      apply mem_center_iff.mpr
      intro y
      exact mem_centralizer_singleton_iff.mp (hle (hg ▸ mem_top y))
    simpa only [hz,mem_bot] using hxc
  rcases hi U V hd (commutator_eq_bot_iff_le_centralizer.mpr hc) hg with hu | hv
  · exact Or.inl (fun a => mem_bot.mp (hu ▸ (show f (a,1) ∈ U from ⟨a,rfl⟩)))
  · exact Or.inr (fun b => mem_bot.mp (hv ▸ (show f (1,b) ∈ V from ⟨b,rfl⟩)))


private theorem ranges_of_coordinates
    {X Y : Type*} [Group X] [Group Y]
    (f : X × Y →* A × B) (hf : Function.Surjective f)
    (hX : ∀ x, (f (x,1)).2 = 1) (hY : ∀ y, (f (1,y)).1 = 1) :
    (f.comp (MonoidHom.inl X Y)).range = (MonoidHom.inl A B).range ∧
    (f.comp (MonoidHom.inr X Y)).range = (MonoidHom.inr A B).range := by
  have hs (x : X) (y : Y) : f (x,y) = f (x,1) * f (1,y) := by
    rw [← map_mul]; simp
  constructor
  · ext z
    constructor
    · rintro ⟨x,rfl⟩
      exact ⟨(f (x,1)).1, Prod.ext rfl (hX x).symm⟩
    · rintro ⟨a,rfl⟩
      obtain ⟨⟨x,y⟩,hxy⟩ := hf (a,1)
      refine ⟨x,Prod.ext ?_ (hX x)⟩
      have hh := congrArg Prod.fst hxy
      rw [hs] at hh
      change (f (x,1)).1 = a
      simpa only [Prod.fst_mul, hY y, mul_one] using hh
  · ext z
    constructor
    · rintro ⟨y,rfl⟩
      exact ⟨(f (1,y)).2, Prod.ext (hY y).symm rfl⟩
    · rintro ⟨b,rfl⟩
      obtain ⟨⟨x,y⟩,hxy⟩ := hf (1,b)
      refine ⟨y,Prod.ext (hY y) ?_⟩
      have hh := congrArg Prod.snd hxy
      rw [hs] at hh
      change (f (1,y)).2 = b
      simpa only [Prod.snd_mul, hX x, one_mul] using hh

/-- Centerless directly indecomposable factors are permuted by automorphisms. -/
theorem coordinate_factors [Nontrivial A] [Nontrivial B]
    (hA : ∀ U V : Subgroup A, Disjoint U V → ⁅U,V⁆ = ⊥ → U ⊔ V = ⊤ →
      U = ⊥ ∨ V = ⊥)
    (hB : ∀ U V : Subgroup B, Disjoint U V → ⁅U,V⁆ = ⊥ → U ⊔ V = ⊤ →
      U = ⊥ ∨ V = ⊥)
    (hzA : center A = ⊥) (hzB : center B = ⊥) (e : MulAut (A × B)) :
    ((e.toMonoidHom.comp (MonoidHom.inl A B)).range = (MonoidHom.inl A B).range ∧
     (e.toMonoidHom.comp (MonoidHom.inr A B)).range = (MonoidHom.inr A B).range) ∨
    ((e.toMonoidHom.comp (MonoidHom.inl A B)).range = (MonoidHom.inr A B).range ∧
     (e.toMonoidHom.comp (MonoidHom.inr A B)).range = (MonoidHom.inl A B).range) := by
  have hf := range_choice ((MonoidHom.fst A B).comp e.toMonoidHom)
    (by
      intro a
      obtain ⟨x,hx⟩ := e.surjective (a,1)
      exact ⟨x,congrArg Prod.fst hx⟩) hzA hA
  have hg := range_choice ((MonoidHom.snd A B).comp e.toMonoidHom)
    (by
      intro b
      obtain ⟨x,hx⟩ := e.surjective (1,b)
      exact ⟨x,congrArg Prod.snd hx⟩) hzB hB
  change (∀ a, (e (a,1)).1 = 1) ∨ (∀ b, (e (1,b)).1 = 1) at hf
  change (∀ a, (e (a,1)).2 = 1) ∨ (∀ b, (e (1,b)).2 = 1) at hg
  rcases hf with hf | hf <;> rcases hg with hg | hg
  · obtain ⟨a,ha⟩ := exists_ne (1 : A)
    have he : e (a,1) = e 1 := (Prod.ext (hf a) (hg a)).trans (map_one e).symm
    exact (ha (congrArg Prod.fst (e.injective he))).elim
  · have hh := ranges_of_coordinates
      (e.toMonoidHom.comp (MulEquiv.prodComm : B × A ≃* A × B).toMonoidHom)
      (e.surjective.comp (MulEquiv.prodComm : B × A ≃* A × B).surjective) hg hf
    exact Or.inr ⟨hh.2,hh.1⟩
  · exact Or.inl (ranges_of_coordinates e.toMonoidHom e.surjective hg hf)
  · obtain ⟨b,hb⟩ := exists_ne (1 : B)
    have he : e (1,b) = e 1 := (Prod.ext (hf b) (hg b)).trans (map_one e).symm
    exact (hb (congrArg Prod.snd (e.injective he))).elim


end Theory.GroupTheory.CenterlessDirectFactors
