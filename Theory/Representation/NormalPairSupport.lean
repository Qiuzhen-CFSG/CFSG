module
public import Theory.GroupTheory.AutomorphismSquareRank
public import Theory.Representation.NormalInvariants
public import Theory.Representation.SubrepresentationLattice
public import Mathlib.LinearAlgebra.Projection

/-!
# Canonical support spaces for a normal simple square

In a faithful irreducible ambient action, a nonzero vector fixed by one factor
of a normal simple square forces the two factor-fixed spaces to be complementary.
Every ambient operator preserves or exchanges them, by the exact automorphism
normal form of the square. The construction retains arbitrary multiplicities.

Source application: Aschbacher--Smith D.3.21, printed p.206, on the original
full central quotient of the separated A₅ branch.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace Representation.NormalPairSupport
variable {k S Q V : Type*} [Field k] [Group S] [Finite S] [IsQuasisimple S]
  [Group Q] [AddCommGroup V] [Module k V]
  (ρ : Representation k Q V) (i : S × S →* Q)

/-- Vectors supported on the first factor are fixed by the second factor. -/
def left : Submodule k V := invariants (ρ.comp (i.comp (MonoidHom.inr S S)))
/-- Vectors supported on the second factor are fixed by the first factor. -/
def right : Submodule k V := invariants (ρ.comp (i.comp (MonoidHom.inl S S)))

omit [Finite S] [IsQuasisimple S] in
private theorem image_fixed_of_covariance
    {a b : S →* Q} (g : Q) (f : MulAut S)
    (h : ∀ s, g * a s * g⁻¹ = b (f s))
    {v : V} (hv : v ∈ invariants (ρ.comp a)) :
    ρ g v ∈ invariants (ρ.comp b) := by
  intro s
  obtain ⟨s,rfl⟩ := f.surjective s
  change ρ (b (f s)) (ρ g v) = ρ g v
  rw [←h]
  have he : ρ (g * a s * g⁻¹) (ρ g v) = ρ g (ρ (a s) v) := by
    simp only [←Module.End.mul_apply, ←map_mul, mul_assoc, inv_mul_cancel, mul_one]
  rw [he]
  exact congrArg (ρ g) (hv s)

/-- Normality of the marked simple square gives the two literal covariance alternatives. -/
theorem covariance_alternatives (hi : Function.Injective i) [i.range.Normal]
    (hZ : center S = ⊥) (g : Q) :
    (∃ a b : MulAut S, ∀ x y, g * i (x,y) * g⁻¹ = i (a x,b y)) ∨
      (∃ a b : MulAut S, ∀ x y, g * i (x,y) * g⁻¹ = i (a y,b x)) := by
  let e : S × S ≃* i.range := MonoidHom.ofInjective hi
  let n : MulAut i.range := i.range.normalizerMonoidHom ⟨g, by
    rw [normalizer_eq_top]; exact mem_top g⟩
  let f : MulAut (S × S) := e.trans (n.trans e.symm)
  have hf (z : S × S) : i (f z) = g * i z * g⁻¹ := by
    have he := congrArg (fun w : i.range => (w : Q)) (e.apply_symm_apply (n (e z)))
    exact he
  rcases Theory.GroupTheory.AutomorphismSquare.normal_form hZ f with ⟨a,b,hab⟩ | ⟨a,b,hab⟩
  · exact Or.inl ⟨a,b,fun x y => (hf (x,y)).symm.trans (by rw [hab]; rfl)⟩
  · exact Or.inr ⟨a,b,fun x y => (hf (x,y)).symm.trans (by rw [hab]; rfl)⟩

/-- Every ambient operator either preserves or exchanges the two support spaces. -/
theorem support_stable_or_exchanged (hi : Function.Injective i) [i.range.Normal]
    (hZ : center S = ⊥) (g : Q) :
    ((left ρ i).map (ρ g) ≤ left ρ i ∧ (right ρ i).map (ρ g) ≤ right ρ i) ∨
      ((left ρ i).map (ρ g) ≤ right ρ i ∧ (right ρ i).map (ρ g) ≤ left ρ i) := by
  rcases covariance_alternatives i hi hZ g with ⟨a,b,h⟩ | ⟨a,b,h⟩
  · left
    constructor
    · rintro _ ⟨v,hv,rfl⟩
      exact image_fixed_of_covariance ρ g b (fun s => by simpa only [map_one, MonoidHom.comp_apply, MonoidHom.inl_apply, MonoidHom.inr_apply] using h 1 s) hv
    · rintro _ ⟨v,hv,rfl⟩
      exact image_fixed_of_covariance ρ g a (fun s => by simpa only [map_one, MonoidHom.comp_apply, MonoidHom.inl_apply, MonoidHom.inr_apply] using h s 1) hv
  · right
    constructor
    · rintro _ ⟨v,hv,rfl⟩
      exact image_fixed_of_covariance ρ g a (fun s => by simpa only [map_one, MonoidHom.comp_apply, MonoidHom.inl_apply, MonoidHom.inr_apply] using h 1 s) hv
    · rintro _ ⟨v,hv,rfl⟩
      exact image_fixed_of_covariance ρ g b (fun s => by simpa only [map_one, MonoidHom.comp_apply, MonoidHom.inl_apply, MonoidHom.inr_apply] using h s 1) hv

/-- A separated nonzero vector in an irreducible ambient module forces the
sum of the two literal support spaces to be the whole module. -/
theorem support_sup_eq_top (hi : Function.Injective i) [i.range.Normal]
    (hZ : center S = ⊥) [ρ.IsIrreducible]
    (hsep : left ρ i ≠ ⊥ ∨ right ρ i ≠ ⊥) : left ρ i ⊔ right ρ i = ⊤ := by
  let U : Subrepresentation ρ := {
    toSubmodule := left ρ i ⊔ right ρ i
    apply_mem_toSubmodule g v hv := by
      obtain ⟨a,ha,b,hb,rfl⟩ := Submodule.mem_sup.mp hv
      rw [map_add]
      rcases support_stable_or_exchanged ρ i hi hZ g with h | h
      · exact Submodule.add_mem_sup (h.1 ⟨a,ha,rfl⟩) (h.2 ⟨b,hb,rfl⟩)
      · simpa only [add_comm] using
          Submodule.add_mem_sup (h.2 ⟨b,hb,rfl⟩) (h.1 ⟨a,ha,rfl⟩) }
  have hU : U ≠ ⊥ := by
    intro he
    have hu : left ρ i ⊔ right ρ i = ⊥ := congrArg Subrepresentation.toSubmodule he
    rcases hsep with h | h
    · exact h (bot_unique (le_sup_left.trans hu.le))
    · exact h (bot_unique (le_sup_right.trans hu.le))
  exact congrArg Subrepresentation.toSubmodule ((IsSimpleOrder.eq_bot_or_eq_top U).resolve_left hU)

omit [Finite S] [IsQuasisimple S] in
/-- In a faithful irreducible ambient module, no nonzero vector is fixed by
both factors of a nontrivial normal pair. -/
theorem support_disjoint (hi : Function.Injective i) [i.range.Normal]
    [Nontrivial S] [ρ.IsIrreducible] (hρ : Function.Injective ρ) :
    Disjoint (left ρ i) (right ρ i) := by
  apply Submodule.disjoint_def.mpr
  intro v hv₁ hv₂
  have hfixed : v ∈ invariants (ρ.comp i.range.subtype) := by
    rintro ⟨_,⟨⟨x,y⟩,rfl⟩⟩
    change ρ (i (x,y)) v = v
    have hp : (x,y) = (x,1) * (1,y) := by simp
    rw [hp,map_mul,map_mul,Module.End.mul_apply]
    exact (congrArg (ρ (i (x,1))) (hv₁ y)).trans (hv₂ x)
  by_contra hne
  have hk := le_ker_of_normal_invariants_ne_bot ρ i.range (by
    intro h
    have hz : v ∈ (⊥ : Submodule k V) := h ▸ hfixed
    exact hne hz)
  obtain ⟨s,hs⟩ := exists_ne (1 : S)
  have he : i (s,1) = 1 := hρ ((hk ⟨(s,1),rfl⟩).trans ρ.map_one.symm)
  exact hs (congrArg Prod.fst (hi (he.trans i.map_one.symm)))

/-- Canonical separated-support decomposition, independent of multiplicity bounds. -/
theorem support_isCompl (hi : Function.Injective i) [i.range.Normal]
    (hZ : center S = ⊥) [Nontrivial S] [ρ.IsIrreducible] (hρ : Function.Injective ρ)
    (hsep : left ρ i ≠ ⊥ ∨ right ρ i ≠ ⊥) : IsCompl (left ρ i) (right ρ i) :=
  ⟨support_disjoint ρ i hi hρ, codisjoint_iff.mpr (support_sup_eq_top ρ i hi hZ hsep)⟩
end Representation.NormalPairSupport
