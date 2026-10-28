module
public import Theory.Representation.BinaryConjugationSection.FixedMoving
public import Theory.Representation.SL2FourNaturalBorelFixedLifting.Gaschutz
public import Theory.GroupTheory.ConjugateSpanOrder

/-!
# Gaschütz decomposition of a conjugate-generated binary section

If the seed of an actual conjugate span is fixed modulo the section kernel
by a Sylow two-subgroup, its coordinates are sums of moving vectors and
globally fixed vectors. Gaschütz lifts the fixed seed modulo the moving
space; invariance and conjugate generation extend the result to the whole
section. No complement to the central kernel is chosen.

Source application: Aschbacher--Smith, 14.6.23(3), printed p.1038,
using A.1.39.
-/

public section
open Subgroup
namespace Representation.BinaryConjugationSection
open OneCohomology BinaryOffender
variable {G X : Type*} [Group G] [Finite G]
  [AddCommGroup X] [Module (ZMod 2) X] [Finite X]
  {H U Z : Subgroup G} {ρ : Representation (ZMod 2) H X}

/-- Decomposition on the coordinates of the literal U/Z, proved from
Sylow-fixed seed generation and trivial action on the moving quotient. -/
theorem sup_fixed_eq_top_of_sylow_fixed_seed
    (c : BinaryConjugationSection H U Z ρ)
    (V : Subgroup G) (hVU : V ≤ U) (hgen : U = conjugateSpanBy V H)
    (S : Sylow 2 H)
    (hfixed : ∀ v : V, ∀ s : S,
      ρ s.val (c.coordinates (inclusion hVU v)).toAdd =
        (c.coordinates (inclusion hVU v)).toAdd)
    (N : Submodule (ZMod 2) X) (hd : ∀ h x, ρ h x - x ∈ N) :
    N ⊔ fixed ρ = ⊤ := by
  let P₀ : Subgroup U := ((N ⊔ fixed ρ).toAddSubgroup.toSubgroup).comap c.coordinates
  let P := P₀.map U.subtype
  have hVP : V ≤ P := by
    intro v hv
    let vU : U := ⟨v,hVU hv⟩
    obtain ⟨w,hw,hn⟩ := SL2FourNaturalBorelFixedLifting.exists_fixed_lift
      ρ N hd S (c.coordinates vU).toAdd (hfixed ⟨v,hv⟩)
    refine ⟨vU,?_,rfl⟩
    change (c.coordinates vU).toAdd ∈ N ⊔ fixed ρ
    have hh := (N ⊔ fixed ρ).add_mem
      ((le_sup_left : N ≤ N ⊔ fixed ρ) hn)
      ((le_sup_right : fixed ρ ≤ N ⊔ fixed ρ) (show w ∈ fixed ρ from hw))
    simpa only [sub_add_cancel] using hh
  have hHP : H ≤ normalizer (P : Set G) := by
    apply le_normalizer_iff.mpr
    intro h hh p hp
    obtain ⟨u,hu,rfl⟩ := hp
    let v : U := ⟨h*u*h⁻¹,(mem_normalizer_iff.mp (c.normalized hh) u).mp u.property⟩
    refine ⟨v,?_,rfl⟩
    change (c.coordinates v).toAdd ∈ N ⊔ fixed ρ
    rw [c.equivariant ⟨h,hh⟩ u]
    have hm := (N ⊔ fixed ρ).add_mem
      ((le_sup_left : N ≤ N ⊔ fixed ρ) (hd ⟨h,hh⟩ (c.coordinates u).toAdd)) hu
    simpa only [sub_add_cancel] using hm
  have hUP : U ≤ P := hgen ▸ conjugateSpanBy_le hVP hHP
  apply top_unique
  intro x _
  obtain ⟨u,hu⟩ := c.onto (Multiplicative.ofAdd x)
  obtain ⟨v,hv,he⟩ := hUP u.property
  have hve : v = u := Subtype.ext he
  subst v
  change (c.coordinates u).toAdd ∈ N ⊔ fixed ρ at hv
  rw [hu] at hv
  exact hv

/-- A literal factorization H=JS and an S-fixed seed reduce the moving
space to the J-displacements. No prior triviality of the H-quotient is
assumed: conjugate generation proves that every H-displacement lies there. -/
theorem sup_fixed_eq_top_of_sylow_supplement
    (c : BinaryConjugationSection H U Z ρ)
    (V : Subgroup G) (hVU : V ≤ U) (hgen : U = conjugateSpanBy V H)
    (S : Sylow 2 H)
    (hfixed : ∀ v : V, ∀ s : S,
      ρ s.val (c.coordinates (inclusion hVU v)).toAdd =
        (c.coordinates (inclusion hVU v)).toAdd)
    (J : Subgroup H)
    (hsplit : ∀ h : H, ∃ j ∈ J, ∃ s ∈ (S : Subgroup H), j * s = h)
    (N : Submodule (ZMod 2) X) (hd : ∀ j ∈ J, ∀ x, ρ j x - x ∈ N) :
    N ⊔ fixed ρ = ⊤ := by
  let E : Submodule (ZMod 2) X := ⨅ a : H, N.comap (ρ a - 1)
  have hmem (x : X) : x ∈ E ↔ ∀ a, ρ a x - x ∈ N := by
    simp [E]
  have hE (a : H) (x : X) (hx : x ∈ E) : ρ a x ∈ E := by
    apply (hmem _).mpr
    intro b
    have hn := N.sub_mem ((hmem _).mp hx (b*a)) ((hmem _).mp hx a)
    convert hn using 1
    simp only [map_mul, Module.End.mul_apply]
    abel
  let P₀ : Subgroup U := E.toAddSubgroup.toSubgroup.comap c.coordinates
  let P := P₀.map U.subtype
  have hVP : V ≤ P := by
    intro v hv
    let vU : U := ⟨v,hVU hv⟩
    refine ⟨vU,?_,rfl⟩
    change (c.coordinates vU).toAdd ∈ E
    apply (hmem _).mpr
    intro h
    obtain ⟨j,hj,s,hs,rfl⟩ := hsplit h
    have hf : ρ s (c.coordinates vU).toAdd = (c.coordinates vU).toAdd :=
      hfixed ⟨v,hv⟩ ⟨s,hs⟩
    rw [map_mul, Module.End.mul_apply, hf]
    exact hd j hj _
  have hHP : H ≤ normalizer (P : Set G) := by
    apply le_normalizer_iff.mpr
    intro h hh p hp
    obtain ⟨u,hu,rfl⟩ := hp
    let v : U := ⟨h*u*h⁻¹,(mem_normalizer_iff.mp (c.normalized hh) u).mp u.property⟩
    refine ⟨v,?_,rfl⟩
    change (c.coordinates v).toAdd ∈ E
    rw [c.equivariant ⟨h,hh⟩ u]
    exact hE ⟨h,hh⟩ _ hu
  have hUP : U ≤ P := hgen ▸ conjugateSpanBy_le hVP hHP
  apply c.sup_fixed_eq_top_of_sylow_fixed_seed V hVU hgen S hfixed N
  intro a x
  obtain ⟨u,hu⟩ := c.onto (Multiplicative.ofAdd x)
  obtain ⟨v,hv,he⟩ := hUP u.property
  have hve : v = u := Subtype.ext he
  subst v
  change (c.coordinates u).toAdd ∈ E at hv
  rw [hu] at hv
  exact (hmem _).mp hv a

end Representation.BinaryConjugationSection
