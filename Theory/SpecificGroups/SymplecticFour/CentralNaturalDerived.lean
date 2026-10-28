module
public import Theory.GroupTheory.ClassTwoCentralOrbit
public import Theory.SpecificGroups.SymplecticFour.NaturalPointCoinvariants
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.TwoLocalCover.Geometry
/-!
# Central derived groups with a natural symplectic quotient

Let a group act on a central extension of the natural symplectic four-space
and fix its derived group pointwise. Natural-vector transitivity makes every
nonzero commutator row generate the derived group. Descending one row through
the central kernel, its point-stabilizer invariance bounds its image by the
coefficient field. In particular the derived group has order at most four in
the Sp4(4) case. No splitting of the central kernel is assumed.

Source: MS93 (3.10)(i), printed p.880, used in the terminal proof of (5.12).
-/
public section
open Subgroup
open scoped commutatorElement

namespace Subgroup.ClassTwo
open Theory.SpecificGroups.SymplecticFour
variable {P A F : Type*} [Group P] [Group A] [Field F]

theorem commutator_eq_row_of_symplectic_section
    (α : A →* MulAut P) (π : A →* Sp F) (hπ : Function.Surjective π)
    (f : P →* Multiplicative (Vector F)) (hker : f.ker ≤ center P)
    (hequiv : ∀ a v, (f (α a v)).toAdd = π a • (f v).toAdd)
    (hfix : ∀ a : A, ∀ c ∈ _root_.commutator P, α a c = c)
    (x : P) (hx : f x ≠ 1) :
    _root_.commutator P = ⁅zpowers x,(⊤ : Subgroup P)⁆ := by
  apply commutator_eq_row_of_central_orbit α hfix x
  intro y hy
  have hy0 : (f y).toAdd ≠ 0 := fun h => hy (hker h)
  obtain ⟨g,hg⟩ := TwoLocalCover.nonzero_vector_transitive
    (show (f x).toAdd ≠ 0 from hx) hy0
  obtain ⟨a,rfl⟩ := hπ g
  refine ⟨a,hker ?_⟩
  change f ((α a x)⁻¹ * y) = 1
  rw [map_mul,map_inv]
  have he : f (α a x) = f y := Multiplicative.toAdd.injective ((hequiv a x).trans hg)
  rw [he,inv_mul_cancel]
end Subgroup.ClassTwo

namespace Subgroup.ClassTwo
open Theory.SpecificGroups.SymplecticFour
variable {P A F : Type*} [Group P] [Group A] [Field F] [CharP F 2] [Finite F]

/-- The nonbinary natural-module bound on a central derived group. -/
theorem card_commutator_le_of_symplectic_section
    (hc : _root_.commutator P ≤ center P)
    (α : A →* MulAut P) (π : A →* Sp F) (hπ : Function.Surjective π)
    (f : P →* Multiplicative (Vector F)) (hf : Function.Surjective f)
    (hker : f.ker ≤ center P)
    (hequiv : ∀ a v, (f (α a v)).toAdd = π a • (f v).toAdd)
    (hfix : ∀ a : A, ∀ c ∈ _root_.commutator P, α a c = c) :
    Nat.card (_root_.commutator P) ≤ Nat.card F := by
  obtain ⟨x,hx⟩ := hf (Multiplicative.ofAdd (e 0))
  have hx0 : f x ≠ 1 := by
    rw [hx]
    intro h
    have hh := congrFun (congrArg Multiplicative.toAdd h) (.inl 0)
    simp [Theory.SpecificGroups.SymplecticFour.e] at hh
  have hrow := commutator_eq_row_of_symplectic_section α π hπ f hker hequiv hfix x hx0
  let r := commutatorHom hc x
  have hkr : f.ker ≤ r.ker := by
    intro u hu
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mem_center_iff.mp (hker hu) x)
  let φ : Multiplicative (Vector F) →* P := f.liftOfSurjective hf ⟨r,hkr⟩
  have hφ (u : P) : φ (f u) = ⁅x,u⁆ := f.liftOfRightInverse_comp_apply _ _ _ u
  have hinv (g : pointLocal (F := F)) (v : Vector F) :
      φ (Multiplicative.ofAdd (g.val • v)) = φ (Multiplicative.ofAdd v) := by
    obtain ⟨a,ha⟩ := hπ g.val
    obtain ⟨u,hu⟩ := hf (Multiplicative.ofAdd v)
    have hv : f (α a u) = Multiplicative.ofAdd (g.val • v) := by
      apply Multiplicative.toAdd.injective
      rw [hequiv,ha,hu]
      rfl
    have hax : f (α a x) = f x := by
      apply Multiplicative.toAdd.injective
      rw [hequiv,ha,hx]
      exact (mem_pointLocal_iff_fixed g.val).mp g.property
    have hk : (α a x)⁻¹ * x ∈ center P := hker (by
      change f ((α a x)⁻¹ * x) = 1
      rw [map_mul,map_inv,hax,inv_mul_cancel])
    have hz : ⁅(α a x)⁻¹ * x,α a u⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr ((mem_center_iff.mp hk _).symm)
    have he : ⁅x,α a u⁆ = ⁅α a x,α a u⁆ := by
      calc
        _ = ⁅α a x * ((α a x)⁻¹ * x),α a u⁆ := by group
        _ = _ := by rw [commutatorElement_mul_left_eq_conj_mul,hz]; simp
    rw [←hv,←hu,hφ,hφ,he,←map_commutatorElement]
    exact hfix a _ (commutator_mem_commutator (mem_top _) (mem_top _))
  have hrange : φ.range = _root_.commutator P := by
    have he : φ.range = r.range := by
      apply le_antisymm
      · rintro _ ⟨v,rfl⟩
        obtain ⟨u,rfl⟩ := hf v
        exact ⟨u,hφ u |>.symm⟩
      · rintro _ ⟨u,rfl⟩
        exact ⟨f u,hφ u⟩
    rw [he,commutatorHom_range,hrow]
  rw [←hrange]
  exact pointInvariantHom_card_le φ hinv
end Subgroup.ClassTwo
