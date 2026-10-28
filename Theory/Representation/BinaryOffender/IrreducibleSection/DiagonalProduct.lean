module
public import Theory.Representation.BinaryOffender.IrreducibleSection

/-!
# An Irr⁺ section cannot be a diagonal double copy

The first coordinate kernel is invariant. Irreducibility modulo fixed vectors
makes it central or makes it supplement the fixed vectors. In the two cases
the first or second copy is fixed; since the actions on both copies agree,
the entire section is fixed. This contradicts the noncentrality of an Irr⁺
section. No irreducibility or faithfulness assumption on the proposed model
is needed.

Source use: Aschbacher--Smith, combined manuscript, 1 March 2004,
Theorem 12.2.2, p.795, in the surviving A₅ case of the 6.2.20 reduction.
-/

public section
open Representation Subgroup
namespace Representation.BinaryOffender
variable {G V D W : Type*} [Group G] [Group D]
  [AddCommGroup V] [Module (ZMod 2) V]
  [AddCommGroup W] [Module (ZMod 2) W]
  (ρ : Representation (ZMod 2) G V)

set_option backward.isDefEq.respectTransparency false in
/-- Every actual Irr⁺ section excludes a diagonal product of two identical
module actions, retaining the original acting-group homomorphism. -/
theorem IsIrrPlus.not_diagonal_product {X : Subgroup G} {I : Submodule (ZMod 2) V}
    (hI : IsIrrPlus ρ X I) (σ : Representation (ZMod 2) D W)
    (f : X →* D) (e : I ≃ₗ[ZMod 2] W × W)
    (he : ∀ (g : X) (v : I),
      e ((invariantSubspace ρ X I hI.choose).toRepresentation g v) =
        (σ (f g) (e v).1, σ (f g) (e v).2)) : False := by
  let τ := (invariantSubspace ρ X I hI.choose).toRepresentation
  let C := centralSubspace ρ X I hI.choose
  let : IsIrreducible C.quotientRepresentation := hI.choose_spec.2
  let J : Subrepresentation τ :=
    ⟨(LinearMap.snd (ZMod 2) W W).comp e.toLinearMap |>.ker, by
      intro g v hv
      change (e (τ g v)).2 = 0
      rw [he]
      change σ (f g) (e v).2 = 0
      change (e v).2 = 0 at hv
      rw [hv, map_zero]⟩
  have hfix (g : X) (w : W) : σ (f g) w = w := by
    rcases Subrepresentation.le_or_sup_eq_top_of_irreducible_quotient C J with h | h
    · let v := e.symm (w, 0)
      have hv : v ∈ J := by change (e v).2 = 0; simp [v]
      have hc : v ∈ C := h hv
      have hg : τ g v = v := Subtype.ext (hc g)
      have hh := congrArg (fun v : I => (e v).1) hg
      rw [he] at hh
      simpa only [v, e.apply_symm_apply] using hh
    · let v := e.symm (0, w)
      have hv : v ∈ C.toSubmodule ⊔ J.toSubmodule := by
        rw [h]
        trivial
      obtain ⟨c, hc, j, hj, hv⟩ := Submodule.mem_sup.mp hv
      have hcfix : τ g c = c := Subtype.ext (hc g)
      have hh := congrArg (fun c : I => (e c).2) hcfix
      rw [he] at hh
      have hj0 : (e j).2 = 0 := hj
      have hw : (e c).2 = w := by
        have hh := congrArg (fun v : I => (e v).2) hv
        simpa only [map_add, Prod.fst_add, Prod.snd_add, hj0, add_zero,
          v, e.apply_symm_apply] using hh
      simpa only [hw] using hh
  apply hI.not_le_fixedSpace ρ
  intro v hv g
  have heq := he g ⟨v, hv⟩
  rw [hfix, hfix] at heq
  have hh := e.injective heq
  exact congrArg Subtype.val hh

end Representation.BinaryOffender
