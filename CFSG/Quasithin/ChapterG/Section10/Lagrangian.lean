module
public import CFSG.Quasithin.ChapterG.Section10.Recognition
public import CFSG.Quasithin.ChapterG.Section10.TwoCore
public import Theory.LinearAlgebra.BinaryInvariantAlternating
public import Theory.Representation.SymplecticLagrangianDuality
public import Theory.LinearAlgebra.AlternatingFinrank

/-!
# The actual Lagrangian reduction in G.10.4

A proper irreducible submodule of dimension at least three carries the full
linear action, so the original form vanishes there. The source rank equality
then forces it to be its own orthogonal complement. Its action kernel fixes
both successive layers, has exponent two, and vanishes by G.10.3. Thus the
remaining splitting problem has the original faithful group GL(U), without
an additional recognition or kernel hypothesis.

Source: Aschbacher--Smith, G.10.4, printed p.358, case H=G.
-/

public section
open Subgroup Module Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterG.Section10.Hypothesis
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {B : LinearMap.BilinForm (ZMod 2) V}
  {v : V} {W : Submodule (ZMod 2) V} {X : Subgroup G}
  [IsElementaryAbelian 2 X] {X₀ : Subgroup X}
  (h : Hypothesis ρ B v W X X₀)
include h

/-- A proper invariant plane forces exactly the source degree four. -/
theorem degree_four_of_plane_submodule (U : Subrepresentation ρ)
    (hU0 : U.toSubmodule ≠ ⊥) (hUt : U.toSubmodule ≠ ⊤)
    (hdim : finrank (ZMod 2) U.toSubmodule = 2) : finrank (ZMod 2) V = 4 := by
  have he := (h.full_axis_on_submodule U hU0 hUt).2.1
  have hb := h.dimension_bound.1
  have ht := Submodule.finrank_lt hUt
  obtain ⟨m, hm⟩ := AlternatingForm.even_finrank B h.alternating h.nondegenerate
  omega

/-- In the large-degree reducible branch the literal submodule is Lagrangian. -/
theorem lagrangian_of_large_irreducible_submodule (U : Subrepresentation ρ)
    [IsIrreducible U.toRepresentation] (hU0 : U.toSubmodule ≠ ⊥)
    (hUt : U.toSubmodule ≠ ⊤) (hdim : 3 ≤ finrank (ZMod 2) U.toSubmodule) :
    B.orthogonal U.toSubmodule = U.toSubmodule ∧
      finrank (ZMod 2) V = 2 * finrank (ZMod 2) U.toSubmodule := by
  have hz : B.restrict U.toSubmodule = 0 :=
    (B.restrict U.toSubmodule).eq_zero_of_full_binary_linear_invariance
      (fun u => h.alternating u) (by
        intro e u w
        obtain ⟨g, hg⟩ := h.full_linear_on_irreducible_submodule U hU0 hUt e
        rw [← hg u, ← hg w]
        exact h.preserves g u w) hdim
  have hi : ∀ u ∈ U.toSubmodule, ∀ w ∈ U.toSubmodule, B u w = 0 := by
    intro u hu w hw
    exact congrArg (fun b : LinearMap.BilinForm (ZMod 2) U.toSubmodule => b ⟨u,hu⟩ ⟨w,hw⟩) hz
  have hle : U.toSubmodule ≤ B.orthogonal U.toSubmodule := fun u hu w hw => hi w hw u hu
  have hsize := B.twice_finrank_le_of_isotropic h.nondegenerate U.toSubmodule hi
  have heq := (h.full_axis_on_submodule U hU0 hUt).2.1
  have hb := h.dimension_bound.1
  have hd : finrank (ZMod 2) V = 2 * finrank (ZMod 2) U.toSubmodule := by omega
  refine ⟨(Submodule.eq_of_le_of_finrank_eq hle ?_).symm, hd⟩
  rw [B.finrank_orthogonal h.nondegenerate]
  omega

/-- The action of the original group on that actual Lagrangian is faithful. -/
theorem faithful_on_large_irreducible_submodule (U : Subrepresentation ρ)
    [IsIrreducible U.toRepresentation] (hU0 : U.toSubmodule ≠ ⊥)
    (hUt : U.toSubmodule ≠ ⊤) (hdim : 3 ≤ finrank (ZMod 2) U.toSubmodule) :
    Function.Injective U.toRepresentation := by
  have horth := (h.lagrangian_of_large_irreducible_submodule U hU0 hUt hdim).1
  let K := U.toRepresentation.asGroupHom.ker
  have hfix (x : K) (u : U.toSubmodule) : ρ (x : G) u = u := by
    have he : U.toRepresentation (x : G) u = u :=
      congrArg (fun a : LinearMap.GeneralLinearGroup (ZMod 2) U.toSubmodule => a.val u) x.property
    exact congrArg Subtype.val he
  have hm (x : K) (w : V) : ρ (x : G) w - w ∈ U.toSubmodule := by
    rw [← horth]
    intro u hu
    have he := h.preserves (x : G) u w
    rw [hfix x ⟨u,hu⟩] at he
    exact (map_sub (B u) _ _).trans (sub_eq_zero.mpr he)
  have hp : IsPGroup 2 K := by
    intro x
    refine ⟨1, ?_⟩
    apply Subtype.ext
    apply h.faithful
    ext w
    have he := hfix x ⟨ρ (x : G) w - w, hm x w⟩
    rw [map_sub] at he
    have htwo (u : V) : u + u = 0 := by
      simpa only [add_smul, one_smul, zero_smul] using
        congrArg (fun c : ZMod 2 => c • u) (show (1 : ZMod 2) + 1 = 0 by decide)
    have hh : ρ (x : G) (ρ (x : G) w) = w := by
      apply add_right_cancel (b := w)
      exact (sub_eq_sub_iff_add_eq_add.mp he).trans ((htwo _).trans (htwo w).symm)
    simpa only [pow_one, pow_two, Subgroup.coe_mul, Subgroup.coe_one, map_mul, Module.End.mul_apply,
      map_one, Module.End.one_apply] using hh
  have hK : K = ⊥ := by
    apply bot_unique
    have he : K ≤ pCore 2 G := le_sSup ⟨inferInstance, hp⟩
    rwa [h.twoCore_eq_bot] at he
  intro a b hab
  apply (MonoidHom.ker_eq_bot_iff U.toRepresentation.asGroupHom).mp hK
  exact Units.ext hab

/-- The original actor is identified with the full linear group on the
literal invariant subspace, with the action itself as the marking. -/
theorem exists_full_linear_marking_of_large_irreducible_submodule (U : Subrepresentation ρ)
    [IsIrreducible U.toRepresentation] (hU0 : U.toSubmodule ≠ ⊥)
    (hUt : U.toSubmodule ≠ ⊤) (hdim : 3 ≤ finrank (ZMod 2) U.toSubmodule) :
    ∃ e : G ≃* (U.toSubmodule ≃ₗ[ZMod 2] U.toSubmodule),
      ∀ g u, e g u = U.toRepresentation g u := by
  let f := (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) U.toSubmodule).toMonoidHom.comp
    U.toRepresentation.asGroupHom
  have hf : Function.Injective f := by
    intro a b he
    apply h.faithful_on_large_irreducible_submodule U hU0 hUt hdim
    apply LinearMap.ext
    intro u
    exact congrArg (fun t : U.toSubmodule ≃ₗ[ZMod 2] U.toSubmodule => t u) he
  have hs : Function.Surjective f := by
    intro e
    obtain ⟨g, hg⟩ := h.full_linear_on_irreducible_submodule U hU0 hUt e
    exact ⟨g, LinearEquiv.ext hg⟩
  exact ⟨MulEquiv.ofBijective f ⟨hf,hs⟩, fun _ _ => rfl⟩

/-- The natural-by-dual factors use the original quotient map and pairing. -/
theorem quotient_dual_of_large_irreducible_submodule (U : Subrepresentation ρ)
    [IsIrreducible U.toRepresentation] (hU0 : U.toSubmodule ≠ ⊥)
    (hUt : U.toSubmodule ≠ ⊤) (hdim : 3 ≤ finrank (ZMod 2) U.toSubmodule) :
    ∃ e : Representation.Equiv U.quotientRepresentation U.toRepresentation.dual,
      ∀ w, e (U.toSubmodule.mkQ w) = submodulePairing ρ B U w :=
  exists_lagrangian_quotient_dual_equiv ρ B h.alternating h.nondegenerate h.preserves U
    (h.lagrangian_of_large_irreducible_submodule U hU0 hUt hdim).1

end CFSG.Quasithin.ChapterG.Section10.Hypothesis
