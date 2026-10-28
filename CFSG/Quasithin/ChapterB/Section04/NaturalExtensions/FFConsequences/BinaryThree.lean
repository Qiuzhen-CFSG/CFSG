module
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.FFConsequences
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.AbelianCore.QuotientRecognition.ExtensionControl.SelfExtensions
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.AbelianCore.QuotientRecognition.ExtensionControl.DualExclusion
public import Theory.Representation.PSL3Two.IrreducibleCatalogue.Irreducibility
public import Mathlib.LinearAlgebra.Projection

/-!
# The binary SL₃ branch of B.4.9(2)

The literal SL₃(2) elementary rank bound and the two faithful factor costs
exclude the dual orientation and force quadratic ratio one. The existing
matrix-derivation theorem splits the homogeneous extension abstractly.
Projecting that product onto a nonzero coordinate of the irreducible
original submodule constructs an equivariant retraction; its kernel is a
complement to that original submodule.

Thus B.4.9(2)(i)–(ii) in field degree one requires no extra splitting
premise. The larger-field and dimensions at least four remain separate.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
B.4.9, printed pp.92–94.
-/

public section
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.NaturalExtensions
open QuasisimpleSource
namespace DoubleNatural
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
  (d : DoubleNatural BinaryField.two 3 ρ)

omit [FiniteDimensional (ZMod 2) V] in
include d in
private theorem binary_three_rank_le_two {A : Subgroup G} (hA : IsElementaryTwo A) :
    rank A ≤ 2 := by
  let f := d.natural.groupEquiv.toMonoidHom
  let : IsElementaryAbelian 2 A := hA.2
  have he : IsElementaryAbelian 2 (A.map f) := IsElementaryAbelian.map f
  have hr := ChapterC.BinaryMS.AbelianCore.QuotientRecognition.ExtensionControl.elementary_rank_le_two
    (A.map f) he
  exact (rank_map_injective f d.natural.groupEquiv.injective A).symm.trans_le hr

/-- The quotient in a binary SL₃ FF-extension has the same orientation as
its marked natural submodule. No splitting hypothesis is used. -/
theorem binary_three_same_orientation (hff : IsFFModule ρ) :
    Nonempty (d.space.quotientRepresentation.Equiv d.space.toRepresentation) := by
  rcases d.quotient with h | h
  · exact h
  · obtain ⟨e⟩ := h
    obtain ⟨A, hA⟩ := hff
    have := d.binary_three_rank_le_two hA.1
    let : Finite G := Finite.of_injective d.natural.groupEquiv d.natural.groupEquiv.injective
    have := (d.dual_offender_bounds e hA).2.2
    omega

include d in
/-- The exact quadratic ratio in B.4.9(2)(ii) for the binary SL₃ case. -/
theorem binary_three_ratio (hff : IsFFModule ρ) : quadraticRatio ρ = 1 := by
  let : Finite G := Finite.of_injective d.natural.groupEquiv d.natural.groupEquiv.injective
  apply quadraticRatio_eq_one_of_no_strong ρ hff
  intro A hA
  obtain ⟨h1, h2⟩ := d.factor_costs_pos hA.1.1
  have := d.binary_three_rank_le_two hA.1
  have := fixedCodim_quotient_add_subrepresentation_le ρ d.space A
  have := hA.2
  omega

omit [FiniteDimensional (ZMod 2) V] in
private theorem complement_of_product {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    {σ : Representation (ZMod 2) G W} [IsIrreducible σ]
    (N : Subrepresentation ρ) (eN : N.toRepresentation.Equiv σ)
    (eV : ρ.Equiv (σ.prod σ)) :
    ∃ C : Subrepresentation ρ, IsCompl N.toSubmodule C.toSubmodule := by
  let p₁ : ρ.IntertwiningMap σ :=
    ⟨(LinearMap.fst (ZMod 2) W W).comp eV.toLinearEquiv.toLinearMap, by
      intro g
      ext v
      exact congrArg Prod.fst (LinearMap.congr_fun (eV.isIntertwining' g) v)⟩
  let p₂ : ρ.IntertwiningMap σ :=
    ⟨(LinearMap.snd (ZMod 2) W W).comp eV.toLinearEquiv.toLinearMap, by
      intro g
      ext v
      exact congrArg Prod.snd (LinearMap.congr_fun (eV.isIntertwining' g) v)⟩
  let i : σ.IntertwiningMap ρ :=
    ⟨N.toSubmodule.subtype.comp eN.symm.toLinearEquiv.toLinearMap, by
      intro g
      ext w
      exact congrArg Subtype.val (LinearMap.congr_fun (eN.symm.isIntertwining' g) w)⟩
  have hex : ∃ p : ρ.IntertwiningMap σ, Function.Bijective (p.comp i) := by
    rcases IsIrreducible.bijective_or_eq_zero (p₁.comp i) with h | h₁
    · exact ⟨p₁, h⟩
    rcases IsIrreducible.bijective_or_eq_zero (p₂.comp i) with h | h₂
    · exact ⟨p₂, h⟩
    have hi : ∀ w, i w = 0 := by
      intro w
      apply eV.toLinearEquiv.injective
      rw [map_zero]
      apply Prod.ext
      · exact congrArg (fun f : σ.IntertwiningMap σ => f w) h₁
      · exact congrArg (fun f : σ.IntertwiningMap σ => f w) h₂
    have ht : (⊤ : Subrepresentation σ) = ⊥ := by
      apply Subrepresentation.toSubmodule_injective
      apply bot_unique
      intro w _
      have he : i w = i 0 := (hi w).trans (hi 0).symm
      exact eN.symm.toLinearEquiv.injective (Subtype.ext he)
    exact (top_ne_bot ht).elim
  obtain ⟨p, hp⟩ := hex
  let e := (p.comp i).ofBijective hp
  let r : ρ.IntertwiningMap N.toRepresentation :=
    eN.symm.toIntertwiningMap.comp (e.symm.toIntertwiningMap.comp p)
  let C : Subrepresentation ρ :=
    ⟨r.toLinearMap.ker, by
      intro g v hv
      change r (ρ g v) = 0
      rw [r.isIntertwining, show r v = 0 from hv, map_zero]⟩
  refine ⟨C, LinearMap.isCompl_of_proj ?_⟩
  intro v
  change eN.symm (e.symm (p v.val)) = v
  have he : p v.val = e (eN v) := by
    change p v.val = p (i (eN v))
    change p v.val = p (eN.symm (eN v)).val
    rw [eN.symm_apply_apply]
  rw [he, e.symm_apply_apply, eN.symm_apply_apply]

set_option backward.isDefEq.respectTransparency false in
omit [FiniteDimensional (ZMod 2) V] in
/-- The binary SL₃ homogeneous extension has a complement to the original
submodule, not merely an abstract product-module isomorphism. -/
theorem binary_three_splits_of_same_orientation
    (eQ : d.space.quotientRepresentation.Equiv d.space.toRepresentation) : d.Splits := by
  let f := d.natural.groupEquiv
  let τ := ρ.comp f.symm.toMonoidHom
  let N : Subrepresentation τ :=
    ⟨d.space.toSubmodule, fun g _ hv => d.space.apply_mem_toSubmodule (f.symm g) hv⟩
  let eN : N.toRepresentation.Equiv BinaryLinearThree.W :=
    .mk d.natural.linearEquiv (by
      intro g
      apply LinearMap.ext
      intro v
      exact (d.natural.intertwines (f.symm g) v).trans (by rw [f.apply_symm_apply]; rfl))
  let eQ' : N.quotientRepresentation.Equiv BinaryLinearThree.W :=
    .mk (eQ.toLinearEquiv.trans d.natural.linearEquiv) (by
      intro g
      apply LinearMap.ext
      intro v
      change d.natural.linearEquiv (eQ (d.space.quotientRepresentation (f.symm g) v)) = _
      have h := LinearMap.congr_fun (eQ.isIntertwining' (f.symm g)) v
      change eQ (d.space.quotientRepresentation (f.symm g) v) =
        d.space.toRepresentation (f.symm g) (eQ v) at h
      exact (congrArg d.natural.linearEquiv h).trans
        ((d.natural.intertwines (f.symm g) (eQ v)).trans (by rw [f.apply_symm_apply]; rfl)))
  obtain ⟨e⟩ := ChapterC.BinaryMS.AbelianCore.QuotientRecognition.ExtensionControl.homogeneous_splitting
    τ N (MulEquiv.refl _) ⟨eN⟩ ⟨eQ'⟩
  let : IsIrreducible BinaryLinearThree.W := BinaryLinearThree.IrreducibleCatalogue.natural_irreducible
  obtain ⟨C, hC⟩ := complement_of_product (σ := BinaryLinearThree.W) N eN e
  let C' : Subrepresentation ρ := ⟨C.toSubmodule, by
    intro g v hv
    have hc := C.apply_mem_toSubmodule (f g) hv
    change ρ (f.symm (f g)) v ∈ C.toSubmodule at hc
    simpa only [f.symm_apply_apply] using hc⟩
  exact ⟨C', hC⟩

/-- Both source conclusions in the binary SL₃ branch, with the original
natural submodule and an actual equivariant quotient identification. -/
theorem binary_three_ff (hff : IsFFModule ρ) : d.Splits ∧
    Nonempty (d.space.quotientRepresentation.Equiv d.space.toRepresentation) ∧
      quadraticRatio ρ = 1 := by
  obtain ⟨e⟩ := d.binary_three_same_orientation hff
  exact ⟨d.binary_three_splits_of_same_orientation e, ⟨e⟩, d.binary_three_ratio hff⟩
end DoubleNatural
end CFSG.Quasithin.ChapterB.NaturalExtensions
