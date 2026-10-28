module
public import Theory.Representation.NormalSemisimpleSpan
public import Theory.Representation.SubrepresentationLattice
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.RingTheory.SimpleModule.Basic
/-!
# Constituent types in a normal subgroup's ambient span

For a normal subgroup D, an irreducible model invariant under conjugation by H
has an H-invariant span of all its intertwiner images. Thus H-generating seeds
contained in the ranges of two such models force the sum of their type spans
to be the whole restriction. If the restriction is semisimple, project onto any
simple constituent: a nonzero composite from one model identifies its type.

The actual consumer is the trivial-or-Steinberg restriction of the original
U_H/V₁ in Aschbacher--Smith, 13.6, printed p.918.
-/

@[expose] public noncomputable section
open scoped MonoidAlgebra
namespace Representation
variable {k G V W : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W]

/-- Pull back an intertwiner through an actor homomorphism. -/
def IntertwiningMap.compActors (ρ : Representation k G V) (τ : Representation k G W)
    (f : ρ.IntertwiningMap τ) {D : Type*} [Group D] (p : D →* G) :
    IntertwiningMap (ρ.comp p) (τ.comp p) where
  toLinearMap := f.toLinearMap
  isIntertwining' d := f.isIntertwining' (p d)

/-- The sum of all images of one representation inside another. -/
def typeSpan (ρ : Representation k G V) (τ : Representation k G W) : Subrepresentation ρ :=
  ⨆ f : τ.IntertwiningMap ρ, f.range

/-- Ambient conjugation of a map twists its domain representation. -/
def conjugateIntertwiner {H : Type*} [Group H]
    (ρ : Representation k H V) (D : Subgroup H) [D.Normal]
    (τ : Representation k D W) (f : τ.IntertwiningMap (ρ.comp D.subtype)) (x : H) :
    (conjugateRep (G := H) τ x).IntertwiningMap (ρ.comp D.subtype) where
  toLinearMap := (ρ x⁻¹).comp f.toLinearMap
  isIntertwining' d := by
    ext w
    change ρ x⁻¹ (f (τ ⟨x * d.val * x⁻¹,_⟩ w)) = ρ d.val (ρ x⁻¹ (f w))
    rw [f.isIntertwining]
    change ρ x⁻¹ (ρ (x*d.val*x⁻¹) (f w)) = _
    simp only [← Module.End.mul_apply, ← map_mul]
    congr 1
    group

/-- A conjugation-invariant model type has an ambient invariant type span. -/
theorem typeSpan_normal_stable {H : Type*} [Group H]
    (ρ : Representation k H V) (D : Subgroup H) [D.Normal]
    (τ : Representation k D W)
    (ht : ∀ x : H, Nonempty ((conjugateRep (G := H) τ x).Equiv τ))
    (x : H) (v : V) (hv : v ∈ typeSpan (ρ.comp D.subtype) τ) :
    ρ x v ∈ typeSpan (ρ.comp D.subtype) τ := by
  let R := typeSpan (ρ.comp D.subtype) τ
  let P : Subrepresentation (ρ.comp D.subtype) := {
    toSubmodule := R.toSubmodule.comap (ρ x)
    apply_mem_toSubmodule d w hw := by
      change ρ x (ρ d.val w) ∈ R.toSubmodule
      let d' : D := ⟨x*d.val*x⁻¹, Subgroup.Normal.conj_mem (inferInstance : D.Normal) d.val d.property x⟩
      have hh := R.apply_mem_toSubmodule d' hw
      change ρ (x*d.val*x⁻¹) (ρ x w) ∈ R.toSubmodule at hh
      simpa only [← Module.End.mul_apply, ← map_mul, mul_assoc, inv_mul_cancel, mul_one] using hh }
  have hle : R ≤ P := by
    apply iSup_le
    intro f w hw
    obtain ⟨a,rfl⟩ := hw
    obtain ⟨e⟩ := ht x⁻¹
    let f' := (conjugateIntertwiner ρ D τ f x⁻¹).comp e.symm.toIntertwiningMap
    change ρ x (f a) ∈ R
    apply (show f'.range ≤ R from le_iSup _ f')
    refine ⟨e a, ?_⟩
    change ρ (x⁻¹)⁻¹ (f (e.symm (e a))) = ρ x (f a)
    rw [e.symm_apply_apply, inv_inv]
  exact hle hv
variable {W₀ : Type*} [AddCommGroup W₀] [Module k W₀]

/-- Two conjugation-invariant model types containing the ambient generating
seeds span the complete restricted representation. -/
theorem typeSpan_sup_eq_top_of_seed {H : Type*} [Group H]
    (ρ : Representation k H V) (D : Subgroup H) [D.Normal]
    (τ₀ : Representation k D W₀) (τ₁ : Representation k D W)
    (ht₀ : ∀ x : H, Nonempty ((conjugateRep (G := H) τ₀ x).Equiv τ₀))
    (ht₁ : ∀ x : H, Nonempty ((conjugateRep (G := H) τ₁ x).Equiv τ₁))
    {ι : Type*} (seed : ι → V)
    (hs : ∀ i, seed i ∈ typeSpan (ρ.comp D.subtype) τ₀ ⊔ typeSpan (ρ.comp D.subtype) τ₁)
    (hgen : ∀ U : Subrepresentation ρ, (∀ i, seed i ∈ U) → U = ⊤) :
    typeSpan (ρ.comp D.subtype) τ₀ ⊔ typeSpan (ρ.comp D.subtype) τ₁ = ⊤ := by
  let R₀ := typeSpan (ρ.comp D.subtype) τ₀
  let R₁ := typeSpan (ρ.comp D.subtype) τ₁
  let U : Subrepresentation ρ := {
    toSubmodule := (R₀ ⊔ R₁).toSubmodule
    apply_mem_toSubmodule x v hv := by
      obtain ⟨a,ha,b,hb,rfl⟩ := Submodule.mem_sup.mp hv
      rw [map_add]
      exact Submodule.mem_sup.mpr ⟨ρ x a,typeSpan_normal_stable ρ D τ₀ ht₀ x a ha,
        ρ x b,typeSpan_normal_stable ρ D τ₁ ht₁ x b hb,rfl⟩ }
  have hu := hgen U hs
  apply Subrepresentation.toSubmodule_injective
  change U.toSubmodule = (⊤ : Subrepresentation ρ).toSubmodule
  exact congrArg Subrepresentation.toSubmodule hu

/-- Conjugation preserves the trivial one-dimensional representation. -/
theorem conjugate_trivial_equiv {H : Type*} [Group H] (D : Subgroup H) [D.Normal]
    (x : H) : Nonempty ((conjugateRep (G := H) (trivial k D k) x).Equiv (trivial k D k)) :=
  ⟨{ toLinearEquiv := LinearEquiv.refl k k, isIntertwining' := fun _ => rfl }⟩

set_option backward.isDefEq.respectTransparency false in
/-- Every simple constituent of a semisimple sum of two simple model types is
isomorphic to one of those models. -/
theorem constituent_of_typeSpan_sup_eq_top
    (ρ : Representation k G V) (τ₀ : Representation k G W₀) (τ₁ : Representation k G W)
    [IsSemisimpleModule k[G] ρ.asModule] [τ₀.IsIrreducible] [τ₁.IsIrreducible]
    (htop : typeSpan ρ τ₀ ⊔ typeSpan ρ τ₁ = ⊤)
    (J : Subrepresentation ρ) (hJ : IsAtom J) :
    Nonempty (J.toRepresentation.Equiv τ₀) ∨ Nonempty (J.toRepresentation.Equiv τ₁) := by
  let := (Subrepresentation.irreducible_iff_isAtom J).mpr hJ
  let j : J.toRepresentation.IntertwiningMap ρ := {
    toLinearMap := J.toSubmodule.subtype
    isIntertwining' _ := rfl }
  let jm := IntertwiningMap.equivLinearMapAsModule _ _ j
  obtain ⟨pm,hpm⟩ := IsSemisimpleModule.extension_property jm
    (show Function.Injective jm from Subtype.val_injective) (LinearMap.id :
      J.toRepresentation.asModule →ₗ[k[G]] J.toRepresentation.asModule)
  let p := (IntertwiningMap.equivLinearMapAsModule ρ J.toRepresentation).symm pm
  have hp : p ≠ 0 := by
    intro hz
    have hz' : pm = 0 := by
      have hh := congrArg (IntertwiningMap.equivLinearMapAsModule ρ J.toRepresentation) hz
      simpa [p] using hh
    rw [hz', LinearMap.zero_comp] at hpm
    have hnontriv : Nontrivial J.toRepresentation.asModule := IsSimpleModule.nontrivial k[G] _
    have hh : (1 : Module.End k[G] J.toRepresentation.asModule) = 0 := hpm.symm
    exact one_ne_zero hh
  by_contra hn
  rcases not_or.mp hn with ⟨hn₀,hn₁⟩
  have hz₀ (f : τ₀.IntertwiningMap ρ) : p.comp f = 0 := by
    rcases IsIrreducible.bijective_or_eq_zero (p.comp f) with hb | hz
    · exact (hn₀ ⟨((p.comp f).ofBijective hb).symm⟩).elim
    · exact hz
  have hz₁ (f : τ₁.IntertwiningMap ρ) : p.comp f = 0 := by
    rcases IsIrreducible.bijective_or_eq_zero (p.comp f) with hb | hz
    · exact (hn₁ ⟨((p.comp f).ofBijective hb).symm⟩).elim
    · exact hz
  have hle : typeSpan ρ τ₀ ⊔ typeSpan ρ τ₁ ≤ p.ker := by
    apply sup_le
    · apply iSup_le
      intro f w hw
      obtain ⟨v,rfl⟩ := hw
      exact congrArg (fun q : τ₀.IntertwiningMap J.toRepresentation => q v) (hz₀ f)
    · apply iSup_le
      intro f w hw
      obtain ⟨v,rfl⟩ := hw
      exact congrArg (fun q : τ₁.IntertwiningMap J.toRepresentation => q v) (hz₁ f)
  have hker : p.ker = ⊤ := top_unique (htop ▸ hle)
  apply hp
  apply IntertwiningMap.ext
  apply LinearMap.ext
  intro v
  exact (show v ∈ p.ker from hker.symm ▸ Submodule.mem_top)

/-- The trivial line is an irreducible representation over every field. -/
theorem trivial_line_irreducible : (trivial k G k).IsIrreducible := by
  let : IsSimpleModule k k := inferInstance
  rw [IsIrreducible, isSimpleOrder_iff]
  refine ⟨inferInstance, fun S => ?_⟩
  rcases eq_bot_or_eq_top S.toSubmodule with hs | hs
  · exact Or.inl (Subrepresentation.toSubmodule_injective hs)
  · exact Or.inr (Subrepresentation.toSubmodule_injective hs)

end Representation
