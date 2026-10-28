module
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Theory.Representation.BinaryOffender.PermutationConjugacy
public import Mathlib.GroupTheory.Sylow
public import Theory.ElementaryAbelian.Injective

/-!
# Elementary action geometry through a Sylow-containing image

An elementary two-subgroup can be conjugated into any fixed Sylow subgroup.
If that Sylow lies in a faithfully marked action image, pull the conjugate
back and preserve its rank and fixed codimension. Equivariant descent along
a surjective faithful-action quotient constructs such markings without
unfolding the caller's representation internals.

The natural unitary orbit uses these lemmas to transfer its elementary
geometry to the full ambient automizer, as in Aschbacher--Smith H.2 and
7.2.1 (printed pp.378,698).
-/
public noncomputable section
open Subgroup Representation
namespace Representation.BinaryOffender

/-- Transfer elementary-actor geometry along a faithful action whose image
contains an actual Sylow subgroup of the target. -/
theorem elementary_geometry_of_sylow_range
    {X Y E W : Type*} [Group X] [Group Y] [Finite Y]
    [AddCommGroup E] [Module (ZMod 2) E] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) E] [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) X E) (τ : Representation (ZMod 2) Y W)
    (f : X →* Y) (hf : Function.Injective f) (e : E ≃ₗ[ZMod 2] W)
    (he : ∀ x v, e (ρ x v) = τ (f x) (e v))
    (S : Sylow 2 Y) (hS : (S : Subgroup Y) ≤ f.range)
    (A : Subgroup Y) (hA : IsElementaryTwo A) :
    ∃ B : Subgroup X, IsElementaryTwo B ∧ rank B = rank A ∧
      fixedCodim ρ B = fixedCodim τ A := by
  let : IsElementaryAbelian 2 A := hA.2
  obtain ⟨P,hAP⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq Y P S
  let C := A.map (MulAut.conj g).toMonoidHom
  have hC := hA.map_conj g
  have hCP : C ≤ (S : Subgroup Y) := (congrArg Sylow.toSubgroup hg) ▸ map_mono hAP
  let B := C.comap f
  have hmap : B.map f = C := map_comap_eq_self (hCP.trans hS)
  let : IsElementaryAbelian 2 C := hC.2
  let fC : B →* C := f.restrict (fun _ hx => hx)
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.of_injective
    fC (fun x y h => Subtype.ext (hf (congrArg Subtype.val h)))
  have hB : IsElementaryTwo B := ⟨fun hz => hC.1 (by change C = ⊥; rw [←hmap,hz,Subgroup.map_bot]),inferInstance⟩
  refine ⟨B,hB,?_,?_⟩
  · rw [←rank_map_injective f hf B,hmap,rank_map_conj]
  · rw [fixedCodim_map_equivariant ρ τ f e he B,hmap,fixedCodim_map_conj]

/-- Descend a literal equivariant action along its faithful quotient. -/
theorem faithful_action_factor
    {X Y Z E W : Type*} [Group X] [Group Y] [Group Z]
    [AddCommGroup E] [Module (ZMod 2) E] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) X E) (τ : Representation (ZMod 2) Y W)
    (hρ : Function.Injective ρ) (hτ : Function.Injective τ)
    (q : Z →* X) (hq : Function.Surjective q) (k : Z →* Y)
    (e : E ≃ₗ[ZMod 2] W)
    (he : ∀ g v, e (ρ (q g) v) = τ (k g) (e v)) :
    ∃ f : X →* Y, Function.Injective f ∧
      (∀ a v, e (ρ a v) = τ (f a) (e v)) ∧ ∀ g, f (q g) = k g := by
  have hker : q.ker ≤ k.ker := by
    intro g hg
    apply hτ
    apply LinearMap.ext
    intro w
    obtain ⟨v,rfl⟩ := e.surjective w
    have heq := he g v
    rw [show q g = 1 from hg,map_one] at heq
    simpa only [map_one, Module.End.one_apply] using heq.symm
  let f := q.liftOfSurjective hq ⟨k,hker⟩
  have hf (g : Z) : f (q g) = k g := q.liftOfRightInverse_comp_apply _ _ _ g
  have he' (a : X) (v : E) : e (ρ a v) = τ (f a) (e v) := by
    obtain ⟨g,rfl⟩ := hq a
    rw [hf]
    exact he g v
  refine ⟨f,?_,he',hf⟩
  intro a b hab
  apply hρ
  apply LinearMap.ext
  intro v
  apply e.injective
  rw [he',he',hab]

end Representation.BinaryOffender
