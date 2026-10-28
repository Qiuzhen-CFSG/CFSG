module
public import Theory.Representation.BinaryAlternatingFiveExtension.MarkedAlternating
public import Theory.Representation.FirstCohomologyAutomorphism
public import Theory.Representation.BinaryAlternatingNaturalCohomology

/-!
# Correcting automorphisms of the marked natural A₅ extension

Permutation conjugation on A₅ and the five-point core action define the standard
S₅ action on the split model. If an automorphism of the original extension has
these same two actions, dividing by the transported standard action fixes the
kernel and quotient. Vanishing first cohomology makes the difference conjugation
by a kernel element. The conclusion keeps the actual extension and marking.

Source: Aschbacher–Smith, the single alternating case of 2.4.29.
-/

@[expose] public section
namespace BinaryPermutation.AlternatingFiveExtension
open Subgroup
local notation "A5" => alternatingGroup (Fin 5)
local notation "S5" => Equiv.Perm (Fin 5)

theorem standard_compatible (σ : S5) (a : A5) :
    (alternatingAction a).trans (coreAction σ) =
      (coreAction σ).trans (alternatingAction (MulAut.conjNormal σ a)) := by
  apply MulEquiv.ext
  intro v
  change (coreAction σ * coreAction a.val) v =
    (coreAction (σ * a.val * σ⁻¹) * coreAction σ) v
  rw [← map_mul, ← map_mul]
  congr 2
  group

def standardAction : S5 →* MulAut AlternatingModel where
  toFun σ := SemidirectProduct.congr (coreAction σ) (MulAut.conjNormal σ)
    (standard_compatible σ)
  map_one' := by
    ext x <;> simp [SemidirectProduct.congr]
  map_mul' σ τ := by
    ext x <;> simp [SemidirectProduct.congr, map_mul]

@[simp] theorem standardAction_left (σ : S5) (x : AlternatingModel) :
    (standardAction σ x).left = coreAction σ x.left := rfl
@[simp] theorem standardAction_right (σ : S5) (x : AlternatingModel) :
    (standardAction σ x).right = MulAut.conjNormal σ x.right := rfl
@[simp] theorem standardAction_inl (σ : S5) (v : V) :
    standardAction σ (SemidirectProduct.inl v) =
      SemidirectProduct.inl (coreAction σ v) := by
  ext <;> simp

@[simp] theorem standardAction_inr (σ : S5) (a : A5) :
    standardAction σ (SemidirectProduct.inr a) =
      SemidirectProduct.inr (MulAut.conjNormal σ a) := by
  ext <;> simp

def transportedStandard {G : Type*} [Group G]
    (E : G ≃* AlternatingModel) (σ : S5) : MulAut G :=
  (E.trans (standardAction σ)).trans E.symm

theorem automorphism_correction {G : Type*} [Group G]
    (q : G →* A5) (hq : Function.Surjective q) (e : q.ker ≃* V)
    (he : ∀ (g : G) (v : q.ker), e (MulAut.conjNormal g v) =
      Multiplicative.ofAdd (coreRepresentation (Fin 5) (q g).val (e v).toAdd))
    (E : G ≃* AlternatingModel) (hEq : ∀ g, (E g).right = q g)
    (hEe : ∀ v : q.ker, E (v : G) = SemidirectProduct.inl (e v))
    (σ : S5) (α : MulAut G)
    (hαq : ∀ g, q (α g) = MulAut.conjNormal σ (q g))
    (hαe : ∀ v : V, α (e.symm v : G) = (e.symm (coreAction σ v) : G)) :
    ∃ n : q.ker, ∀ g,
      α g = (n : G)⁻¹ * E.symm (standardAction σ (E g)) * n := by
  let δ := transportedStandard E σ
  have hδq (g : G) : q (δ g) = MulAut.conjNormal σ (q g) := by
    rw [← hEq]
    change (E (E.symm (standardAction σ (E g)))).right = _
    rw [E.apply_symm_apply, standardAction_right, hEq]
  have hδe (v : V) : δ (e.symm v : G) = (e.symm (coreAction σ v) : G) := by
    apply E.injective
    change E (E.symm (standardAction σ (E (e.symm v : G)))) = _
    rw [E.apply_symm_apply, hEe, e.apply_symm_apply, standardAction_inl,
      hEe, e.apply_symm_apply]
  let β : MulAut G := α * δ⁻¹
  have hβq (g : G) : q (β g) = q g := by
    change q (α (δ.symm g)) = q g
    rw [hαq, ← hδq, δ.apply_symm_apply]
  have hβe (g : G) (hg : g ∈ q.ker) : β g = g := by
    let v := e ⟨g, hg⟩
    have hδinv : δ.symm g = (e.symm ((coreAction σ).symm v) : G) := by
      apply δ.injective
      rw [δ.apply_symm_apply, hδe, MulEquiv.apply_symm_apply]
      exact (congrArg Subtype.val (e.symm_apply_apply ⟨g, hg⟩)).symm
    change α (δ.symm g) = g
    rw [hδinv, hαe, MulEquiv.apply_symm_apply]
    exact congrArg Subtype.val (e.symm_apply_apply ⟨g, hg⟩)
  let := alternatingCore_subsingleton_H1 (Fin 5) (by simp) (by decide)
  have hcoord (g : G) (v : core (Fin 5)) :
      (e.symm (Multiplicative.ofAdd (alternatingCoreRepresentation (Fin 5) (q g) v)) : G) =
        g * (e.symm (Multiplicative.ofAdd v) : G) * g⁻¹ := by
    have hh := he g (e.symm (Multiplicative.ofAdd v))
    rw [e.apply_symm_apply] at hh
    have hh' := congrArg (fun u : V => (e.symm u : G)) hh
    rw [e.symm_apply_apply] at hh'
    exact hh'.symm
  obtain ⟨n, hn⟩ := Representation.OneCohomology.automorphism_inner_of_H1_zero
    q.ker q hq rfl e (alternatingCoreRepresentation (Fin 5)) hcoord β hβq hβe
  refine ⟨n, fun g => ?_⟩
  have hh := hn (δ g)
  change α (δ.symm (δ g)) = _ at hh
  rw [δ.symm_apply_apply] at hh
  exact hh
end BinaryPermutation.AlternatingFiveExtension
