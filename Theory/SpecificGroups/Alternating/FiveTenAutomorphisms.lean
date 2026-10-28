module
public import Theory.SpecificGroups.Alternating.FiveLocalGeometry.TenConjugacy
public import Theory.SpecificGroups.Alternating.FiveExtensionAction
import all Theory.SpecificGroups.Alternating.FiveLocalGeometry

/-!
# Full automorphism control on an actual D₁₀ in A₅

Conjugacy of order-ten subgroups reduces to the checked pentagon embedding.
In that embedding every dihedral automorphism is induced by a permutation
of the five letters, and a permutation fixing both dihedral generators
centralizes only trivially. The resulting A₅ automorphism is therefore
uniquely determined by its restriction to any actual order-ten subgroup.
These are restriction statements, retaining the actual subgroup and map.
-/

public noncomputable section
namespace alternatingGroup.FiveLocalGeometry.TenAutomorphisms
open Subgroup DihedralGroup
local notation "A" => alternatingGroup (Fin 5)
private abbrev S := Equiv.Perm (Fin 5)
private def i : DihedralGroup 5 →* S := (alternatingGroup (Fin 5)).subtype.comp dihedralHom
private def B : Subgroup A := dihedralHom.range
private def eB : DihedralGroup 5 ≃* B := MonoidHom.ofInjective dihedralHom_injective
private theorem cardB : Nat.card B = 10 := by
  rw [←Nat.card_congr eB.toEquiv,DihedralGroup.nat_card]

private theorem generator_coordinates :
    ∀ (a b : ZMod 5), a ≠ 0 → ∃ s : S,
      s * i (r 1) * s⁻¹ = i (r a) ∧ s * i (sr 0) * s⁻¹ = i (sr b) := by
  decide +kernel

private theorem generator_centralizer : ∀ s : S,
    s * i (r 1) = i (r 1) * s → s * i (sr 0) = i (sr 0) * s → s = 1 := by
  decide +kernel

private theorem hom_ext {E : Type*} [Group E] (f g : DihedralGroup 5 →* E)
    (hr : f (r 1) = g (r 1)) (hs : f (sr 0) = g (sr 0)) : f=g := by
  have hrot (a : ZMod 5) : f (r a) = g (r a) := by
    have he : (r 1 : DihedralGroup 5)^a.val = r a := by simp
    rw [←he,map_pow,map_pow,hr]
  apply MonoidHom.ext
  rintro (a|a)
  · exact hrot a
  · have he : sr a = sr 0 * r a := by simp
    rw [he,map_mul,map_mul,hs,hrot]

private theorem model_extension (φ : MulAut (DihedralGroup 5)) :
    ∃ s : S, ∀ d, s * i d * s⁻¹ = i (φ d) := by
  have hp (d : DihedralGroup 5) (n : ℕ) (h : d^n=1) : φ d ^ n = 1 := by
    rw [←map_pow,h,map_one]
  have hn (d : DihedralGroup 5) (h : d≠1) : φ d≠1 := by
    intro he
    exact h (φ.injective (he.trans φ.map_one.symm))
  have rot : ∀ x : DihedralGroup 5, x^5=1 → x≠1 → ∃ a : ZMod 5, a≠0 ∧ x=r a := by
    decide +kernel
  have ref : ∀ x : DihedralGroup 5, x^2=1 → x≠1 → ∃ b : ZMod 5, x=sr b := by
    decide +kernel
  obtain ⟨a,ha,hea⟩ := rot (φ (r 1)) (hp _ 5 (by decide +kernel)) (hn _ (by decide +kernel))
  obtain ⟨b,heb⟩ := ref (φ (sr 0)) (hp _ 2 (by decide +kernel)) (hn _ (by decide +kernel))
  obtain ⟨s,hsr,hss⟩ := generator_coordinates a b ha
  have he := hom_ext ((MulAut.conj s).toMonoidHom.comp i) (i.comp φ.toMonoidHom)
    (by change s * i (r 1) * s⁻¹ = i (φ (r 1)); rw [hea]; exact hsr)
    (by change s * i (sr 0) * s⁻¹ = i (φ (sr 0)); rw [heb]; exact hss)
  exact ⟨s,fun d => DFunLike.congr_fun he d⟩

private theorem model_rigid (φ : MulAut A) (hfix : ∀ x∈B,φ x=x) : φ=1 := by
  let e : S ≃* MulAut A := MulEquiv.ofBijective MulAut.conjNormal
    (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 (by decide) (by decide))
  obtain ⟨s,hs⟩ := e.surjective φ
  have hc (d : DihedralGroup 5) : s * i d = i d * s := by
    have hh := congrArg Subtype.val (hfix (dihedralHom d) ⟨d,rfl⟩)
    rw [←hs] at hh
    change ((MulAut.conjNormal s) (dihedralHom d) : S) = (dihedralHom d : S) at hh
    rw [MulAut.conjNormal_apply] at hh
    change s * i d * s⁻¹ = i d at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  have h1 := generator_centralizer s (hc (r 1)) (hc (sr 0))
  rw [←hs,h1,map_one]

/-- An automorphism of an actual A₅ is determined by its pointwise action
on any original subgroup of order ten. -/
theorem eq_one_of_fixes_ten (D : Subgroup A) (hD : Nat.card D=10)
    (φ : MulAut A) (hfix : ∀ x∈D,φ x=x) : φ=1 := by
  obtain ⟨g,hg⟩ := ten_subgroups_conjugate (MulEquiv.refl A) B D cardB hD
  let ψ : MulAut A := (MulAut.conj g).symm * φ * MulAut.conj g
  have hψ : ψ=1 := model_rigid ψ (by
    intro x hx
    have hm : MulAut.conj g x ∈ D := hg ▸ mem_map_of_mem _ hx
    change (MulAut.conj g).symm (φ (MulAut.conj g x)) = x
    rw [hfix _ hm,MulEquiv.symm_apply_apply])
  apply MulEquiv.ext
  intro x
  have hh := congrArg (fun q : MulAut A => MulAut.conj g (q ((MulAut.conj g).symm x))) hψ
  change MulAut.conj g ((MulAut.conj g).symm (φ
    (MulAut.conj g ((MulAut.conj g).symm x)))) = MulAut.conj g ((MulAut.conj g).symm x) at hh
  simpa only [MulEquiv.apply_symm_apply,MulAut.one_apply] using hh

/-- Every automorphism of the same actual order-ten subgroup extends to
A₅, with equality on every subgroup element. -/
theorem automorphism_extends (D : Subgroup A) (hD : Nat.card D=10)
    (φ : MulAut D) : ∃ Φ : MulAut A, ∀ x : D, Φ x = (φ x : A) := by
  obtain ⟨g,hg⟩ := ten_subgroups_conjugate (MulEquiv.refl A) B D cardB hD
  let e : DihedralGroup 5 ≃* D := eB.trans
    (((MulAut.conj g).subgroupMap B).trans (MulEquiv.subgroupCongr hg))
  let α : MulAut (DihedralGroup 5) := e.trans (φ.trans e.symm)
  obtain ⟨s,hs⟩ := model_extension α
  let Ψ : MulAut A := MulAut.conjNormal s
  let Φ : MulAut A := MulAut.conj g * Ψ * (MulAut.conj g).symm
  refine ⟨Φ,?_⟩
  intro x
  obtain ⟨d,rfl⟩ := e.surjective x
  have he (d : DihedralGroup 5) : (e d : A) = MulAut.conj g (dihedralHom d) := rfl
  have hα : e (α d) = φ (e d) := by
    change e (e.symm (φ (e d))) = _
    exact e.apply_symm_apply _
  have hmodel : Ψ (dihedralHom d) = dihedralHom (α d) := by
    apply Subtype.ext
    change ((MulAut.conjNormal s) (dihedralHom d) : S) = _
    rw [MulAut.conjNormal_apply]
    exact hs d
  change MulAut.conj g (Ψ ((MulAut.conj g).symm (e d))) = _
  rw [he,MulEquiv.symm_apply_apply,hmodel,←he,hα]
end alternatingGroup.FiveLocalGeometry.TenAutomorphisms
