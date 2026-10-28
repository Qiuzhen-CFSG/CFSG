module
public import Theory.Representation.BinaryOffender.Homogeneous.AutomorphismTwist
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms

/-!
# Homogeneous seed stability from one active factor

If X=A B and B fixes the seed, its central image remains irreducible for A.
An automorphism twist on A extends to X because B is in the kernel and its
conjugate is again B. The quotient twist criterion therefore fixes the seed.
The application supplies all twists from the complete binary A₅ classifier.

Source: Aschbacher–Smith, D.3.6 and A.1.40–42, printed pp.196 and31–32.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous

namespace Representation.BinaryOffender.Homogeneous
universe u
variable {G : Type*} {V : Type u} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

theorem IsIrrPlusWith.map_eq_of_active_factor_twist
    {X T : Subgroup G} {I : Submodule (ZMod 2) V}
    (hI : IsIrrPlusWith ρ X T I) (t : T)
    (A B : Subgroup G) (hAB : A ⊔ B = X)
    (hB : I ≤ fixedSpace ρ B)
    (htA : t.val ∈ normalizer (A : Set G))
    (htB : t.val ∈ normalizer (B : Set G))
    (htwist : ∀ {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
      [FiniteDimensional (ZMod 2) W] (σ : Representation (ZMod 2) A W)
      [σ.IsIrreducible] (a : MulAut A),
        ∃ c : W ≃ₗ[ZMod 2] W, ∀ g v, c (σ g v) = σ (a g) (c v)) :
    I.map (ρ t.val) = I := by
  have hAX : A ≤ X := hAB ▸ le_sup_left
  have hBX : B ≤ X := hAB ▸ le_sup_right
  let S := quotientImage ρ X I hI.invariant
  let σ := S.toRepresentation
  let : σ.IsIrreducible := quotientImage_irreducible ρ hI.isIrrPlus
  have hBfix (b : B) (v : S.toSubmodule) : σ ⟨b.val, hBX b.property⟩ v = v := by
    apply Subtype.ext
    obtain ⟨w, hw, he⟩ := v.property
    change fixedQuotientRepresentation ρ X ⟨b.val, hBX b.property⟩ v.val = v.val
    rw [←he]
    change (fixedSpace ρ X).mkQ (ρ b.val w) = (fixedSpace ρ X).mkQ w
    have hbfix : ρ (b : G) w = w := hB hw b
    rw [hbfix]
  have hker : B.subgroupOf X ≤ σ.ker := by
    intro b hb
    apply MonoidHom.mem_ker.mpr
    apply LinearMap.ext
    exact hBfix ⟨b.val, hb⟩
  have hgen : A.subgroupOf X ⊔ B.subgroupOf X = ⊤ := by
    rw [←subgroupOf_sup hAX hBX, hAB, subgroupOf_self]
  let τ : Representation (ZMod 2) A S.toSubmodule := σ.comp (inclusion hAX)
  let e := subgroupOfEquivOfLe hAX
  let : IsIrreducible (σ.comp (A.subgroupOf X).subtype) :=
    irreducible_restrict_of_sup_kernel σ _ _ hgen hker
  let : τ.IsIrreducible :=
    (irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective
      (σ.comp (A.subgroupOf X).subtype)).mpr inferInstance
  let n := X.normalizerMonoidHom
    ⟨t.val⁻¹, hI.normalizes (T.inv_mem t.property)⟩
  let a := A.normalizerMonoidHom ⟨t.val⁻¹, (normalizer (A : Set G)).inv_mem htA⟩
  obtain ⟨c, hc⟩ := htwist τ a
  let E := ((c.conjRingEquiv.toMonoidHom).comp σ).eqLocus (σ.comp n.toMonoidHom)
  have hAE : A.subgroupOf X ≤ E := by
    intro x hx
    apply LinearMap.ext
    intro v
    change c (τ ⟨x.val, hx⟩ (c.symm v)) = σ (n x) v
    rw [hc, c.apply_symm_apply]
    rfl
  have hBE : B.subgroupOf X ≤ E := by
    intro x hx
    apply LinearMap.ext
    intro v
    change c (σ x (c.symm v)) = σ (n x) v
    have hnx : (n x).val ∈ B := by
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
      exact (mem_normalizer_iff.mp ((normalizer (B : Set G)).inv_mem htB) x.val).mp hx
    rw [hBfix ⟨x.val, hx⟩, hBfix ⟨(n x).val, hnx⟩, c.apply_symm_apply]
  have hE : (⊤ : Subgroup X) ≤ E := hgen ▸ sup_le hAE hBE
  apply hI.map_eq_of_central_twist ρ t c
  intro x v
  have he := LinearMap.congr_fun (hE (mem_top x)) (c v)
  change c (σ x (c.symm (c v))) = σ (n x) (c v) at he
  simpa only [c.symm_apply_apply] using he

end Representation.BinaryOffender.Homogeneous
