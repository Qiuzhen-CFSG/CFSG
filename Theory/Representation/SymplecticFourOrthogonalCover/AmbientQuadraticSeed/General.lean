module
public import Theory.Representation.SymplecticFourOrthogonalCover.QuadraticSeed
public import Theory.Representation.SymplecticNaturalNormalizer.QuadraticOuter.General

/-!
# Degree bound for actors moving a normalized Sylow cover seed

A quadratic actor preserving the full Sylow fixed seed fixes it whenever
its image lies in the symplectic component. A moving actor therefore has
an outer field twist and injects into the coefficient-field automorphism
group. This extends the existing field-four bound to every nonbinary field.

The source consumer is the upper intersection comparison in MS93 (3.4),
printed p.868. The cover and its complete central kernel are retained.
-/

public section
noncomputable section
open Subgroup Representation Representation.BinaryOffender Representation.OneCohomology
open Theory.SpecificGroups.SymplecticFour
namespace Representation.SymplecticFourOrthogonalCover
variable {F G W : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
  [Group G] [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]

theorem quadratic_card_le_ringAut_of_moves_sylow_cover_seed
    (hF : 2 < Nat.card F) (B : Subgroup G) [B.Normal]
    (hcent : centralizer (B : Set G) ≤ B)
    (e : B ≃* L (K := F))
    (ρ : Representation (ZMod 2) G W)
    (τ : Representation (ZMod 2) G (Vector F)) (hfaith : Function.Injective τ)
    (hB : ∀ b : B, ∀ v, τ (b : G) v = binaryNatural (e b) v)
    (p : Representation.IntertwiningMap (ρ.comp (B.subtype.comp e.symm.toMonoidHom))
      (binaryNatural (K := F))) (hp : IsCover p)
    (P : Sylow 2 (L (K := F))) (A : Subgroup G)
    (hq : IsQuadratic τ A)
    (hn : ∀ a ∈ A, ∀ w ∈ fixed ((ρ.comp (B.subtype.comp e.symm.toMonoidHom)).comp
      (P : Subgroup (L (K := F))).subtype),
      ρ a w ∈ fixed ((ρ.comp (B.subtype.comp e.symm.toMonoidHom)).comp
        (P : Subgroup (L (K := F))).subtype))
    (hm : ∃ a ∈ A, ∃ w ∈ fixed ((ρ.comp (B.subtype.comp e.symm.toMonoidHom)).comp
      (P : Subgroup (L (K := F))).subtype), ρ a w ≠ w) :
    Nat.card A ≤ Nat.card (F ≃+* F) := by
  let d : L (K := F) ≃* Sp F :=
    (MulEquiv.subgroupCongr
      (OneCohomology.SymplecticFour.LargeField.commutator_eq_top (by omega : 2 < Nat.card F))).trans
        Subgroup.topEquiv
  apply SymplecticNaturalNormalizer.quadratic_card_le_ringAut_of_not_le_component
    hF B hcent (e.trans d) τ hfaith hB A hq
  intro hAB
  let A' : Subgroup (L (K := F)) := (A.subgroupOf B).map e.toMonoidHom
  have hA' (a : L (K := F)) (ha : a ∈ A') : (e.symm a : G) ∈ A := by
    obtain ⟨b,hb,rfl⟩ := ha
    change (e.symm (e b) : G) ∈ A
    rw [e.symm_apply_apply]
    exact hb
  have hq' : IsQuadratic (binaryNatural (K := F)) A' := by
    intro a ha b hb v
    have hh := hq (e.symm a) (hA' a ha) (e.symm b) (hA' b hb) v
    simpa only [hB, e.apply_symm_apply] using hh
  have hn' : ∀ a ∈ A', ∀ w ∈ fixed ((ρ.comp (B.subtype.comp e.symm.toMonoidHom)).comp
      (P : Subgroup (L (K := F))).subtype),
      (ρ.comp (B.subtype.comp e.symm.toMonoidHom)) a w ∈
        fixed ((ρ.comp (B.subtype.comp e.symm.toMonoidHom)).comp
          (P : Subgroup (L (K := F))).subtype) := by
    intro a ha w hw
    exact hn (e.symm a) (hA' a ha) w hw
  obtain ⟨a,ha,w,hw,hm⟩ := hm
  have ha' : e ⟨a,hAB ha⟩ ∈ A' := mem_map_of_mem e.toMonoidHom ha
  have hh := quadratic_fixes_normalized_sylow_cover_seed p hp P A' hq' hn'
    (e ⟨a,hAB ha⟩) ha' w hw
  apply hm
  change ρ (e.symm (e ⟨a,hAB ha⟩)) w = w at hh
  simpa only [e.symm_apply_apply] using hh

end Representation.SymplecticFourOrthogonalCover
