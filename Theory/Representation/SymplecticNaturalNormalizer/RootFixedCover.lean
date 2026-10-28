module
public import Theory.Representation.SymplecticNaturalNormalizer.FixedSeedInner
public import Theory.SpecificGroups.SymplecticFour.RootHyperplane
/-!
# The ambient image of an actor fixing a critical root cover seed

Fixed-point lifting gives the entire natural fixed hyperplane. The centric
normal component first removes the field automorphism; the full hyperplane
fixer is then the original root group. The conclusion retains that literal
root image, including all central attachments in the cover.

Source: Meierfrankenfeld--Stellmacher (1993), (3.4), printed p.868.
-/

public section
noncomputable section
open Subgroup Representation Representation.OneCohomology
open Representation.SymplecticFourOrthogonalCover
open Theory.SpecificGroups.SymplecticFour
namespace SymplecticNaturalNormalizer
variable {J W F : Type*} [Group J]
  [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
  [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
theorem mem_root_image_of_fixes_cover_seed
    (B : Subgroup J) [B.Normal] (hcent : centralizer (B : Set J) ≤ B)
    (hF : 2 < Nat.card F) (e : B ≃* Sp F)
    (ρ : Representation (ZMod 2) J (Vector F))
    (hB : ∀ b : B, ∀ v, ρ (b:J) v = symplecticNatural 2 (e b) v)
    {σ : Representation (ZMod 2) (L (K := F)) W}
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (S : Subgroup (L (K := F))) (hS : IsPGroup 2 S)
    (hd : Module.finrank F (displacementSpace (S.map (commutator (Sp F)).subtype)) = 1)
    (hc : Nat.card S = Nat.card F)
    (x : J) (f : W → W) (hcompat : ∀ w, p (f w) = ρ x (p w))
    (hfix : ∀ w ∈ fixed (σ.comp S.subtype), f w = w) :
    ∃ t : L (K := F), t ∈ S ∧ (e.symm t.val : J) = x := by
  have hx : x ∈ B := mem_component_of_fixes_cover_seed B hcent hF e ρ hB
    p hp S hS x f hcompat hfix
  have hxf : e ⟨x,hx⟩ ∈ fixingSubgroup (Sp F)
      (TwoLocalCover.fixedSpace (S.map (commutator (Sp F)).subtype) : Set (Vector F)) := by
    apply (mem_fixingSubgroup_iff _).mpr
    intro v hv
    obtain ⟨w,rfl⟩ := hp.1 v
    have hw : w ∈ fixed (σ.comp S.subtype) := by
      rw [cover_fixed_preimage p hp]
      intro t
      exact hv t.val.val (mem_map_of_mem _ t.property)
    have he := hB ⟨x,hx⟩ (p w)
    change ρ x (p w) = e ⟨x,hx⟩ • p w at he
    rw [←he,←hcompat,hfix w hw]
  rw [root_fixedSpace_fixer_eq _ hd (by
    rw [card_map_of_injective (commutator (Sp F)).subtype_injective,hc])] at hxf
  obtain ⟨t,ht,he⟩ := hxf
  refine ⟨t,ht,?_⟩
  change t.val = e ⟨x,hx⟩ at he
  rw [he,e.symm_apply_apply]
end SymplecticNaturalNormalizer
