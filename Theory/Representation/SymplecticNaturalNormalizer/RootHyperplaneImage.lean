module
public import Theory.Representation.SymplecticNaturalNormalizer.RootFixedCover
/-!
# The ambient image of a natural root hyperplane fixer

A pointwise fixer of the root hyperplane fixes a field line, hence belongs
to the centric symplectic component. The full hyperplane fixer inside that
component is precisely the marked root group. This retains its literal image.

Source: Meierfrankenfeld--Stellmacher (1993), (3.4), printed p.868.
-/
public section
noncomputable section

open Subgroup Representation Representation.OneCohomology
open Representation.SymplecticFourOrthogonalCover
open Theory.SpecificGroups.SymplecticFour
namespace SymplecticNaturalNormalizer
variable {J F : Type*} [Group J]
  [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
theorem mem_root_image_of_fixes_natural_hyperplane
    (B : Subgroup J) [B.Normal] (hcent : centralizer (B : Set J) ≤ B)
    (hF : 2 < Nat.card F) (e : B ≃* Sp F)
    (ρ : Representation (ZMod 2) J (Vector F))
    (hB : ∀ b : B, ∀ v, ρ (b:J) v = symplecticNatural 2 (e b) v)
    (S : Subgroup (L (K := F))) (hS : IsPGroup 2 S)
    (hd : Module.finrank F (displacementSpace (S.map (commutator (Sp F)).subtype)) = 1)
    (hc : Nat.card S = Nat.card F)
    (x : J) (hfix : ∀ v ∈ TwoLocalCover.fixedSpace
      (S.map (commutator (Sp F)).subtype), ρ x v = v) :
    ∃ t : L (K := F), t ∈ S ∧ (e.symm t.val : J) = x := by
  obtain ⟨v,hv,hSv⟩ := pGroup_fix_nonzero_vector
    (F := F) (by rw [ringChar.eq F 2]; decide)
    (by simpa only [ringChar.eq F 2] using hS)
    ((symplecticDerivedNatural (k := F) 2).comp S.subtype)
  have hx : x ∈ B := by
    apply mem_component_of_fixes_field_line B hcent hF e ρ hB x v hv
    intro c
    apply hfix
    rintro g ⟨t,ht,rfl⟩
    change symplecticDerivedNatural 2 t (c • v) = c • v
    rw [map_smul]
    exact congrArg (c • ·) (hSv ⟨t,ht⟩)
  have hxf : e ⟨x,hx⟩ ∈ fixingSubgroup (Sp F)
      (TwoLocalCover.fixedSpace (S.map (commutator (Sp F)).subtype) : Set (Vector F)) := by
    apply (mem_fixingSubgroup_iff _).mpr
    intro v hv
    exact (hB ⟨x,hx⟩ v).symm.trans (hfix v hv)
  rw [root_fixedSpace_fixer_eq _ hd (by
    rw [card_map_of_injective (commutator (Sp F)).subtype_injective,hc])] at hxf
  obtain ⟨t,ht,he⟩ := hxf
  refine ⟨t,ht,?_⟩
  change t.val = e ⟨x,hx⟩ at he
  rw [he,e.symm_apply_apply]
end SymplecticNaturalNormalizer
