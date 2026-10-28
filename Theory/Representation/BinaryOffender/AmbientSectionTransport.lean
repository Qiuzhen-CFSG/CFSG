module

public import Theory.Representation.BinaryOffender.IrreducibleMovedTransport
public import Theory.Representation.BinaryOffender.CentralSectionAction
public import Theory.Representation.BinaryOffender.EquivariantOffender
/-!
# Central sections in a subgroup and its ambient group

Passing from a subgroup K to the original ambient group preserves the concrete
Irr⁺ family for L ≤ K. Fixed-space equality gives a linear equivalence of the
literal central quotients. The subgroup inclusion identifies the two acting
groups, intertwines their quotient actions, and transports the FF property of
the action image. Relative centralizer inclusions also pass to the ambient group.
Only normalization inside the chosen overgroup is required.

This is the final change of ambient group in the reduction of
Aschbacher–Smith, *The Classification of Quasithin Groups*, B.1.11,
printed pp. 72–73 (PDF pp. 83–84).
-/

@[expose] public section

open Subgroup
namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

theorem fixedSpace_subgroupOf (L K : Subgroup G) (hLK : L ≤ K) :
    fixedSpace (ρ.comp K.subtype) (L.subgroupOf K) = fixedSpace ρ L := by
  rw [fixedSpace_comp_map, map_subgroupOf_eq_of_le hLK]

theorem IsIrrPlus.subgroupOf_iff (L K : Subgroup G) (hLK : L ≤ K)
    (I : Submodule (ZMod 2) V) :
    IsIrrPlus (ρ.comp K.subtype) (L.subgroupOf K) I ↔ IsIrrPlus ρ L I := by
  let f := subgroupOfEquivOfLe hLK
  constructor
  · intro h
    exact h.of_intertwining (ρ.comp K.subtype) ρ f.toMonoidHom f.surjective
      LinearMap.id Function.injective_id (fun _ _ => rfl) (Submodule.map_id _)
  · intro h
    apply h.of_intertwining ρ (ρ.comp K.subtype) f.symm.toMonoidHom f.symm.surjective
      LinearMap.id Function.injective_id
    · intro x v
      rfl
    · exact Submodule.map_id _

theorem map_stabilizes (K : Subgroup G) (H : Subgroup K) (I : Submodule (ZMod 2) V)
    (h : H ≤ subspaceStabilizer (ρ.comp K.subtype) I) :
    H.map K.subtype ≤ subspaceStabilizer ρ I := by
  rintro _ ⟨h', hh', rfl⟩
  exact h hh'

noncomputable def subgroupCentralQuotientEquiv (L K : Subgroup G) (hLK : L ≤ K)
    (I : Submodule (ZMod 2) V) :
    centralQuotient (ρ.comp K.subtype) (L.subgroupOf K) I ≃ₗ[ZMod 2]
      centralQuotient ρ L I :=
  Submodule.Quotient.equiv _ _ (LinearEquiv.refl (ZMod 2) I) (by
    change ((fixedSpace (ρ.comp K.subtype) (L.subgroupOf K)).comap I.subtype).map LinearMap.id = _
    rw [Submodule.map_id, fixedSpace_subgroupOf ρ L K hLK])

theorem map_normalizes (L K : Subgroup G) (hLK : L ≤ K) (H : Subgroup K)
    (hN : H ≤ normalizer (L.subgroupOf K : Set K)) :
    H.map K.subtype ≤ normalizer (L : Set G) := by
  rintro _ ⟨h, hh, rfl⟩
  rw [mem_normalizer_iff]
  intro l
  constructor
  · intro hl
    exact (mem_normalizer_iff.mp (hN hh) ⟨l, hLK hl⟩).mp hl
  · intro hl
    have hinv := (normalizer (L.subgroupOf K : Set K)).inv_mem (hN hh)
    have hm := (mem_normalizer_iff.mp hinv
      ⟨(h : G) * l * (h : G)⁻¹, hLK hl⟩).mp hl
    change (h : G)⁻¹ * ((h : G) * l * (h : G)⁻¹) * (h : G)⁻¹⁻¹ ∈ L at hm
    simpa [mul_assoc] using hm

theorem subgroupCentralQuotientEquiv_intertwines (L K : Subgroup G) (hLK : L ≤ K)
    (H : Subgroup K) (I : Submodule (ZMod 2) V)
    (hI : H ≤ subspaceStabilizer (ρ.comp K.subtype) I)
    (hN : H ≤ normalizer (L.subgroupOf K : Set K))
    (h : H) (v : centralQuotient (ρ.comp K.subtype) (L.subgroupOf K) I) :
    subgroupCentralQuotientEquiv ρ L K hLK I
      (centralSectionRepresentation (ρ.comp K.subtype) (L.subgroupOf K) H I hI hN h v) =
    centralSectionRepresentation ρ L (H.map K.subtype) I (map_stabilizes ρ K H I hI)
      (map_normalizes L K hLK H hN) (H.equivMapOfInjective K.subtype K.subtype_injective h)
      (subgroupCentralQuotientEquiv ρ L K hLK I v) := by
  induction v using Submodule.Quotient.induction_on with | _ v => rfl


theorem section_centralizer_to_ambient (L K : Subgroup G) (hLK : L ≤ K)
    (H : Subgroup K) (I : Submodule (ZMod 2) V)
    (hI : H ≤ subspaceStabilizer (ρ.comp K.subtype) I)
    (hN : H ≤ normalizer (L.subgroupOf K : Set K))
    (hcent : (centralSectionRepresentation (ρ.comp K.subtype) (L.subgroupOf K) H I hI hN).ker.map
      H.subtype ≤ H ⊓ centralizer (L.subgroupOf K : Set K)) :
    (centralSectionRepresentation ρ L (H.map K.subtype) I (map_stabilizes ρ K H I hI)
      (map_normalizes L K hLK H hN)).ker.map (H.map K.subtype).subtype ≤
      H.map K.subtype ⊓ centralizer (L : Set G) := by
  rintro _ ⟨h, hh, rfl⟩
  obtain ⟨h', rfl⟩ := (H.equivMapOfInjective K.subtype K.subtype_injective).surjective h
  have hk : h' ∈ (centralSectionRepresentation (ρ.comp K.subtype) (L.subgroupOf K) H I hI hN).ker := by
    apply LinearMap.ext
    intro v
    apply (subgroupCentralQuotientEquiv ρ L K hLK I).injective
    rw [subgroupCentralQuotientEquiv_intertwines ρ L K hLK H I hI hN]
    rw [show centralSectionRepresentation ρ L (H.map K.subtype) I (map_stabilizes ρ K H I hI)
      (map_normalizes L K hLK H hN) (H.equivMapOfInjective K.subtype K.subtype_injective h') = 1 from hh]
    rfl
  have hc := (hcent ⟨h', hk, rfl⟩).2
  refine ⟨Subgroup.mem_map_of_mem _ h'.property, ?_⟩
  change ((h' : K) : G) ∈ centralizer (L : Set G)
  rw [mem_centralizer_iff]
  intro l hl
  exact congrArg (fun x : K => (x : G)) ((mem_centralizer_iff.mp hc) ⟨l, hLK hl⟩ hl)

theorem section_image_isFFModule_to_ambient (L K : Subgroup G) (hLK : L ≤ K)
    (H : Subgroup K) (I : Submodule (ZMod 2) V)
    (hI : H ≤ subspaceStabilizer (ρ.comp K.subtype) I)
    (hN : H ≤ normalizer (L.subgroupOf K : Set K))
    (hFF : IsFFModule (imageRepresentation
      (centralSectionRepresentation (ρ.comp K.subtype) (L.subgroupOf K) H I hI hN))) :
    IsFFModule (imageRepresentation (centralSectionRepresentation ρ L (H.map K.subtype) I
      (map_stabilizes ρ K H I hI) (map_normalizes L K hLK H hN))) := by
  let f := H.equivMapOfInjective K.subtype K.subtype_injective
  apply image_isFFModule_of_equivariant _ _ f.symm.toMonoidHom f.symm.surjective
    (subgroupCentralQuotientEquiv ρ L K hLK I) _ hFF
  intro h v
  have he := subgroupCentralQuotientEquiv_intertwines ρ L K hLK H I hI hN (f.symm h) v
  simpa only [f, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply] using he.symm

end Representation.BinaryOffender
