module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.Support
public import Theory.Representation.BinaryConjugationSection
/-!
# The intrinsic block model from an original moved section

For a block K in a finite local ambient group, its nonzero commutator with
any normal elementary module U is exactly the ambient image of U(K).
Transporting a marked section of that actual commutator identifies the
intrinsic quotient U(K)/C_U(K)(K), with the given core quotient map and
literal conjugation action. The central kernel is retained throughout.

Source: Aschbacher–Smith C.1.7–8 and C.1.27, pp.123,133; applied in
10.2.3(4), printed pp.746–747.
-/
public section
open Subgroup Theory.GroupTheory Representation
namespace CFSG.Quasithin.ChapterC
noncomputable section
variable {G A W : Type*} [Group G] [Group A] [AddCommGroup W]
  [Module (ZMod 2) W]
variable (K U : Subgroup G) (hmoved : (blockU K).map K.subtype = ⁅U,K⁆)
  (e : (K ⧸ pCore 2 K) ≃* A) (ρ : Representation (ZMod 2) A W)
  (r : A →* MulAut (Multiplicative W))
  (hr : ∀ a w, (r a w).toAdd = ρ a w.toAdd)
  (c : BinaryConjugationSection K ⁅U,K⁆ (⁅U,K⁆ ⊓ centralizer (K : Set G))
    (ρ.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K)))))


private def movedCoordinates : blockU K →* Multiplicative W :=
  c.coordinates.comp {
    toFun := fun u => ⟨u,hmoved.le (mem_map_of_mem K.subtype u.property)⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }

private theorem movedCoordinates_surjective :
    Function.Surjective (movedCoordinates K U hmoved e ρ c) := by
  intro v
  obtain ⟨w,rfl⟩ := c.onto v
  obtain ⟨u,hu,he⟩ := hmoved.ge w.property
  refine ⟨⟨u,hu⟩,?_⟩
  exact congrArg c.coordinates (Subtype.ext he)

private theorem movedCoordinates_ker :
    (movedCoordinates K U hmoved e ρ c).ker = blockFixed K := by
  ext u
  rw [MonoidHom.mem_ker]
  change c.coordinates _ = 1 ↔ (u : K) ∈ center K
  rw [c.coordinates_eq_one_iff]
  constructor
  · intro hu
    exact mem_center_iff.mpr (fun k => Subtype.ext (hu.2 k k.property))
  · intro hu
    have hw : ((u : K) : G) ∈ ⁅U,K⁆ := by
      rw [←hmoved]
      exact mem_map_of_mem K.subtype u.property
    exact ⟨hw, fun k hk => congrArg K.subtype (mem_center_iff.mp hu ⟨k,hk⟩)⟩

include hr in
private theorem movedCoordinates_equivariant (k : K) (u : blockU K) :
    movedCoordinates K U hmoved e ρ c (blockConjugate K k u) =
      r (e (QuotientGroup.mk' (pCore 2 K) k)) (movedCoordinates K U hmoved e ρ c u) := by
  apply Multiplicative.toAdd.injective
  rw [hr]
  let w : (⁅U,K⁆ : Subgroup G) := ⟨u,hmoved.le (mem_map_of_mem K.subtype u.property)⟩
  exact c.equivariant k w

/-- The natural section of the actual moved module identifies the intrinsic block module. -/
def blockModelOfIdentifiedMovedSection : BlockModuleModel K r := by
  let f := movedCoordinates K U hmoved e ρ c
  let m : BlockModule K ≃* Multiplicative W :=
    (QuotientGroup.quotientMulEquivOfEq (movedCoordinates_ker K U hmoved e ρ c).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f (movedCoordinates_surjective K U hmoved e ρ c))
  exact { quotientIso := e
          moduleIso := m
          intertwining := movedCoordinates_equivariant K U hmoved e ρ r hr c }
/-- The nonzero original normal-module commutator supplies the identification. -/
def blockModelOfMovedSection [Finite G]
    (hK : IsBlock K) [U.Normal] [IsElementaryAbelian 2 U]
    (hne : ⁅U,K⁆ ≠ ⊥) : BlockModuleModel K r :=
  blockModelOfIdentifiedMovedSection K U
    (RankOne.ChiProduct.SelectedRankOne.blockU_eq_nontrivial_normal_module_commutator K U hK hne)
    e ρ r hr c

end
end CFSG.Quasithin.ChapterC
