module
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedSylowSieveInner
public import Theory.Representation.BinaryOffender.Homogeneous.Core
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedSylowSieveKernel

public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedSylowSieveTwists
public import Theory.Representation.BinaryOffender.GeneratedCore
public import Theory.Representation.Quotient

/-!
# Component actions on faithful homogeneous constituents

A center-free constituent image makes the quasisimple component faithful:
the kernel is central, fixes the constituent, and hence fixes its full orbit.
The literal restricted image and the component action also have identical
fixed spaces. Thus the common cubic actor's constituent budget gives an
actual offender for the unchanged component subgroup.

These transports feed `SeedAlternativesMovedSylowExterior`, the exterior-five
exclusion of Aschbacher--Smith D.3.5(5), printed p.196.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
namespace CFSG.Quasithin.Chapter3.Section02.ChosenSource325
variable {H W : Type*} [Group H] [AddCommGroup W] [Module (ZMod 2) W]
  (ρ : Representation (ZMod 2) H W)

theorem restrictedActionSurjection_injective_of_center_free
    (K : Subgroup H) [K.Normal] [IsQuasisimple K]
    (I : Submodule (ZMod 2) W) (hKI : K ≤ subspaceStabilizer ρ I)
    (hf : Function.Injective ρ) (hgen : orbitSpan ρ ⊤ I = ⊤)
    [Nontrivial (restrictedSubgroup ρ I K)]
    (hz : center (restrictedSubgroup ρ I K) = ⊥) :
    Function.Injective (restrictedActionSurjection ρ I K hKI) := by
  let f := restrictedActionSurjection ρ I K hKI
  have hk : f.ker = center K := by
    change (⊥ : Subgroup (restrictedSubgroup ρ I K)).comap f = _
    rw [←hz]
    exact IsQuasisimple.comap_center_of_surjective f (restrictedActionSurjection_surjective ρ I K hKI)
  let P := (center K).map K.subtype
  have hI : I ≤ fixedSpace ρ P := by
    intro v hv p
    obtain ⟨k,hkz,he⟩ := p.property
    have hfk : f k = 1 := hk.ge hkz
    have hfv := congrArg (fun x : restrictedSubgroup ρ I K =>
      (subspaceImageRepresentation ρ I x.val ⟨v,hv⟩ : W)) hfk
    change ρ k.val v = v at hfv
    change ρ p.val v = v
    rwa [←he]
  have hP : P = ⊥ := eq_bot_of_faithful_orbitSpan ρ hf hI hgen
  apply (MonoidHom.ker_eq_bot_iff f).mp
  rw [hk]
  apply bot_unique
  intro k hkz
  exact mem_bot.mpr (Subtype.ext (mem_bot.mp (hP.le (mem_map_of_mem K.subtype hkz))))
theorem restrictedSubgroup_from_component (K A : Subgroup H)
    (I : Submodule (ZMod 2) W) (hKI : K ≤ subspaceStabilizer ρ I) (hAK : A ≤ K) :
    (A.subgroupOf K).map (subgroupActionHom ρ I K hKI) = restrictedSubgroup ρ I A := by
  apply le_antisymm
  · rintro _ ⟨a,ha,rfl⟩
    exact ⟨⟨a.val,hKI a.property⟩,ha,rfl⟩
  · rintro _ ⟨a,ha,rfl⟩
    exact ⟨⟨a.val,hAK ha⟩,ha,rfl⟩

theorem component_offender_of_restricted_budget
    (K A : Subgroup H) (I : Submodule (ZMod 2) W)
    (hKI : K ≤ subspaceStabilizer ρ I) (hAK : A ≤ K) (hA : IsElementaryTwo A)
    (hb : fixedCodim (subspaceImageRepresentation ρ I) (restrictedSubgroup ρ I A) ≤ rank A) :
    IsOffender (invariantSubspace ρ K I hKI).toRepresentation (A.subgroupOf K) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : IsElementaryAbelian 2 A := hA.2
  have hne : A.subgroupOf K ≠ ⊥ := by
    intro hz
    have hh := congrArg (fun S : Subgroup K => S.map K.subtype) hz
    rw [map_subgroupOf_eq_of_le hAK,Subgroup.map_bot] at hh
    exact hA.1 hh
  refine ⟨⟨hne,IsElementaryAbelian.subgroupOf hAK⟩,?_⟩
  rw [rank_subgroupOf hAK]
  have he : fixedSpace (invariantSubspace ρ K I hKI).toRepresentation (A.subgroupOf K) =
      fixedSpace (subspaceImageRepresentation ρ I) (restrictedSubgroup ρ I A) := by
    rw [←restrictedSubgroup_from_component ρ K A I hKI hAK,←fixedSpace_comp_map]
    rfl
  change Module.finrank (ZMod 2) (I ⧸ _) ≤ _
  rw [he]
  exact hb

theorem invariant_irreducible_of_isIrrPlus
    (K : Subgroup H) (I : Submodule (ZMod 2) W) (hI : IsIrrPlus ρ K I)
    (hz : I ⊓ fixedSpace ρ K = ⊥) :
    IsIrreducible (invariantSubspace ρ K I hI.choose).toRepresentation := by
  let e := zeroFixedImageEquiv ρ K I hI.choose hz
  exact (Representation.RepEquiv.ofRepresentationEquiv e).irreducible_of_euqiv
    (quotientImage_irreducible ρ hI)

end CFSG.Quasithin.Chapter3.Section02.ChosenSource325
