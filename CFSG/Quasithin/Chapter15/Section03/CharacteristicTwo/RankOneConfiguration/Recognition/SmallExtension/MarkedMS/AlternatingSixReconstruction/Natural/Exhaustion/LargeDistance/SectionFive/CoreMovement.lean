module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CoreActor

/-!
# Movement retained by the exceptional source restriction

For the two-disjoint-transposition actor on the full augmentation core,
the fixed hyperplane of the third transposition has the same moved space
as the entire core. This space is the plane on the first two duads and
has order four. The calculation uses the original five-dimensional cover;
conjugation transports both the actor and its restricted domain together.

`CoreRestriction` uses this equality to retain the actual critical
commutator when choosing the index-at-most-two controlling subactor.
Source: Meierfrankenfeld--Stellmacher (1993), (3.3)(ii)(1), printed
pp.866--867, and the restricted actor of (5.0), p.912.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender BinaryPermutation
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open CoreCrossing
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CoreMovement
local notation "ρ" => coreRepresentation (Fin 6)
local notation "A₂" => disjointTranspositions 6 2

def movedPlane : Submodule (ZMod 2) C := Submodule.span (ZMod 2) {pairWord 0 1,pairWord 2 3}

private theorem full_displacement : ∀ i : Fin 4, ∀ v : Full (Fin 6),
    ∃ a b : ZMod 2, ∀ j, (representation (Fin 6) (initialWords 2 i) v-v) j =
      (a • (pairWord 0 1).val+b • (pairWord 2 3).val) j := by
  decide +kernel

private theorem displacement : ∀ i : Fin 4, ∀ v : C,
    ∃ a b : ZMod 2, ρ (initialWords 2 i) v-v = a • pairWord 0 1+b • pairWord 2 3 := by
  intro i v
  obtain ⟨a,b,hh⟩ := full_displacement i v.val
  exact ⟨a,b,Subtype.ext (funext hh)⟩

private theorem pair01_mem : pairWord 0 1 ∈ subspaceCommutator ρ hyperplane A₂ := by
  have hh : ρ (pairSwap 6 0) (pairWord 0 2)-pairWord 0 2 = pairWord 0 1 := by decide
  rw [←hh]
  exact Submodule.subset_span ⟨_,pairSwap_mem 0 (by decide),_,(mem_hyperplane _).mpr (by decide),rfl⟩

private theorem pair23_mem : pairWord 2 3 ∈ subspaceCommutator ρ hyperplane A₂ := by
  have hh : ρ (pairSwap 6 1) (pairWord 0 2)-pairWord 0 2 = pairWord 2 3 := by decide
  rw [←hh]
  exact Submodule.subset_span ⟨_,pairSwap_mem 1 (by decide),_,(mem_hyperplane _).mpr (by decide),rfl⟩

theorem exceptional_moved_eq : subspaceCommutator ρ ⊤ A₂ = movedPlane := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨a,ha,v,_,rfl⟩
    obtain ⟨i,rfl⟩ := (mem_disjointTranspositions_iff (2 : Fin 4) a).mp ha
    obtain ⟨x,y,hxy⟩ := displacement i v
    rw [hxy]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  · apply Submodule.span_le.mpr
    intro v hv
    rcases hv with rfl | rfl
    · exact subspaceCommutator_mono_left ρ le_top A₂ pair01_mem
    · exact subspaceCommutator_mono_left ρ le_top A₂ pair23_mem

/-- The source restriction retains the entire critical moved plane. -/
theorem exceptional_restricted_moved_eq :
    subspaceCommutator ρ hyperplane A₂ = subspaceCommutator ρ ⊤ A₂ := by
  apply le_antisymm (subspaceCommutator_mono_left ρ le_top A₂)
  rw [exceptional_moved_eq]
  apply Submodule.span_le.mpr
  intro v hv
  rcases hv with rfl | rfl
  · exact pair01_mem
  · exact pair23_mem

/-- The original critical plane has order four. -/
theorem exceptional_moved_card : Nat.card (subspaceCommutator ρ ⊤ A₂) = 4 := by
  rw [exceptional_moved_eq]
  let f : (ZMod 2 × ZMod 2) → movedPlane := fun x =>
    ⟨x.1 • pairWord 0 1+x.2 • pairWord 2 3,
      Submodule.mem_span_pair.mpr ⟨x.1,x.2,rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y hh
      have h0 := congrArg (fun v : movedPlane => v.val.val 0) hh
      have h2 := congrArg (fun v : movedPlane => v.val.val 2) hh
      apply Prod.ext
      · simpa [f,pairWord] using h0
      · simpa [f,pairWord] using h2
    · intro v
      obtain ⟨a,b,he⟩ := Submodule.mem_span_pair.mp v.property
      exact ⟨(a,b),Subtype.ext he⟩
  rw [←Nat.card_congr (Equiv.ofBijective f hf),Nat.card_prod,Nat.card_zmod]

private theorem conjugate_equivariant (g a : S) (v : C) :
    ρ a (ρ g v) = ρ g (ρ ((MulAut.conj g⁻¹) a) v) := by
  simp only [←Module.End.mul_apply,←map_mul]
  congr 2
  change a*g = g*(g⁻¹*a*g)
  group

private theorem conjugate_cancel (A : Subgroup S) (g : S) :
    (A.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = A := by
  have he : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom = MonoidHom.id S := by
    ext x : 1
    change g⁻¹*(g*x*g⁻¹)*g = x
    group
  rw [Subgroup.map_map,he,Subgroup.map_id]

/-- Movement is computed in the original permutation coordinates. -/
theorem conjugate_moved (A : Subgroup S) (W : Submodule (ZMod 2) C) (g : S) :
    subspaceCommutator ρ (W.map (ρ g)) (A.map (MulAut.conj g).toMonoidHom) =
      (subspaceCommutator ρ W A).map (ρ g) := by
  have hh := subspaceCommutator_map_embedding ρ ρ (MulAut.conj g⁻¹).toMonoidHom (ρ g)
    (conjugate_equivariant g) (A.map (MulAut.conj g).toMonoidHom) W
  rwa [conjugate_cancel] at hh

/-- Conjugating the source restriction still retains the full moved plane. -/
theorem conjugate_restricted_moved_eq (g : S) :
    subspaceCommutator ρ (hyperplane.map (ρ g)) ((A₂).map (MulAut.conj g).toMonoidHom) =
      subspaceCommutator ρ ⊤ ((A₂).map (MulAut.conj g).toMonoidHom) := by
  have ht : (⊤ : Submodule (ZMod 2) C).map (ρ g) = ⊤ := by
    rw [Submodule.map_top,LinearMap.range_eq_top]
    exact (LinearMap.GeneralLinearGroup.toLinearEquiv ((coreRepresentation (Fin 6)).asGroupHom g)).surjective
  rw [conjugate_moved,exceptional_restricted_moved_eq,←conjugate_moved,ht]

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CoreMovement
