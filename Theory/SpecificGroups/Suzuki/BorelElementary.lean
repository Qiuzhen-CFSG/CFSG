module
public import Theory.SpecificGroups.Suzuki.SylowOmegaGeometry
public import Theory.SpecificGroups.Suzuki.SchurEightUpper.KernelGeneration.SuzukiActions
import all Theory.SpecificGroups.Suzuki.SchurEightUpper.KernelGeneration.SuzukiActions

/-!
# Elementary subgroups invariant under a Suzuki Borel

A nontrivial elementary subgroup of a Suzuki Sylow lies in its first omega,
which is its embedded center. If the full Sylow normalizer normalizes the
subgroup, transitivity on nonidentity central elements makes it the whole
center. Sylow conjugacy transports this calculation to the prescribed Sylow.

The internal import deliberately reuses the root-coordinate transitivity
proof from the kernel-generation development; no private name enters this
module's public statement. The concrete consumer is the nonsymplectic center
marking in `HermitianSourceSelectionCenter`.

Source: Huppert--Blackburn III, XI.3.1--3.3; Aschbacher--Smith E.2.14(2),
printed pp.226--227 (refs/quasithin.pdf).
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace BenderSuzuki.MatrixGroups

private theorem root_center_eq_of_normalized (m : ℕ) (hm : 0 < m)
    (E : Subgroup (SuzukiMatrixGroup m))
    (hE : E ≤ (center (SuzukiRootSubgroup m)).map (SuzukiRootSubgroup m).subtype)
    (hne : E ≠ ⊥)
    (hN : normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)) ≤
      normalizer (E : Set (SuzukiMatrixGroup m))) :
    E = (center (SuzukiRootSubgroup m)).map (SuzukiRootSubgroup m).subtype := by
  apply le_antisymm hE
  obtain ⟨z,hz,hz1⟩ := E.bot_or_exists_ne_one.resolve_left hne
  obtain ⟨z',hz',rfl⟩ := hE hz
  rintro _ ⟨w,hw,rfl⟩
  by_cases hw1 : w = 1
  · simpa only [hw1,map_one] using E.one_mem
  obtain ⟨a,ha⟩ := SchurCover.EightLocal.KernelActions.torus_center_transitive m hm
    ⟨z',hz'⟩ ⟨w,hw⟩ (fun he => hz1 (congrArg (fun x : center (SuzukiRootSubgroup m) =>
      ((x : SuzukiRootSubgroup m) : SuzukiMatrixGroup m)) he))
    (fun he => hw1 (congrArg Subtype.val he))
  have hc := (mem_normalizer_iff.mp (hN a.property) (z' : SuzukiMatrixGroup m)).mp hz
  have he := congrArg (fun x : center (SuzukiRootSubgroup m) =>
      ((x : SuzukiRootSubgroup m) : SuzukiMatrixGroup m)) ha
  change a.val * (z' : SuzukiMatrixGroup m) * a.val⁻¹ = w at he
  rwa [he] at hc

theorem suzuki_elementary_eq_center_of_borel_normalized
    {X : Type*} [Group X] [Finite X] {m : ℕ} (hm : 0 < m)
    (e : X ≃* SuzukiMatrixGroup m) (S : Sylow 2 X)
    (E : Subgroup X) [IsElementaryAbelian 2 E]
    (hES : E ≤ S) (hne : E ≠ ⊥)
    (hN : normalizer (S : Set X) ≤ normalizer (E : Set X)) :
    E = (center S).map (S : Subgroup X).subtype := by
  have hEZ : E ≤ (center S).map (S : Subgroup X).subtype := by
    rw [← suzukiSylow_omega_eq_center hm e S, ← omegaOneAmbient_eq_self E]
    exact omegaOneAmbient_mono hES
  obtain ⟨f,hS,hB⟩ := suzukiSylow_aligned_equiv hm e S
  have hf : (S : Subgroup X).map f.symm.toMonoidHom = SuzukiRootSubgroup m := by
    rw [←hS,map_map]
    simp
  have hEZ' := map_mono (f := f.symm.toMonoidHom) hEZ
  rw [map_embeddedCenter _ _ f.symm.injective,hf] at hEZ'
  have hN' := map_mono (f := f.symm.toMonoidHom) hN
  change (normalizer ((S : Subgroup X) : Set X)).map f.symm.toMonoidHom ≤
    (normalizer (E : Set X)).map f.symm.toMonoidHom at hN'
  rw [map_equiv_normalizer_eq,map_equiv_normalizer_eq,hf] at hN'
  have hne' : E.map f.symm.toMonoidHom ≠ ⊥ := by
    intro hh
    exact hne ((map_eq_bot_iff_of_injective (f := f.symm.toMonoidHom) E f.symm.injective).mp hh)
  apply map_injective (f := f.symm.toMonoidHom) f.symm.injective
  rw [map_embeddedCenter _ _ f.symm.injective,hf]
  exact root_center_eq_of_normalized m hm _ hEZ' hne' hN'
end BenderSuzuki.MatrixGroups
