module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.Geometry
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.OuterAction

/-!
# Recovering basis coordinates for the supplied minimal parabolic

Choose coordinates for a Sylow subgroup contained in the parabolic. Every
space of the supplied flag is invariant under the full binary Sylow flag,
so the checked invariant-subspace theorem makes it one of the basis cuts.
Its dimension identifies that cut uniquely. The prescribed flag types then
recover exactly the cuts other than the specified omitted dimension.

The resulting parabolic equality keeps the original model and omitted node.
It supplies the coordinate premise of the checked invariant-node outer-action
theorem; no diagram action or basis alignment is assumed.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed
p.1145, the T-invariant minimal-parabolic argument.
-/

@[expose] public section

open Subgroup
open CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Binary
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification.Linear
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.BinaryGeneration
variable {X : Type*} [Group X] [Finite X] {K P : Subgroup X}

lemma position_deletedFlag {m : ℕ} (hm : 2 ≤ m)
    (pos : BinaryGeometry.Position K P (m + 1))
    (S : Sylow 2 K) (hSP : (S : Subgroup K) ≤ P.subgroupOf K) :
    ∃ (b : Basis m) (i : Fin m), i.val + 1 = pos.node ∧
      P = ambientFlagStabilizer pos.model (deletedFlag hm b i) := by
  classical
  let e := linearModel pos.model
  let U := S.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨b, hb⟩ := BinaryLinear.InvariantNodeActions.sylow_eq_cutStabilizer U
  have hSP' : (S : Subgroup K) ≤ flagStabilizer pos.model pos.flag := by
    have he : P.subgroupOf K = flagStabilizer pos.model pos.flag := by
      calc
        _ = (ambientFlagStabilizer pos.model pos.flag).subgroupOf K :=
          congrArg (fun Q : Subgroup X => Q.subgroupOf K) pos.parabolic_eq
        _ = _ := comap_map_eq_self_of_injective K.subtype_injective _
    exact he ▸ hSP
  have hcut : ∀ W ∈ pos.flag.spaces, ∃ j : Fin m,
      W = BinaryLinear.InvariantNodeActions.cutSpace b j := by
    intro W hW
    apply BinaryLinear.InvariantNodeActions.fullFlag_invariant_subspace b W
      (pos.flag.proper W hW).1 (pos.flag.proper W hW).2
    rw [← hb]
    change (S : Subgroup K).map e.toMonoidHom ≤ _
    rintro g ⟨s, hs, rfl⟩
    exact (mem_flagStabilizer pos.model pos.flag s).mp (hSP' hs) W hW
  let i : Fin m := ⟨pos.node - 1, by have := pos.node_lt; have := pos.node_pos; omega⟩
  have hi : i.val + 1 = pos.node := by dsimp [i]; have := pos.node_pos; omega
  have hspaces : pos.flag.spaces = (deletedFlag hm b i).spaces := by
    ext W
    constructor
    · intro hW
      obtain ⟨j, hj⟩ := hcut W hW
      have hd : Module.finrank (ZMod 2) W ∈ pos.flag.types :=
        Finset.mem_image.mpr ⟨W, hW, rfl⟩
      rw [pos.types_eq] at hd
      have hjn : j ≠ i := by
        intro hji
        have hdim : Module.finrank (ZMod 2) W = pos.node := by
          rw [hj, BinaryLinear.InvariantNodeActions.cutSpace_finrank, hji, hi]
        exact (Finset.mem_erase.mp hd).1 hdim
      exact Finset.mem_image.mpr ⟨j, Finset.mem_erase.mpr ⟨hjn, Finset.mem_univ _⟩, hj.symm⟩
    · intro hW
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hW
      have hji := (Finset.mem_erase.mp hj).1
      have hd : j.val + 1 ∈ pos.flag.types := by
        rw [pos.types_eq]
        apply Finset.mem_erase.mpr
        refine ⟨?_, Finset.mem_erase.mpr ⟨by omega, Finset.mem_range.mpr (by omega)⟩⟩
        intro he
        apply hji
        apply Fin.ext
        have := j.isLt
        omega
      obtain ⟨W, hW, hdW⟩ := Finset.mem_image.mp hd
      obtain ⟨k, hk⟩ := hcut W hW
      have hkj : k = j := by
        rw [hk, BinaryLinear.InvariantNodeActions.cutSpace_finrank] at hdW
        apply Fin.ext
        omega
      simpa only [hk, hkj, cutSpace, BinaryLinear.InvariantNodeActions.cutSpace] using hW
  refine ⟨b, i, hi, ?_⟩
  refine pos.parabolic_eq.trans ?_
  simp only [ambientFlagStabilizer]
  congr 1
  ext g
  simp only [mem_flagStabilizer, hspaces]
end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.BinaryGeneration
