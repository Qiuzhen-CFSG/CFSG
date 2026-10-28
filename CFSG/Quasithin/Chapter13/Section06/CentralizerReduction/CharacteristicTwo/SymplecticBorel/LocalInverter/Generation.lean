module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.SymplecticBorel.Transport
public import Theory.SpecificGroups.SymplecticFour.EvenBorelTorus.ResidualGeneration

/-!
# Two-perfectness of the higher-field symplectic Borel

The root-torus commutator calculations put the unipotent group in
O²(B), and the diagonal torus section surjects onto B/O₂(B). Together
they prove B = O²(B), transported to the specified component Sylow.
This is the intrinsic input for identifying the B-image on V with
the cubic Lᵥ-image in the local five-point stabilizer.

Source: Aschbacher–Smith, proof of 13.6.6, printed p.927. Only the
intrinsic matrix/root proofs are reused; no later 13.8 theorem is used.
-/

@[expose] public section

open Subgroup Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.EvenBorelTorus
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SymplecticBorel.LocalInverter
variable {H F : Type*} [Group H] [Field F] [Finite F] [CharP F 2]

private theorem model_borel_twoPerfect {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n) :
    pResidual 2 (borel (F := F)) = ⊤ := by
  have hker : (borelCharacters (F := F)).ker ≤ pResidual 2 (borel (F := F)) := by
    intro b hb
    have hU := (borelCharacters_eq_one b).mp hb
    exact (mem_map_iff_mem (borel (F := F)).subtype_injective).mp
      (unipotent_le_residual hF hn hU)
  have hm : (pResidual 2 (borel (F := F))).map borelCharacters = ⊤ := by
    apply top_unique
    intro x _
    refine ⟨torusSection x, ?_, characters_torusSection x⟩
    exact (mem_map_iff_mem (borel (F := F)).subtype_injective).mp
      (torusSection_mem_residual hF x)
  have he := congrArg (Subgroup.comap (borelCharacters (F := F))) hm
  rwa [comap_map_eq, comap_top, sup_of_le_left hker] at he

/-- The actual higher-field Borel equals its two-residual. This uses only
root-torus commutators and the diagonal section, with no later chapter result. -/
theorem localBorel_twoPerfect (K : Subgroup H) (e : K ≃* Sp F)
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n) (S : Sylow 2 (Sp F)) :
    pResidual 2 (localBorel K e S) = ⊤ := by
  let f := borelEquiv K e hF hn.le S
  let : Finite (localBorel K e S) := Finite.of_injective f f.injective
  apply map_injective (f := f.toMonoidHom) f.injective
  rw [map_pResidual_of_surjective 2 f.toMonoidHom f.surjective,
    model_borel_twoPerfect hF hn, ← MonoidHom.range_eq_map,
    MonoidHom.range_eq_top.mpr f.surjective]
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SymplecticBorel.LocalInverter
