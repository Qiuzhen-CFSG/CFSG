module

public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.CubicRecognition.CubicSylow.Promotion
public import Theory.GroupTheory.PGroup.ExtraspecialPrimeCube
public import Theory.GroupTheory.PGroup.ExtraspecialAutomorphisms

/-!
# The nonabelian branch of the cubic Sylow construction

A nonabelian group of order 27 is extraspecial with center of order three.
Since the original B is already central of order three, both the center
and the commutator have exactly ambient image B. The characteristic-center
argument then promotes this same subgroup to a Sylow subgroup of G.

Noncommutativity remains an explicit premise until the E₂₇ branch has
been excluded. Exponent three and element fusion are separate obligations.

Source: Aschbacher–Smith, J.2.7, printed p.437 (PDF p.448).
-/

public section
namespace CFSG.Quasithin.ChapterJ.Centralizers.CubicSylow
open Subgroup
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G} (c : Choices d)

/-- Noncommutativity identifies both characteristic subgroups with the actual B. -/
theorem nonabelian_structure (hB : Nat.card c.B = 3)
    (e : c.NormalizerQuotient ≃* MulAut (alternatingGroup (Fin 6)))
    (hM : c.centralizerImage.map e.toMonoidHom = AlternatingSix.M10.extension)
    (R : Sylow 3 c.NB) (hn : ¬ IsMulCommutative (ambient c R)) :
    IsExtraspecial 3 (ambient c R) ∧
      (center (ambient c R)).map (ambient c R).subtype = c.B ∧
      (_root_.commutator (ambient c R)).map (ambient c R).subtype = c.B := by
  let : IsExtraspecial 3 (ambient c R) :=
    IsExtraspecial.of_noncommutative_card_prime_cube
      (show Nat.card (ambient c R) = 3 ^ 3 from ambient_card c hB e R) hn
  have hle : c.B ≤ (center (ambient c R)).map (ambient c R).subtype := by
    rw [← map_subgroupOf_eq_of_le (B_le c hB R)]
    exact map_mono (B_le_center c hB e hM R)
  have hz : (center (ambient c R)).map (ambient c R).subtype = c.B := by
    apply (eq_of_le_of_card_ge hle ?_).symm
    rw [card_map_of_injective (ambient c R).subtype_injective,
      IsExtraspecial.center_order_p 3 (ambient c R), hB]
  refine ⟨inferInstance, hz, ?_⟩
  rw [IsExtraspecial.commutator_eq_center (p := 3), hz]

/-- The nonabelian branch produces an ambient Sylow with exactly R's image. -/
theorem exists_ambient_sylow_of_noncommutative (hB : Nat.card c.B = 3)
    (e : c.NormalizerQuotient ≃* MulAut (alternatingGroup (Fin 6)))
    (hM : c.centralizerImage.map e.toMonoidHom = AlternatingSix.M10.extension)
    (R : Sylow 3 c.NB) (hn : ¬ IsMulCommutative (ambient c R)) :
    ∃ S : Sylow 3 G, (S : Subgroup G) = ambient c R :=
  exists_ambient_sylow_of_center c R (nonabelian_structure c hB e hM R hn).2.1

end CFSG.Quasithin.ChapterJ.Centralizers.CubicSylow
