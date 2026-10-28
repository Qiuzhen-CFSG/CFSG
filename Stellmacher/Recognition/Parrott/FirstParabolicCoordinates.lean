module
public import Stellmacher.Recognition.Parrott.LocalGenerators
public import Stellmacher.Recognition.Parrott.SylowPresentation
public import Theory.SpecificGroups.Tits.FirstParabolicCoordinateTransport
/-!
# The first Weyl actor on a normalized Parrott frame

The actual compatible Parrott frame satisfies the seven first-actor equations
on p.683. Its eight Sylow words generate the literal local Sylow subgroup.
Restricting these words and the actor to C_G(z) gives a Sylow frame with an
outside actor. The actor is outside because otherwise the centralizer of
order 10240 would equal its Sylow subgroup of order 2048.

Source: Parrott (1972), §§3,5--6, pp.678--684. The normalizer frame here is
constructed from local inputs by the source consumer; no second actor or
compatibility is an input to that consumer.
-/

public section
open Subgroup Tits.FirstParabolicCoordinates
namespace Stellmacher.Recognition
variable {G : Type*} [Group G] {z : G}
variable {e : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData e}
namespace ParrottNormalizerGeneratorData
variable {f : ParrottCentralizerGeneratorData n} (k : ParrottNormalizerGeneratorData f)
include k in
/-- The seven equations I(r1), VI(s1,r1), and VII, in the printed word order. -/
theorem sylow_words_weyl :
    WeylRelations f.toParrottSylowGeneratorData.sylowWords f.r := by
  constructor
  · simpa only [words, Tits.parrottRecognitionWords, Tits.parrottRelator,
      map_mul, map_pow, map_inv,
      FreeGroup.lift_apply_of, mul_inv_eq_one] using k.relators_except_braid .i_r1 (by decide)
  · simpa only [ParrottSylowGeneratorData.sylowWords, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val, words, Tits.parrottRecognitionWords, Tits.parrottRelator,
      map_mul, map_pow, map_inv,
      FreeGroup.lift_apply_of, mul_inv_eq_one] using k.relators_except_braid .vi_s1_r1 (by decide)
  · simpa only [ParrottSylowGeneratorData.sylowWords, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val, words, Tits.parrottRecognitionWords, Tits.parrottRelator,
      map_mul, map_pow, map_inv,
      FreeGroup.lift_apply_of, mul_inv_eq_one] using k.relators_except_braid .vii_s2 (by decide)
  · simpa only [ParrottSylowGeneratorData.sylowWords, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val, words, Tits.parrottRecognitionWords, Tits.parrottRelator,
      map_mul, map_pow, map_inv,
      FreeGroup.lift_apply_of, mul_inv_eq_one] using k.relators_except_braid .vii_s4 (by decide)
  · simpa only [ParrottSylowGeneratorData.sylowWords, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val, words, Tits.parrottRecognitionWords, Tits.parrottRelator,
      map_mul, map_pow, map_inv,
      FreeGroup.lift_apply_of, mul_inv_eq_one] using k.relators_except_braid .vii_s5 (by decide)
  · simpa only [ParrottSylowGeneratorData.sylowWords, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val, words, Tits.parrottRecognitionWords, Tits.parrottRelator,
      Tits.parrottR3, Tits.parrottR7, Tits.FirstParabolicCoordinates.r3,
      Tits.FirstParabolicCoordinates.r7, map_mul, map_pow, map_inv,
      FreeGroup.lift_apply_of, mul_inv_eq_one] using k.relators_except_braid .vii_s3 (by decide)
  · simpa only [ParrottSylowGeneratorData.sylowWords, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val, words, Tits.parrottRecognitionWords, Tits.parrottRelator,
      Tits.parrottR3, Tits.parrottR7, Tits.FirstParabolicCoordinates.r3,
      Tits.FirstParabolicCoordinates.r7, map_mul, map_pow, map_inv,
      FreeGroup.lift_apply_of, mul_inv_eq_one] using k.relators_except_braid .vii_r3 (by decide)

include k in
/-- The first actor and a normalized frame live in the actual centralizer. -/
theorem exists_first_weylExtension [Finite G] (hp : ParrottCentralizerHypotheses z) :
    ∃ d : SylowCoordinates (e.localSylow : Subgroup (centralizer ({z} : Set G))),
      Nonempty (WeylExtension d) := by
  let C := centralizer ({z} : Set G)
  let h := f.toParrottSylowGeneratorData
  have hout : f.r ∉ (e.sylow : Subgroup G) := by
    intro hr
    have he : C = (e.sylow : Subgroup G) :=
      f.centralizer_generators.symm.trans (sup_eq_left.mpr (zpowers_le.mpr hr))
    have hc := Nat.card_congr (MulEquiv.subgroupCongr he).toEquiv
    rw [(hp.card_and_solvable z).1, e.sylow_card hp] at hc
    contradiction
  let w : Fin 8 → C := fun i =>
    ⟨h.sylowWords i, e.sylow_le_centralizer (h.sylowTuple i).property⟩
  have hrel : SylowRelations w :=
    h.sylowWords_relations.of_injective C.subtype C.subtype_injective
  have hgen : closure (Set.range w) = (e.localSylow : Subgroup C) := by
    apply map_injective C.subtype_injective
    rw [MonoidHom.map_closure, ← e.sylow_map, ← Set.range_comp]
    exact h.sylowWords_closure
  let d := SylowCoordinates.ofAmbient (e.localSylow : Subgroup C) w hrel hgen
  refine ⟨d, ⟨{ element := ⟨f.r, f.r_mem_centralizer⟩, outside := ?_, relations := ?_ }⟩⟩
  · intro hr
    apply hout
    rw [e.sylow_map]
    exact mem_map_of_mem C.subtype hr
  · have hw : WeylRelations w (⟨f.r, f.r_mem_centralizer⟩ : C) :=
      k.sylow_words_weyl.of_injective C.subtype C.subtype_injective
    simpa only [d, SylowCoordinates.coe_ofAmbient] using hw

end ParrottNormalizerGeneratorData
end Stellmacher.Recognition
