module

public import Theory.SpecificGroups.Tits.AmalgamRigidity.LocalRestrictions.SecondExtension.Collection

/-!
# Transport of collection equations

The equations are preserved by products and reflected by injective homomorphisms.
This lets the finite graph subgroup use the original and image certificates.
Source conventions: `Words`.
-/

@[expose] public section
namespace Tits.AmalgamRigidity.SecondExtension
variable {G H : Type*} [Group G] [Group H] {g : Fin 9 → G} {h : Fin 9 → H}

theorem SylowRelations.of_injective (f : G →* H) (hf : Function.Injective f)
    (hh : SylowRelations (f ∘ g)) : SylowRelations g := by
  constructor
  · apply hf
    simpa only [Function.comp_apply, map_mul, map_pow, map_inv, map_one] using hh.power_1
  · apply hf
    simpa only [Function.comp_apply, map_mul, map_pow, map_inv, map_one] using hh.power_2
  · apply hf
    simpa only [Function.comp_apply, map_mul, map_pow, map_inv, map_one] using hh.power_3
  · apply hf
    simpa only [Function.comp_apply, map_mul, map_pow, map_inv, map_one] using hh.power_4
  · apply hf
    simpa only [Function.comp_apply, map_mul, map_pow, map_inv, map_one] using hh.power_5
  · apply hf
    simpa only [Function.comp_apply, map_mul, map_pow, map_inv, map_one] using hh.power_6
  · apply hf
    simpa only [Function.comp_apply, map_mul, map_pow, map_inv, map_one] using hh.power_7
  · apply hf
    simpa only [Function.comp_apply, map_mul, map_pow, map_inv, map_one] using hh.power_8
  · apply hf
    simpa only [Function.comp_apply, map_mul, map_pow, map_inv, map_one] using hh.conjugate_2_1
  · apply hf
    simpa only [Function.comp_apply, map_mul, map_pow, map_inv, map_one] using hh.conjugate_3_1
  · apply hf
    simpa only [Function.comp_apply, map_mul, map_pow, map_inv, map_one] using hh.conjugate_3_2
  · apply hf
    simpa only [Function.comp_apply, map_mul, map_pow, map_inv, map_one] using hh.conjugate_4_1
  · apply hf
    simpa only [Function.comp_apply, map_mul, map_pow, map_inv, map_one] using hh.conjugate_4_2
  · apply hf
    simpa only [Function.comp_apply, map_mul, map_pow, map_inv, map_one] using hh.conjugate_4_3
  · apply hf
    simpa only [Function.comp_apply, map_mul, map_pow, map_inv, map_one] using hh.conjugate_5_1
  · apply hf
    simpa only [Function.comp_apply, map_mul, map_pow, map_inv, map_one] using hh.conjugate_5_2
  · apply hf
    simpa only [Function.comp_apply, map_mul, map_pow, map_inv, map_one] using hh.conjugate_5_3
  · apply hf
    simpa only [Function.comp_apply, map_mul, map_pow, map_inv, map_one] using hh.conjugate_5_4
  · apply hf
    simpa only [Function.comp_apply, map_mul, map_pow, map_inv, map_one] using hh.conjugate_6_1
  · apply hf
    simpa only [Function.comp_apply, map_mul, map_pow, map_inv, map_one] using hh.conjugate_6_2
  · apply hf
    simpa only [Function.comp_apply, map_mul, map_pow, map_inv, map_one] using hh.conjugate_6_3
  · apply hf
    simpa only [Function.comp_apply, map_mul, map_pow, map_inv, map_one] using hh.conjugate_6_4
  · apply hf
    simpa only [Function.comp_apply, map_mul, map_pow, map_inv, map_one] using hh.conjugate_6_5
  · apply hf
    simpa only [Function.comp_apply, map_mul, map_pow, map_inv, map_one] using hh.conjugate_7_1
  · apply hf
    simpa only [Function.comp_apply, map_mul, map_pow, map_inv, map_one] using hh.conjugate_7_2
  · apply hf
    simpa only [Function.comp_apply, map_mul, map_pow, map_inv, map_one] using hh.conjugate_7_3
  · apply hf
    simpa only [Function.comp_apply, map_mul, map_pow, map_inv, map_one] using hh.conjugate_7_4
  · apply hf
    simpa only [Function.comp_apply, map_mul, map_pow, map_inv, map_one] using hh.conjugate_7_5
  · apply hf
    simpa only [Function.comp_apply, map_mul, map_pow, map_inv, map_one] using hh.conjugate_7_6
  · apply hf
    simpa only [Function.comp_apply, map_mul, map_pow, map_inv, map_one] using hh.conjugate_8_1
  · apply hf
    simpa only [Function.comp_apply, map_mul, map_pow, map_inv, map_one] using hh.conjugate_8_2
  · apply hf
    simpa only [Function.comp_apply, map_mul, map_pow, map_inv, map_one] using hh.conjugate_8_3
  · apply hf
    simpa only [Function.comp_apply, map_mul, map_pow, map_inv, map_one] using hh.conjugate_8_4
  · apply hf
    simpa only [Function.comp_apply, map_mul, map_pow, map_inv, map_one] using hh.conjugate_8_5
  · apply hf
    simpa only [Function.comp_apply, map_mul, map_pow, map_inv, map_one] using hh.conjugate_8_6
  · apply hf
    simpa only [Function.comp_apply, map_mul, map_pow, map_inv, map_one] using hh.conjugate_8_7

theorem SylowRelations.prod (hg : SylowRelations g) (hh : SylowRelations h) :
    SylowRelations (fun a => (g a, h a)) := by
  constructor
  · exact Prod.ext hg.power_1 hh.power_1
  · exact Prod.ext hg.power_2 hh.power_2
  · exact Prod.ext hg.power_3 hh.power_3
  · exact Prod.ext hg.power_4 hh.power_4
  · exact Prod.ext hg.power_5 hh.power_5
  · exact Prod.ext hg.power_6 hh.power_6
  · exact Prod.ext hg.power_7 hh.power_7
  · exact Prod.ext hg.power_8 hh.power_8
  · exact Prod.ext hg.conjugate_2_1 hh.conjugate_2_1
  · exact Prod.ext hg.conjugate_3_1 hh.conjugate_3_1
  · exact Prod.ext hg.conjugate_3_2 hh.conjugate_3_2
  · exact Prod.ext hg.conjugate_4_1 hh.conjugate_4_1
  · exact Prod.ext hg.conjugate_4_2 hh.conjugate_4_2
  · exact Prod.ext hg.conjugate_4_3 hh.conjugate_4_3
  · exact Prod.ext hg.conjugate_5_1 hh.conjugate_5_1
  · exact Prod.ext hg.conjugate_5_2 hh.conjugate_5_2
  · exact Prod.ext hg.conjugate_5_3 hh.conjugate_5_3
  · exact Prod.ext hg.conjugate_5_4 hh.conjugate_5_4
  · exact Prod.ext hg.conjugate_6_1 hh.conjugate_6_1
  · exact Prod.ext hg.conjugate_6_2 hh.conjugate_6_2
  · exact Prod.ext hg.conjugate_6_3 hh.conjugate_6_3
  · exact Prod.ext hg.conjugate_6_4 hh.conjugate_6_4
  · exact Prod.ext hg.conjugate_6_5 hh.conjugate_6_5
  · exact Prod.ext hg.conjugate_7_1 hh.conjugate_7_1
  · exact Prod.ext hg.conjugate_7_2 hh.conjugate_7_2
  · exact Prod.ext hg.conjugate_7_3 hh.conjugate_7_3
  · exact Prod.ext hg.conjugate_7_4 hh.conjugate_7_4
  · exact Prod.ext hg.conjugate_7_5 hh.conjugate_7_5
  · exact Prod.ext hg.conjugate_7_6 hh.conjugate_7_6
  · exact Prod.ext hg.conjugate_8_1 hh.conjugate_8_1
  · exact Prod.ext hg.conjugate_8_2 hh.conjugate_8_2
  · exact Prod.ext hg.conjugate_8_3 hh.conjugate_8_3
  · exact Prod.ext hg.conjugate_8_4 hh.conjugate_8_4
  · exact Prod.ext hg.conjugate_8_5 hh.conjugate_8_5
  · exact Prod.ext hg.conjugate_8_6 hh.conjugate_8_6
  · exact Prod.ext hg.conjugate_8_7 hh.conjugate_8_7

theorem CosetRelations.prod (hg : CosetRelations g) (hh : CosetRelations h) :
    CosetRelations (fun a => (g a, h a)) := by
  intro a i
  exact Prod.ext (hg a i) (hh a i)

end Tits.AmalgamRigidity.SecondExtension
