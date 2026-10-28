module
public import Theory.SpecificGroups.Tits.FirstParabolicCoordinates
public import Mathlib.GroupTheory.Sylow
/-!
# Transport of first-parabolic Sylow frames

The scalar equations reflect along injective homomorphisms. Generating ambient
words therefore define coordinates on their literal subgroup. Equivalences
transport the coordinates together with the outside actor, and Sylow conjugacy
places a constructed pair on any prescribed Sylow subgroup. No assertion is
made that an arbitrary preassigned frame extends unchanged.

Source: Parrott (1972), §5, p.683, together with Sylow conjugacy.
-/

public section
open Subgroup
namespace Tits.FirstParabolicCoordinates
variable {H K : Type*} [Group H] [Group K]

theorem WeylRelations.map {s : Fin 8 → H} {r : H} (h : WeylRelations s r) (f : H →* K) :
    WeylRelations (fun i => f (s i)) (f r) := by
  constructor
  · simpa only [map_pow, map_one] using congrArg f h.square
  · simpa only [map_mul, map_pow, map_one] using congrArg f h.five
  · simpa only [map_mul] using congrArg f h.s2
  · simpa only [map_mul] using congrArg f h.s4
  · simpa only [map_mul, map_pow] using congrArg f h.s5
  · simpa only [map_mul, map_pow, FirstParabolicCoordinates.r7, FirstParabolicCoordinates.r3] using congrArg f h.s3
  · simpa only [map_mul, map_pow, FirstParabolicCoordinates.r7, FirstParabolicCoordinates.r3] using congrArg f h.r3

/-- Scalar relations reflect along an injective homomorphism. -/
theorem SylowRelations.of_injective {s : Fin 8 → H} (f : H →* K)
    (hf : Function.Injective f) (h : SylowRelations (fun i => f (s i))) :
    SylowRelations s := by
  constructor
  · apply hf
    simpa only [map_mul, map_inv, map_pow, map_one, parrottCommutator,
      FirstParabolicCoordinates.r3, r5, r7] using h.s1_sq
  · apply hf
    simpa only [map_mul, map_inv, map_pow, map_one, parrottCommutator,
      FirstParabolicCoordinates.r3, r5, r7] using h.s2_sq
  · apply hf
    simpa only [map_mul, map_inv, map_pow, map_one, parrottCommutator,
      FirstParabolicCoordinates.r3, r5, r7] using h.s4_sq
  · apply hf
    simpa only [map_mul, map_inv, map_pow, map_one, parrottCommutator,
      FirstParabolicCoordinates.r3, r5, r7] using h.s6_sq
  · apply hf
    simpa only [map_mul, map_inv, map_pow, map_one, parrottCommutator,
      FirstParabolicCoordinates.r3, r5, r7] using h.s8_sq
  · apply hf
    simpa only [map_mul, map_inv, map_pow, map_one, parrottCommutator,
      FirstParabolicCoordinates.r3, r5, r7] using h.s3_four
  · apply hf
    simpa only [map_mul, map_inv, map_pow, map_one, parrottCommutator,
      FirstParabolicCoordinates.r3, r5, r7] using h.s5_four
  · apply hf
    simpa only [map_mul, map_inv, map_pow, map_one, parrottCommutator,
      FirstParabolicCoordinates.r3, r5, r7] using h.s7_four
  · apply hf
    simpa only [map_mul, map_inv, map_pow, map_one, parrottCommutator,
      FirstParabolicCoordinates.r3, r5, r7] using h.s1_s2
  · apply hf
    simpa only [map_mul, map_inv, map_pow, map_one, parrottCommutator,
      FirstParabolicCoordinates.r3, r5, r7] using h.s1_s3
  · apply hf
    simpa only [map_mul, map_inv, map_pow, map_one, parrottCommutator,
      FirstParabolicCoordinates.r3, r5, r7] using h.s1_s5
  · apply hf
    simpa only [map_mul, map_inv, map_pow, map_one, parrottCommutator,
      FirstParabolicCoordinates.r3, r5, r7] using h.s1_s6
  · apply hf
    simpa only [map_mul, map_inv, map_pow, map_one, parrottCommutator,
      FirstParabolicCoordinates.r3, r5, r7] using h.s1_s7
  · apply hf
    simpa only [map_mul, map_inv, map_pow, map_one, parrottCommutator,
      FirstParabolicCoordinates.r3, r5, r7] using h.s1_s8
  · apply hf
    simpa only [map_mul, map_inv, map_pow, map_one, parrottCommutator,
      FirstParabolicCoordinates.r3, r5, r7] using h.s2_s4
  · apply hf
    simpa only [map_mul, map_inv, map_pow, map_one, parrottCommutator,
      FirstParabolicCoordinates.r3, r5, r7] using h.s2_s6
  · apply hf
    simpa only [map_mul, map_inv, map_pow, map_one, parrottCommutator,
      FirstParabolicCoordinates.r3, r5, r7] using h.s2_s8
  · apply hf
    simpa only [map_mul, map_inv, map_pow, map_one, parrottCommutator,
      FirstParabolicCoordinates.r3, r5, r7] using h.s7_s2
  · apply hf
    simpa only [map_mul, map_inv, map_pow, map_one, parrottCommutator,
      FirstParabolicCoordinates.r3, r5, r7] using h.s7_s4
  · apply hf
    simpa only [map_mul, map_inv, map_pow, map_one, parrottCommutator,
      FirstParabolicCoordinates.r3, r5, r7] using h.s3_s5
  · apply hf
    simpa only [map_mul, map_inv, map_pow, map_one, parrottCommutator,
      FirstParabolicCoordinates.r3, r5, r7] using h.s5_s4

/-- Scalar actor relations reflect along an injective homomorphism. -/
theorem WeylRelations.of_injective {s : Fin 8 → H} {r : H} (f : H →* K)
    (hf : Function.Injective f) (h : WeylRelations (fun i => f (s i)) (f r)) :
    WeylRelations s r := by
  constructor
  · apply hf
    simpa only [map_mul, map_pow, map_one, FirstParabolicCoordinates.r3,
      FirstParabolicCoordinates.r7] using h.square
  · apply hf
    simpa only [map_mul, map_pow, map_one, FirstParabolicCoordinates.r3,
      FirstParabolicCoordinates.r7] using h.five
  · apply hf
    simpa only [map_mul, map_pow, map_one, FirstParabolicCoordinates.r3,
      FirstParabolicCoordinates.r7] using h.s2
  · apply hf
    simpa only [map_mul, map_pow, map_one, FirstParabolicCoordinates.r3,
      FirstParabolicCoordinates.r7] using h.s4
  · apply hf
    simpa only [map_mul, map_pow, map_one, FirstParabolicCoordinates.r3,
      FirstParabolicCoordinates.r7] using h.s5
  · apply hf
    simpa only [map_mul, map_pow, map_one, FirstParabolicCoordinates.r3,
      FirstParabolicCoordinates.r7] using h.s3
  · apply hf
    simpa only [map_mul, map_pow, map_one, FirstParabolicCoordinates.r3,
      FirstParabolicCoordinates.r7] using h.r3

/-- Lift ambient generating words to their actual subgroup. -/
@[expose] noncomputable def SylowCoordinates.ofAmbient (S : Subgroup H) (s : Fin 8 → H)
    (hs : SylowRelations s) (hgen : closure (Set.range s) = S) : SylowCoordinates S where
  s i := ⟨s i, hgen ▸ subset_closure ⟨i, rfl⟩⟩
  relations := hs.of_injective S.subtype S.subtype_injective
  generates := by
    apply Subgroup.map_injective S.subtype_injective
    rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, range_subtype]
    simpa only [← Set.range_comp, Function.comp_def, Subgroup.subtype_apply] using hgen

@[simp] theorem SylowCoordinates.coe_ofAmbient (S : Subgroup H) (s : Fin 8 → H)
    (hs : SylowRelations s) (hgen : closure (Set.range s) = S) (i : Fin 8) :
    ((SylowCoordinates.ofAmbient S s hs hgen).s i : H) = s i := rfl

/-- Transport the whole frame along an automorphism which sends one actual
subgroup to another. -/
noncomputable def SylowCoordinates.map {S : Subgroup H} (d : SylowCoordinates S)
    (f : H ≃* K) : SylowCoordinates (S.map f.toMonoidHom) where
  s i := equivMapOfInjective S f.toMonoidHom f.injective (d.s i)
  relations := d.relations.map (equivMapOfInjective S f.toMonoidHom f.injective).toMonoidHom
  generates := by
    have hh := congrArg (Subgroup.map (equivMapOfInjective S f.toMonoidHom f.injective).toMonoidHom) d.generates
    rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.mpr (equivMapOfInjective S f.toMonoidHom f.injective).surjective] at hh
    simpa only [← Set.range_comp, Function.comp_def, MulEquiv.coe_toMonoidHom] using hh

noncomputable def WeylExtension.map {S : Subgroup H} {d : SylowCoordinates S}
    (r : WeylExtension d) (f : H ≃* K) : WeylExtension (d.map f) where
  element := f r.element
  outside := by
    intro hh
    obtain ⟨a, ha, he⟩ := hh
    exact r.outside (f.injective he ▸ ha)
  relations := r.relations.map f.toMonoidHom

/-- All Sylow subgroups admit a frame with an actor once any one does.
This transports a constructed frame; it does not assert that arbitrary
prescribed coordinates extend unchanged. -/
theorem exists_weylExtension_of_sylow_conjugacy
    {p : ℕ} [Fact p.Prime] [Finite H] {P : Sylow p H} (S : Sylow p H)
    (d : SylowCoordinates (P : Subgroup H)) (r : WeylExtension d) :
    ∃ d' : SylowCoordinates (S : Subgroup H), Nonempty (WeylExtension d') := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H P S
  have he : (P : Subgroup H).map (MulAut.conj g).toMonoidHom = (S : Subgroup H) :=
    congrArg (fun Q : Sylow p H => (Q : Subgroup H)) hg
  rw [← he]
  exact ⟨d.map (MulAut.conj g), ⟨r.map (MulAut.conj g)⟩⟩

end Tits.FirstParabolicCoordinates
