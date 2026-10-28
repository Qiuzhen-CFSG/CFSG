module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Endpoint.Recognition.Cyclic.OrbitValues.Geometry
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Endpoint.Recognition.Cyclic.OrbitValues.Stabilizer

/-!
# Additive equivariant flag values from an endpoint highest vector

Choose a translate of the highest-root flag for each incident flag. Its
value is the corresponding translate of the supplied highest vector.
The proved stabilizer fixedness makes this independent of the choice and
hence equivariant. Every additive triple is a translate of an endpoint
relation, which proves additivity. No dimension, faithfulness, irreducibility,
or nonzero hypothesis is required for this construction.

Source: Aschbacher–Smith, K.3.2, printed pp.451,454–455;
Guralnick–Malle, Classification of 2F-modules II, author manuscript,
Lemma 4.5 step 2 and Proposition 4.8 step 3A. The separate consumer descends
these values to the trace kernel once its relation presentation is complete.
-/

set_option backward.isDefEq.respectTransparency false
public section
open Representation
open CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FourSmallModules
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Endpoint.Cyclic

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
variable {σ : Representation (ZMod 2) Group V} {v : V}

private noncomputable def representative (a : Flag) : Group :=
  (exists_translate_seed a).choose
private theorem representative_spec (a : Flag) : translate (representative a) seed = a :=
  (exists_translate_seed a).choose_spec

private noncomputable def orbitValues (σ : Representation (ZMod 2) Group V) (v : V) (a : Flag) : V :=
  σ (representative a) v

private theorem orbitValues_eq (h : LocalHighestVector σ {0,2} v)
    (g : Group) (a : Flag) (hg : translate g seed = a) : orbitValues σ v a = σ g v := by
  have hf : translate ((representative a)⁻¹ * g) seed = seed := by
    calc
      translate ((representative a)⁻¹ * g) seed =
          translate (representative a)⁻¹ (translate g seed) := translate_mul _ _ _
      _ = translate (representative a)⁻¹ a := congrArg _ hg
      _ = translate (representative a)⁻¹ (translate (representative a) seed) :=
        congrArg _ (representative_spec a).symm
      _ = seed := by rw [← translate_mul, inv_mul_cancel, translate_one]
  have hv := localHighest_stabilizer_fixed h _ hf
  calc
    orbitValues σ v a = σ (representative a) v := rfl
    _ = σ (representative a) (σ ((representative a)⁻¹ * g) v) := congrArg _ hv.symm
    _ = σ g v := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]

private theorem orbitValues_equivariant (h : LocalHighestVector σ {0,2} v) (g : Group) (a : Flag) :
    orbitValues σ v (translate g a) = σ g (orbitValues σ v a) := by
  rw [orbitValues_eq h (g * representative a) _ (by rw [translate_mul, representative_spec])]
  rw [map_mul]
  rfl

private theorem orbitValues_seed (h : LocalHighestVector σ {0,2} v) : orbitValues σ v seed = v := by
  rw [orbitValues_eq h 1 seed (translate_one seed), map_one]
  rfl

private theorem binary_add_self (x : V) : x + x = 0 := by
  have he : (1 : ZMod 2) + 1 = 0 := by decide
  simpa only [add_smul, one_smul, zero_smul] using congrArg (fun c : ZMod 2 => c • x) he

private theorem orbitValues_add_seed (h : LocalHighestVector σ {0,2} v)
    {b c : Flag} (hab : AdditiveTriple seed b c) :
    orbitValues σ v seed + orbitValues σ v b = orbitValues σ v c := by
  obtain ⟨g,i,hi,hg,hb,hc⟩ := seed_additiveTriple_orbit hab
  have ha : v + σ (simpleSwap i) v = σ (simpleLower i) v := by
    have hr := congrArg (fun x => x + σ (simpleLower i) v) (h.active_relation i hi)
    simpa only [add_assoc, binary_add_self, add_zero, zero_add] using hr
  have hv := localHighest_stabilizer_fixed h g hg
  rw [← hb, ← hc, orbitValues_equivariant h, orbitValues_equivariant h,
    orbitValues_equivariant h, orbitValues_equivariant h, orbitValues_seed h]
  calc
    v + σ g (σ (simpleSwap i) v) = σ g v + σ g (σ (simpleSwap i) v) :=
      congrArg (fun z => z + σ g (σ (simpleSwap i) v)) hv.symm
    _ = σ g (v + σ (simpleSwap i) v) := (map_add _ _ _).symm
    _ = σ g (σ (simpleLower i) v) := congrArg (σ g) ha

/-- The endpoint highest-vector relations define additive, equivariant values
on all incident flags, normalized at the literal highest-root flag. No
faithfulness, irreducibility, dimension, or nonzero assumption is needed. -/
theorem exists_flag_values_of_localHighest (h : LocalHighestVector σ {0,2} v) :
    ∃ b : Flag → V,
      (∀ a b' c, AdditiveTriple a b' c → b a + b b' = b c) ∧
      (∀ g a, b (translate g a) = σ g (b a)) ∧ b seed = v := by
  refine ⟨orbitValues σ v, ?_, orbitValues_equivariant h, orbitValues_seed h⟩
  intro a b c hab
  obtain ⟨g,hg⟩ := exists_translate_seed a
  have ha : translate g⁻¹ a = seed := by
    rw [← hg, ← translate_mul, inv_mul_cancel, translate_one]
  have ht := additiveTriple_translate g⁻¹ hab
  rw [ha] at ht
  have he := congrArg (σ g) (orbitValues_add_seed h ht)
  rw [map_add, orbitValues_equivariant h, orbitValues_equivariant h] at he
  have hb : σ g (σ g⁻¹ (orbitValues σ v b)) = orbitValues σ v b := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  have hc : σ g (σ g⁻¹ (orbitValues σ v c)) = orbitValues σ v c := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  rw [hb,hc] at he
  rw [← orbitValues_equivariant h, hg] at he
  exact he

end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Endpoint.Cyclic
