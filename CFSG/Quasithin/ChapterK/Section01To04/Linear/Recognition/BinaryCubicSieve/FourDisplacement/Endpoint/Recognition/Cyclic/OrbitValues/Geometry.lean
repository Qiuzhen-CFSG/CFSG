module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Endpoint.Recognition.Cyclic.Flags
public import Theory.Representation.BinaryNaturalDual.ModelOrbits.Coordinate

/-!
# Orbits of endpoint flags and their additive triples

Nonzero incident point–covector pairs form one orbit under the original
binary SL₄ action. At the seed, fixing either coordinate leaves six possible
second flags in a nondegenerate additive triple. Explicit shears and the
middle exchange carry these to the two endpoint-root configurations.
The small coordinate checks use kernel reduction over three binary scalars;
there is no enumeration of SL₄ or assumption of orbit consistency.

Source: Aschbacher–Smith, K.3.2, printed pp.451,454–455;
Guralnick–Malle, Classification of 2F-modules II, author manuscript,
Lemma 4.5 step 2 and Proposition 4.8 step 3A. These orbit calculations
transport the two local endpoint relations to all flag relations.
-/

public section
open Representation
open BinaryLinear.OuterCyclic
open CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FourSmallModules
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Endpoint.Cyclic
set_option backward.isDefEq.respectTransparency false
private theorem dualTranslate_eq (g : Group) (y z : Natural)
    (h : (form z).comp (natural g) = form y) : dualTranslate g y = z := by
  apply (dotProductEquiv (ZMod 2) (Fin 4)).injective
  change form (dualTranslate g y) = form z
  rw [form_dualTranslate, ← h]
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply]
  have hi : natural g (natural g⁻¹ x) = x := by
    change (natural g * natural g⁻¹) x = x
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl
  rw [hi]

private theorem dualTranslate_add (g : Group) (y z : Natural) :
    dualTranslate g (y+z) = dualTranslate g y + dualTranslate g z := by
  apply (dotProductEquiv (ZMod 2) (Fin 4)).injective
  change form (dualTranslate g (y+z)) = form (dualTranslate g y + dualTranslate g z)
  simp only [form_dualTranslate, form_add, LinearMap.add_comp]

/-- The literal flag action preserves both kinds of elementary addition. -/
theorem additiveTriple_translate (g : Group) {a b c : Flag} (h : AdditiveTriple a b c) :
    AdditiveTriple (translate g a) (translate g b) (translate g c) := by
  rcases h with ⟨hb,hc,hd⟩ | ⟨hb,hc,hd⟩
  · exact Or.inl ⟨by simp [hb], by simp [hc], by simp [hd]⟩
  · exact Or.inr ⟨by simp [hb], by simp [hc], by simp [hd, dualTranslate_add]⟩

private abbrev e (i : Fin 4) : Natural := Pi.single i 1
private def pointMover (a b c : ZMod 2) : Group :=
  if b = 0 then
    Matrix.SpecialLinearGroup.transvection (i := 0) (j := 2) (by decide) a * simpleSwap 1
  else Matrix.SpecialLinearGroup.transvection (i := 0) (j := 1) (by decide) a *
    (if c = 0 then 1 else simpleLower 1)
private def covectorMover (a b c : ZMod 2) : Group :=
  if b = 0 then
    Matrix.SpecialLinearGroup.transvection (i := 1) (j := 3) (by decide) c * simpleSwap 1
  else Matrix.SpecialLinearGroup.transvection (i := 2) (j := 3) (by decide) c *
    (if a = 0 then 1 else simpleLower 1)

private theorem pointMover_checks : ∀ a b c : ZMod 2, b ≠ 0 ∨ c ≠ 0 →
    natural (pointMover a b c) (e 0) = e 0 ∧
    (∀ k : Fin 4, natural (pointMover a b c) (e k) 3 = e k 3) ∧
    natural (pointMover a b c) (e 1) = ![a,b,c,0] := by decide

private theorem covectorMover_checks : ∀ a b c : ZMod 2, a ≠ 0 ∨ b ≠ 0 →
    natural (covectorMover a b c) (e 0) = e 0 ∧
    (∀ k : Fin 4, natural (covectorMover a b c) (e k) 3 = e k 3) ∧
    (∀ k : Fin 4, dotProduct ![0,a,b,c] (natural (covectorMover a b c) (e k)) = e k 2) := by decide

private theorem endpoint_coordinates : ∀ i : Fin 3, i ∈ ({0,2} : Finset (Fin 3)) →
    (natural (simpleSwap i) (e 0) = if i = 0 then e 1 else e 0) ∧
    (∀ k : Fin 4, dotProduct (if i = 0 then e 3 else e 2)
      (natural (simpleSwap i) (e k)) = e k 3) ∧
    (natural (simpleLower i) (e 0) = if i = 0 then e 0 + e 1 else e 0) ∧
    (∀ k : Fin 4, dotProduct (if i = 0 then e 3 else e 3 + e 2)
      (natural (simpleLower i) (e k)) = e k 3) := by decide

private theorem endpoint_flags (i : Fin 3) (hi : i ∈ ({0,2} : Finset (Fin 3))) :
    point (translate (simpleSwap i) seed) = (if i = 0 then e 1 else e 0) ∧
    covector (translate (simpleSwap i) seed) = (if i = 0 then e 3 else e 2) ∧
    point (translate (simpleLower i) seed) = (if i = 0 then e 0 + e 1 else e 0) ∧
    covector (translate (simpleLower i) seed) = (if i = 0 then e 3 else e 3 + e 2) := by
  obtain ⟨hp, hc, hp', hc'⟩ := endpoint_coordinates i hi
  refine ⟨hp, ?_, hp', ?_⟩
  · apply dualTranslate_eq
    apply (Pi.basisFun (ZMod 2) (Fin 4)).ext
    intro k
    simpa only [LinearMap.comp_apply, Pi.basisFun_apply, form_apply,
      show covector seed = e 3 from rfl, single_one_dotProduct]
      using hc k
  · apply dualTranslate_eq
    apply (Pi.basisFun (ZMod 2) (Fin 4)).ext
    intro k
    simpa only [LinearMap.comp_apply, Pi.basisFun_apply, form_apply,
      show covector seed = e 3 from rfl, single_one_dotProduct]
      using hc' k

private theorem fixes_covector (g : Group)
    (h : ∀ k : Fin 4, natural g (e k) 3 = e k 3) : dualTranslate g (e 3) = e 3 := by
  apply dualTranslate_eq
  apply (Pi.basisFun (ZMod 2) (Fin 4)).ext
  intro k
  simpa only [LinearMap.comp_apply, Pi.basisFun_apply, form_apply, single_one_dotProduct]
    using h k

private theorem middle_nonzero_point : ∀ a b c : ZMod 2,
    ![a,b,c,0] ≠ (0 : Natural) → e 0 + ![a,b,c,0] ≠ (0 : Natural) → b ≠ 0 ∨ c ≠ 0 := by decide
private theorem middle_nonzero_covector : ∀ a b c : ZMod 2,
    ![0,a,b,c] ≠ (0 : Natural) → e 3 + ![0,a,b,c] ≠ (0 : Natural) → a ≠ 0 ∨ b ≠ 0 := by decide

private theorem point_triple_orbit (b c : Flag)
    (hb : covector b = covector seed) (hc : covector c = covector seed)
    (hd : point c = point seed + point b) :
    ∃ g : Group, translate g seed = seed ∧
      translate g (translate (simpleSwap 0) seed) = b ∧
      translate g (translate (simpleLower 0) seed) = c := by
  have hx3 : point b 3 = 0 := by
    have hh : dotProduct (covector b) (point b) = 0 := b.property.2.2
    rw [hb] at hh
    simpa only [covector, seed, single_one_dotProduct] using hh
  have hx : point b = ![point b 0, point b 1, point b 2, 0] := by
    ext k
    fin_cases k <;> simp [hx3]
  have hm : point b 1 ≠ 0 ∨ point b 2 ≠ 0 := by
    apply middle_nonzero_point (point b 0) (point b 1) (point b 2)
    · rw [← hx]; exact b.property.1
    · rw [← hx]
      change point seed + point b ≠ 0
      rw [← hd]; exact c.property.1
  let g := pointMover (point b 0) (point b 1) (point b 2)
  obtain ⟨hp, hf, hq⟩ := pointMover_checks (point b 0) (point b 1) (point b 2) hm
  change natural g (e 0) = e 0 at hp
  have hy : dualTranslate g (e 3) = e 3 := fixes_covector g hf
  have hq' : natural g (e 1) = point b := hq.trans hx.symm
  obtain ⟨ps, cs, pl, cl⟩ := endpoint_flags 0 (by decide)
  simp only [ite_true] at ps cs pl cl
  refine ⟨g, Flag.ext hp hy, Flag.ext ?_ ?_, Flag.ext ?_ ?_⟩
  · simpa only [point_translate, ps] using hq'
  · simpa only [covector_translate, cs] using hy.trans hb.symm
  · change natural g (point (translate (simpleLower 0) seed)) = point c
    rw [pl, map_add, hp, hq']
    exact hd.symm
  · simpa only [covector_translate, cl] using hy.trans hc.symm

private theorem covector_triple_orbit (b c : Flag)
    (hb : point b = point seed) (hc : point c = point seed)
    (hd : covector c = covector seed + covector b) :
    ∃ g : Group, translate g seed = seed ∧
      translate g (translate (simpleSwap 2) seed) = b ∧
      translate g (translate (simpleLower 2) seed) = c := by
  have hy0 : covector b 0 = 0 := by
    have hh : dotProduct (covector b) (point b) = 0 := b.property.2.2
    rw [hb] at hh
    simpa only [point, seed, dotProduct_single_one] using hh
  have hy : covector b = ![0, covector b 1, covector b 2, covector b 3] := by
    ext k
    fin_cases k <;> simp [hy0]
  have hm : covector b 1 ≠ 0 ∨ covector b 2 ≠ 0 := by
    apply middle_nonzero_covector (covector b 1) (covector b 2) (covector b 3)
    · rw [← hy]; exact b.property.2.1
    · rw [← hy]
      change covector seed + covector b ≠ 0
      rw [← hd]; exact c.property.2.1
  let g := covectorMover (covector b 1) (covector b 2) (covector b 3)
  obtain ⟨hp, hf, hq⟩ := covectorMover_checks (covector b 1) (covector b 2) (covector b 3) hm
  change natural g (e 0) = e 0 at hp
  have hf' : dualTranslate g (e 3) = e 3 := fixes_covector g hf
  have hq' : dualTranslate g (e 2) = covector b := by
    apply dualTranslate_eq
    apply (Pi.basisFun (ZMod 2) (Fin 4)).ext
    intro k
    simp only [LinearMap.comp_apply, Pi.basisFun_apply, form_apply, single_one_dotProduct]
    rw [hy]
    exact hq k
  obtain ⟨ps, cs, pl, cl⟩ := endpoint_flags 2 (by decide)
  simp only [show (2 : Fin 3) ≠ 0 by decide, ite_false] at ps cs pl cl
  refine ⟨g, Flag.ext hp hf', Flag.ext ?_ ?_, Flag.ext ?_ ?_⟩
  · simpa only [point_translate, ps] using hp.trans hb.symm
  · simpa only [covector_translate, cs] using hq'
  · simpa only [point_translate, pl] using hp.trans hc.symm
  · change dualTranslate g (covector (translate (simpleLower 2) seed)) = covector c
    rw [cl, dualTranslate_add, hf', hq']
    exact hd.symm

/-- Every elementary relation based at the seed is a stabilizer translate
of one of the two active endpoint relations. -/
theorem seed_additiveTriple_orbit {b c : Flag} (h : AdditiveTriple seed b c) :
    ∃ (g : Group) (i : Fin 3), i ∈ ({0,2} : Finset (Fin 3)) ∧ translate g seed = seed ∧
      translate g (translate (simpleSwap i) seed) = b ∧
      translate g (translate (simpleLower i) seed) = c := by
  rcases h with ⟨hb,hc,hd⟩ | ⟨hb,hc,hd⟩
  · obtain ⟨g,hg⟩ := point_triple_orbit b c hb hc hd
    exact ⟨g,0,by decide,hg⟩
  · obtain ⟨g,hg⟩ := covector_triple_orbit b c hb hc hd
    exact ⟨g,2,by decide,hg⟩

/-- Every incident flag is in the orbit of the literal highest-root flag. -/
theorem exists_translate_seed (a : Flag) : ∃ g : Group, translate g seed = a := by
  have hn (y : Natural) (hy : y ≠ 0) : form y ≠ 0 := by
    exact fun hz => hy ((dotProductEquiv (ZMod 2) (Fin 4)).injective (by simpa [form] using hz))
  obtain ⟨g, hg⟩ := BinaryNaturalDual.ModelOrbits.exists_naturalDual_eq
    (v := (point seed, form (covector seed))) (w := (point a, form (covector a)))
    seed.property.1 a.property.1 (hn _ seed.property.2.1) (hn _ a.property.2.1)
    (seed.property.2.2.trans a.property.2.2.symm)
  let s := (slEquivLinear 4).symm g
  have hs : slEquivLinear 4 s = g := (slEquivLinear 4).apply_symm_apply g
  rw [BinaryNaturalDual.naturalDualRepresentation_apply] at hg
  have hp := congrArg Prod.fst hg
  have hc := congrArg Prod.snd hg
  refine ⟨s, Flag.ext ?_ ?_⟩
  · change natural s (point seed) = point a
    rw [show natural s (point seed) = slEquivLinear 4 s (point seed) from rfl, hs]
    exact hp
  · apply (dotProductEquiv (ZMod 2) (Fin 4)).injective
    change form (dualTranslate s (covector seed)) = form (covector a)
    rw [form_dualTranslate]
    have hi : slEquivLinear 4 s⁻¹ = g⁻¹ := by rw [map_inv, hs]
    apply LinearMap.ext
    intro x
    change form (covector seed) (natural s⁻¹ x) = form (covector a) x
    rw [show natural s⁻¹ x = slEquivLinear 4 s⁻¹ x from rfl, hi]
    exact LinearMap.congr_fun hc x
end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Endpoint.Cyclic
