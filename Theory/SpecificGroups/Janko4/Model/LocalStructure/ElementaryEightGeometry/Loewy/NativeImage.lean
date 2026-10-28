module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.Loewy.Differential
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.Loewy.SmallImage

/-!
# The native four-coordinate image

This module transports the checked `smallSpan` calculation to the actual
112-dimensional row action. The canonical-layer inputs are supplied by the
final layer assembly: layers three and four are the displayed row spans, and
layer five vanishes. The source and forward certificates identify each native
generator displacement with the corresponding `thirdActions` row.
-/

@[expose] public noncomputable section
namespace Janko4.LocalStructure.ElementaryEightGeometry.Loewy
open Matrix GeneratorCertificates
open scoped Matrix

def maskCoordinates (m : Fin 256) : Four × Four :=
  (fun i => bit m.val i.val, fun i => bit m.val (4 + i.val))

def maskElement (m : Fin 256) : Model :=
  ((eightCoordinates 0 (maskCoordinates m)).toMul : Model)

theorem maskElement_mem (m : Fin 256) : maskElement m ∈ nativeEight 0 :=
  (eightCoordinates 0 (maskCoordinates m)).property

theorem maskElement_coordinates (m : Fin 256) :
    Additive.ofMul ⟨maskElement m, maskElement_mem m⟩ =
      eightCoordinates 0 (maskCoordinates m) := by
  rfl

theorem forward3_thirdActions (i : Fin 32) (j : Fin 8) :
    forward3.get (finProdFinEquiv (i,j)) = (thirdActions.get j).get i := by
  decide +kernel +revert

private theorem mask_displacement_coordinates
    (hzero : layer (nativeEight 0) 5 = ⊥) (m : Fin 256)
    (v : layer (nativeEight 0) 3) :
    displacement (maskElement m) v =
      ∑ j : Fin 8, bit m.val j.val •
        displacement (nativeGenerator j) v := by
  unfold maskElement
  rw [differential_coordinates 3 hzero v]
  rw [Fin.sum_univ_add (a := 4) (b := 4)]
  simp only [maskCoordinates, nativeGenerator,
    Fin.addCases_left, Fin.addCases_right, Fin.val_castAdd, Fin.val_natAdd]

private theorem layer4_pivots :
    ∀ i : Fin 4, ∀ k : Fin 4,
      decode (layer4Rows.get k) ((![18,0,12,16] : Fin 4 → Fin 112) i) =
        if i = k then 1 else 0 := by
  decide +kernel

def layer4Embed : Four →ₗ[ZMod 2] V :=
  Fintype.linearCombination (ZMod 2) (fun i : Fin 4 => decode (layer4Rows.get i))

theorem layer4Embed_apply (a : Four) :
    layer4Embed a = ∑ i : Fin 4, a i • decode (layer4Rows.get i) := by
  rfl

theorem layer4Embed_range : LinearMap.range layer4Embed = rowSpan layer4Rows := by
  rw [layer4Embed, Fintype.range_linearCombination]
  rfl

theorem layer4Embed_injective : Function.Injective layer4Embed := by
  intro a b h
  funext i
  have hi := congrArg (fun v : V => v (((![18,0,12,16] : Fin 4 → Fin 112) i))) h
  simp only [layer4Embed_apply, Finset.sum_apply, Pi.smul_apply, layer4_pivots,
    smul_eq_mul] at hi
  simpa using hi

private theorem mask_displacement_row
    (hthree : layer (nativeEight 0) 3 = rowSpan layer3Rows)
    (hzero : layer (nativeEight 0) 5 = ⊥)
    (hgen : ∀ i : Fin 32, ∀ j : Fin 8,
      displacement (nativeGenerator j) (decode (layer3Rows.get i)) =
        decode (combine layer4Rows ((thirdActions.get j).get i)))
    (m : Fin 256) (i : Fin 32) :
    displacement (maskElement m) (decode (layer3Rows.get i)) =
      layer4Embed (smallDecode ((smallRows m).get i)) := by
  rw [mask_displacement_coordinates hzero m ⟨decode (layer3Rows.get i),
    (by rw [hthree]; exact Submodule.subset_span (Set.mem_range_self i))⟩]
  rw [smallDecode_smallRows, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul, hgen i j, layer4Embed_apply, decode_combine]
  rfl

theorem movedBy_maskElement_eq_map
    (hthree : layer (nativeEight 0) 3 = rowSpan layer3Rows)
    (hzero : layer (nativeEight 0) 5 = ⊥)
    (hgen : ∀ i : Fin 32, ∀ j : Fin 8,
      displacement (nativeGenerator j) (decode (layer3Rows.get i)) =
        decode (combine layer4Rows ((thirdActions.get j).get i)))
    (m : Fin 256) :
    movedBy (nativeEight 0) 3 (maskElement m) =
      (smallSpan m).map layer4Embed := by
  rw [movedBy_rows 3 layer3Rows hthree, smallSpan, Submodule.map_span, ← Set.range_comp]
  apply congrArg (Submodule.span (ZMod 2))
  apply congrArg Set.range
  funext i
  exact mask_displacement_row hthree hzero hgen m i

theorem layer4Embed_map_eq_range_iff (S : Submodule (ZMod 2) Four) :
    S.map layer4Embed = LinearMap.range layer4Embed ↔ S = ⊤ := by
  constructor
  · intro h
    apply top_unique
    intro a ha
    have hmem : layer4Embed a ∈ LinearMap.range layer4Embed := ⟨a,rfl⟩
    rw [← h] at hmem
    obtain ⟨b,hb,hba⟩ := hmem
    exact (layer4Embed_injective hba.symm) ▸ hb
  · intro h
    rw [h, Submodule.map_top]

theorem movedBy_maskElement_eq_layer4_iff
    (hthree : layer (nativeEight 0) 3 = rowSpan layer3Rows)
    (hfour : layer (nativeEight 0) 4 = rowSpan layer4Rows)
    (hzero : layer (nativeEight 0) 5 = ⊥)
    (hgen : ∀ i : Fin 32, ∀ j : Fin 8,
      displacement (nativeGenerator j) (decode (layer3Rows.get i)) =
        decode (combine layer4Rows ((thirdActions.get j).get i)))
    (m : Fin 256) :
    movedBy (nativeEight 0) 3 (maskElement m) = layer (nativeEight 0) 4 ↔
      ¬ isotropicCode m := by
  rw [movedBy_maskElement_eq_map hthree hzero hgen m, hfour, ← layer4Embed_range,
    layer4Embed_map_eq_range_iff, smallSpan_eq_top_iff]

end Janko4.LocalStructure.ElementaryEightGeometry.Loewy
