module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.AmbientOrder.FixedAction
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# An explicit binary configuration for the seed fixed-space action

Eleven displayed natural columns are sent through the literal seed displacement,
so their images belong to the actual fixed space without any computational
assumption. `codeLift` maps the binary coordinate space into this fixed space.
The coordinate configuration has 154 displayed entries, paired by addition of
the first coordinate vector. Its marked linear stabilizer is a separate,
concrete finite group: its definition does not mention J₄ membership or order.

These are candidate coordinates, not an assertion that the full centralizer
preserves them or is determined by its restriction to them. Those geometric
claims and the stabilizer count are separate proof obligations.

The witnesses were found using the original LEFT COLUMN matrices from
`Cardinality.LocalOrder.KernelCount.Tables`, with provenance in
`Cardinality.Subgroup`. GLS3 Table 5.3i motivates the expected bound but is not a
proof input. The exterior-contraction experiment is saved in
`Scratch/J4SeedFixedImage`; no rank calculation is asserted by these definitions.
-/

@[expose] public section
namespace Janko4.LocalStructure.MathieuSeedCentralizer.AmbientOrder.FixedImage

/-- Binary coordinates for the proposed small invariant subspace. -/
abbrev CodeModule := Fin 11 → ZMod 2

/-- Decode a binary column using bit i as its i-th entry. -/
def binaryColumn (n r : ℕ) : Fin n → ZMod 2 :=
  fun i => if r.testBit i.val then 1 else 0

/-- Explicit preimages under the literal seed displacement. -/
def codePreimages : Vector ℕ 11 := #v[
  20192266346556179,
  94055395191903769,
  34494871361334874,
  102045897574449200,
  93488469915361737,
  26194215863081203,
  4873638336997352,
  77862136688480499,
  25950082423833031,
  104398961000019981,
  27107521924217799]

/-- These columns are fixed by the seed because its displacement squares to zero. -/
def codeBasis (i : Fin 11) : fixedVectors :=
  ⟨displacement (binaryColumn 112 (codePreimages.get i)),
    displacement_mem_fixedVectors _⟩

/-- The actual linear map from candidate coordinates into the seed fixed space. -/
def codeLift : CodeModule →ₗ[ZMod 2] fixedVectors :=
  Fintype.linearCombination (ZMod 2) codeBasis

theorem codeLift_single (i : Fin 11) : codeLift (Pi.single i 1) = codeBasis i := by
  simp only [codeLift, Fintype.linearCombination_apply_single, one_smul]

/-- Distinguished first coordinate, whose image is the candidate marked line. -/
def codeSeed : CodeModule := Pi.single 0 1

/-- Entries of the candidate configuration, in eleven binary coordinates. -/
def codeMasks : Vector ℕ 154 := #v[
  18, 19, 20, 21, 78, 79, 258, 259, 262, 263, 282,
  283, 298, 299, 300, 301, 302, 303, 346, 347, 374, 375,
  384, 385, 432, 433, 438, 439, 460, 461, 484, 485, 508,
  509, 550, 551, 556, 557, 602, 603, 628, 629, 640, 641,
  748, 749, 786, 787, 790, 791, 796, 797, 802, 803, 818,
  819, 840, 841, 846, 847, 864, 865, 870, 871, 894, 895,
  900, 901, 944, 945, 994, 995, 1000, 1001, 1034, 1035, 1146,
  1147, 1174, 1175, 1176, 1177, 1242, 1243, 1260, 1261, 1284, 1285,
  1310, 1311, 1322, 1323, 1330, 1331, 1350, 1351, 1384, 1385, 1392,
  1393, 1406, 1407, 1412, 1413, 1436, 1437, 1448, 1449, 1488, 1489,
  1492, 1493, 1502, 1503, 1606, 1607, 1630, 1631, 1650, 1651, 1654,
  1655, 1672, 1673, 1756, 1757, 1850, 1851, 1866, 1867, 1868, 1869,
  1910, 1911, 1912, 1913, 1916, 1917, 1936, 1937, 1946, 1947, 1974,
  1975, 1976, 1977, 2016, 2017, 2020, 2021, 2026, 2027, 2028, 2029]

/-- A concrete set of coordinate vectors; no orbit identification is built in. -/
def codePoints : Set CodeModule :=
  Set.range (fun i : Fin 154 => binaryColumn 11 (codeMasks.get i))

abbrev CodeActor := (Module.End (ZMod 2) CodeModule)ˣ

instance codeActorFinite : Finite CodeActor :=
  Finite.of_injective (fun g : CodeActor => (g.val : CodeModule → CodeModule))
    (by intro g h he; exact Units.ext (LinearMap.ext (congrFun he)))

/-- Linear automorphisms fixing the marked vector and permuting the configuration. -/
def codeStabilizer : Subgroup CodeActor where
  carrier := {g | g.val codeSeed = codeSeed ∧
    ∀ v, g.val v ∈ codePoints ↔ v ∈ codePoints}
  one_mem' := ⟨rfl, fun _ => Iff.rfl⟩
  mul_mem' := by
    rintro g h ⟨hgs, hgp⟩ ⟨hhs, hhp⟩
    constructor
    · change g.val (h.val codeSeed) = codeSeed
      rw [hhs, hgs]
    · intro v
      exact (hgp (h.val v)).trans (hhp v)
  inv_mem' := by
    rintro g ⟨hgs, hgp⟩
    have cancel (v : CodeModule) : g.val (g⁻¹.val v) = v := by
      change ((g * g⁻¹).val) v = v
      rw [mul_inv_cancel]
      rfl
    constructor
    · have he := congrArg (fun v => g⁻¹.val v) hgs
      have cancel' : g⁻¹.val (g.val codeSeed) = codeSeed := by
        change ((g⁻¹ * g).val) codeSeed = codeSeed
        rw [inv_mul_cancel]
        rfl
      exact he.symm.trans cancel'
    · intro v
      have he := hgp (g⁻¹.val v)
      rw [cancel] at he
      exact he.symm

end Janko4.LocalStructure.MathieuSeedCentralizer.AmbientOrder.FixedImage
