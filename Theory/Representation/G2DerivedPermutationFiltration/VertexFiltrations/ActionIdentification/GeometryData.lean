module

public import Theory.Representation.G2DerivedPermutationFiltration.VertexFiltrations.Generators
/-!
# Geometric certificates for the two binary G₂ parabolic actions

The images of a fixed three-point line and a fixed point separate the 63
published coset representatives. Their known coset counts give coverage;
finite action checks then identify both literal generator tables.
This supports Aschbacher–Smith G.7.2(3), printed p.348.
The byte tables below are evaluated from the root words in Coordinates;
their use is certified by kernel reduction, not by the generating script.
-/

@[expose] public section

open Atlas.G2 Atlas.SplitOctonion
open scoped Pointwise
namespace G2DerivedPermutationFiltration.VertexCoordinates.ActionGeometry
set_option maxRecDepth 10000

def decode (n : Fin 256) : Carrier (ZMod 2) :=
  fun i => if n.val.testBit i.val then 1 else 0

def imageTable : Fin 2 → Fin 63 → Finset (Fin 256) :=
  ![![{1, 2, 3}, {65, 130, 195}, {2, 33, 35}, {97, 130, 227}, {34, 153, 187}, {123, 162, 217}, {34, 155, 185}, {91, 162, 249}, {5, 90, 95}, {69, 159, 218}, {90, 165, 255}, {63, 218, 229}, {122, 167, 221}, {103, 157, 250}, {7, 122, 125}, {61, 199, 250}, {1, 6, 7}, {65, 134, 199}, {6, 97, 103}, {33, 134, 167}, {102, 153, 255}, {63, 217, 230}, {102, 159, 249}, {95, 185, 230}, {5, 91, 94}, {69, 155, 222}, {94, 187, 229}, {123, 165, 222}, {62, 221, 227}, {35, 157, 190}, {3, 61, 62}, {125, 190, 195}, {1, 4, 5}, {33, 132, 165}, {4, 65, 69}, {97, 132, 229}, {68, 153, 221}, {125, 185, 196}, {68, 157, 217}, {61, 196, 249}, {3, 60, 63}, {35, 159, 188}, {60, 195, 255}, {95, 188, 227}, {124, 187, 199}, {103, 155, 252}, {7, 123, 124}, {91, 167, 252}, {2, 32, 34}, {6, 96, 102}, {32, 130, 162}, {96, 134, 230}, {90, 160, 250}, {94, 190, 224}, {122, 160, 218}, {62, 222, 224}, {4, 64, 68}, {64, 132, 196}, {60, 192, 252}, {124, 188, 192}, {32, 128, 160}, {96, 128, 224}, {64, 128, 192}], ![{1}, {33}, {65}, {153}, {3}, {5}, {4}, {2}, {97}, {185}, {35}, {165}, {132}, {130}, {6}, {217}, {195}, {69}, {155}, {157}, {60}, {90}, {187}, {95}, {68}, {34}, {221}, {63}, {64}, {32}, {249}, {227}, {229}, {134}, {61}, {188}, {218}, {62}, {255}, {196}, {162}, {7}, {125}, {159}, {102}, {96}, {94}, {91}, {123}, {199}, {124}, {122}, {167}, {103}, {252}, {250}, {192}, {160}, {128}, {190}, {222}, {230}, {224}]]

def base (i : Fin 2) : Finset (Carrier (ZMod 2)) :=
  (if i = 0 then ({1,2,3} : Finset (Fin 256)) else {1}).image decode

def image (i : Fin 2) (x : Fin 63) : Finset (Carrier (ZMod 2)) :=
  (imageTable i x).image decode

set_option maxHeartbeats 4000000 in
theorem representative_images : ∀ (i : Fin 2) (x : Fin 63),
    (evalWord (representativeWord i x))⁻¹ • base i = image i x := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem image_injective : ∀ (i : Fin 2), Function.Injective (image i) := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem generator_images : ∀ (i j : Fin 2) (x : Fin 63),
    ambientGenerator j • image i x = image i (generator i j x) := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem root_fixes_base : ∀ (i : Fin 2) (j : Fin 8),
    (j.val < 6 ∨ j = (if i = 0 then 7 else 6)) → rootGenerator j • base i = base i := by
  decide +kernel

end G2DerivedPermutationFiltration.VertexCoordinates.ActionGeometry
