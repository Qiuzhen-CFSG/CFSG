module

public import Theory.AtlasPort.LinearGroups.G2.TernaryLocals

/-!
# Common eigenvectors of the specified ternary elementary eight

The two torus involutions act by diagonal signs, and the specified longest
Weyl element reverses the eight coordinates. Their common eigenvectors with
nonzero norm lie on the four opposite-coordinate pairs. For either nonzero
norm there are at most eight vectors.

This calculation concerns the actual `TernaryLocals.elementary`. It is used
to audit whether its normalizer is the local group described in
Aschbacher–Smith, *The Classification of Quasithin Groups*, §I.4(G2),
printed p.417. The octonion coordinates are those of the licensed ATLAS port;
see `LICENSES/ATLAS.txt` and `LICENSES/ATLAS-CITATION.cff`.
-/

@[expose] public section

namespace CFSG.Quasithin.MainConverse.ExceptionalLocal.TernaryCover

open Atlas.SplitOctonion

abbrev Space := Carrier (ZMod 3)

/-- The possible signed vectors on the four opposite-coordinate pairs. -/
def eigenvectorChoices (t : ZMod 3) : Finset Space :=
  Finset.univ.image (fun p : Fin 4 × Bool =>
    (if p.2 then (-1 : ZMod 3) else 1) •
      (basisVector p.1.castSucc.castSucc.castSucc.castSucc +
        t • basisVector (7 - p.1.castSucc.castSucc.castSucc.castSucc)))

def firstSign (v : Space) : Space :=
  ![-v 0, v 1, -v 2, v 3, v 4, -v 5, v 6, -v 7]

def secondSign (v : Space) : Space :=
  ![v 0, -v 1, -v 2, v 3, v 4, -v 5, -v 6, v 7]

def reverseCoordinates (v : Space) : Space :=
  ![v 7, v 6, v 5, v 4, v 3, v 2, v 1, v 0]

/-- Being an eigenvector with eigenvalue either one or minus one. -/
def IsSignEigenvector (f : Space → Space) (v : Space) : Prop :=
  f v = v ∨ f v = -v

instance (f : Space → Space) (v : Space) : Decidable (IsSignEigenvector f v) :=
  inferInstanceAs (Decidable (_ ∨ _))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- Exhaustive coordinate calculation, checked by kernel reduction. -/
theorem mem_eigenvectorChoices (v : Space)
    (h₀ : IsSignEigenvector firstSign v)
    (h₁ : IsSignEigenvector secondSign v)
    (h₂ : IsSignEigenvector reverseCoordinates v) (hn : norm v ≠ 0) :
    v ∈ eigenvectorChoices (norm v) := by
  exact (by decide +kernel : ∀ v : Space,
    IsSignEigenvector firstSign v → IsSignEigenvector secondSign v →
    IsSignEigenvector reverseCoordinates v → norm v ≠ 0 →
    v ∈ eigenvectorChoices (norm v)) v h₀ h₁ h₂ hn

theorem card_eigenvectorChoices_le (t : ZMod 3) :
    (eigenvectorChoices t).card ≤ 8 := by
  exact Finset.card_image_le.trans (by decide)

end CFSG.Quasithin.MainConverse.ExceptionalLocal.TernaryCover
