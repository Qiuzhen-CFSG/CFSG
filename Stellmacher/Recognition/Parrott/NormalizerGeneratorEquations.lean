module

public import Stellmacher.Recognition.Parrott.NormalizerGeneratorSeedActions
public import Stellmacher.Recognition.Parrott.NormalizerGeneratorCubic

/-!
# Assembly of the remaining normalizer generator equations

The seed action calculation determines the a, b and w equations. Once the
remaining x-branch has been excluded, involutivity gives the c equation.
The cubic calculation then gives equation (26). The conditional assembly retains
the exact supplied seed and every centralizer coordinate. The original assembly
with an explicit cubic premise is retained as well.

The recorded interfaces do not exclude the other x-branch uniformly:
`NormalizerGeneratorBranch` proves a central-coordinate-twist obstruction.
Consequently the selected x-image remains an explicit premise here; removing
it requires an additional normalization of the supplied frame and seed.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
printed p.682, equations (25)–(26).
-/

namespace Stellmacher.Recognition.ParrottNormalizerSeedData
variable {G : Type*} [Group G] {z : G}
variable {e : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData e}
variable {f : ParrottCentralizerGeneratorData n} (k : ParrottNormalizerSeedData f)

/-- Conditional final assembly: only branch exclusion and the cubic relation
remain to be discharged by the actual normalizer argument. -/
public theorem equations_of_x_conj_and_cube
    (hx : k.s⁻¹*f.x*k.s = f.c*f.a*f.w*n.t*z)
    (hcube : (k.s*f.d*n.v*z)^3 = 1) :
    k.s⁻¹*f.w*k.s = f.y*f.a*n.v*z ∧
    k.s⁻¹*f.a*k.s = f.u ∧
    k.s⁻¹*f.b*k.s = f.b*f.a*f.u*n.v*z ∧
    k.s⁻¹*f.c*k.s = f.x*f.y*f.a*f.u*n.v*n.t ∧
    k.s⁻¹*f.x*k.s = f.c*f.a*f.w*n.t*z ∧
    (k.s*f.d*n.v*z)^3 = 1 :=
  ⟨k.w_conj, k.a_conj_eq, k.b_conj, k.c_conj_of_x_conj hx, hx, hcube⟩

/-- Equations (25)–(26) for the exact supplied seed, conditional only on its
selected x-image. The cubic equation follows from the actual normalizer action. -/
public theorem equations_of_x_conj
    (hx : k.s⁻¹*f.x*k.s = f.c*f.a*f.w*n.t*z) :
    k.s⁻¹*f.w*k.s = f.y*f.a*n.v*z ∧
    k.s⁻¹*f.a*k.s = f.u ∧
    k.s⁻¹*f.b*k.s = f.b*f.a*f.u*n.v*z ∧
    k.s⁻¹*f.c*k.s = f.x*f.y*f.a*f.u*n.v*n.t ∧
    k.s⁻¹*f.x*k.s = f.c*f.a*f.w*n.t*z ∧
    (k.s*f.d*n.v*z)^3 = 1 :=
  k.equations_of_x_conj_and_cube hx (k.cube_eq_one_of_x_conj hx)

end Stellmacher.Recognition.ParrottNormalizerSeedData
