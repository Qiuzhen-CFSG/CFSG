module
public import Theory.SpecificGroups.G2.RootPresentationRecognition.Positive

/-!
# The characteristic-two G₂ Borel–Weyl equations

This interface lists the equations on six additive positive roots, the full
split torus and the two Weyl elements. The reflections `r` and `s` are long
and short, respectively. The simple positive roots are E and F.

These are proposed presentation data for the G₂ row of DGS, Groups and
Graphs, Theorem D, p.224. The record states equations, not faithfulness or
recognition; those require the internal finite Bruhat collection argument.
The A–F convention is that of the licensed ATLAS octonion model.
-/

@[expose] public section
namespace Atlas.G2.RootPresentationRecognition
variable (F G : Type*) [Field F] [Group G]

/-- The root, torus and Weyl maps, all in the same group. -/
structure BorelWeylData extends PositiveRoots F G where
  torus : Fˣ × Fˣ →* G
  r : G
  s : G

namespace BorelWeylData
variable {F G}

/-- The weights in literal A–F order. -/
def weight (l m : Fˣ) : Fin 6 → F :=
  ![(l:F)*(m:F), (l:F)^2/(m:F), (l:F), (m:F), (m:F)^2/(l:F), (l:F)/(m:F)]

/-- Explicit finite families of equations; no ambient identification is an input. -/
structure Relations (d : BorelWeylData F G) : Prop
    extends d.toPositiveRoots.CharTwoRelations where
  torus_root : ∀ l m i a,
    d.torus (l,m) * d.x i a * (d.torus (l,m))⁻¹ = d.x i (weight l m i * a)
  r_sq : d.r ^ 2 = 1
  s_sq : d.s ^ 2 = 1
  braid : (d.r * d.s) ^ 6 = 1
  r_torus : ∀ l m, d.r * d.torus (l,m) * d.r⁻¹ = d.torus (l,l/m)
  s_torus : ∀ l m, d.s * d.torus (l,m) * d.s⁻¹ = d.torus (m,l)
  rA : ∀ a, d.r * d.x 0 a * d.r⁻¹ = d.x 1 a
  rB : ∀ a, d.r * d.x 1 a * d.r⁻¹ = d.x 0 a
  rC : ∀ a, d.r * d.x 2 a * d.r⁻¹ = d.x 2 a
  rD : ∀ a, d.r * d.x 3 a * d.r⁻¹ = d.x 5 a
  rF : ∀ a, d.r * d.x 5 a * d.r⁻¹ = d.x 3 a
  sA : ∀ a, d.s * d.x 0 a * d.s⁻¹ = d.x 0 a
  sB : ∀ a, d.s * d.x 1 a * d.s⁻¹ = d.x 4 a
  sC : ∀ a, d.s * d.x 2 a * d.s⁻¹ = d.x 3 a
  sD : ∀ a, d.s * d.x 3 a * d.s⁻¹ = d.x 2 a
  sE : ∀ a, d.s * d.x 4 a * d.s⁻¹ = d.x 1 a
  long_word : ∀ a : Fˣ,
    d.x 4 (a:F) * (d.r * d.x 4 (↑a⁻¹:F) * d.r⁻¹) * d.x 4 (a:F) =
      d.torus (1,a) * d.r
  short_word : ∀ a : Fˣ,
    d.x 5 (a:F) * (d.s * d.x 5 (↑a⁻¹:F) * d.s⁻¹) * d.x 5 (a:F) =
      d.torus (a,a⁻¹) * d.s

end BorelWeylData
end Atlas.G2.RootPresentationRecognition
