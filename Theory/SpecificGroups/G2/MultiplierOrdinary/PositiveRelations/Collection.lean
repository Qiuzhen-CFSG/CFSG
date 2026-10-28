module
public import Theory.SpecificGroups.G2.MultiplierOrdinary.UnipotentSection
/-!
# Collection of the six positive G₂ roots

Ten commuting relations and five polynomial interchange formulas imply the
entire six-parameter multiplication law. The proof collects an ordered product
using adjacent interchanges, and then verifies the resulting field polynomials.
No compatibility of lifts is inferred from their individual additivity.

The root order and signs are those of the attributed ATLAS octonion model in
`Unipotent`. This is the collection step in the defining-prime calculation for
Aschbacher–Smith I.1.3–I.1.4 (PDF pp.418–419), referring to GLS III §6.1.
The relations in a central cover must still be proved separately.
-/

@[expose] public section
namespace Atlas.G2.MultiplierOrdinary.RootSections
variable {F E : Type*} [Field F] [Group E] {f : E →* Model F}

abbrev x (L : RootSections f) (i : Fin 6) (t : F) : E := L.root i (.ofAdd t)

@[simp] theorem x_zero (L : RootSections f) (i : Fin 6) : L.x i 0 = 1 :=
  (L.root i).map_one

theorem x_add (L : RootSections f) (i : Fin 6) (s t : F) :
    L.x i (s + t) = L.x i s * L.x i t := (L.root i).map_mul _ _

/-- The ten pairs whose sums are not roots in this ordering. -/
structure CommutingRelations (L : RootSections f) : Prop where
  ba : ∀ b a, L.x 1 b * L.x 0 a = L.x 0 a * L.x 1 b
  ca : ∀ c a, L.x 2 c * L.x 0 a = L.x 0 a * L.x 2 c
  cb : ∀ c b, L.x 2 c * L.x 1 b = L.x 1 b * L.x 2 c
  da : ∀ d a, L.x 3 d * L.x 0 a = L.x 0 a * L.x 3 d
  db : ∀ d b, L.x 3 d * L.x 1 b = L.x 1 b * L.x 3 d
  ea : ∀ e a, L.x 4 e * L.x 0 a = L.x 0 a * L.x 4 e
  ec : ∀ e c, L.x 4 e * L.x 2 c = L.x 2 c * L.x 4 e
  ed : ∀ e d, L.x 4 e * L.x 3 d = L.x 3 d * L.x 4 e
  fa : ∀ z a, L.x 5 z * L.x 0 a = L.x 0 a * L.x 5 z
  fb : ∀ z b, L.x 5 z * L.x 1 b = L.x 1 b * L.x 5 z

/-- The five noncommuting pairs, with the coefficients of the literal
A–F octonion root maps. -/
structure PolynomialRelations (L : RootSections f) : Prop where
  dc : ∀ d c, L.x 3 d * L.x 2 c = L.x 0 (3*c*d) * L.x 2 c * L.x 3 d
  eb : ∀ e b, L.x 4 e * L.x 1 b = L.x 0 (-b*e) * L.x 1 b * L.x 4 e
  fc : ∀ z c, L.x 5 z * L.x 2 c = L.x 1 (-3*c*z) * L.x 2 c * L.x 5 z
  fd : ∀ z d, L.x 5 z * L.x 3 d =
    L.x 0 (-3*d^2*z) * L.x 1 (3*d*z^2) * L.x 2 (-2*d*z) * L.x 3 d * L.x 5 z
  fe : ∀ z e, L.x 5 z * L.x 4 e =
    L.x 0 (-e^2*z^3) * L.x 1 (-e*z^3) * L.x 2 (e*z^2) * L.x 3 (-e*z) *
      L.x 4 e * L.x 5 z

/-- Pairwise relations sufficient for collection in A–F order. -/
structure CollectionRelations (L : RootSections f) : Prop
    extends L.CommutingRelations, L.PolynomialRelations

private theorem append_relation {a b c : E} (h : a * b = c) (z : E) :
    a * (b * z) = c * z := by rw [← mul_assoc, h]

private theorem collect_same (L : RootSections f) (i : Fin 6) (s t : F) (z : E) :
    L.x i s * (L.x i t * z) = L.x i (s + t) * z := by
  rw [← mul_assoc, ← x_add]

theorem CollectionRelations.productCompatible (L : RootSections f)
    (R : L.CollectionRelations) : L.ProductCompatible := by
  intro t u
  change L.x 0 (t 0) * L.x 1 (t 1) * L.x 2 (t 2) * L.x 3 (t 3) *
    L.x 4 (t 4) * L.x 5 (t 5) *
    (L.x 0 (u 0) * L.x 1 (u 1) * L.x 2 (u 2) * L.x 3 (u 3) *
      L.x 4 (u 4) * L.x 5 (u 5)) = _
  simp only [mul_assoc, append_relation (R.ba _ _), append_relation (R.ca _ _),
    append_relation (R.cb _ _), append_relation (R.da _ _), append_relation (R.db _ _),
    append_relation (R.dc _ _), append_relation (R.ea _ _), append_relation (R.eb _ _),
    append_relation (R.ec _ _), append_relation (R.ed _ _), append_relation (R.fa _ _),
    append_relation (R.fb _ _), append_relation (R.fc _ _), append_relation (R.fd _ _),
    append_relation (R.fe _ _), collect_same, ← x_add]
  simp only [product, mul_assoc]
  change _ = L.x 0 (unipotentProductParameters t u 0) *
    (L.x 1 (unipotentProductParameters t u 1) *
      (L.x 2 (unipotentProductParameters t u 2) *
        (L.x 3 (unipotentProductParameters t u 3) *
          (L.x 4 (unipotentProductParameters t u 4) *
            L.x 5 (unipotentProductParameters t u 5)))))
  repeat' first
    | apply congrArg₂ (fun a b : E => a * b)
    | apply congrArg (L.x _)
  all_goals dsimp [unipotentProductParameters]
  all_goals ring
end Atlas.G2.MultiplierOrdinary.RootSections
end
