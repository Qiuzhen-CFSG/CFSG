module

public import Theory.Character.ModularBlock.IdempotentRestriction

/-!
# Left Ideal Restriction

An idempotent in a group algebra which commutes with a subgroup defines a
representation on the image of left multiplication. Its inclusion into the
restricted regular representation has an equivariant retraction given by
left multiplication. The split summand is therefore projective; if the
ambient group is finite, it is also finitely generated.

These exposed image, action, representation, and splitting constructions
supply the exact module API for the subsequent Higman and Nagao range
arguments.

Ported from `public/lean-eval/glauberman_zStar`,
`Submission/ZStar/LeftIdealHigman.lean` (revision `c3503435`).
-/

@[expose] public section

noncomputable section

namespace ModularBlock.LeftIdealHigman

universe u v w

attribute [local instance] Fintype.ofFinite

abbrev leftIdeal
    (R : Type u) {G : Type v} [CommRing R] [Group G]
    (f : MonoidAlgebra R G) : Submodule R (MonoidAlgebra R G) :=
  LinearMap.range (LinearMap.mulLeft R f)

def leftIdealAction
    (R : Type u) {G : Type v} [CommRing R] [Group G]
    (f : MonoidAlgebra R G) {S : Type w} [Group S]
    (phi : S →* G)
    (hcomm : ∀ s : S,
      Commute f (MonoidAlgebra.of R G (phi s)))
    (s : S) :
    leftIdeal R f →ₗ[R] leftIdeal R f :=
  (LinearMap.mulLeft R (MonoidAlgebra.of R G (phi s))).restrict (by
    rintro _ ⟨x, rfl⟩
    refine ⟨MonoidAlgebra.of R G (phi s) * x, ?_⟩
    change f * (MonoidAlgebra.of R G (phi s) * x) =
      MonoidAlgebra.of R G (phi s) * (f * x)
    rw [← mul_assoc, (hcomm s).eq, mul_assoc])

@[simp] theorem leftIdealAction_apply
    {R : Type u} {G : Type v} [CommRing R] [Group G]
    (f : MonoidAlgebra R G) {S : Type w} [Group S]
    (phi : S →* G)
    (hcomm : ∀ s : S,
      Commute f (MonoidAlgebra.of R G (phi s)))
    (s : S) (x : leftIdeal R f) :
    (leftIdealAction R f phi hcomm s x : MonoidAlgebra R G) =
      MonoidAlgebra.of R G (phi s) * (x : MonoidAlgebra R G) :=
  rfl

def leftIdealRepresentation
    (R : Type u) {G : Type v} [CommRing R] [Group G]
    (f : MonoidAlgebra R G) {S : Type w} [Group S]
    (phi : S →* G)
    (hcomm : ∀ s : S,
      Commute f (MonoidAlgebra.of R G (phi s))) :
    Representation R S (leftIdeal R f) where
  toFun := leftIdealAction R f phi hcomm
  map_one' := by
    ext x
    simp [leftIdealAction]
  map_mul' s t := by
    ext x
    simp [leftIdealAction, mul_assoc, map_mul]

/-! The left ideal cut out by an equivariant idempotent is already a split
summand of the restricted regular representation.  This elementary splitting
is useful when the ambient representation is the regular representation: no
relative-trace hypothesis is then needed to obtain projectivity. -/

/-- Inclusion of the equivariant left ideal into the restricted regular
representation. -/
def leftIdealInclusionIntertwiningMap
    (R : Type u) {G : Type v} [CommRing R] [Group G]
    (f : MonoidAlgebra R G) (S : Subgroup G)
    (hcomm : ∀ s : S,
      Commute f (MonoidAlgebra.of R G (S.subtype s))) :
    (leftIdealRepresentation R f S.subtype hcomm).IntertwiningMap
      (CentralIdempotentSupport.restrictedLeftRegularRepresentation R S) where
  toLinearMap := (leftIdeal R f).subtype
  isIntertwining' s := by
    apply LinearMap.ext
    intro x
    exact
      (CentralIdempotentSupport.leftRegular_apply_eq_mul
        (R := R) (G := G) (s : G) (x : MonoidAlgebra R G)).symm

/-- Left multiplication by `f`, with codomain restricted to its range, is
an equivariant projection whenever `f` commutes with the subgroup. -/
def leftIdealProjectionIntertwiningMap
    (R : Type u) {G : Type v} [CommRing R] [Group G]
    (f : MonoidAlgebra R G) (S : Subgroup G)
    (hcomm : ∀ s : S,
      Commute f (MonoidAlgebra.of R G (S.subtype s))) :
    (CentralIdempotentSupport.restrictedLeftRegularRepresentation R S).IntertwiningMap
      (leftIdealRepresentation R f S.subtype hcomm) where
  toLinearMap := (LinearMap.mulLeft R f).codRestrict (leftIdeal R f)
    (fun x ↦ ⟨x, rfl⟩)
  isIntertwining' s := by
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply]
    apply Subtype.ext
    change f * (show MonoidAlgebra R G from
        Representation.leftRegular R G (s : G) x) =
      MonoidAlgebra.of R G (s : G) * (f * x)
    rw [CentralIdempotentSupport.leftRegular_apply_eq_mul]
    have hscomm :
        f * MonoidAlgebra.of R G (s : G) =
          MonoidAlgebra.of R G (s : G) * f := by
      simpa using (hcomm s).eq
    calc
      f * (MonoidAlgebra.of R G (s : G) * x) =
          (f * MonoidAlgebra.of R G (s : G)) * x :=
        (mul_assoc _ _ _).symm
      _ = (MonoidAlgebra.of R G (s : G) * f) * x := by
        rw [hscomm]
      _ = MonoidAlgebra.of R G (s : G) * (f * x) :=
        mul_assoc _ _ _

/-- The inclusion above, regarded as a linear map over the subgroup
algebra. -/
abbrev leftIdealInclusionAsModule
    (R : Type u) {G : Type v} [CommRing R] [Group G]
    (f : MonoidAlgebra R G) (S : Subgroup G)
    (hcomm : ∀ s : S,
      Commute f (MonoidAlgebra.of R G (S.subtype s))) :
    (leftIdealRepresentation R f S.subtype hcomm).asModule
        →ₗ[MonoidAlgebra R S]
      (CentralIdempotentSupport.restrictedLeftRegularRepresentation R S).asModule :=
  (Representation.IntertwiningMap.equivLinearMapAsModule _ _)
    (leftIdealInclusionIntertwiningMap R f S hcomm)

/-- The left-multiplication projection above, regarded as a linear map over
the subgroup algebra. -/
abbrev leftIdealProjectionAsModule
    (R : Type u) {G : Type v} [CommRing R] [Group G]
    (f : MonoidAlgebra R G) (S : Subgroup G)
    (hcomm : ∀ s : S,
      Commute f (MonoidAlgebra.of R G (S.subtype s))) :
    (CentralIdempotentSupport.restrictedLeftRegularRepresentation R S).asModule
        →ₗ[MonoidAlgebra R S]
      (leftIdealRepresentation R f S.subtype hcomm).asModule :=
  (Representation.IntertwiningMap.equivLinearMapAsModule _ _)
    (leftIdealProjectionIntertwiningMap R f S hcomm)

/-- For idempotent `f`, left multiplication splits the inclusion of its
equivariant left ideal over the subgroup algebra. -/
theorem leftIdealProjection_comp_inclusion
    {R : Type u} {G : Type v} [CommRing R] [Group G]
    (f : MonoidAlgebra R G) (hf : IsIdempotentElem f)
    (S : Subgroup G)
    (hcomm : ∀ s : S,
      Commute f (MonoidAlgebra.of R G (S.subtype s))) :
    (leftIdealProjectionAsModule R f S hcomm).comp
        (leftIdealInclusionAsModule R f S hcomm) = LinearMap.id := by
  apply LinearMap.ext
  rintro ⟨x, hx⟩
  apply Subtype.ext
  rcases hx with ⟨y, hy⟩
  change f * x = x
  rw [← hy]
  change f * (f * y) = f * y
  rw [← mul_assoc, hf]

/-- An equivariant idempotent left ideal of the regular representation is
projective after restriction to the subgroup. -/
theorem projective_leftIdealRepresentation_asModule
    {R : Type u} {G : Type v} [CommRing R] [Group G]
    (f : MonoidAlgebra R G) (hf : IsIdempotentElem f)
    (S : Subgroup G)
    (hcomm : ∀ s : S,
      Commute f (MonoidAlgebra.of R G (S.subtype s))) :
    Module.Projective (MonoidAlgebra R S)
      (leftIdealRepresentation R f S.subtype hcomm).asModule := by
  let : Module.Projective (MonoidAlgebra R S)
      (CentralIdempotentSupport.restrictedLeftRegularRepresentation R S).asModule :=
    CentralIdempotentSupport.projective_restrictedLeftRegular_asModule S
  exact Module.Projective.of_split
    (leftIdealInclusionAsModule R f S hcomm)
    (leftIdealProjectionAsModule R f S hcomm)
    (leftIdealProjection_comp_inclusion f hf S hcomm)

/-- For finite ambient `G`, the same equivariant left ideal is finite over
the subgroup algebra. -/
theorem finite_leftIdealRepresentation_asModule
    {R : Type u} {G : Type v} [CommRing R] [Group G] [Finite G]
    (f : MonoidAlgebra R G) (hf : IsIdempotentElem f)
    (S : Subgroup G)
    (hcomm : ∀ s : S,
      Commute f (MonoidAlgebra.of R G (S.subtype s))) :
    Module.Finite (MonoidAlgebra R S)
      (leftIdealRepresentation R f S.subtype hcomm).asModule := by
  let : Module.Finite R
      (CentralIdempotentSupport.restrictedLeftRegularRepresentation R S).asModule :=
    inferInstance
  let : Module.Finite (MonoidAlgebra R S)
      (CentralIdempotentSupport.restrictedLeftRegularRepresentation R S).asModule :=
    Module.Finite.of_restrictScalars_finite R (MonoidAlgebra R S)
      (CentralIdempotentSupport.restrictedLeftRegularRepresentation R S).asModule
  apply Module.Finite.of_surjective (leftIdealProjectionAsModule R f S hcomm)
  intro x
  refine ⟨leftIdealInclusionAsModule R f S hcomm x, ?_⟩
  have hx := LinearMap.congr_fun
    (leftIdealProjection_comp_inclusion f hf S hcomm) x
  simpa [LinearMap.comp_apply] using hx

end ModularBlock.LeftIdealHigman

