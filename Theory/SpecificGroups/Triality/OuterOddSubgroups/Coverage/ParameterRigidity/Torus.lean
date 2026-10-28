module

public import Theory.SpecificGroups.Triality.OuterOddSubgroups.Coverage.ParameterRigidity.RankOne
public import Theory.SpecificGroups.Triality.RadicalCoordinates.FullLevi.Normalization

/-!
# All root scalars are realized by the genuine triality torus

For coroot coordinates (u,v), the two simple-root characters are u²/v and
v²/N(u), with the norm in the actual q-Frobenius fixed subfield. Their kernel
is trivial in characteristic two: u²=v forces u to be fixed by Frobenius,
and the second character then forces u⁴=u³. On the finite coordinate group,
injectivity proves surjectivity without excluding q = 2.

The published positive and negative Geck coroot formulas establish these
characters on the literal signed roots. Elementary descent and the actual
central quotient therefore realize every pair of nonzero root scalars by
conjugation with an element of ConcreteBruhat.torus.

Source: GLS3 §§2.4–2.5, especially 2.5.1(b), 2.5.8 and 2.5.12(c)
(`refs/KGroup/GLS3/chapter2.tex`); the diagonal normalization in Steinberg,
Theorem 30(2) and Theorem 36 (`refs/KGroup/GLS3/Chapter2St1.tex`).
-/

@[expose] public section
open Theory.AlgebraicGroup.StandardRootSystem
namespace Triality.Standard.OuterOdd.Coverage.ParameterRigidity
open Parabolics ConcreteBruhat TorusCoordinates ElementaryCentralKernel
noncomputable section

/-- Cubic norm on units, valued in the actual fixed subfield. -/
def normUnit (P : Parameters) : (ExtensionField P)ˣ →* (fixedField P)ˣ where
  toFun t := restrictUnit P (t * frobenius P t * frobenius P (frobenius P t)) (by
    simp only [map_mul, frobenius_three]
    ac_rfl)
  map_one' := by apply Units.ext; apply Subtype.ext; simp [restrictUnit]
  map_mul' t u := by
    apply Units.ext
    apply Subtype.ext
    simp only [restrictUnit, Units.val_mul, map_mul]
    change (t.val * u.val) * (fieldFrobenius P t.val * fieldFrobenius P u.val) *
      (fieldFrobenius P (fieldFrobenius P t.val) * fieldFrobenius P (fieldFrobenius P u.val)) = _
    change _ = (t.val * fieldFrobenius P t.val * fieldFrobenius P (fieldFrobenius P t.val)) *
      (u.val * fieldFrobenius P u.val * fieldFrobenius P (fieldFrobenius P u.val))
    ring

theorem fixedUnit_normUnit (P : Parameters) (t : (ExtensionField P)ˣ) :
    fixedUnit P (normUnit P t) = t * frobenius P t * frobenius P (frobenius P t) := rfl

/-- The two folded simple-root characters of the descended torus. -/
def rootCharacters (P : Parameters) : OrbitParameters P →* OrbitParameters P where
  toFun t := (t.1 ^ 2 / fixedUnit P t.2, t.2 ^ 2 / normUnit P t.1)
  map_one' := by simp
  map_mul' t u := by
    ext <;> simp [mul_pow, map_mul, div_eq_mul_inv] <;> ring

theorem units_square_injective (P : Parameters) (hp : P.prime = 2) :
    Function.Injective (fun u : (ExtensionField P)ˣ => u ^ 2) := by
  let := rankOneExtensionCharTwo P hp
  intro u v h
  apply Units.ext
  exact (frobenius_inj (ExtensionField P) 2) (congrArg Units.val h)

theorem rootCharacters_injective (P : Parameters) (hp : P.prime = 2) :
    Function.Injective (rootCharacters P) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply (Subgroup.eq_bot_iff_forall _).mpr
  rintro ⟨u, v⟩ h
  have h1 : u ^ 2 = fixedUnit P v := div_eq_one.mp (congrArg Prod.fst h)
  have h2 : v ^ 2 = normUnit P u := div_eq_one.mp (congrArg Prod.snd h)
  have hu : frobenius P u = u := by
    apply units_square_injective P hp
    change (frobenius P u) ^ 2 = u ^ 2
    rw [← map_pow, h1, frobenius_fixedUnit]
  have h4 : u ^ 4 = u ^ 3 := by
    calc
      u ^ 4 = (u ^ 2) ^ 2 := by group
      _ = fixedUnit P (v ^ 2) := by rw [h1, map_pow]
      _ = u ^ 3 := by simp only [h2, fixedUnit_normUnit, hu]; simp [pow_succ]
  have hu1 : u = 1 := by
    have he : u ^ 3 * u = u ^ 3 * 1 := by simpa only [mul_one, ← pow_succ] using h4
    exact mul_left_cancel he
  have hv1 : v = 1 := by
    apply Units.ext
    apply Subtype.ext
    have he := congrArg Units.val h1
    simpa [hu1, fixedUnit] using he.symm
  exact Prod.ext hu1 hv1

theorem rootCharacters_surjective (P : Parameters) (hp : P.prime = 2) :
    Function.Surjective (rootCharacters P) :=
  Finite.surjective_of_injective (rootCharacters_injective P hp)

private theorem conjugate_product {G : Type*} [Group G] (g h x : G) :
    (g * h) * x * (g * h)⁻¹ = g * (h * x * h⁻¹) * g⁻¹ := by group

private theorem conjugate_mul {G : Type*} [Group G] (g x y : G) :
    g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group

theorem torusWord_signed (P : Parameters) (hp : P.prime = 2)
    (k : Fin 4) (t : (ExtensionField P)ˣ) (s : Bool) (j : Fin 4) (r : ExtensionField P) :
    torusWord P k t * simpleRoot P s j r * (torusWord P k t)⁻¹ =
      simpleRoot P s j (t.val ^ (if s then typeDCartanMatrix 2 j k else
        -typeDCartanMatrix 2 j k) * r) := by
  cases s
  · exact RadicalCoordinates.torusWord_negativeRoot_conjugate P hp k t j r
  · exact RadicalCoordinates.torusWord_positiveRoot_conjugate_cartan P hp k t j r

def signedScalar {F : Type*} [Field F] (s : Bool) (c : F) : F := if s then c else c⁻¹

def nodeCharacter (P : Parameters) (t : OrbitParameters P) :
    (i : Node) → (RootField P i)ˣ
  | .arms => (rootCharacters P t).1
  | .central => (rootCharacters P t).2


def splitCharacter (P : Parameters) (t : OrbitParameters P) (j : Fin 4) : ExtensionField P :=
  t.1.val ^ (typeDCartanMatrix 2 j 0) *
    (fieldFrobenius P t.1.val) ^ (typeDCartanMatrix 2 j 2) *
    (fieldFrobenius P (fieldFrobenius P t.1.val)) ^ (typeDCartanMatrix 2 j 3) *
    t.2.val.val ^ (typeDCartanMatrix 2 j 1)

private theorem product_simpleRoot (P : Parameters) (hp : P.prime = 2)
    (t : OrbitParameters P) (s : Bool) (j : Fin 4) (r : ExtensionField P) :
    product P (expand P t) * simpleRoot P s j r * (product P (expand P t))⁻¹ =
      simpleRoot P s j (signedScalar s (splitCharacter P t j) * r) := by
  simp only [product, expand, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, conjugate_product, torusWord_signed P hp]
  congr 1
  cases s <;>
    simp [splitCharacter, signedScalar, fixedUnit, TorusCoordinates.frobenius,
      mul_assoc, mul_comm, mul_left_comm]

private theorem splitCharacter_zero (P : Parameters) (t : OrbitParameters P) :
    splitCharacter P t 0 = (nodeCharacter P t .arms).val := by
  simp [splitCharacter, nodeCharacter, rootCharacters, fixedUnit, typeDCartanMatrix,
    div_eq_mul_inv]

private theorem splitCharacter_one (P : Parameters) (t : OrbitParameters P) :
    splitCharacter P t 1 = (nodeCharacter P t .central).val.val := by
  simp [splitCharacter, nodeCharacter, rootCharacters, normUnit, restrictUnit,
    TorusCoordinates.frobenius, typeDCartanMatrix, div_eq_mul_inv,
    mul_assoc, mul_comm, mul_left_comm]

private theorem splitCharacter_two (P : Parameters) (t : OrbitParameters P) :
    splitCharacter P t 2 = fieldFrobenius P (nodeCharacter P t .arms).val := by
  have hv : fieldFrobenius P t.2.val.val = t.2.val.val := t.2.val.property
  simp [splitCharacter, nodeCharacter, rootCharacters, fixedUnit, typeDCartanMatrix,
    div_eq_mul_inv, hv, -fieldFrobenius_apply]

private theorem splitCharacter_three (P : Parameters) (t : OrbitParameters P) :
    splitCharacter P t 3 = fieldFrobenius P (fieldFrobenius P (nodeCharacter P t .arms).val) := by
  have hv : fieldFrobenius P t.2.val.val = t.2.val.val := t.2.val.property
  simp [splitCharacter, nodeCharacter, rootCharacters, fixedUnit, typeDCartanMatrix,
    div_eq_mul_inv, hv, -fieldFrobenius_apply]

private theorem signedScalar_map {F K : Type*} [Field F] [Field K]
    (f : F →+* K) (s : Bool) (c : F) : f (signedScalar s c) = signedScalar s (f c) := by
  cases s <;> simp [signedScalar]

theorem orbitElementary_root_conjugate (P : Parameters) (hp : P.prime = 2)
    (t : OrbitParameters P) (s : Bool) (i : Node) (r : RootField P i) :
    orbitElementary P hp t * rootElementary P hp s i r * (orbitElementary P hp t)⁻¹ =
      rootElementary P hp s i (signedScalar s (nodeCharacter P t i).val * r) := by
  apply Subtype.ext
  apply Subtype.ext
  change elementaryInclusion P (orbitElementary P hp t * rootElementary P hp s i r *
    (orbitElementary P hp t)⁻¹) = elementaryInclusion P (rootElementary P hp s i
      (signedScalar s (nodeCharacter P t i).val * r))
  simp only [map_mul, map_inv, inclusion_orbitElementary]
  cases i with
  | arms =>
    simp only [rootElementary, elementaryInclusion_foldedElementary, foldedRoot,
      conjugate_mul, product_simpleRoot P hp, splitCharacter_zero, splitCharacter_two,
      splitCharacter_three, map_mul]
    cases s <;> simp [signedScalar, -fieldFrobenius_apply]
  | central =>
    change product P (expand P t) * simpleRoot P s 1 r.val * (product P (expand P t))⁻¹ =
      simpleRoot P s 1 (signedScalar s (nodeCharacter P t .central).val * r).val
    rw [product_simpleRoot P hp, splitCharacter_one]
    congr 1
    change _ = (fixedField P).subtype (signedScalar s (nodeCharacter P t .central).val * r)
    rw [map_mul, signedScalar_map]
    rfl

/-- Conjugation by the actual descended torus realizes its two root characters. -/
theorem torus_root_conjugate (P : Parameters) (hp : P.prime = 2)
    (t : OrbitParameters P) (s : Bool) (i : Node) (r : RootField P i) :
    (torusMulEquiv P hp t).val * rootElement P hp s i r * (torusMulEquiv P hp t).val⁻¹ =
      rootElement P hp s i (signedScalar s (nodeCharacter P t i).val * r) := by
  simpa only [torusMulEquiv_val, rootElement, map_mul, map_inv] using
    congrArg (toCarrier P) (orbitElementary_root_conjugate P hp t s i r)


/-- Every independent pair of nonzero root scalars is induced by a torus element. -/
theorem exists_torus_scalars (P : Parameters) (hp : P.prime = 2)
    (c : (i : Node) → (RootField P i)ˣ) :
    ∃ t ∈ torus P, ∀ s i r, t * rootElement P hp s i r * t⁻¹ =
      rootElement P hp s i (signedScalar s (c i).val * r) := by
  obtain ⟨v, hv⟩ := rootCharacters_surjective P hp (c .arms, c .central)
  refine ⟨(torusMulEquiv P hp v).val, (torusMulEquiv P hp v).property, ?_⟩
  intro s i r
  rw [torus_root_conjugate]
  have hi : nodeCharacter P v i = c i := by
    cases i with
    | arms => exact congrArg Prod.fst hv
    | central => exact congrArg Prod.snd hv
  rw [hi]

end
end Triality.Standard.OuterOdd.Coverage.ParameterRigidity
