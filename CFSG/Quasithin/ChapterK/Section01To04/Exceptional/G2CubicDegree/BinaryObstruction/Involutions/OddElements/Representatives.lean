module

public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.G2CubicDegree.BinaryObstruction.Involutions.OddElements.Factors

/-!
# Separating conjugacy coverage from the concrete matrix bounds

Two short words in the certified root-word marking suffice for the odd
calculations: `a * b` for the regular-three class and `a * b⁻¹` for the
seven-subgroups. The coverage assertion below is an explicit obligation,
not a claim that these exploratory choices have already been certified.
The vertex quotient actions respect equality under the actual marking, so
cyclic conjugacy in the derived group transports their fixed codimensions.

This connects independent group and matrix certificates to the literal
flag-factor assembly for Guralnick–Malle, Classification of 2F-modules I,
Proposition 4.3, pp.10–11, including the additional degree-32 branch.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree.BinaryObstruction.Involutions.OddElements
open Representation Representation.BinaryOffender Subgroup
open G2DerivedPermutationFiltration
open G2DerivedPermutationFiltration.VertexCoordinates
open G2DerivedPermutationFiltration.VertexCoordinates.CoordinateFiltrations

/-- Candidate word for the regular-three calculation, in Lean's multiplication convention. -/
def regularWord : WordGroup := FreeGroup.of 0 * FreeGroup.of 1

/-- Candidate word for the seven calculation, using the same literal generators. -/
def sevenWord : WordGroup := FreeGroup.of 0 * (FreeGroup.of 1)⁻¹

/-- The only group coverage required by the matrix certificates. Cyclic subgroup
conjugacy covers both seven-element classes without identifying those classes. -/
structure ConjugacyCoverage : Prop where
  regular_three : ∀ x : Derived, RegularThree x → ∃ g : Derived,
    zpowers x = zpowers (g * groupHom regularWord * g⁻¹)
  seven : ∀ x : Derived, orderOf x = 7 → ∃ g : Derived,
    zpowers x = zpowers (g * groupHom sevenWord * g⁻¹)

/-- Bounds at the specified actors only; global coverage is a separate premise. -/
structure RepresentativeBounds {G V : Type*} [_root_.Group G]
    [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (a b : G) : Prop where
  regular_three : 10 ≤ fixedCodim ρ (zpowers a)
  seven : 12 ≤ fixedCodim ρ (zpowers b)

/-- The matrix calculation on every degree-14 literal vertex quotient. -/
def VertexSamples : Prop :=
  ∀ (i : Fin 2) (t : Factor i), degree i t = 14 →
    RepresentativeBounds (vertexFactorRepresentation i t) regularWord sevenWord

/-- Separate calculations on both literal degree-32 cycle factors. -/
structure CycleSamples : Prop where
  half : RepresentativeBounds (V := cycleCoordinates.half.toSubmodule)
    cycleCoordinates.half.toRepresentation
    (groupHom regularWord) (groupHom sevenWord)
  quotient : RepresentativeBounds
    (V := cycleSubrepresentation.toSubmodule ⧸ cycleCoordinates.half.toSubmodule)
    cycleCoordinates.half.quotientRepresentation
    (groupHom regularWord) (groupHom sevenWord)

/-- The seven-word calculation needs only the difference of the two generator
operators: multiplication by the invertible second operator preserves rank. -/
theorem fixedCodim_mul_inv_eq_rank_sub {G V : Type*} [_root_.Group G]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (a b : G) :
    fixedCodim ρ (zpowers (a * b⁻¹)) =
      Module.finrank (ZMod 2) (LinearMap.range (ρ a - ρ b)) := by
  rw [fixedCodim_zpowers_eq_displacement_rank]
  have he : ρ (a * b⁻¹) - LinearMap.id = (ρ a - ρ b).comp (ρ b⁻¹) := by
    change ρ (a * b⁻¹) - 1 = (ρ a - ρ b) * ρ b⁻¹
    rw [sub_mul, ← map_mul, ← map_mul, mul_inv_cancel, map_one]
  have hr : LinearMap.range (ρ b⁻¹) = ⊤ := by
    apply LinearMap.range_eq_top.mpr
    intro v
    refine ⟨ρ b v, ?_⟩
    have hb : ρ b⁻¹ * ρ b = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
    exact LinearMap.congr_fun hb v
  rw [he, LinearMap.range_comp_of_range_eq_top _ hr]

/-- A consumer of the inverse-free rank identity at the exact two sample words. -/
theorem representativeBounds_of_generator_ranks {G V : Type*} [_root_.Group G]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (a b : G)
    (hthree : 10 ≤ Module.finrank (ZMod 2)
      (LinearMap.range (ρ a * ρ b - LinearMap.id)))
    (hseven : 12 ≤ Module.finrank (ZMod 2) (LinearMap.range (ρ a - ρ b))) :
    RepresentativeBounds ρ (a * b) (a * b⁻¹) := by
  constructor
  · rw [fixedCodim_zpowers_eq_displacement_rank, map_mul]
    exact hthree
  · rwa [fixedCodim_mul_inv_eq_rank_sub]

private theorem fixedCodim_eq_of_marking {G H V : Type*} [_root_.Group G] [_root_.Group H]
    [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (π : G →* H)
    (hk : ∀ a b, π a = π b → ρ a = ρ b)
    (A B : Subgroup G) (h : A.map π = B.map π) : fixedCodim ρ A = fixedCodim ρ B := by
  have hs : fixedSpace ρ A = fixedSpace ρ B := by
    ext v
    constructor
    · intro hv b
      have hb : π b.val ∈ A.map π := by
        rw [h]
        exact mem_map_of_mem π b.property
      obtain ⟨a, ha, he⟩ := hb
      change ρ b.val v = v
      rw [← hk a b.val he]
      exact hv ⟨a, ha⟩
    · intro hv a
      have ha : π a.val ∈ B.map π := by
        rw [← h]
        exact mem_map_of_mem π a.property
      obtain ⟨b, hb, he⟩ := ha
      change ρ a.val v = v
      rw [← hk b a.val he]
      exact hv ⟨b, hb⟩
  unfold fixedCodim
  rw [hs]

/-- Equality under the actual group marking gives equality of the literal
vertex quotient operators. Thus no free-group kernel is silently discarded. -/
theorem vertexFactor_action_eq_of_marking (i : Fin 2) (t : Factor i)
    (a b : WordGroup) (h : groupHom a = groupHom b) :
    vertexFactorRepresentation i t a = vertexFactorRepresentation i t b := by
  have hp : wordPerm i a = wordPerm i b := by
    let e : Fin 63 ≃ Vertex i := Equiv.ofBijective (vertex i) (vertex_bijective i)
    apply Equiv.ext
    intro x
    apply e.injective
    rw [vertex_word_equivariance i e (fun j x => vertex_generator_action i j x),
      vertex_word_equivariance i e (fun j x => vertex_generator_action i j x), h]
  have hr : representation i a = representation i b := by
    change BinaryPermutation.representation (Fin 63) (wordPerm i a) =
      BinaryPermutation.representation (Fin 63) (wordPerm i b)
    rw [hp]
  apply LinearMap.ext
  intro v
  induction v using Submodule.Quotient.induction_on with
  | H v =>
    apply congrArg (within ((adaptedFlagCoordinates i).stage t.val)
      ((adaptedFlagCoordinates i).stage (t.val + 1))).toSubmodule.mkQ
    apply Subtype.ext
    exact LinearMap.congr_fun hr v.val

/-- Conjugacy in the finite actor transports bounds on a marked word action,
provided its actual kernel is respected. -/
theorem markedBounds_of_samples {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) WordGroup V)
    (hk : ∀ a b, groupHom a = groupHom b → ρ a = ρ b)
    (hcov : ConjugacyCoverage) (hs : RepresentativeBounds ρ regularWord sevenWord) :
    MarkedBounds groupHom ρ := by
  have transfer (x w : WordGroup) (g : Derived)
      (h : zpowers (groupHom x) = zpowers (g * groupHom w * g⁻¹)) :
      fixedCodim ρ (zpowers x) = fixedCodim ρ (zpowers w) := by
    obtain ⟨c, rfl⟩ := groupHom_surjective g
    have hm : (zpowers x).map groupHom = (zpowers (c * w * c⁻¹)).map groupHom := by
      simpa only [MonoidHom.map_zpowers, map_mul, map_inv] using h
    rw [fixedCodim_eq_of_marking ρ groupHom hk _ _ hm, fixedCodim_zpowers_conj]
  constructor
  · intro x hx
    obtain ⟨g, hg⟩ := hcov.regular_three (groupHom x) hx
    rw [transfer x regularWord g hg]
    exact hs.regular_three
  · intro x hx
    obtain ⟨g, hg⟩ := hcov.seven (groupHom x) hx
    rw [transfer x sevenWord g hg]
    exact hs.seven

/-- The certified marking kernel discharges the descent premise for every
actual degree-14 vertex quotient. -/
theorem vertexBounds_of_samples (hcov : ConjugacyCoverage) (hs : VertexSamples) :
    VertexBounds := by
  intro i t ht
  exact markedBounds_of_samples (vertexFactorRepresentation i t)
    (vertexFactor_action_eq_of_marking i t) hcov (hs i t ht)

/-- On representations of the actual derived group, cyclic conjugacy directly
extends the representative calculations to both required odd classes. -/
theorem actualBounds_of_samples {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) Derived V)
    (hcov : ConjugacyCoverage)
    (hs : RepresentativeBounds ρ (groupHom regularWord) (groupHom sevenWord)) :
    MarkedBounds (MonoidHom.id Derived) ρ := by
  constructor
  · intro x hx
    obtain ⟨g, hg⟩ := hcov.regular_three x hx
    rw [hg, fixedCodim_zpowers_conj]
    exact hs.regular_three
  · intro x hx
    obtain ⟨g, hg⟩ := hcov.seven x hx
    rw [hg, fixedCodim_zpowers_conj]
    exact hs.seven

/-- The two cycle certificates are kept distinct in the final factor bound. -/
theorem cycleBounds_of_samples (hcov : ConjugacyCoverage) (hs : CycleSamples) :
    CycleBounds :=
  ⟨actualBounds_of_samples (V := cycleCoordinates.half.toSubmodule) _ hcov hs.half,
    actualBounds_of_samples
      (V := cycleSubrepresentation.toSubmodule ⧸ cycleCoordinates.half.toSubmodule)
      _ hcov hs.quotient⟩

/-- The three independent concrete certificates imply the requested bound
for every irreducible module above degree eight, including degree 32. -/
theorem oddDisplacementBounds_of_certificates
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) Derived V) [IsIrreducible σ]
    (hd : 8 < Module.finrank (ZMod 2) V)
    (hcov : ConjugacyCoverage) (hv : VertexSamples) (hc : CycleSamples) :
    OddDisplacementBounds σ :=
  oddDisplacementBounds_of_factors σ hd
    (vertexBounds_of_samples hcov hv) (cycleBounds_of_samples hcov hc)

/-- Full-normalizer consumer with the independent inversion witnesses explicit. -/
theorem involutionBounds_of_certificates
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) Derived V) [IsIrreducible σ]
    (hf : Function.Injective σ) (hd : 8 < Module.finrank (ZMod 2) V)
    (w : InversionWitnesses) (hcov : ConjugacyCoverage) (hv : VertexSamples) (hc : CycleSamples) :
    InvolutionBounds σ :=
  involutionBounds_of_odd_displacement σ hf w
    (oddDisplacementBounds_of_certificates σ hd hcov hv hc)

end CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree.BinaryObstruction.Involutions.OddElements
