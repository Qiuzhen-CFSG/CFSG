module
public import Theory.Representation.G2OrthogonalCover.Universal
public import Theory.Representation.G2NaturalTransitivity
public import Theory.Representation.BinaryQuadraticTransitivity

/-!
# A fixed nonsingular vector in every natural binary G₂ cover

For any invariant quadratic form on the seven-dimensional orthogonal cover,
its polar annihilates the fixed scalar line: the associated linear functional
vanishes on every displacement, and the cover is commutator-generated. If the
quadratic value on that line were also zero, the form would descend to the
natural six-space. Nonzero-vector transitivity forces that descended form to
vanish. Thus any nonzero invariant quadratic form has a nonsingular fixed
vector. The universal cover transports it to every full natural cover.

This is the quadratic obstruction used in Aschbacher–Smith13.5.25, printed
p.925. It supplies an order-four lift without classifying the entire center.
-/

@[expose] public noncomputable section
open Representation Representation.OneCohomology
namespace Atlas.G2.Natural.OrthogonalCover
local notation "F" => ZMod 2
local notation "E" => TraceZero F
local notation "D" => _root_.commutator (Model F)

/-- Fullness makes the fixed scalar line orthogonal to the entire seven-space
for every invariant quadratic form. -/
theorem invariantQuadratic_polar_identity
    (q : QuadraticForm F E) (hq : ∀ (g : D) x, q (action F g x)=q x) :
    q.polarBilin (identity F) = 0 := by
  have hi (g : D) : action F g (identity F) = identity F :=
    traceZeroAction_identity F g.val
  have hp (g : D) (x y : E) :
      q.polarBilin (action F g x) (action F g y) = q.polarBilin x y := by
    simp only [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar,←map_add,hq]
  have hle : Coinvariants.ker (action F) ≤ (q.polarBilin (identity F)).ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨g,v⟩,rfl⟩
    change q.polarBilin (identity F) (action F g v-v)=0
    rw [map_sub,←hi g,hp,hi g,sub_self]
  rw [commutator_eq_top] at hle
  ext v
  exact hle Submodule.mem_top

/-- A nonzero invariant quadratic form on the seven-cover is nonzero on the
fixed scalar line: otherwise it descends to the forbidden natural form. -/
theorem invariantQuadratic_identity_ne_zero
    (q : QuadraticForm F E) (hq : ∀ (g : D) x, q (action F g x)=q x)
    (hne : q ≠ 0) : q (identity F) ≠ 0 := by
  intro hz
  have hr : scalarLine F ≤ q.radical := by
    apply Submodule.span_le.mpr
    intro x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    exact ⟨hz,invariantQuadratic_polar_identity q hq⟩
  let q' : QuadraticForm F (Space F) := q.lift (scalarLine F) hr
  have hinv (g : D) (x : Space F) : q' (derivedAction F g x)=q' x := by
    obtain ⟨x,rfl⟩ := mk_surjective F x
    rw [derivedAction_mk]
    exact hq g x
  have he : q'=0 := quadratic_eq_zero_of_nonzero_transitive (derivedAction F)
    (by rw [finrank_space];decide) (derivedAction_transitive F) q' hinv
  apply hne
  ext x
  exact congrArg (fun r : QuadraticForm F (Space F) => r (mk F x)) he

/-- Any full natural cover carrying a nonzero invariant quadratic form has a
fixed vector with nonzero quadratic value. This retains the actual quotient. -/
theorem cover_exists_fixed_quadratic_ne_zero
    {W : Type*} [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    (σ : Representation F D W) (p : σ.IntertwiningMap (binaryNatural F))
    (hp : IsCover p) (q : QuadraticForm F W)
    (hq : ∀ g x, q (σ g x)=q x) (hne : q≠0) :
    ∃ w : W, (∀ g, σ g w=w) ∧ q w≠0 := by
  obtain ⟨f,hf,_⟩ := exists_quotient F p hp
  have hn : q.comp f.toLinearMap ≠ 0 := by
    intro he
    apply hne
    ext w
    obtain ⟨x,rfl⟩ := hf w
    exact congrArg (fun r : QuadraticForm F E => r x) he
  have hqi (g : D) (x : E) :
      (q.comp f.toLinearMap) (action F g x) = (q.comp f.toLinearMap) x := by
    change q (f (binaryAction F g x))=q (f x)
    rw [f.isIntertwining,hq]
  refine ⟨f (identity F),?_,invariantQuadratic_identity_ne_zero _ hqi hn⟩
  intro g
  rw [←f.isIntertwining]
  change f (action F g (identity F)) = _
  rw [show action F g (identity F)=identity F from traceZeroAction_identity F g.val]

end Atlas.G2.Natural.OrthogonalCover
