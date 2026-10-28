module
public import Theory.SpecificGroups.Triality.OddFundamentalCentralizer.Centralizer.ElementaryIndex.HighestUnipotent.OrthogonalModel
public import Theory.SpecificGroups.Triality.OddFundamentalCentralizer.Centralizer.ElementaryIndex.HighestUnipotent.OrthogonalComparison.Natural

/-!
# Assembly of the odd Geck-to-orthogonal comparison

The signed integral coordinates intertwine the actual simple-root generators.
Generation then constructs a homomorphism into the literal scalar quotient.
Coordinate recovery proves injectivity; scalar detection makes the lift unique.
Pinning propagates the simple-root formulas to every rank-one element, including
the precise central-times-arms Weyl word in the highest-root marking.

The remaining hypotheses, `NaturalPinning` and `ScalarDetection`, concern only
the natural eight-space. They are explicitly retained here until their separate
geometric proofs are available; no unconditional comparison is claimed.

Sources: GLS3 §§2.4, 2.6–2.7; Aschbacher–Smith A.2.17, printed pp.38–39.
-/

@[expose] public section
noncomputable section
open Matrix
open scoped MatrixGroups
namespace Triality.Standard.OddFundamentalCentralizer.ElementaryIndex.HighestUnipotent.OrthogonalComparison
open Geometry.Integral ClassicalOrthogonal Parabolics
open Theory.AlgebraicGroup.StandardRootSystem RootPairing.SimpleGeckGroup
variable {P : Parameters}

/-- Tautological action on the original 28 coordinates, in their fixed ordering. -/
def matrixAction : SplitGroup P →* Module.End (ExtensionField P) (Ix → ExtensionField P) where
  toFun g := Matrix.mulVecLin (Geometry.matrixHom P g)
  map_one' := by rw [map_one]; exact Matrix.mulVecLin_one
  map_mul' _ _ := by rw [map_mul]; exact Matrix.mulVecLin_mul _ _

@[simp] theorem matrixAction_apply (g : SplitGroup P) (v : Ix → ExtensionField P) :
    matrixAction g v = Geometry.matrixHom P g *ᵥ v := rfl

theorem matrixAction_injective : Function.Injective (matrixAction (P := P)) := by
  intro g h e
  apply Geometry.matrixHom_injective P
  exact Matrix.mulVec_injective (congrArg DFunLike.coe e)

/-- Equality of the actual projective adjoint action and Geck action on the columns. -/
def Intertwines (g : SplitGroup P) (x : POmegaPlus 4 (ExtensionField P)) : Prop :=
  ∀ v, projectiveAdjoint (ExtensionField P) x (embedding (ExtensionField P) v) =
    embedding (ExtensionField P) (matrixAction g v)

theorem intertwines_one : Intertwines (P := P) 1 1 := by
  intro v
  simp only [map_one, Module.End.one_apply]

private theorem intertwines_mul_aux
    {K G H V W : Type*} [Semiring K] [Monoid G] [Monoid H]
    [AddCommMonoid V] [AddCommMonoid W] [Module K V] [Module K W]
    (ρ : G →* Module.End K V) (τ : H →* Module.End K W) (ι : V → W)
    {g h : G} {x y : H}
    (hx : ∀ v, τ x (ι v) = ι (ρ g v))
    (hy : ∀ v, τ y (ι v) = ι (ρ h v)) :
    ∀ v, τ (x * y) (ι v) = ι (ρ (g * h) v) := by
  intro v
  simp only [map_mul, Module.End.mul_apply, hy, hx]

theorem Intertwines.mul {g h : SplitGroup P}
    {x y : POmegaPlus 4 (ExtensionField P)} (hx : Intertwines g x) (hy : Intertwines h y) :
    Intertwines (g * h) (x * y) :=
  intertwines_mul_aux (matrixAction (P := P)) (projectiveAdjoint (ExtensionField P))
    (embedding (ExtensionField P)) hx hy

theorem Intertwines.inv {g : SplitGroup P} {x : POmegaPlus 4 (ExtensionField P)}
    (hx : Intertwines g x) : Intertwines g⁻¹ x⁻¹ := by
  intro v
  have h := congrArg (projectiveAdjoint (ExtensionField P) x⁻¹)
    (hx (matrixAction g⁻¹ v))
  have hg : matrixAction g (matrixAction g⁻¹ v) = v := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have hxi (w : NaturalMatrix (ExtensionField P)) :
      projectiveAdjoint (ExtensionField P) x⁻¹ (projectiveAdjoint (ExtensionField P) x w) = w := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  rw [hg, hxi] at h
  exact h.symm

theorem Intertwines.orthogonal_unique (hdet : ScalarDetection (ExtensionField P))
    {g : SplitGroup P} {x y : POmegaPlus 4 (ExtensionField P)}
    (hx : Intertwines g x) (hy : Intertwines g y) : x = y := by
  have hz := hx.mul hy.inv
  have hf : ∀ v, projectiveAdjoint (ExtensionField P) (x * y⁻¹)
      (embedding (ExtensionField P) v) = embedding (ExtensionField P) v := by
    simpa only [Intertwines, mul_inv_cancel, map_one, Module.End.one_apply] using hz
  exact mul_inv_eq_one.mp (projective_detect _ hdet _ hf)

private theorem two_ne_zero (hp : Odd P.prime) : (2 : ExtensionField P) ≠ 0 := by
  intro h
  have hd : P.prime ∣ 2 := (CharP.cast_eq_zero_iff (ExtensionField P) P.prime 2).mp h
  have he : P.prime = 2 := ((Nat.dvd_prime (by decide : Nat.Prime 2)).mp hd).resolve_left
    P.prime_prime.ne_one
  exact (by decide : ¬Odd (2 : ℕ)) (he ▸ hp)

theorem Intertwines.geck_unique (hp : Odd P.prime)
    {g h : SplitGroup P} {x : POmegaPlus 4 (ExtensionField P)}
    (hg : Intertwines g x) (hh : Intertwines h x) : g = h := by
  apply matrixAction_injective
  apply LinearMap.ext
  intro v
  exact embedding_injective (two_ne_zero hp) ((hg v).symm.trans (hh v))

variable (N : NaturalPinning (ExtensionField P))

theorem positive_intertwines (i : Fin 4) (t : ExtensionField P) :
    Intertwines (positiveRoot P i t)
      (projectiveElementaryMap (formD 4 (ExtensionField P)) (N.hom i
        (SpecialLinearGroup.transvection (i := (0 : Fin 2)) (j := 1) (by decide) t))) := by
  intro v
  simp only [projectiveAdjoint_mk, conjugation_apply, matrixAction_apply,
    Geometry.matrixHom_positive, ← map_inv, SpecialLinearGroup.transvection_inv, N.positive]
  exact curve_intertwines _ i true t v

theorem negative_intertwines (i : Fin 4) (t : ExtensionField P) :
    Intertwines (negativeRoot P i t)
      (projectiveElementaryMap (formD 4 (ExtensionField P)) (N.hom i
        (SpecialLinearGroup.transvection (i := (1 : Fin 2)) (j := 0) (by decide) t))) := by
  intro v
  simp only [projectiveAdjoint_mk, conjugation_apply, matrixAction_apply,
    Geometry.matrixHom_negative, ← map_inv, SpecialLinearGroup.transvection_inv, N.negative]
  exact curve_intertwines _ i false t v

/-- Generator lifting uses only the actual definition of `SplitGroup`. -/
theorem exists_intertwines (N : NaturalPinning (ExtensionField P)) (g : SplitGroup P) :
    ∃ x : POmegaPlus 4 (ExtensionField P), Intertwines g x := by
  let H : Subgroup (SplitGroup P) :=
    { carrier := {g | ∃ x, Intertwines g x}
      one_mem' := ⟨1, intertwines_one⟩
      mul_mem' := by
        rintro g h ⟨x, hx⟩ ⟨y, hy⟩
        exact ⟨x * y, hx.mul hy⟩
      inv_mem' := by
        rintro g ⟨x, hx⟩
        exact ⟨x⁻¹, hx.inv⟩ }
  have hgen : subgroup (typeDRootPairing_base 2) (ExtensionField P) ≤
      H.map (subgroup (typeDRootPairing_base 2) (ExtensionField P)).subtype := by
    apply (Subgroup.closure_le _).mpr
    rintro a ⟨⟨s, j⟩, t, rfl⟩
    obtain ⟨i, rfl⟩ := (typeDRootPairing_baseEquiv 2).surjective j
    cases s
    · exact ⟨negativeRoot P i t, ⟨_, negative_intertwines N i t⟩, rfl⟩
    · exact ⟨positiveRoot P i t, ⟨_, positive_intertwines N i t⟩, rfl⟩
  obtain ⟨g', hg', he⟩ := hgen g.property
  have he' : g' = g := Subtype.ext he
  subst g'
  exact hg'

variable (hdet : ScalarDetection (ExtensionField P))

/-- The unique projective lift compatible with the signed adjoint coordinates. -/
def comparisonHom (N : NaturalPinning (ExtensionField P))
    (hdet : ScalarDetection (ExtensionField P)) : SplitGroup P →* POmegaPlus 4 (ExtensionField P) where
  toFun g := (exists_intertwines N g).choose
  map_one' := (exists_intertwines N 1).choose_spec.orthogonal_unique hdet intertwines_one
  map_mul' g h := (exists_intertwines N (g * h)).choose_spec.orthogonal_unique hdet
    ((exists_intertwines N g).choose_spec.mul (exists_intertwines N h).choose_spec)

theorem comparisonHom_intertwines (g : SplitGroup P) :
    Intertwines g (comparisonHom N hdet g) := (exists_intertwines N g).choose_spec

theorem comparisonHom_injective (hp : Odd P.prime) :
    Function.Injective (comparisonHom N hdet) := by
  intro g h he
  apply (comparisonHom_intertwines N hdet g).geck_unique hp
  simpa only [he] using comparisonHom_intertwines N hdet h

/-- Arbitrary pinned maps agree with the constructed natural maps on all SL₂ elements. -/
theorem comparisonHom_pinned (D : PinnedRankOneMaps P) (i : Fin 4)
    (a : SL(2, ExtensionField P)) :
    comparisonHom N hdet (D.hom i a) =
      projectiveElementaryMap (formD 4 (ExtensionField P)) (N.hom i a) := by
  apply sl2_root_induction (fun a => comparisonHom N hdet (D.hom i a) =
    projectiveElementaryMap (formD 4 (ExtensionField P)) (N.hom i a)) ?_ ?_ ?_ a
  · intro t
    rw [D.positive]
    exact (comparisonHom_intertwines N hdet _).orthogonal_unique hdet (positive_intertwines N i t)
  · intro t
    rw [D.negative]
    exact (comparisonHom_intertwines N hdet _).orthogonal_unique hdet (negative_intertwines N i t)
  · intro a b ha hb
    simp only [map_mul, ha, hb]

private theorem comparisonHom_weyl (D : PinnedRankOneMaps P) (C : ArmRootCommutation P) :
    comparisonHom N hdet (splitHighestWeyl D C) =
      projectiveElementaryMap (formD 4 (ExtensionField P)) (naturalHighestWeyl _ N.hom) := by
  have hb : sl2BaseEmbedding P (weylMatrix _) = weylMatrix _ := Geometry.map_weyl _
  have hf : sl2Frobenius P (weylMatrix _) = weylMatrix _ := Geometry.map_weyl _
  change comparisonHom N hdet (D.hom 1 (sl2BaseEmbedding P (weylMatrix _)) *
    (D.hom 0 (weylMatrix _) * D.hom 2 (sl2Frobenius P (weylMatrix _)) *
      D.hom 3 (sl2Frobenius P (sl2Frobenius P (weylMatrix _))))) = _
  simp only [hb, hf, map_mul, comparisonHom_pinned, naturalHighestWeyl]

/-- Conditional final assembly; the two natural-space obligations remain explicit. -/
def markedComparison (N : NaturalPinning (ExtensionField P))
    (hdet : ScalarDetection (ExtensionField P)) (hp : Odd P.prime) (D : PinnedRankOneMaps P)
    (C : ArmRootCommutation P) : MarkedComparison D C where
  hom := comparisonHom N hdet
  injective := comparisonHom_injective N hdet hp
  highest_range := by
    have he : (comparisonHom N hdet).comp (highestHom D C) = naturalHighestHom _ N.hom := by
      ext a
      change comparisonHom N hdet (splitHighestWeyl D C * D.hom 1 a *
        (splitHighestWeyl D C)⁻¹) =
        projectiveElementaryMap _ (naturalHighestWeyl _ N.hom * N.hom 1 a *
          (naturalHighestWeyl _ N.hom)⁻¹)
      simp only [map_mul, map_inv, comparisonHom_weyl, comparisonHom_pinned]
    rw [he]
    exact N.highest_range
  armZero_range := by
    have he : (comparisonHom N hdet).comp (D.hom 0) =
        (projectiveElementaryMap _).comp (N.hom 0) := MonoidHom.ext (comparisonHom_pinned N hdet D 0)
    rw [he]
    exact N.armZero_range
  armTwo_range := by
    have he : (comparisonHom N hdet).comp (D.hom 2) =
        (projectiveElementaryMap _).comp (N.hom 2) := MonoidHom.ext (comparisonHom_pinned N hdet D 2)
    rw [he]
    exact N.armTwo_range
  armThree_range := by
    have he : (comparisonHom N hdet).comp (D.hom 3) =
        (projectiveElementaryMap _).comp (N.hom 3) := MonoidHom.ext (comparisonHom_pinned N hdet D 3)
    rw [he]
    exact N.armThree_range

end Triality.Standard.OddFundamentalCentralizer.ElementaryIndex.HighestUnipotent.OrthogonalComparison
