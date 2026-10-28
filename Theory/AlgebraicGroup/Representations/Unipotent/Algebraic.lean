module

public import Theory.AlgebraicGroup.Representations.Triangular
public import Theory.AlgebraicGroup.Representations.Unipotent.Triangularization

universe u v

namespace Theory.AlgebraicGroup.Subrepresentation

section

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G] {V : Type v}
  [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- A rational representation which is unitriangular in a chosen basis
defines an algebraic-group morphism to the corresponding unitriangular
group. -/
@[expose]
public noncomputable def unitriangularRepresentationMorphismOfBasis
    (ρ : RationalRepresentation G V) (hρ : IsRationalRepresentation ρ)
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (hunitriangular : ∀ g, uUnipotent (Module.finrank k V)
      (LinearMap.toMatrix b b (ρ.action g : Module.End k V))) :
    AlgebraicGroup.Morphism G (uVariety k (Module.finrank k V)) := by
  let htriangular : ∀ g, tTriangular (Module.finrank k V)
      (LinearMap.toMatrix b b (ρ.action g : Module.End k V)) :=
    fun g ↦ (hunitriangular g).1
  let f := triangularRepresentationMorphismOfBasis ρ hρ b htriangular
  let hmap : ∀ g, f.onPoints g ∈
      (tUnipotentKernel (k := k) (Module.finrank k V)).toSubgroup := by
    intro g
    apply (tDiagonalMorphism_mem_kernel_iff (Module.finrank k V)
      (f.onPoints g)).2
    intro i
    change (tPointEquiv k (Module.finrank k V) (f.onPoints g)).1.1 i i = 1
    rw [triangularRepresentationMorphismOfBasis_pointEquiv]
    exact (hunitriangular g).2 i
  let r := f.codRestrictClosedSubgroup
    (tUnipotentKernel (k := k) (Module.finrank k V)) hmap
  exact (tKernelToUMorphism (k := k) (Module.finrank k V)).comp r

/-- The unitriangular factorization recovers the original triangular
representation after inclusion into the triangular group. -/
public lemma uToTMorphism_unitriangularRepresentationMorphismOfBasis
    (ρ : RationalRepresentation G V) (hρ : IsRationalRepresentation ρ)
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (hunitriangular : ∀ g, uUnipotent (Module.finrank k V)
      (LinearMap.toMatrix b b (ρ.action g : Module.End k V)))
    (g : Variety.Point G) :
    (uToTMorphism (k := k) (Module.finrank k V)).onPoints
        ((unitriangularRepresentationMorphismOfBasis
          ρ hρ b hunitriangular).onPoints g) =
      (triangularRepresentationMorphismOfBasis ρ hρ b
        (fun x ↦ (hunitriangular x).1)).onPoints g := by
  let htriangular : ∀ x, tTriangular (Module.finrank k V)
      (LinearMap.toMatrix b b (ρ.action x : Module.End k V)) :=
    fun x ↦ (hunitriangular x).1
  let f := triangularRepresentationMorphismOfBasis ρ hρ b htriangular
  let hmap : ∀ x, f.onPoints x ∈
      (tUnipotentKernel (k := k) (Module.finrank k V)).toSubgroup := by
    intro x
    apply (tDiagonalMorphism_mem_kernel_iff (Module.finrank k V)
      (f.onPoints x)).2
    intro i
    change (tPointEquiv k (Module.finrank k V) (f.onPoints x)).1.1 i i = 1
    rw [triangularRepresentationMorphismOfBasis_pointEquiv]
    exact (hunitriangular x).2 i
  let r := f.codRestrictClosedSubgroup
    (tUnipotentKernel (k := k) (Module.finrank k V)) hmap
  change (uToTMorphism (k := k) (Module.finrank k V)).onPoints
      ((tKernelToUMorphism (k := k) (Module.finrank k V)).onPoints
        (r.onPoints g)) = f.onPoints g
  have h := congrArg
    (tUnipotentKernel (k := k) (Module.finrank k V)).inclusion.onPoints
    (uToTKernelMorphism_tKernelToUPoint (k := k)
      (Module.finrank k V) (r.onPoints g))
  change (uToTMorphism (k := k) (Module.finrank k V)).onPoints
      ((tKernelToUMorphism (k := k) (Module.finrank k V)).onPoints
        (r.onPoints g)) =
    (tUnipotentKernel (k := k) (Module.finrank k V)).inclusion.onPoints
      (r.onPoints g) at h
  rw [Morphism.codRestrictClosedSubgroup_inclusion_apply] at h
  exact h

/-- Faithfulness of a rational representation transfers to its
unitriangular factorization. -/
public lemma unitriangularRepresentationMorphismOfBasis_injective
    (ρ : RationalRepresentation G V) (hρ : IsRationalRepresentation ρ)
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (hunitriangular : ∀ g, uUnipotent (Module.finrank k V)
      (LinearMap.toMatrix b b (ρ.action g : Module.End k V)))
    (hinjective : Function.Injective ρ.action) :
    Function.Injective
      (unitriangularRepresentationMorphismOfBasis
        ρ hρ b hunitriangular).onPoints := by
  intro x y hxy
  apply triangularRepresentationMorphismOfBasis_injective ρ hρ b
    (fun g ↦ (hunitriangular g).1) hinjective
  rw [← uToTMorphism_unitriangularRepresentationMorphismOfBasis
      ρ hρ b hunitriangular x,
    ← uToTMorphism_unitriangularRepresentationMorphismOfBasis
      ρ hρ b hunitriangular y, hxy]

omit [FiniteDimensional k V] in
private lemma representation_to_uVarietyMorphism_injective_iff
    (ρ : Variety.Point G →* LinearMap.GeneralLinearGroup k V)
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (F : ℕ → Submodule k V)
    (hstable : ∀ (m : ℕ) (g : Variety.Point G),
      F m ≤ (F m).comap (ρ g : Module.End k V))
    (hb : ∀ (m : ℕ) (hm : m ≤ Module.finrank k V),
      F m = Submodule.span k (Set.range fun l : Fin m =>
        b (Fin.castLE hm l)))
    (hunipotent : ∀ g : Variety.Point G,
      IsNilpotent ((ρ g : Module.End k V) - 1))
    (matrixCoefficient : Fin (Module.finrank k V) →
      Fin (Module.finrank k V) → G.PolynomialFunction)
    (matrixCoefficient_apply : ∀ i j g,
      matrixCoefficient i j g =
        b.repr ((ρ g : Module.End k V) (b j)) i)
    (inverseDeterminant : G.PolynomialFunction)
    (inverseDeterminant_apply : ∀ g,
      inverseDeterminant g =
        (LinearMap.toMatrix b b (ρ g : Module.End k V)).det⁻¹) :
    ∃ f : AlgebraicGroup.Morphism G (uVariety k (Module.finrank k V)),
      Function.Injective f.onPoints ↔ Function.Injective ρ := by
  obtain ⟨φ, hφ, hcoord⟩ :=
    representation_to_uVarietyPoint_coordinates_eq_generalLinearRepresentationPoint
      ρ b F hstable hb hunipotent
  let ψ : Variety.Point G →* Variety.Point (uVariety k (Module.finrank k V)) :=
    { toFun := fun g => (uPointEquiv k (Module.finrank k V)).symm (φ g)
      map_one' := by
        apply (uPointEquiv k (Module.finrank k V)).injective
        rw [Equiv.apply_symm_apply, uPointEquiv_one]
        simp
      map_mul' := by
        intro g h
        apply (uPointEquiv k (Module.finrank k V)).injective
        simp [uPointEquiv_mul] }
  let gl : AlgebraicGroup.Morphism G
      (glVariety (Module.finrank k V) : Variety k) :=
    generalLinearRepresentationMorphism b ρ matrixCoefficient matrixCoefficient_apply
      inverseDeterminant inverseDeterminant_apply
  let f : AlgebraicGroup.Morphism G (uVariety k (Module.finrank k V)) :=
    { toVariety :=
        { toFun := ψ
          regular := by
            intro q
            rcases q with ⟨⟨i, j⟩⟩
            rcases gl.toVariety.regular (Sum.inl (i, j)) with ⟨p, hp⟩
            refine ⟨p, fun g => ?_⟩
            calc
              (ψ g).val (ULift.up (i, j)) =
                  (generalLinearRepresentationPoint b (ρ g)).val
                    (Sum.inl (i, j)) := hcoord g i j
              _ = evalPolynomial g.val p := by
                change (gl.toVariety.toFun g).val (Sum.inl (i, j)) = _
                exact hp g }
      map_one := ψ.map_one
      map_mul := ψ.map_mul }
  refine ⟨f, ?_⟩
  constructor
  · intro hf g h hρ
    apply hf
    change ψ g = ψ h
    have hφeq : φ g = φ h := by
      apply Subtype.ext
      rw [hφ g, hφ h, hρ]
    exact congrArg (uPointEquiv k (Module.finrank k V)).symm hφeq
  · intro hρ g h hgh
    change ψ g = ψ h at hgh
    have hφeq : φ g = φ h := by
      have h := congrArg (uPointEquiv k (Module.finrank k V)) hgh
      simpa [ψ] using h
    apply hρ
    have hgl := congrArg (fun z : uUnipotentGL k (Module.finrank k V) =>
      (z : GL (Fin (Module.finrank k V)) k)) hφeq
    have hlin := congrArg (Matrix.GeneralLinearGroup.toLin' b) hgl
    rw [hφ g, hφ h] at hlin
    simpa using hlin

omit [FiniteDimensional k V] in
/-- A regular unitriangular factorization has trivial kernel exactly when the
original adapted-basis representation is faithful. -/
public lemma representation_to_uVarietyMorphism_kernel_bot_iff
    (ρ : Variety.Point G →* LinearMap.GeneralLinearGroup k V)
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (F : ℕ → Submodule k V)
    (hstable : ∀ (m : ℕ) (g : Variety.Point G),
      F m ≤ (F m).comap (ρ g : Module.End k V))
    (hb : ∀ (m : ℕ) (hm : m ≤ Module.finrank k V),
      F m = Submodule.span k (Set.range fun l : Fin m =>
        b (Fin.castLE hm l)))
    (hunipotent : ∀ g : Variety.Point G,
      IsNilpotent ((ρ g : Module.End k V) - 1))
    (matrixCoefficient : Fin (Module.finrank k V) →
      Fin (Module.finrank k V) → G.PolynomialFunction)
    (matrixCoefficient_apply : ∀ i j g,
      matrixCoefficient i j g =
        b.repr ((ρ g : Module.End k V) (b j)) i)
    (inverseDeterminant : G.PolynomialFunction)
    (inverseDeterminant_apply : ∀ g,
      inverseDeterminant g =
        (LinearMap.toMatrix b b (ρ g : Module.End k V)).det⁻¹) :
    ∃ f : AlgebraicGroup.Morphism G (uVariety k (Module.finrank k V)),
      f.kernel = ⊥ ↔ Function.Injective ρ := by
  obtain ⟨f, hf⟩ :=
    representation_to_uVarietyMorphism_injective_iff ρ b F hstable hb hunipotent
      matrixCoefficient matrixCoefficient_apply inverseDeterminant inverseDeterminant_apply
  refine ⟨f, ?_⟩
  change f.onPoints.ker = ⊥ ↔ Function.Injective ρ
  rw [MonoidHom.ker_eq_bot_iff]
  exact hf

end

end Theory.AlgebraicGroup.Subrepresentation
