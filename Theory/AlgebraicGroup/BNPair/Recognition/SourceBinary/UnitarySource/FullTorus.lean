module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitarySource.ActorCartanRange
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitarySource.FourCartan
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitarySource.TensorScalars

/-!
# The constructed U4 torus is the full source Cartan

A fixed-product pair of diagonal parameters is equivalent to an arbitrary
fixed-field determinant and an arbitrary large-field coroot parameter.
Taking the unique fixed-field square root constructs every such pair.
Consequently the torus map has range equal to the product of the scalar
image and the aligned SL2 torus. The scalar image is the entire true panel
kernel, by the proved coefficient-unit bijection. ActorCartanRange supplies
the remaining factorization, so the resulting torus is the full B ∩ N.

No tensor realization is needed for this range calculation. The original
actor quotient maps supply the exact kernel order in ActorCartanApplication;
TorusRangeApplication applies the range equality to the literal original
quotient, its full Borel and both oriented endpoints. Remainder containment
and the irreducible core action remain the explicit earlier-source inputs.
The tensor and compatible field-label obligations remain with this owner.

Source: Fong--Seitz II (8.1)--(8.2), p.197, and the characteristic-two
argument in (8B), pp.201--202; the parameter convention is FourCartan.
-/

@[expose] public noncomputable section
open Subgroup
open scoped MatrixGroups IsMulCommutative
open Theory.SpecificGroups.ClassicalUnitary
open Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitarySource
namespace FourCartan
variable (E : Type*) [Field E] [Finite E] [CharP E 2] (σ : E ≃+* E)

def factorParameter (k : (UnitaryFourSylow.FixedField E σ)ˣ) (a : Eˣ) : (FourWeyl.torusParameters E σ) := by
  let r : Eˣ := Units.map (FixedBy.subfield E σ).subtype.toMonoidHom (squareRoot E σ k)
  refine ⟨(r*a,r/a),?_⟩
  have he : (r:E)*(r:E) = (k:(UnitaryFourSylow.FixedField E σ)) := by
    have hr : (r:E) = ((squareRoot E σ k : UnitaryFourSylow.FixedField E σ) : E) := rfl
    rw [hr]
    have ht : (squareRoot E σ k : UnitaryFourSylow.FixedField E σ) *
        (squareRoot E σ k : UnitaryFourSylow.FixedField E σ) = k := by
      simpa only [pow_two] using squareRoot_square E σ k
    exact congrArg (fun z : UnitaryFourSylow.FixedField E σ => (z:E)) ht
  change σ ((↑(r*a):E)*(↑(r/a):E)) = (↑(r*a):E)*(↑(r/a):E)
  simp only [Units.val_mul, Units.val_div_eq_div_val]
  have hp : ((r:E)*(a:E))*((r:E)/(a:E)) = (r:E)*(r:E) := by field_simp
  rw [hp,he]
  exact (k:(UnitaryFourSylow.FixedField E σ)).property

@[simp] theorem determinant_factorParameter (k : (UnitaryFourSylow.FixedField E σ)ˣ) (a : Eˣ) :
    determinant E σ (factorParameter E σ k a) = k := by
  apply Units.ext
  apply Subtype.ext
  let r : Eˣ := Units.map (FixedBy.subfield E σ).subtype.toMonoidHom (squareRoot E σ k)
  change (↑(r*a):E)*(↑(r/a):E) = ((k:(UnitaryFourSylow.FixedField E σ)):E)
  simp only [Units.val_mul, Units.val_div_eq_div_val]
  calc
    _ = (r:E)*(r:E) := by field_simp
    _ = _ := by
      have hr : (r:E) = ((squareRoot E σ k : UnitaryFourSylow.FixedField E σ) : E) := rfl
      rw [hr]
      exact congrArg (fun z : UnitaryFourSylow.FixedField E σ => (z:E))
        (by simpa only [pow_two] using squareRoot_square E σ k)

@[simp] theorem coroot_factorParameter (k : (UnitaryFourSylow.FixedField E σ)ˣ) (a : Eˣ) :
    coroot E σ (factorParameter E σ k a) = a := by
  have hr : halfDeterminant E σ (factorParameter E σ k a) =
      Units.map (FixedBy.subfield E σ).subtype.toMonoidHom (squareRoot E σ k) := by
    simp only [halfDeterminant, MonoidHom.comp_apply, determinant_factorParameter]
  change (factorParameter E σ k a).val.1 / halfDeterminant E σ (factorParameter E σ k a) = a
  rw [hr]
  change ((Units.map (FixedBy.subfield E σ).subtype.toMonoidHom (squareRoot E σ k))*a)/
    (Units.map (FixedBy.subfield E σ).subtype.toMonoidHom (squareRoot E σ k)) = a
  exact mul_div_cancel_left _ _

theorem factor_surjective : Function.Surjective ((determinant E σ).prod (coroot E σ)) := by
  rintro ⟨k,a⟩
  exact ⟨factorParameter E σ k a,Prod.ext
    (determinant_factorParameter E σ k a) (coroot_factorParameter E σ k a)⟩

variable {Y : Type*} [Group Y]
variable (l : Matrix.SpecialLinearGroup (Fin 2) E →* Y) (scalarMap : (UnitaryFourSylow.FixedField E σ)ˣ →* Y)
variable (hc : ∀ (k : (UnitaryFourSylow.FixedField E σ)ˣ) (g : Matrix.SpecialLinearGroup (Fin 2) E), Commute (scalarMap k) (l g))

theorem hom_range : (hom E σ l scalarMap hc).range =
    scalarMap.range ⊔ (l.comp (BenderSuzuki.Converse.torHom E)).range := by
  have hf : hom E σ l scalarMap hc =
      (scalarMap.noncommCoprod (l.comp (BenderSuzuki.Converse.torHom E)) (fun k a => hc k _)).comp
        ((determinant E σ).prod (coroot E σ)) := by ext p; rfl
  rw [hf,MonoidHom.range_comp,MonoidHom.range_eq_top.mpr (factor_surjective E σ),
    ←MonoidHom.range_eq_map,MonoidHom.noncommCoprod_range]


end FourCartan
open RootCoordinates HexagonStructure GTwoSource ReeSource
variable {X E : Type*} [Group X] [Field E] [Finite E] [CharP E 2]
variable {P : Fin 2 → Subgroup X} (Q : MarkedQuotient P) (split : SplitData Q.tits)
variable (i : Fin 2) (hV : simpleRemainder Q split i ≤ localKernel Q i)
variable (μ : localGroup Q split i ≃* PSL(2,E)) (s : HexagonStructure.RootReflection Q split i)

variable [Representation.IsIrreducible (coreActorRepresentation Q split i hV)]
variable (n : ℕ) (hn : 0 < n)
variable (hc : centralizer (pCore 2 (Q.tits.standardParabolic {Q.simple i}) :
  Set (Q.tits.standardParabolic {Q.simple i})) ≤ pCore 2 (Q.tits.standardParabolic {Q.simple i}))
variable (hcard : Nat.card (coreCartan Q i) = 2^n-1)
variable (σ : E ≃+* E)
variable (η : UnitaryFourSylow.FixedField E σ ≃+* CoreCoefficientField Q split i hV n)

omit [Finite E] [CharP E 2] in
theorem intrinsicScalar_range : (intrinsicScalar Q split i hV n hn hc hcard σ η).range =
    coreCartan Q i := by
  apply le_antisymm
  · rintro x ⟨a,rfl⟩
    exact intrinsicScalar_mem Q split i hV n hn hc hcard σ η a
  intro x hx
  obtain ⟨a,ha⟩ := (coreCoefficientLift Q split i hV n hn hc hcard).surjective ⟨x,hx⟩
  obtain ⟨b,hb⟩ := (Units.map_bijective (f := η.toMonoidHom) η.bijective).surjective a
  refine ⟨b,?_⟩
  change (coreCoefficientLift Q split i hV n hn hc hcard (Units.map η.toMonoidHom b) : X ⧸ Q.D) = x
  rw [hb,ha]

theorem intrinsicFourCartan_range :
    (FourCartan.hom E σ (alignedPinningHom Q split i hV μ s)
      (intrinsicScalar Q split i hV n hn hc hcard σ η)
      (fun k g => intrinsicScalar_commute Q split i hV n hn hc hcard σ η k
        ((inclusion le_sup_right) ((alignedPinning Q split i hV μ s) g)))).range =
      Q.tits.B ⊓ Q.tits.N := by
  calc
    _ = (intrinsicScalar Q split i hV n hn hc hcard σ η).range ⊔
        (alignedTorusHom Q split i hV μ s).range :=
      FourCartan.hom_range E σ (alignedPinningHom Q split i hV μ s)
        (intrinsicScalar Q split i hV n hn hc hcard σ η) _
    _ = _ := by
      rw [intrinsicScalar_range]
      exact coreCartan_sup_actorTorus Q split i hV μ s

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitarySource
