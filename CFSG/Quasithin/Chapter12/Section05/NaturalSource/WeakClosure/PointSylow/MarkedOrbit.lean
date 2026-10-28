module

public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.PointGeometry
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.PointOrbitCardinality

/-!
# The nonsingular orbit in the original chosen module

The original quotient L → L/O₂(L), followed by the marking, is onto SL₅(2).
Equivariance therefore identifies C_L(z′) with the preimage of the literal
nonsingular stabilizer. Its index is 868, while V has order 1024. No actor
on an unrelated quotient and no assertion about C_T of the fixed z′ is used.

Source: Aschbacher--Smith, 12.5.5(3) and the choice preceding 12.5.9,
printed pp.819,821.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Section02
universe u
variable {G : Type u} [Group G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V}

/-- The actual quotient marking preserves the point-stabilizer index. -/
theorem ExteriorMarking.pointCentralizer_relIndex_model (a : ExteriorMarking D) :
    (centralizer ({a.zPrime} : Set G)).relIndex L =
      Representation.SL5ExteriorSquare.nondecomposableStabilizer.index := by
  let f : L →* Representation.SL5TenDimensional.Group :=
    a.quotientEquiv.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hf : Function.Surjective f :=
    a.quotientEquiv.surjective.comp (QuotientGroup.mk'_surjective _)
  have he : (centralizer ({a.zPrime} : Set G)).subgroupOf L =
      Representation.SL5ExteriorSquare.nondecomposableStabilizer.comap f := by
    ext l
    let v := a.coordinates.symm
      (Multiplicative.ofAdd Representation.SL5ExteriorSquare.nondecomposable)
    have heq := a.equivariant l v
    simp only [v, MulEquiv.apply_symm_apply, toAdd_ofAdd] at heq
    constructor
    · intro hl
      have hc : (l : G) * (v : G) * (l : G)⁻¹ = (v : G) :=
        mul_inv_eq_of_eq_mul (mem_centralizer_singleton_iff.mp hl)
      have hh : (⟨(l : G) * (v : G) * (l : G)⁻¹,
        (mem_normalizer_iff.mp (D.normalizes l.property) v).mp v.property⟩ : V) = v :=
        Subtype.ext hc
      rw [hh, MulEquiv.apply_symm_apply] at heq
      exact congrArg Multiplicative.toAdd heq.symm
    · intro hl
      change Representation.SL5TenDimensional.exteriorAction 2 (f l)
        Representation.SL5ExteriorSquare.nondecomposable =
          Representation.SL5ExteriorSquare.nondecomposable at hl
      change _ = Multiplicative.ofAdd
        (Representation.SL5TenDimensional.exteriorAction 2 (f l)
          Representation.SL5ExteriorSquare.nondecomposable) at heq
      rw [hl] at heq
      have hh := a.coordinates.injective (heq.trans (a.coordinates.apply_symm_apply _).symm)
      exact mem_centralizer_singleton_iff.mpr
        (mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val hh))
  change ((centralizer ({a.zPrime} : Set G)).subgroupOf L).index = _
  rw [he, index_comap_of_surjective _ hf]

/-- Orbit length for the canonical nonsingular representative in the original V. -/
theorem ExteriorMarking.pointCentralizer_relIndex (a : ExteriorMarking D) :
    (centralizer ({a.zPrime} : Set G)).relIndex L = 868 :=
  a.pointCentralizer_relIndex_model.trans
    Representation.SL5ExteriorSquare.index_nondecomposableStabilizer

/-- Cardinality transported through the original multiplicative marking. -/
theorem ExteriorMarking.card_module (a : ExteriorMarking D) : Nat.card V = 1024 := by
  rw [Nat.card_congr a.coordinates.toEquiv, Nat.card_congr Multiplicative.toAdd]
  exact Representation.SL5ExteriorSquare.card_exteriorSquare

end CFSG.Quasithin.Chapter12.Section05.NaturalSource
