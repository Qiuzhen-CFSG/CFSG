module

public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.Actions
public import Theory.Representation.GeneralLinearNatural
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Theory.Representation.BinaryOffender.QuadraticSection
public import Theory.Representation.SL3DoubledNaturalOffenders.TensorEstimate.ProjectionBounds

/-!
# Strong offenders in the native natural-three clauses

For a field of order 2^m with m odd, an elementary subgroup of SL₃ has
rank at most 2m. The fixed space of the natural action is an F-subspace,
so a nontrivial subgroup has binary fixed codimension at least m, divisible
by m. A strong offender therefore has codimension exactly m. Doubling the
natural module doubles this codimension and excludes all strong offenders.

The final two lemmas transport these calculations using the native action
isomorphism, including its one common actor on the two repeated summands.
The parent NativeThree module applies them to the literal quotient summands
in B.5.6(3). They do not lift quotient offenders to elementary subgroups.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.5.6(3),
printed p.105, and its use in 13.6.13, p.929. The elementary rank estimate
comes from the checked SL₃ Sylow root-plane calculation.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open scoped MatrixGroups

namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Products.NormalThompson.Maximum.Singleton.MixedTransfer.NativeThree

private theorem field_finrank (F : BinaryField) : Module.finrank (ZMod 2) F.Carrier = F.degree := by
  have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F.Carrier)
  rw [F.card_eq, Nat.card_zmod] at h
  exact (Nat.pow_right_injective (by decide : 1 < 2) h).symm

private theorem natural_codim_mul (F : BinaryField)
    (A : Subgroup (SL(3,F.Carrier))) :
    fixedCodim (linearNatural F 3) A = F.degree *
      Module.finrank F.Carrier ((Fin 3 → F.Carrier) ⧸
        Representation.invariants ((specialLinearNatural (k := F.Carrier) 3).comp A.subtype)) := by
  let W := Representation.invariants ((specialLinearNatural (k := F.Carrier) 3).comp A.subtype)
  have he : fixedSpace (linearNatural F 3) A = W.restrictScalars (ZMod 2) := by
    ext v
    rfl
  rw [fixedCodim, he,
    (Submodule.Quotient.restrictScalarsEquiv (ZMod 2) W).finrank_eq,
    ← Module.finrank_mul_finrank (ZMod 2) F.Carrier, field_finrank]

private theorem natural_rank_le (F : BinaryField) (ho : Odd F.degree)
    (A : Subgroup (SL(3,F.Carrier))) (hA : IsElementaryAbelian 2 A) :
    rank A ≤ F.degree * 2 := by
  let := hA
  have hcard := Representation.SL3DoubledNaturalOffenders.natural_elementary_card_le
    F.card_eq ho F.degree_pos A
  rw [F.card_eq, ← pow_mul] at hcard
  have hr := Nat.log_mono_right (b := 2) hcard
  rwa [Nat.log_pow Nat.one_lt_two] at hr

private theorem natural_codim_ge (F : BinaryField)
    (A : Subgroup (SL(3,F.Carrier))) (hA : A ≠ ⊥) :
    F.degree ≤ fixedCodim (linearNatural F 3) A := by
  let W := Representation.invariants ((specialLinearNatural (k := F.Carrier) 3).comp A.subtype)
  have hW : W ≠ ⊤ := by
    intro ht
    apply hA
    apply A.eq_bot_iff_forall.mpr
    intro a ha
    apply specialLinearNatural_injective 3
    apply LinearMap.ext
    intro v
    have hv : v ∈ W := ht ▸ Submodule.mem_top
    exact (hv ⟨a,ha⟩).trans (by simp)
  have hproper := Submodule.finrank_lt hW
  have hsum := W.finrank_quotient_add_finrank
  have hpos : 1 ≤ Module.finrank F.Carrier ((Fin 3 → F.Carrier) ⧸ W) := by omega
  rw [natural_codim_mul]
  exact Nat.le_mul_of_pos_right _ hpos

private theorem repeated_two_codim {D V : Type*} [Group D] [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (A : Subgroup D) :
    fixedCodim (repeated ρ 2) A = 2 * fixedCodim ρ A := by
  have he := fixedCodim_map_equivariant (repeated ρ 2) (ρ.prod ρ)
    (MonoidHom.id D) (LinearEquiv.finTwoArrow (R := ZMod 2) (M := V))
    (fun _ _ => rfl) A
  simpa only [Subgroup.map_id, fixedCodim_prod, two_mul] using he

private theorem natural_strong_bounds (F : BinaryField) (ho : Odd F.degree)
    (A : Subgroup (SL(3,F.Carrier))) (hA : IsStrongOffender (linearNatural F 3) A) :
    fixedCodim (linearNatural F 3) A = F.degree ∧
      F.degree < rank A ∧ rank A ≤ 2 * F.degree := by
  have hr := natural_rank_le F ho A hA.1.2
  have hd := natural_codim_ge F A hA.1.1
  let d := Module.finrank F.Carrier ((Fin 3 → F.Carrier) ⧸
    Representation.invariants ((specialLinearNatural (k := F.Carrier) 3).comp A.subtype))
  have he : fixedCodim (linearNatural F 3) A = F.degree * d := natural_codim_mul F A
  have hlt : d < 2 := (Nat.mul_lt_mul_left F.degree_pos).mp
    (he ▸ hA.2.trans_le hr)
  have hne : d ≠ 0 := by
    intro hzero
    rw [he, hzero, mul_zero] at hd
    exact (Nat.not_le_of_gt F.degree_pos) hd
  have hdone : d = 1 := by omega
  have hcodim : fixedCodim (linearNatural F 3) A = F.degree := by
    simpa only [hdone, mul_one] using he
  exact ⟨hcodim, hcodim ▸ hA.2, by omega⟩

private theorem repeated_not_strong (F : BinaryField) (ho : Odd F.degree) :
    ¬ IsStrongFFModule (repeated (linearNatural F 3) 2) := by
  rintro ⟨A, hA⟩
  have hr := natural_rank_le F ho A hA.1.2
  have hd := natural_codim_ge F A hA.1.1
  have ht := hA.2
  rw [repeated_two_codim] at ht
  omega

variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) D V)

private theorem strong_map {B W : Type*} [Group B] [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) B W) (e : ActionEquiv ρ σ)
    (A : Subgroup D) (hA : IsStrongOffender ρ A) :
    IsStrongOffender σ (A.map e.groupEquiv.toMonoidHom) := by
  refine ⟨(IsOffender.map_equivariant ρ σ e.groupEquiv.toMonoidHom
    e.groupEquiv.injective e.linearEquiv e.intertwines ⟨hA.1, hA.2.le⟩).1, ?_⟩
  rw [← fixedCodim_map_equivariant ρ σ e.groupEquiv.toMonoidHom
    e.linearEquiv e.intertwines A, rank_map_injective _ e.groupEquiv.injective]
  exact hA.2

/-- Two copies of the same native natural SL₃ action have no strong offenders.
The actual group equivalence and intertwiner are used to transport the bound. -/
theorem repeatedLinearThree_not_strong (F : BinaryField) (ho : Odd F.degree)
    (h : IsRepeatedLinearNatural ρ F 3 2) : ¬ IsStrongFFModule ρ := by
  rintro ⟨A, hA⟩
  exact repeated_not_strong F ho ⟨_, strong_map ρ _ h.some A hA⟩

/-- A strong offender in a native natural SL₃ action fixes an F-hyperplane:
its binary fixed codimension is m, and its rank is strictly between m and 2m,
with the upper endpoint allowed. The conclusion is on the original actor. -/
theorem linearThree_strong_bounds (F : BinaryField) (ho : Odd F.degree)
    (h : IsLinearNatural ρ F 3) (A : Subgroup D) (hA : IsStrongOffender ρ A) :
    fixedCodim ρ A = F.degree ∧ F.degree < rank A ∧ rank A ≤ 2 * F.degree := by
  have hb := natural_strong_bounds F ho _ (strong_map ρ _ h.some A hA)
  rwa [← fixedCodim_map_equivariant ρ _ h.some.groupEquiv.toMonoidHom
    h.some.linearEquiv h.some.intertwines A,
    rank_map_injective _ h.some.groupEquiv.injective] at hb

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Products.NormalThompson.Maximum.Singleton.MixedTransfer.NativeThree

end
