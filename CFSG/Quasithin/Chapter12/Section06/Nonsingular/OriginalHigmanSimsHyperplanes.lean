module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.MovedModule
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.FullCoordinates
public import CFSG.Quasithin.Chapter12.Section06.Nonabelian.PointPerpendicular
public import Theory.Representation.BinaryPermutation.EightNonsingularStabilizer.Generation
public import Theory.Representation.BinaryPermutation.EightCoreLine

/-!
# The original nonsingular moved subgroups are polar hyperplanes

The original action preserves the polar form, and L_u fixes u. Therefore
every commutator in [V,L_u] is perpendicular to u. Both subgroups have
order 32, so they agree inside the unchanged V. Distinct nonsingular
points consequently give moved subgroups whose join is V.

The original six-letter core marking also supplies two distinct
nonsingular vectors in each moved subgroup. At least one differs from
its defining point. These statements retain the original action marking
and require no nonsingular-centralizer containment.

Source: Aschbacher--Smith, Section 12.6, the actual module V_v preceding
12.6.6 and the HS case of 12.6.12, printed pp.824--826.
-/

public noncomputable section
open Subgroup BinaryPermutation BinaryPermutation.EightNonsingular
open BinaryPermutation.TerminalOrthogonal.Eight
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- The actual commutator at a nonsingular point is its polar hyperplane
in the unchanged full module. -/
theorem OrthogonalMarking.nonsingular_moved_eq_perpendicular
    (chosen : Section02.ChosenModule T L V)
    (D : OrthogonalMarking L V chosen.normalizes) (hZ : ZV L V = ⊥)
    (u : V) (hu : D.Nonsingular u) :
    Vv L V (u : G) = (D.fullSetup hZ T u).V₅ := by
  let E := D.fullSetup hZ T u
  have hle : Vv L V (u : G) ≤ E.V₅ := by
    rw [Vv,commutator_comm]
    apply commutator_le.mpr
    intro l hl x hx
    let a : L := ⟨l,Lv_le_L L (u : G) hl⟩
    let v : V := ⟨x,hx⟩
    let α := conjugation L V chosen.normalizes a
    let p := (D.groupEquiv (QuotientGroup.mk' (conjugation L V chosen.normalizes).ker a)).val
    have he (w : V) : (E.coordinates (α w)).toAdd =
        naturalRepresentation (Fin 8) p (E.coordinates w).toAdd :=
      D.fullCoordinates_equivariant hZ a w
    have hfix : α u = u := by
      apply Subtype.ext
      change l * (u : G) * l⁻¹ = (u : G)
      rw [mem_centralizer_singleton_iff.mp (Lv_le_Gv L (u : G) hl),mul_inv_cancel_right]
    have hp : form.polarBilin (E.coordinates u).toAdd (E.coordinates (α v)).toAdd =
        form.polarBilin (E.coordinates u).toAdd (E.coordinates v).toAdd := by
      calc
        _ = form.polarBilin
            (naturalRepresentation (Fin 8) p (E.coordinates u).toAdd)
            (naturalRepresentation (Fin 8) p (E.coordinates v).toAdd) := by
          rw [←he u,←he v,hfix]
        _ = _ := by
          simp only [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar,
            ←map_add,form_invariant]
    have hm : ((α v / v : V) : G) ∈ E.V₅ := by
      apply (E.mem_V₅_iff (α v / v)).mpr
      change form.polarBilin (D.fullCoordinates hZ u).toAdd
        (D.fullCoordinates hZ (α v / v)).toAdd = 0
      rw [map_div,toAdd_div,map_sub]
      exact sub_eq_zero.mpr hp
    change l * x * l⁻¹ / x ∈ E.V₅ at hm
    simpa only [commutatorElement_def,div_eq_mul_inv] using hm
  apply eq_of_le_of_card_ge hle
  rw [E.perpendicular_card (nonsingular_ne_one D hu),D.nonsingular_moved_card chosen u hu]

/-- Distinct nonsingular points have moved subgroups generating the original V. -/
theorem OrthogonalMarking.nonsingular_moved_sup
    (chosen : Section02.ChosenModule T L V)
    (D : OrthogonalMarking L V chosen.normalizes) (hZ : ZV L V = ⊥)
    (u w : V) (hu : D.Nonsingular u) (hw : D.Nonsingular w) (hne : u ≠ w) :
    Vv L V (u : G) ⊔ Vv L V (w : G) = V := by
  rw [D.nonsingular_moved_eq_perpendicular chosen hZ u hu,
    D.nonsingular_moved_eq_perpendicular chosen hZ w hw]
  exact (D.fullSetup hZ T u).pointPerpendicular_sup u w hne

private theorem pair_nonsingular (i j : Fin 8) (hij : i ≠ j) :
    form (coreToNatural (Fin 8) (pair i j)) ≠ 0 := by
  have hw : hammingNorm (pair i j).val = 2 := EightCoreLine.pair_weight i j hij
  rw [(EightGeometry.nonsingular_core_iff _).mpr (Or.inl hw)]
  exact one_ne_zero

/-- The actual moved subgroup contains a nonsingular point different from
its defining point; the witnesses come from the original six-letter core. -/
theorem OrthogonalMarking.exists_other_nonsingular_in_moved
    (chosen : Section02.ChosenModule T L V)
    (D : OrthogonalMarking L V chosen.normalizes)
    (u : V) (hu : D.Nonsingular u) :
    ∃ w : V, D.Nonsingular w ∧ w ≠ u ∧ (w : G) ∈ Vv L V (u : G) := by
  obtain ⟨i,j,hij,hpair⟩ := nonsingular_pair _ hu
  obtain ⟨F,hF,hFR,_,hproj⟩ := D.local_core_image chosen u i j hij hpair
  have hn (a b : Fin 6) (hab : a ≠ b) : D.Nonsingular (F (sixPair a b)).toMul := by
    change form (D.coordinates (Submodule.Quotient.mk (F (sixPair a b)))) ≠ 0
    rw [hproj,extendSix_pair]
    exact pair_nonsingular _ _ (fun he => hab ((complementLetters i j hij).injective he))
  have hm (a b : Fin 6) : ((F (sixPair a b)).toMul : G) ∈ Vv L V (u : G) := by
    apply hFR.le
    exact ⟨Multiplicative.ofAdd (sixPair a b),rfl⟩
  have hdiff : (F (sixPair 0 1)).toMul ≠ (F (sixPair 0 2)).toMul := by
    intro he
    have hpair' : sixPair 0 1 = sixPair 0 2 := hF (Additive.toMul.injective he)
    exact (by decide : sixPair 0 1 ≠ sixPair 0 2) hpair'
  by_cases hfirst : (F (sixPair 0 1)).toMul = u
  · exact ⟨(F (sixPair 0 2)).toMul,hn 0 2 (by decide),
      fun he => hdiff (hfirst.trans he.symm),hm 0 2⟩
  · exact ⟨(F (sixPair 0 1)).toMul,hn 0 1 (by decide),hfirst,hm 0 1⟩

end CFSG.Quasithin.Chapter12.Section06
