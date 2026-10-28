module
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.RecognitionGeometry.VertexExtension.CentralCover.Words
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order360

/-!
# Recognition through the ten literal fixed points

The table in `Data.x` has been proved equal to the permutation induced by the
published x. Its ten fixed points support the action of the full centralizer.
Three checked words act as the standard PSL₂(9) generators. Since the literal
quotient by XC has order 360, the quotient action has precisely that image
and is faithful. This uses no assumed presentation or generation of C.

The table-backed fixed-point subtype avoids expanding the original ATLAS
cycle expression inside dependent action types. `point_fixed` and `action_point`
retain compatibility with x and the original degree-100 carrier.
Source: Aschbacher, *Sporadic Groups* (1994), proof of 47.3(1), p.262.
-/

@[expose] public section
namespace Sporadic.LeechRelated.J2.RecognitionGeometry.VertexExtension.CentralCover
open Subgroup GeneratorPair Theory.GroupTheory
open Atlas.Comparisons.Exceptional
open scoped MatrixGroups

/-- The literal points fixed by the published x. -/
abbrev FixedPoints := {i : Fin 100 // Data.x i = i}

def point : Fin 10 → Fin 100 := ![3,55,40,62,7,12,72,48,41,59]

theorem point_fixed (i : Fin 10) : inclusion x (point i) = point i := by
  rw [inclusion_x]
  have h : ∀ i : Fin 10, Data.x (point i) = point i := by decide +kernel
  exact h i

def fixedPoint (i : Fin 10) : FixedPoints := ⟨point i, inclusion_x ▸ point_fixed i⟩

theorem fixedPoint_bijective : Function.Bijective fixedPoint := by
  constructor
  · intro i j h
    have ht : ∀ i j : Fin 10, point i = point j → i = j := by decide +kernel
    exact ht i j (congrArg Subtype.val h)
  · intro j
    have ht : ∀ j : Fin 100, Data.x j = j → ∃ i : Fin 10, point i = j := by decide +kernel
    obtain ⟨i, hi⟩ := ht j j.property
    exact ⟨i, Subtype.ext hi⟩

noncomputable def marking : Fin 10 ≃ FixedPoints := Equiv.ofBijective fixedPoint fixedPoint_bijective

private theorem fixed_iff_of_commute {α : Type*} (p q : Equiv.Perm α)
    (h : Commute p q) (i : α) : q (p i) = p i ↔ q i = i := by
  have he := congrArg (fun t : Equiv.Perm α => t i) h.eq
  simp only [Equiv.Perm.mul_apply] at he
  rw [← he]
  exact p.injective.eq_iff

theorem fixed_iff (c : C) (i : Fin 100) :
    Data.x (inclusion (c : Carrier) i) = inclusion (c : Carrier) i ↔ Data.x i = i := by
  apply fixed_iff_of_commute
  change inclusion (c : Carrier) * Data.x = Data.x * inclusion (c : Carrier)
  have hc := congrArg inclusion ((mem_C_iff _).mp c.property)
  simpa only [map_mul, inclusion_x] using hc

def fixedAction : C →* Equiv.Perm FixedPoints where
  toFun c := (inclusion (c : Carrier)).subtypePerm (fixed_iff c)
  map_one' := by ext i; rfl
  map_mul' c d := by ext i; rfl

noncomputable def action : C →* Equiv.Perm (Fin 10) :=
  marking.symm.permCongrHom.toMonoidHom.comp fixedAction

theorem action_point (c : C) (i : Fin 10) :
    point (action c i) = inclusion (c : Carrier) (point i) := by
  change (marking (marking.symm (fixedAction c (marking i)))).val = _
  rw [marking.apply_symm_apply]
  rfl

theorem action_eq (c : C) (t : Equiv.Perm (Fin 10))
    (ht : ∀ i, inclusion (c : Carrier) (point i) = point (t i)) : action c = t := by
  apply Equiv.ext
  intro i
  apply marking.injective
  apply Subtype.ext
  exact (action_point c i).trans (ht i)

theorem xC_mem_action_ker : xC ∈ action.ker := by
  apply action_eq
  exact point_fixed

theorem XC_le_action_ker : XC ≤ action.ker := by
  intro z hz
  obtain ⟨n, hn⟩ := hz
  have he : xC ^ n = z := Subtype.ext hn
  rw [← he]
  exact action.ker.zpow_mem xC_mem_action_ker n

noncomputable def quotientAction : CentralQuotient →* Equiv.Perm (Fin 10) :=
  QuotientGroup.lift XC action XC_le_action_ker

theorem quotientAction_mk (c : C) : quotientAction (centralQuotientMap c) = action c := rfl

def upperWord : List (Fin 4) := [2,1,3,0,2,0,3]
def omegaWord : List (Fin 4) := [1,2,1,3,1,2]
def inversionWord : List (Fin 4) := [3,0,2,1,2,0,2]

def upperLift : C := evalWord letters upperWord
def omegaLift : C := evalWord letters omegaWord
def inversionLift : C := evalWord letters inversionWord

theorem action_upperLift : action upperLift = TriplePartitions.shiftOne := by
  apply action_eq
  intro i
  have he : inclusion (upperLift : Carrier) = evalWord ![Data.u,Data.u⁻¹,Data.v,Data.v⁻¹] upperWord := by
    change (inclusion.comp C.subtype) (evalWord letters upperWord) = _
    rw [map_word]
    congr 1
    exact funext inclusion_letters
  rw [he]
  have h : ∀ i : Fin 10, evalWord ![Data.u,Data.u⁻¹,Data.v,Data.v⁻¹] upperWord (point i) =
    point (TriplePartitions.shiftOne i) := by decide +kernel
  exact h i

theorem action_omegaLift : action omegaLift = TriplePartitions.shiftOmega := by
  apply action_eq
  intro i
  have he : inclusion (omegaLift : Carrier) = evalWord ![Data.u,Data.u⁻¹,Data.v,Data.v⁻¹] omegaWord := by
    change (inclusion.comp C.subtype) (evalWord letters omegaWord) = _
    rw [map_word]
    congr 1
    exact funext inclusion_letters
  rw [he]
  have h : ∀ i : Fin 10, evalWord ![Data.u,Data.u⁻¹,Data.v,Data.v⁻¹] omegaWord (point i) =
    point (TriplePartitions.shiftOmega i) := by decide +kernel
  exact h i

theorem action_inversionLift : action inversionLift = TriplePartitions.invert := by
  apply action_eq
  intro i
  have he : inclusion (inversionLift : Carrier) = evalWord ![Data.u,Data.u⁻¹,Data.v,Data.v⁻¹] inversionWord := by
    change (inclusion.comp C.subtype) (evalWord letters inversionWord) = _
    rw [map_word]
    congr 1
    exact funext inclusion_letters
  rw [he]
  have h : ∀ i : Fin 10, evalWord ![Data.u,Data.u⁻¹,Data.v,Data.v⁻¹] inversionWord (point i) =
    point (TriplePartitions.invert i) := by decide +kernel
  exact h i

/-- The entire standard PSL2(9) image occurs in the concrete quotient action. -/
theorem nine_range_le : Nine.permutation.range ≤ quotientAction.range := by
  apply Atlas.GroupTheory.range_le_of_generators Nine.permutation quotientAction
    Nine.generators Nine.psl_generated
  intro g hg
  rcases hg with rfl | hg
  · exact ⟨centralQuotientMap upperLift, action_upperLift.trans Nine.permutation_upper.symm⟩
  rcases hg with rfl | hg
  · exact ⟨centralQuotientMap omegaLift, action_omegaLift.trans Nine.permutation_omega.symm⟩
  have he : g = (Nine.inversionMatrix : PSL(2, Nine.F)) :=
    Set.mem_singleton_iff.mp hg
  subst g
  exact ⟨centralQuotientMap inversionLift, action_inversionLift.trans Nine.permutation_inversion.symm⟩

/-- The order bound turns the certified generator inclusion into range equality. -/
theorem range_eq_nine (hM : Nat.card M = 2160) :
    quotientAction.range = Nine.permutation.range := by
  symm
  apply Subgroup.eq_of_le_of_card_ge nine_range_le
  have hc : Nat.card Nine.permutation.range = 360 :=
    (Nat.card_congr (MonoidHom.ofInjective Nine.permutation_injective).toEquiv).symm.trans
      (psl2Card9_card Nine.card)
  rw [hc]
  calc
    Nat.card quotientAction.range ≤ Nat.card CentralQuotient :=
      Nat.card_le_card_of_surjective _ quotientAction.rangeRestrict_surjective
    _ = 360 := card_CentralQuotient hM

/-- No extra pointwise fixer survives in the literal central quotient. -/
theorem quotientAction_injective (hM : Nat.card M = 2160) : Function.Injective quotientAction := by
  have hc : Nat.card CentralQuotient = Nat.card quotientAction.range := by
    rw [range_eq_nine hM, card_CentralQuotient hM]
    exact ((Nat.card_congr (MonoidHom.ofInjective Nine.permutation_injective).toEquiv).symm.trans
      (psl2Card9_card Nine.card)).symm
  have hi := ((Nat.bijective_iff_surjective_and_card quotientAction.rangeRestrict).mpr
    ⟨quotientAction.rangeRestrict_surjective, hc⟩).1
  intro a b hab
  exact hi (Subtype.ext hab)

end Sporadic.LeechRelated.J2.RecognitionGeometry.VertexExtension.CentralCover
