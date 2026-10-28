module
public import Theory.SpecificGroups.ReeF4.Octagon.Binary.Automorphisms.FiniteBridge.Seed
public import Theory.SpecificGroups.ReeF4.Octagon.Binary.Automorphisms.FiniteBridge.LineData

/-!
# Realizing the finite line rows as literal second-parabolic cosets

The checked signed-generator tree transports the base triple along the actual
Ree action. Distinct finite rows give distinct line cosets, and the native
parabolic index gives surjectivity. The certificate parameter is discharged by
`FiniteBridge.Checks` in the final graph isomorphism.

Source: the actual binary building used in Aschbacher–Smith J.5.6–J.5.7.
-/

@[expose] public section
noncomputable section
namespace ReeF4.Octagon.Binary.Automorphisms.FiniteBridge
open Subgroup Tits Theory.GroupTheory.CosetEnumeration
open Theory.AlgebraicGroup.TitsSystem.DihedralGeometry
attribute [local instance] pointAction lineAction

theorem mem_moved_points (l : Fin 2925) (hbound : (LineData.points l).Forall (· < 1755))
    (a : Letter ParrottGenerator) (p : Fin 1755) :
    (R1Certificate.table p a).val ∈ (LineData.points l).map (LineData.move a) ↔
      p.val ∈ LineData.points l := by
  have hmove (q : Fin 1755) : LineData.move a q.val = (R1Certificate.table q a).val := by
    unfold LineData.move
    have hq : (⟨q.val % 1755, Nat.mod_lt _ (by decide)⟩ : Fin 1755) = q :=
      Fin.ext (Nat.mod_eq_of_lt q.isLt)
    rw [hq]
  have hi : Function.Injective (fun q : Fin 1755 => R1Certificate.table q a) :=
    (tablePermutation R1Certificate.table R1Certificate.inverse_table a).injective
  constructor
  · rintro hp
    obtain ⟨q,hq,he⟩ := List.mem_map.mp hp
    let q' : Fin 1755 := ⟨q, List.forall_iff_forall_mem.mp hbound q hq⟩
    have he' : R1Certificate.table q' a = R1Certificate.table p a := by
      apply Fin.ext
      exact (hmove q').symm.trans he
    have heq : q = p.val := congrArg Fin.val (hi he')
    exact heq ▸ hq
  · intro hp
    exact List.mem_map.mpr ⟨p.val,hp,hmove p⟩

theorem exists_line_of_valid (hvalid : ∀ i, LineData.Valid i) (i : Fin 2925) :
    ∃ l : LineCoset, ∀ p : Fin 1755,
      pointOnLine (pointEquiv p) l ↔ p.val ∈ LineData.points i := by
  induction i using Fin.strong_induction_on with
  | h i ih =>
    by_cases hi : i.val = 0
    · have hz : i = 0 := Fin.ext hi
      subst i
      have hrow : LineData.points 0 = [0,1,3] := by simpa using (hvalid 0).2.2
      refine ⟨((1 : Model 0) : LineCoset), fun p => ?_⟩
      rw [seed_incidence, hrow]
      simp only [List.mem_cons, List.not_mem_nil, or_false, Fin.ext_iff, Fin.val_zero, Fin.val_one]
      rfl
    · have hrow := (hvalid i).2.2
      rw [if_neg hi] at hrow
      obtain ⟨l,hl⟩ := ih (LineData.parent i) hrow.1
      let a := LineData.letter i
      let g := (presentationMap (letterValue parrottGenerator a))⁻¹
      refine ⟨g • l, fun p => ?_⟩
      obtain ⟨q,hq⟩ := (tablePermutation R1Certificate.table R1Certificate.inverse_table a).surjective p
      change R1Certificate.table q a = p at hq
      subst p
      rw [pointEquiv_letter, pointOnLine_translate, hl]
      have he := Finset.ext_iff.mp hrow.2 (R1Certificate.table q a).val
      simp only [List.mem_toFinset] at he
      change (R1Certificate.table q a).val ∈
        (LineData.points (LineData.parent i)).map (LineData.move a) ↔ _ at he
      exact (mem_moved_points (LineData.parent i)
        (hvalid (LineData.parent i)).1 a q).symm.trans he

def lineMapOfValid (hvalid : ∀ i, LineData.Valid i) (i : Fin 2925) : LineCoset :=
  if i = 0 then ((1 : Model 0) : LineCoset) else (exists_line_of_valid hvalid i).choose

theorem lineMapOfValid_incidence (hvalid : ∀ i, LineData.Valid i)
    (i : Fin 2925) (p : Fin 1755) :
    pointOnLine (pointEquiv p) (lineMapOfValid hvalid i) ↔ p.val ∈ LineData.points i := by
  by_cases hi : i = 0
  · subst i
    have hrow : LineData.points 0 = [0,1,3] := by simpa using (hvalid 0).2.2
    rw [lineMapOfValid, if_pos rfl, seed_incidence, hrow]
    simp only [List.mem_cons, List.not_mem_nil, or_false, Fin.ext_iff, Fin.val_zero, Fin.val_one]
    rfl
  · rw [lineMapOfValid, if_neg hi]
    exact (exists_line_of_valid hvalid i).choose_spec p

theorem lineMapOfValid_injective (hvalid : ∀ i, LineData.Valid i) :
    Function.Injective (lineMapOfValid hvalid) := by
  intro i j he
  have hs : (LineData.points i).toFinset = (LineData.points j).toFinset := by
    ext p
    simp only [List.mem_toFinset]
    constructor
    · intro hp
      let q : Fin 1755 := ⟨p, List.forall_iff_forall_mem.mp (hvalid i).1 p hp⟩
      have hi := (lineMapOfValid_incidence hvalid i q).mpr hp
      rw [he] at hi
      exact (lineMapOfValid_incidence hvalid j q).mp hi
    · intro hp
      let q : Fin 1755 := ⟨p, List.forall_iff_forall_mem.mp (hvalid j).1 p hp⟩
      have hi := (lineMapOfValid_incidence hvalid j q).mpr hp
      rw [← he] at hi
      exact (lineMapOfValid_incidence hvalid i q).mp hi
  apply Fin.ext
  exact (hvalid i).2.1.symm.trans
    ((congrArg LineData.keyInverse (congrArg LineData.keyOf hs)).trans (hvalid j).2.1)

def lineEquivOfValid (hvalid : ∀ i, LineData.Valid i) : Fin 2925 ≃ LineCoset :=
  Equiv.ofBijective (lineMapOfValid hvalid)
    ((lineMapOfValid_injective hvalid).bijective_of_nat_card_le (by rw [Nat.card_fin, line_card]))

theorem lineEquivOfValid_zero (hvalid : ∀ i, LineData.Valid i) :
    lineEquivOfValid hvalid 0 = ((1 : Model 0) : LineCoset) := by
  change lineMapOfValid hvalid 0 = _
  simp only [lineMapOfValid, ↓reduceIte]
end ReeF4.Octagon.Binary.Automorphisms.FiniteBridge
