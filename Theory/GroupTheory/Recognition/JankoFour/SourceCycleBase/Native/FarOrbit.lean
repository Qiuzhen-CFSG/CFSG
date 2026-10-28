module
public import Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.Native.FarOrbit.Checks
public import Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.Native.FarOrbit.Seeds
/-!
# Native far-line transitivity

The checked descending forest supplies a standard-sextet stabilizer
transporter from one of four explicit roots to each listed trio. Sorted
mask triples and strictly increasing keys make this list injective, and the
independently proved count of 3795 native trios makes it exhaustive. Three
roots are near the standard sextet, so every far trio comes from the fourth
root. Composing two transporters proves transitivity, and the actual sextet
conjugator transports the result to every native sextet.

Only the transitivity needed by AS91 (7.8) is asserted: no complete catalogue
of sextets or full orbit-size computation is required.

Source: Aschbacher–Segev (1991), (3.8), p.595, applied in (7.8), p.605.
-/
@[expose] public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.Native.FarOrbit
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open scoped Pointwise

def rootLine (r : Fin 4) : Line := seedLine (r.castLE (by decide))

theorem seed_parts (r : Fin 4) : parts (row (seed r)).masks = (rootLine r).parts := by
  revert r; decide +kernel

theorem exists_transport (i : Fin 3795) : ∃ g : sextetStabilizer standardSextet,
    (g : M24) • (rootLine (row i).root).parts = parts (row i).masks := by
  generalize hn : (row i).depth = n
  induction n using Nat.strong_induction_on generalizing i with
  | h n ih =>
    have hc := (all_rows i).1.2
    by_cases hz : (row i).depth = 0
    · rw [if_pos hz] at hc
      refine ⟨1,?_⟩
      rw [Subgroup.coe_one,one_smul]
      conv_rhs => rw [hc]
      exact (seed_parts _).symm
    · rw [if_neg hz] at hc
      obtain ⟨g,hg⟩ := ih (row (row i).parent).depth (by omega) (row i).parent rfl
      refine ⟨nativeGenerator (row i).generator * g,?_⟩
      rw [Subgroup.coe_mul,mul_smul]
      rw [←hc.2.1,hg]
      exact parts_transport (nativeGenerator (row i).generator : M24) _ _ hc.2.2

noncomputable def entry (i : Fin 3795) : Line :=
  ((exists_transport i).choose : M24) • rootLine (row i).root

theorem entry_parts (i : Fin 3795) : (entry i).parts = parts (row i).masks :=
  (exists_transport i).choose_spec

theorem key_strictMono : StrictMono key := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  exact (all_rows i.castSucc).2 (Nat.succ_lt_succ i.isLt)

theorem entry_injective : Function.Injective entry := by
  intro i j he
  have hp := congrArg (fun l : Line => l.parts) he
  rw [entry_parts,entry_parts] at hp
  have hm := sorted_parts_injective _ _ (all_rows i).1.1 (all_rows j).1.1 hp
  apply key_strictMono.injective
  simp only [key,hm]

theorem entry_surjective : Function.Surjective entry :=
  (entry_injective.bijective_of_nat_card_le (by rw [line_card,Nat.card_fin])).2

theorem root_ne_zero_near (r : Fin 4) (hr : r ≠ 0) : NearPlane standardSextet (rootLine r) := by
  fin_cases r
  · exact (hr rfl).elim
  · exact seed_one_near
  · exact seed_two_near
  · exact seed_three_near

theorem root_zero_of_far (i : Fin 3795) (hi : ¬ NearPlane standardSextet (entry i)) :
    (row i).root = 0 := by
  by_contra hn
  apply hi
  exact nearPlane_transport ((exists_transport i).choose : M24) rfl
    (exists_transport i).choose.property.symm (root_ne_zero_near _ hn)

theorem standard_far_transitive (l m : Line)
    (hl : ¬ NearPlane standardSextet l) (hm : ¬ NearPlane standardSextet m) :
    ∃ g : M24, g • standardSextet.parts = standardSextet.parts ∧ g • l.parts = m.parts := by
  obtain ⟨i,rfl⟩ := entry_surjective l
  obtain ⟨j,rfl⟩ := entry_surjective m
  let a := (exists_transport i).choose
  let b := (exists_transport j).choose
  refine ⟨((b * a⁻¹ : sextetStabilizer standardSextet) : M24),
    (b*a⁻¹).property,?_⟩
  have hi := root_zero_of_far i hl
  have hj := root_zero_of_far j hm
  change ((b : M24) * (a : M24)⁻¹) •
    ((a : M24) • (rootLine (row i).root).parts) =
      (b : M24) • (rootLine (row j).root).parts
  simp only [hi,hj,mul_smul,inv_smul_smul]

/-- AS91 (3.8)'s transitivity on trios coplanar with no trio of the sextet. -/
theorem far_transitive : FarTransitive := farTransitive_of_standard standard_far_transitive
end Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.Native.FarOrbit
