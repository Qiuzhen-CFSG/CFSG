module
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile.Coverage.ElementaryCatalogue.InnerExtensions.Data

/-!
# Certified membership lists for the outer Held nodes

Commuting involutory generators have exactly their binary products as members.
The four-point base checks these products against the proposed normal-form lists.
The resulting equality is transported by the actual inner-automorphism map.
Source: the published Coverage rows and ElementaryCatalogue/source data, for
Aschbacher--Smith 15.3.41--42 and GLS3 Table 5.3p.
-/

@[expose] public section
open Subgroup Held Held.LocalPairs Held.LocalPairs.PairCoverage.LocalActions
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile.CoverageData.ElementaryCatalogue.InnerExtensions
open Exhaustion.CandidateOrderCertificate.Factors
variable {G : Type*} [Group G]
/-- Products selecting zero or one copy of each generator, in the original order. -/
def cube : List G → List G
  | [] => [1]
  | g :: gs => cube gs ++ (cube gs).map (g * ·)

private theorem cube_one (gs : List G) : 1 ∈ cube gs := by
  induction gs with
  | nil => exact List.mem_singleton_self _
  | cons g gs ih => exact List.mem_append_left _ ih

private theorem cube_step (gs : List G)
    (hsq : ∀ g ∈ gs, g * g = 1)
    (hcomm : ∀ g ∈ gs, ∀ h ∈ gs, g * h = h * g)
    (g : G) (hg : g ∈ gs) (x : G) (hx : x ∈ cube gs) : g * x ∈ cube gs := by
  induction gs generalizing x with
  | nil => simp at hg
  | cons a gs ih =>
    have hs : ∀ g ∈ gs, g * g = 1 := fun g h => hsq g (List.mem_cons_of_mem a h)
    have hc : ∀ g ∈ gs, ∀ h ∈ gs, g * h = h * g :=
      fun g hg h hh => hcomm g (List.mem_cons_of_mem a hg) h (List.mem_cons_of_mem a hh)
    rcases List.mem_cons.mp hg with he | hg
    · subst g
      rcases List.mem_append.mp hx with hx | hx
      · exact List.mem_append_right _ (List.mem_map_of_mem hx)
      · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
        rw [← mul_assoc, hsq a (List.mem_cons_self), one_mul]
        exact List.mem_append_left _ hy
    · rcases List.mem_append.mp hx with hx | hx
      · exact List.mem_append_left _ (ih hs hc hg _ hx)
      · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
        rw [← mul_assoc, hcomm g (List.mem_cons_of_mem a hg) a List.mem_cons_self, mul_assoc]
        exact List.mem_append_right _ (List.mem_map_of_mem (ih hs hc hg _ hy))

private theorem cube_mem_closure (gs : List G) (x : G) (hx : x ∈ cube gs) :
    x ∈ Subgroup.closure {g | g ∈ gs} := by
  induction gs generalizing x with
  | nil => simpa [cube] using hx
  | cons a gs ih =>
    have hle : Subgroup.closure {g | g ∈ gs} ≤ Subgroup.closure {g | g ∈ a :: gs} :=
      Subgroup.closure_mono (fun g hg => List.mem_cons_of_mem a hg)
    rcases List.mem_append.mp hx with hx | hx
    · exact hle (ih _ hx)
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      exact Subgroup.mul_mem _ (Subgroup.subset_closure List.mem_cons_self) (hle (ih _ hy))

private theorem closure_iff_cube (gs : List G)
    (hsq : ∀ g ∈ gs, g * g = 1)
    (hcomm : ∀ g ∈ gs, ∀ h ∈ gs, g * h = h * g) (x : G) :
    x ∈ Subgroup.closure {g | g ∈ gs} ↔ x ∈ cube gs := by
  constructor
  · intro hx
    induction hx using Subgroup.closure_induction_left with
    | one => exact cube_one gs
    | mul_left a ha b hb ih => exact cube_step gs hsq hcomm a ha b ih
    | inv_mul_cancel a ha b hb ih =>
      have hi : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hsq a ha)
      rw [hi]
      exact cube_step gs hsq hcomm a ha b ih
  · exact cube_mem_closure gs x

private theorem cube_map {H : Type*} [Group H] (f : G →* H) (gs : List G) :
    (cube gs).map f = cube (gs.map f) := by
  induction gs with
  | nil => simp [cube]
  | cons a gs ih =>
    simp only [cube, List.map_cons, List.map_append]
    rw [ih]
    congr 1
    rw [← ih]
    simp only [List.map_map, Function.comp_def, map_mul]

def pureNode : Option (Fin 4) → Subgroup pureTwo
  | none => ⊥
  | some j => row j

private theorem pureNode_eq_closure (i : Option (Fin 4)) :
    pureNode i = closure {g | g ∈ (rowGenerators i).map word} := by
  cases i with
  | none => simp [pureNode, rowGenerators]
  | some j => simp only [pureNode, row, rowGenerators, List.mem_map]

def generatorRelations (i : Option (Fin 4)) : Bool :=
  let gs := (rowGenerators i).map wordAction
  gs.all (fun g => same (g * g) 1 && gs.all (fun h => same (g * h) (h * g)))

def cubeCheck (i : Option (Fin 4)) : Bool :=
  let cs := cube ((rowGenerators i).map wordAction)
  cs.all (memberCheck i) &&
    (members i).all (fun n => cs.any (fun x => same x (Pair00Two.normalTable n)))

private theorem relations_sound (i : Option (Fin 4)) (h : generatorRelations i = true) :
    (∀ g ∈ (rowGenerators i).map word, g * g = 1) ∧
    (∀ g ∈ (rowGenerators i).map word, ∀ k ∈ (rowGenerators i).map word,
      g * k = k * g) := by
  have hrel (w : List ℤ) (hw : w ∈ rowGenerators i) :
      same (wordAction w * wordAction w) 1 = true ∧
      ((rowGenerators i).map wordAction).all
        (fun k => same (wordAction w * k) (k * wordAction w)) = true := by
    simpa only [Bool.and_eq_true] using
      List.all_eq_true.mp h (wordAction w) (List.mem_map_of_mem hw)
  constructor
  · intro g hg
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hg
    apply same_rho.mp
    simpa only [map_mul, map_one, ← wordAction_eq] using (hrel w hw).1
  · intro g hg k hk
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hg
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hk
    apply same_rho.mp
    simpa only [map_mul, ← wordAction_eq] using
      List.all_eq_true.mp (hrel w hw).2 (wordAction v) (List.mem_map_of_mem hv)

private theorem pure_members_of_checks (i : Option (Fin 4))
    (hr : generatorRelations i = true) (hc : cubeCheck i = true) (x : pureTwo) :
    x ∈ pureNode i ↔ ∃ n ∈ members i, pureElement n = x := by
  obtain ⟨hsq, hcomm⟩ := relations_sound i hr
  have hmap : (cube ((rowGenerators i).map word)).map rho =
      cube ((rowGenerators i).map wordAction) := by
    rw [cube_map, List.map_map]
    congr 1
    apply List.map_congr_left
    intro w _
    exact (wordAction_eq w).symm
  have hc' : ((cube ((rowGenerators i).map word)).map rho).all (memberCheck i) = true ∧
      (members i).all (fun n => ((cube ((rowGenerators i).map word)).map rho).any
        (fun x => same x (Pair00Two.normalTable n))) = true := by
    rw [hmap]
    simpa only [cubeCheck, Bool.and_eq_true] using hc
  rw [pureNode_eq_closure, closure_iff_cube _ hsq hcomm]
  constructor
  · intro hx
    have hm := List.all_eq_true.mp hc'.1 (rho x) (List.mem_map_of_mem hx)
    obtain ⟨n, hn, he⟩ := List.any_eq_true.mp hm
    rw [normalTable_eq] at he
    exact ⟨n, hn, (same_rho.mp he).symm⟩
  · rintro ⟨n, hn, rfl⟩
    obtain ⟨y, hy, he⟩ := List.any_eq_true.mp (List.all_eq_true.mp hc'.2 n hn)
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
    rw [normalTable_eq] at he
    rwa [← same_rho.mp he]

-- Kernel certificates; no discovery output is a premise.
section Checks
set_option Elab.async false

set_option maxRecDepth 8192 in
private theorem membership_checks_none :
    generatorRelations none = true ∧ cubeCheck none = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem membership_checks_0 :
    generatorRelations (some 0) = true ∧ cubeCheck (some 0) = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem membership_checks_1 :
    generatorRelations (some 1) = true ∧ cubeCheck (some 1) = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem membership_checks_2 :
    generatorRelations (some 2) = true ∧ cubeCheck (some 2) = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem membership_checks_3 :
    generatorRelations (some 3) = true ∧ cubeCheck (some 3) = true := by decide +kernel

end Checks

theorem pure_members (i : Option (Fin 4)) (x : pureTwo) :
    x ∈ pureNode i ↔ ∃ n ∈ members i, pureElement n = x := by
  apply pure_members_of_checks
  · cases i with
    | none => exact membership_checks_none.1
    | some j => fin_cases j
                · exact membership_checks_0.1
                · exact membership_checks_1.1
                · exact membership_checks_2.1
                · exact membership_checks_3.1
  · cases i with
    | none => exact membership_checks_none.2
    | some j => fin_cases j
                · exact membership_checks_0.2
                · exact membership_checks_1.2
                · exact membership_checks_2.2
                · exact membership_checks_3.2

theorem node_eq_map (i : Option (Fin 4)) : node i = (pureNode i).map inner := by
  cases i with
  | none => exact (Subgroup.map_bot inner).symm
  | some j =>
    ext x
    change x.val ∈ ambientRow j ↔ x ∈ (row j).map inner
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, he⟩
      exact ⟨z, hz, Subtype.ext he⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z.val, ⟨z, hz, rfl⟩, rfl⟩

theorem element_inner (n : Fin 1024) : element (false, n) = inner (pureElement n) := by
  change inner (pureElement n) * 1 = _
  exact mul_one _

theorem node_members (i : Option (Fin 4)) (x : outerRepresentative) :
    x ∈ node i ↔ ∃ n ∈ members i, element (false, n) = x := by
  rw [node_eq_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨n, hn, rfl⟩ := (pure_members i y).mp hy
    exact ⟨n, hn, element_inner n⟩
  · rintro ⟨n, hn, rfl⟩
    rw [element_inner]
    exact mem_map_of_mem inner ((pure_members i _).mpr ⟨n, hn, rfl⟩)

theorem word_mem_node (i : Option (Fin 4)) (w : List ℤ) (hw : w ∈ rowGenerators i) :
    inner (word w) ∈ node i := by
  rw [node_eq_map]
  apply mem_map_of_mem
  rw [pureNode_eq_closure]
  exact subset_closure (List.mem_map_of_mem hw)

theorem node_le_of_generators (i : Option (Fin 4)) (K : Subgroup outerRepresentative)
    (h : ∀ w ∈ rowGenerators i, inner (word w) ∈ K) : node i ≤ K := by
  rw [node_eq_map, map_le_iff_le_comap, pureNode_eq_closure]
  apply (closure_le _).mpr
  intro x hx
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hx
  exact h w hw

end CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile.CoverageData.ElementaryCatalogue.InnerExtensions
