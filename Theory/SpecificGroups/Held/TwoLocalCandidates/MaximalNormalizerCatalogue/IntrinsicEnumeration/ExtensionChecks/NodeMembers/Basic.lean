module

public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.IntrinsicEnumeration.ExtensionChecks.Action

/-!
# Exact finite-list certificates for the Held nodes

Products selecting each listed generator zero or one times cover the subgroup
when the generators commute and square to one. Closure induction proves the
forward inclusion, and subgroup multiplication proves the reverse inclusion.
The four-point base then identifies this product list with a proposed list of
literal normal forms. Equality of the lists as finite sets allows duplicates;
no independence, ambient coverage or node structure is assumed.

The exported checker soundness theorem uses the actual Held action and the
unchanged original row generators. The numerical certificates are supplied in
`ExtensionChecks.NodeMembers`.

Source: the ATLAS HeG1-p2058B0 words and the original catalogue/normal-form data
in `MaximalNormalizerCatalogue/source/` and `IntrinsicEnumeration/source/`.
-/

namespace Held.TwoLocalCandidates.MaximalNormalizerCatalogue.IntrinsicEnumeration.ExtensionChecks.NodeMembers
variable {G : Type*} [Group G]
/-- Products selecting zero or one copy of each generator, in the original order. -/
@[expose] public def cube : List G → List G
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
open LocalPairs.SylowGeometry.Calculations

/-- Check the original generators are commuting involutions on the faithful base. -/
@[expose] public def generatorRelations (i : Option (Fin 22)) : Bool :=
  let gs := (rowGenerators i).map wordAction
  gs.all (fun g => sameAction (g * g) 1 &&
    gs.all (fun h => sameAction (g * h) (h * g)))

/-- Compare all binary products with the proposed normal-form list on the base. -/
@[expose] public def cubeCheck (i : Option (Fin 22)) (ns : List (Fin 1024)) : Bool :=
  (cube ((rowGenerators i).map wordAction)).isEqv
    (ns.map normalFormAction) sameAction

private abbrev rho : representative →* Equiv.Perm (Fin 2058) :=
  representation.comp representative.subtype

private theorem same_rho {x y : representative} :
    sameAction (rho x) (rho y) = true ↔ x = y := same_eq_true

private theorem list_eq_of_same (xs ys : List representative)
    (h : (xs.map rho).isEqv (ys.map rho) sameAction = true) : xs = ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all
  | cons x xs ih =>
    cases ys with
    | nil => simp at h
    | cons y ys =>
      have hh : sameAction (rho x) (rho y) = true ∧
          (xs.map rho).isEqv (ys.map rho) sameAction = true := by
        simpa only [List.map_cons, List.isEqv_cons_cons, Bool.and_eq_true] using h
      rw [same_rho.mp hh.1, ih ys hh.2]

private theorem relations_sound (i : Option (Fin 22)) (h : generatorRelations i = true) :
    (∀ g ∈ (rowGenerators i).map word, g * g = 1) ∧
    (∀ g ∈ (rowGenerators i).map word, ∀ k ∈ (rowGenerators i).map word,
      g * k = k * g) := by
  have hrel (w : List ℤ) (hw : w ∈ rowGenerators i) :
      sameAction (wordAction w * wordAction w) 1 = true ∧
      ((rowGenerators i).map wordAction).all
        (fun k => sameAction (wordAction w * k) (k * wordAction w)) = true := by
    simpa only [Bool.and_eq_true] using
      List.all_eq_true.mp h (wordAction w) (List.mem_map_of_mem hw)
  constructor
  · intro g hg
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hg
    apply same_rho.mp
    simpa only [map_mul, map_one, rho, MonoidHom.comp_apply, Subgroup.coe_subtype,
      ← wordAction_eq] using (hrel w hw).1
  · intro g hg k hk
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hg
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hk
    apply same_rho.mp
    simpa only [map_mul, rho, MonoidHom.comp_apply, Subgroup.coe_subtype,
      ← wordAction_eq] using
      List.all_eq_true.mp (hrel w hw).2 (wordAction v) (List.mem_map_of_mem hv)

private theorem node_eq_closure (i : Option (Fin 22)) :
    node i = Subgroup.closure {g | g ∈ (rowGenerators i).map word} := by
  cases i with
  | none => simp [node, rowGenerators]
  | some j => simp only [node, entry, rowGenerators, List.mem_map]

/-- Checked relations and word identities certify both directions of node membership.
The finite-set equality compares the proposed product ordering with the unchanged
membership list; it need not preserve order or multiplicities. -/
public theorem members_of_checks (i : Option (Fin 22)) (ns : List (Fin 1024))
    (hrel : generatorRelations i = true) (hcube : cubeCheck i ns = true)
    (hns : ns.toFinset = (members i).toFinset) (x : representative) :
    x ∈ node i ↔ ∃ m ∈ members i, normalForm m = x := by
  obtain ⟨hsq, hcomm⟩ := relations_sound i hrel
  have heq : cube ((rowGenerators i).map word) = ns.map normalForm := by
    apply list_eq_of_same
    rw [cube_map]
    simpa only [cubeCheck, List.map_map, Function.comp_def, rho, MonoidHom.comp_apply,
      Subgroup.coe_subtype, ← wordAction_eq, ← normalFormAction_eq] using hcube
  rw [node_eq_closure, closure_iff_cube _ hsq hcomm, heq, List.mem_map]
  have hm (m : Fin 1024) : m ∈ ns ↔ m ∈ members i := by
    simpa only [List.mem_toFinset] using
      (show m ∈ ns.toFinset ↔ m ∈ (members i).toFinset by rw [hns])
  simp only [hm]
end Held.TwoLocalCandidates.MaximalNormalizerCatalogue.IntrinsicEnumeration.ExtensionChecks.NodeMembers
