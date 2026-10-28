module
public import Theory.SpecificGroups.SymplecticFour.TwoConjugate.CentralPlacement

/-!
# The moving-actor source pair

The exceptional coordinate map sends the two root axes to one another. Thus
nontrivial stable V lies in neither axis. Setwise stability also excludes every
diagonal line for |V|>2. Combining central placement with the actual opposite
operators proves the F-irreducibility required by E.2.7, pp.219–220.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.SpecificGroups.SymplecticFour
open DiagramAutomorphisms EvenBorelTorus CentralRootGeometry
open Representation.OneCohomology.SymplecticFour
namespace Theory.SpecificGroups.SymplecticFour.TwoConjugate
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
private theorem upper_injective {s t u v : F} (he : upper s t = upper u v) :
    s=u ∧ t=v := by
  have hh : parameter (Multiplicative.ofAdd s,Multiplicative.ofAdd t) =
      parameter (Multiplicative.ofAdd u,Multiplicative.ofAdd v) := by
    simpa only [parameter_apply,toAdd_ofAdd,upper] using he
  have h := parameter_injective hh
  exact ⟨congrArg (fun x : Multiplicative F × Multiplicative F => x.1.toAdd) h,
    congrArg (fun x : Multiplicative F × Multiplicative F => x.2.toAdd) h⟩

private theorem upper_mem_long (s t:F) :
    upper s t ∈ RootSubgroup.group 0 ↔ t=0 := by
  rw [RootSubgroup.mem_group_iff]
  constructor
  · rintro ⟨z,hz⟩
    have hh : upper z 0 = upper s t := by simpa [upper,RootSubgroup.element_zero] using hz
    exact (upper_injective hh).2.symm
  · rintro rfl
    exact ⟨s,by simp [upper,RootSubgroup.element_zero]⟩

private theorem upper_mem_short (s t:F) :
    upper s t ∈ RootSubgroup.group 4 ↔ s=0 := by
  rw [RootSubgroup.mem_group_iff]
  constructor
  · rintro ⟨z,hz⟩
    have hh : upper 0 z = upper s t := by simpa [upper,RootSubgroup.element_zero] using hz
    exact (upper_injective hh).1.symm
  · rintro rfl
    exact ⟨t,by simp [upper,RootSubgroup.element_zero]⟩

/-- Diagram stability forbids either individual root axis for nontrivial V. -/
theorem not_root_axes_of_moving_actor (hq : 2 < Nat.card F)
    (a : ActorReduction.stabilizer (F := F)) (ha : ¬PreservesDiagram a.val)
    (V : Subgroup (Sp F)) (hV : V.map a.val.toMonoidHom = V) (hne : V≠⊥) :
    (¬V ≤ RootSubgroup.group 0) ∧ (¬V ≤ RootSubgroup.group 4) := by
  obtain ⟨σ,c,d,hc,hd,hcoord⟩ := moving_actor_coordinates hq a ha
  obtain ⟨x,hx,hx1⟩ := SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr hne)
  have hxne : x≠1 := by simpa using hx1
  constructor
  · intro h
    obtain ⟨s,rfl⟩ := (RootSubgroup.mem_group_iff 0 _).mp (h hx)
    have hs : s≠0 := by intro he; apply hxne; simp [he,RootSubgroup.element_zero]
    have hm : a.val (upper s 0) ∈ V := hV.le (mem_map_of_mem a.val.toMonoidHom
      (by simpa [upper,RootSubgroup.element_zero] using hx))
    rw [hcoord] at hm
    have hh := (upper_mem_long _ _).mp (h hm)
    exact (mul_ne_zero hd ((map_ne_zero σ).mpr hs)) hh
  · intro h
    obtain ⟨t,rfl⟩ := (RootSubgroup.mem_group_iff 4 _).mp (h hx)
    have ht : t≠0 := by intro he; apply hxne; simp [he,RootSubgroup.element_zero]
    have hm : a.val (upper 0 t) ∈ V := hV.le (mem_map_of_mem a.val.toMonoidHom
      (by simpa [upper,RootSubgroup.element_zero] using hx))
    rw [hcoord] at hm
    have hh := (upper_mem_short _ _).mp (h hm)
    exact (mul_ne_zero hc (pow_ne_zero _ ((map_ne_zero σ).mpr ht))) hh

/-- The actual moving-actor source implies irreducibility of the opposite
pair directly; root-axis and diagonal alternatives have been discharged. -/
theorem pairAction_irreducible_of_moving_actor (hq : 2 < Nat.card F)
    (a : ActorReduction.stabilizer (F := F)) (ha : ¬PreservesDiagram a.val)
    (V : Subgroup (Sp F)) (hV : V.map a.val.toMonoidHom = V)
    (hc : V ≤ (center (unipotent (F := F))).map (unipotent (F := F)).subtype)
    (hr : 2 < Nat.card V) : Representation.IsIrreducible (pairAction V) := by
  have hne : V≠⊥ := by intro he; subst V; simp at hr
  obtain ⟨hl,hs⟩ := not_root_axes_of_moving_actor hq a ha V hV hne
  exact pairAction_irreducible_of_no_diagonal V (parameter_range (F := F) ▸ hc)
    hl hs (not_diagonal_of_moving_actor hq a ha V hV hr)

end Theory.SpecificGroups.SymplecticFour.TwoConjugate
