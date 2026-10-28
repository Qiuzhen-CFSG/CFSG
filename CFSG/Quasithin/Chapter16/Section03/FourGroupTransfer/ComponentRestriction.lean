module

public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.Contracts

/-!
# Component restriction and faithful enlargement actions

The normal subgroup E chosen in 16.3.8 has order four and need not be
elementary abelian. For an element e of order four, first apply the
involution theorem to e². Since C_G(e) lies in C_G(e²) and still contains L,
restriction of components then gives the desired statement for e itself.
The component predicate in the result includes all nonidentity elements of E.

The same restriction principle shows that the E-action on a proper
quasisimple enlargement is faithful, the first step of 16.3.5.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
16.3.5–16.3.8, printed pp.1178–1180 / PDF pp.1195–1197.
-/

public section
namespace CFSG.Quasithin.Chapter16.FourGroupTransfer
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G]

/-- Restrict a component from the centralizer of a power to the
centralizer of the element, provided that the element centralizes it. -/
theorem component_of_component_power {L : Subgroup G} {e : G} (n : ℕ)
    (h : IsCentralizerComponent (e ^ n) L)
    (he : e ∈ centralizer (L : Set G)) : IsCentralizerComponent e L := by
  apply Theory.GroupTheory.IsComponentIn.restrict h
  · intro l hl
    exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp he l hl)
  · intro x hx
    exact mem_centralizer_singleton_iff.mpr
      ((show Commute x e from mem_centralizer_singleton_iff.mp hx).pow_right n)

/-- For an arbitrary subgroup of order four, its involutions suffice.
This retains the cyclic possibility and proves the missing order-four case. -/
theorem component_on_order_four_subgroup (E L : Subgroup G)
    (hcard : Nat.card E = 4) (hcentral : E ≤ centralizer (L : Set G))
    (hinvol : ∀ e : G, e ∈ E → orderOf e = 2 → IsCentralizerComponent e L) :
    ∀ e : G, e ∈ E → e ≠ 1 → IsCentralizerComponent e L := by
  intro e he hne
  have hd : orderOf e ∣ 4 := by
    have hh := orderOf_dvd_natCard (⟨e, he⟩ : E)
    rwa [← orderOf_coe (⟨e, he⟩ : E), hcard] at hh
  have hord : orderOf e = 2 ∨ orderOf e = 4 := by
    have hone : orderOf e ≠ 1 := fun hh => hne (orderOf_eq_one_iff.mp hh)
    have hd' : orderOf e = 1 ∨ orderOf e = 2 ∨ orderOf e = 4 := by
      have hle : orderOf e ≤ 4 := Nat.le_of_dvd (by decide) hd
      interval_cases h : orderOf e <;> norm_num at *
    exact hd'.resolve_left hone
  rcases hord with htwo | hfour
  · exact hinvol e he htwo
  · have hpow : orderOf (e ^ 2) = 2 := by
      rw [orderOf_pow', hfour]
      all_goals norm_num
    exact component_of_component_power 2 (hinvol (e ^ 2) (E.pow_mem he 2) hpow)
      (hcentral he)

/-- A proper subgroup of a quasisimple group cannot be a component of
a centralizer containing the whole overgroup. This supplies contrary
involutions from C_G(I) in 16.3.6. -/
theorem not_component_of_proper_quasisimple_overgroup {K I : Subgroup G} [IsQuasisimple I]
    (hKI : K < I) {e : G} (he : e ∈ centralizer (I : Set G)) :
    ¬ IsCentralizerComponent e K := by
  intro hK
  have hI : I ≤ involutionCentralizer e := fun x hx =>
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp he x hx)
  have hcomp := Theory.GroupTheory.IsComponentIn.restrict hK hKI.le hI
  have htop : IsComponent I (⊤ : Subgroup I) :=
    ⟨.top, IsQuasisimple.of_mulEquiv Subgroup.topEquiv.symm⟩
  have heq := hcomp.2.eq_of_le htop le_top
  exact hKI.not_ge (subgroupOf_eq_top.mp heq)

/-- In the proper quasisimple enlargement case of 16.3.5, the action of E
is faithful: a nonidentity kernel element would make K a component of I. -/
theorem faithful_inducedAction_of_components (E K I : Subgroup G) [IsQuasisimple I]
    (hKI : K < I) (hn : E ≤ normalizer (I : Set G))
    (hcomp : CentralizesAsComponent E K) :
    Function.Injective (inducedAction E I hn) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  apply (eq_bot_iff_forall _).mpr
  intro e he
  by_contra hne
  have heC : (e : G) ∈ centralizer (I : Set G) := by
    have heN : (⟨e, hn e.property⟩ : normalizer (I : Set G)) ∈ I.normalizerMonoidHom.ker := he
    rw [normalizerMonoidHom_ker] at heN
    exact heN
  have hene : (e : G) ≠ 1 := fun hh => hne (Subtype.ext hh)
  exact not_component_of_proper_quasisimple_overgroup hKI heC
    (hcomp e e.property hene)

end CFSG.Quasithin.Chapter16.FourGroupTransfer
