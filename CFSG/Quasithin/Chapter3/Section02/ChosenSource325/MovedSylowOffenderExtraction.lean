module
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedSylowOffenderRegular
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedSylowOffenderPair
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedSylowOffenderTransport

/-!
# Extracting an FF offender from a cubic constituent orbit

The same elementary actor is faithful on every summand of an independent
orbit. If it fixes every summand, the common fixed-codimension budget on
two distinct summands makes one an FF module. If it moves a summand, its
stabilizer is nontrivial, cubicity gives a two-summand orbit, and the swapped
pair calculation constructs an offender on that constituent. The actual
conjugation equivalence transports that offender to the original seed.

This proves precisely the single-normal-component FF extraction used in
D.3.5(2). It needs no starred-actor stabilization or natural-plus-dual
exclusion; those stronger conclusions are separate from FF extraction.
The actual chosen-module application is `SeedAlternativesMovedSylowOffender`.
Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
D.2.9, printed pp.180--182, and D.3.5(2), pp.195--196.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter3.Section02.ChosenSource325
variable {H W : Type*} [Group H] [Finite H] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W] (ρ : Representation (ZMod 2) H W)

/-- A moved constituent with faithful common actor is FF: the cubic orbit
has two members, and its stabilizer supplies the actual offender. -/
theorem isFFModule_of_cubic_moved_summand
    (I : Submodule (ZMod 2) W) (A : Subgroup H) (hA : IsElementaryTwo A)
    (hc : IsCubic ρ A) (hind : sSupIndep (subspaceOrbit ρ A I))
    (hdim : 2 < Module.finrank (ZMod 2) I)
    (hbound : fixedCodim ρ A ≤ 2 * rank A)
    (hk : subspaceKernel ρ I A = ⊥)
    {a : H} (ha : a ∈ A) (hm : I.map (ρ a) ≠ I) :
    IsFFModule (subspaceImageRepresentation ρ I) := by
  let : IsElementaryAbelian 2 A := hA.2
  let B := A ⊓ subspaceStabilizer ρ I
  have hB := cubic_stabilizer_ne_bot ρ I A hA hc hind hdim hbound
  obtain ⟨b,hb,hb1⟩ := (Subgroup.bot_or_exists_ne_one _).resolve_left hB
  have hn : ∃ v ∈ I, ρ b v ≠ v := by
    by_contra! hn
    exact hb1 (mem_bot.mp (hk.le ⟨hb.1,hn⟩))
  have ha2 : a*a = 1 := by
    simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) a ha
  have htwo : ∀ c ∈ A, I.map (ρ c) = I ∨ I.map (ρ c) = I.map (ρ a) :=
    fun c hcA => cubic_orbit_eq_self_or_moving_of_noncentral_stabilizer
    ρ I A hc hind ha ha2 hm hb.1 hb.2 hn hcA
  have hImem : I ∈ subspaceOrbit ρ A I := by
    refine ⟨1,?_⟩
    simp only [Subgroup.coe_one,map_one,Module.End.one_eq_id,Submodule.map_id]
  have hd := hind.pairwiseDisjoint hImem ⟨⟨a,ha⟩,rfl⟩ hm.symm
  have hkB : subspaceKernel ρ I B = ⊥ := by
    apply bot_unique
    intro g hg
    exact hk.le ⟨hg.1.1,hg.2⟩
  have hI : I ≠ ⊥ := Submodule.nontrivial_iff_ne_bot.mp
    (Module.nontrivial_of_finrank_pos (by omega : 0 < Module.finrank (ZMod 2) I))
  exact ⟨_,pair_stabilizer_isOffender ρ I hI A hA ha ha2 hd hm htwo hB hkB hbound⟩

/-- A common cubic actor of ratio at most two forces an FF constituent in a
nontrivial independent orbit, provided it is faithful on every constituent.
All comparisons use the one original actor, even in the moved branch. -/
theorem isFFModule_of_cubic_actor_on_independent_orbit
    (I : Submodule (ZMod 2) W) (A : Subgroup H) (hA : IsElementaryTwo A)
    (hc : IsCubic ρ A) (hind : sSupIndep (subspaceOrbit ρ ⊤ I))
    (hdim : 2 < Module.finrank (ZMod 2) I)
    (hbound : fixedCodim ρ A ≤ 2 * rank A)
    (hk : ∀ t : H, subspaceKernel ρ (I.map (ρ t)) A = ⊥)
    (hm : ∃ t : H, I.map (ρ t) ≠ I) : IsFFModule (subspaceImageRepresentation ρ I) := by
  classical
  by_cases hstable : ∀ t : H, A ≤ subspaceStabilizer ρ (I.map (ρ t))
  · obtain ⟨t,ht⟩ := hm
    have hsI : A ≤ subspaceStabilizer ρ I := by
      simpa only [map_one,Module.End.one_eq_id,Submodule.map_id] using hstable 1
    have hkI : subspaceKernel ρ I A = ⊥ := by
      simpa only [map_one,Module.End.one_eq_id,Submodule.map_id] using hk 1
    have hi : I ∈ subspaceOrbit ρ ⊤ I := by
      refine ⟨1,?_⟩
      simp only [Subgroup.coe_one,map_one,Module.End.one_eq_id,Submodule.map_id]
    have hd := hind.pairwiseDisjoint hi ⟨⟨t,mem_top _⟩,rfl⟩ ht.symm
    rcases common_actor_offends_one_of_pair ρ I (I.map (ρ t)) hA hsI
      (hstable t) hd hkI (hk t) hbound with hi | hj
    · exact ⟨_,hi⟩
    · exact isFFModule_of_conjugate_image ρ I t ⟨_,hj⟩
  · push Not at hstable
    obtain ⟨t,ht⟩ := hstable
    obtain ⟨a,ha,has⟩ := Set.not_subset.mp ht
    have hm : (I.map (ρ t)).map (ρ a) ≠ I.map (ρ t) :=
      fun he => has ((subspace_map_eq_iff ρ (I.map (ρ t)) a).mp he)
    have hi : sSupIndep (subspaceOrbit ρ A (I.map (ρ t))) := by
      apply hind.mono
      rintro _ ⟨b,rfl⟩
      refine ⟨⟨b*t,mem_top _⟩,?_⟩
      exact subspace_map_mul ρ I b t
    have hd : 2 < Module.finrank (ZMod 2) (I.map (ρ t)) := by
      rwa [finrank_map_action]
    exact isFFModule_of_conjugate_image ρ I t
      (isFFModule_of_cubic_moved_summand ρ (I.map (ρ t)) A hA hc hi hd hbound (hk t) ha hm)

end CFSG.Quasithin.Chapter3.Section02.ChosenSource325
