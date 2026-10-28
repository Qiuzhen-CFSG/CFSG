module

public import Theory.SpecificGroups.SymmetricSix.Parabolics.QuadrangleActions
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Three-point relations from a line-stabilizer orbit plane

Flag transitivity puts the three base-line images into the orbit plane. Three
distinct nonzero vectors in a binary plane sum to zero, as checked in its
four-element coordinate model. Syntheme transitivity transports this relation
to every line. The syntheme action is always named explicitly, since the global
action on the shared `Fin 15` carrier is the duad action.

Source: Aschbacher–Smith, G.5.3(6), printed pp.343–344 (PDF pp.354–355).
-/

public section

open Theory.SpecificGroups.SymmetricSix

namespace BinaryDuadStructure.OrbitRelations
variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

private theorem binary_plane_triple (P : Submodule (ZMod 2) W)
    (hdim : Module.finrank (ZMod 2) P = 2)
    (a b c : P) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : a + b + c = 0 := by
  let : Module.Finite (ZMod 2) P := Module.finite_of_finrank_eq_succ hdim
  let e : P ≃ₗ[ZMod 2] (Fin 2 → ZMod 2) := LinearEquiv.ofFinrankEq _ _ (by simp [hdim])
  have hsmall : ∀ a b c : Fin 2 → ZMod 2, a ≠ 0 → b ≠ 0 → c ≠ 0 →
      a ≠ b → a ≠ c → b ≠ c → a + b + c = 0 := by decide
  apply e.injective
  simpa only [map_add, map_zero] using hsmall (e a) (e b) (e c)
    (by simpa using ha) (by simpa using hb) (by simpa using hc)
    (e.injective.ne hab) (e.injective.ne hac) (e.injective.ne hbc)

private theorem mem_syntheme_stabilizer (g : A6) :
    g ∈ a6SynthemeStabilizer ↔ synthemeAct g.val 0 = 0 := by
  rw [← a6_syntheme_stabilizer_zero]
  rfl

private theorem base_orbit (d : Duad) (hd : incident d 0) :
    ∃ g : a6SynthemeStabilizer, g.val • (0 : Duad) = d := by
  obtain ⟨g, hg, hs⟩ := a6_flag_transitive 0 d 0 0 (by decide) hd
  exact ⟨⟨g, (mem_syntheme_stabilizer g).mpr hs⟩, hg⟩

private theorem base_relation (ρ : Representation (ZMod 2) A6 W) (v : Duad → W)
    (hnonzero : ∀ d, v d ≠ 0) (hinj : Function.Injective v)
    (hequiv : ∀ g d, v (g • d) = ρ g (v d))
    (hdim : Module.finrank (ZMod 2)
      (Submodule.span (ZMod 2) (Set.range (fun g : a6SynthemeStabilizer => ρ g.val (v 0)))) = 2) :
    ∑ d ∈ synthemeDuads 0, v d = 0 := by
  let P := Submodule.span (ZMod 2)
    (Set.range (fun g : a6SynthemeStabilizer => ρ g.val (v 0)))
  have hmem (d : Duad) (hd : d ∈ synthemeDuads 0) : v d ∈ P := by
    obtain ⟨g, hg⟩ := base_orbit d hd
    apply Submodule.subset_span
    refine ⟨g, ?_⟩
    change ρ g.val (v 0) = v d
    rw [← hequiv, hg]
  obtain ⟨a, b, c, hab, hac, hbc, hset⟩ := Finset.card_eq_three.mp (syntheme_is_partition 0).1
  have ha : a ∈ synthemeDuads 0 := by simp [hset]
  have hb : b ∈ synthemeDuads 0 := by simp [hset]
  have hc : c ∈ synthemeDuads 0 := by simp [hset]
  have h := binary_plane_triple P hdim ⟨v a, hmem a ha⟩ ⟨v b, hmem b hb⟩ ⟨v c, hmem c hc⟩
    (fun h => hnonzero a (congrArg Subtype.val h))
    (fun h => hnonzero b (congrArg Subtype.val h))
    (fun h => hnonzero c (congrArg Subtype.val h))
    (fun h => hab (hinj (congrArg Subtype.val h)))
    (fun h => hac (hinj (congrArg Subtype.val h)))
    (fun h => hbc (hinj (congrArg Subtype.val h)))
  have hval := congrArg Subtype.val h
  simpa [hset, hab, hac, hbc, add_assoc] using hval

/-- An injective equivariant duad configuration whose base line orbit spans a
binary plane satisfies all three-point line relations. The source application
constructs the configuration and proves injectivity from the point stabilizer. -/
theorem line_relations_of_injective_orbit_plane (ρ : Representation (ZMod 2) A6 W) (v : Duad → W)
    (hnonzero : ∀ d, v d ≠ 0) (hinj : Function.Injective v)
    (hequiv : ∀ g d, v (g • d) = ρ g (v d))
    (hdim : Module.finrank (ZMod 2)
      (Submodule.span (ZMod 2) (Set.range (fun g : a6SynthemeStabilizer => ρ g.val (v 0)))) = 2)
    (s : Syntheme) : ∑ d ∈ Finset.univ.filter (fun d => incident d s), v d = 0 := by
  have hs : Finset.univ.filter (fun d => incident d s) = synthemeDuads s := by
    ext d
    exact ⟨fun h => (Finset.mem_filter.mp h).2,
      fun h => Finset.mem_filter.mpr ⟨Finset.mem_univ d, h⟩⟩
  rw [hs]
  obtain ⟨g, rfl⟩ := a6_syntheme_transitive 0 s
  rw [synthemeDuads_act, Finset.sum_image]
  · change ∑ d ∈ synthemeDuads 0, v (g • d) = 0
    simp_rw [hequiv]
    rw [← map_sum, base_relation ρ v hnonzero hinj hequiv hdim, map_zero]
  · intro a _ b _ h
    exact (MulAction.injective g.val) h

end BinaryDuadStructure.OrbitRelations
