module

public import Theory.GroupAction.CardFourCubic
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus

/-!
# Cubic conjugation on a four-group

A cubic element which acts nontrivially on an ambient four-group leaves no
proper nontrivial subgroup invariant. Transport the intrinsic automorphism
lemma through the literal normalizer action. Consequently any nonidentity
point generates the four-group under a normalizing subgroup containing that
cubic element. This supplies the Cartan orbit step for the original V₁ in
Aschbacher–Smith 9.3.1, printed p.732 of the combined manuscript (1 March 2004).
-/

public section

open Subgroup Theory.GroupTheory
namespace Theory.GroupAction.CardFourCubic
variable {G : Type*} [Group G] [Finite G]

/-- Ambient subgroups normalized by the given cubic element are trivial or full. -/
theorem invariant_ambient_subgroup
    (V : Subgroup G) (hV : Nat.card V = 4)
    (d : G) (hdV : d ∈ normalizer (V : Set G)) (hd3 : d ^ 3 = 1)
    (hdC : d ∉ centralizer (V : Set G))
    (N : Subgroup G) (hNV : N ≤ V) (hdN : d ∈ normalizer (N : Set G)) :
    N = ⊥ ∨ N = V := by
  let a := V.normalizerMonoidHom ⟨d, hdV⟩
  have ha3 : a ^ 3 = 1 := by
    change V.normalizerMonoidHom ⟨d, hdV⟩ ^ 3 = 1
    rw [← map_pow]
    have he : (⟨d, hdV⟩ : normalizer (V : Set G)) ^ 3 = 1 := Subtype.ext hd3
    rw [he, map_one]
  have hane : a ≠ 1 := by
    intro he
    have hh : (⟨d, hdV⟩ : normalizer (V : Set G)) ∈ V.normalizerMonoidHom.ker := he
    rw [normalizerMonoidHom_ker] at hh
    exact hdC hh
  obtain hbot | htop := invariant_subgroup hV a ha3 hane (N.subgroupOf V)
    (fun x hx => (hdN (x : G)).mp hx)
  · left
    have he := congrArg (map V.subtype) hbot
    simpa only [map_subgroupOf_eq_of_le hNV, Subgroup.map_bot] using he
  · right
    have he := congrArg (map V.subtype) htop
    simpa only [map_subgroupOf_eq_of_le hNV, ← MonoidHom.range_eq_map, range_subtype] using he

/-- The original Cartan orbit of any nonidentity point fills the four-group. -/
theorem componentOrbit_zpowers_eq
    (V D : Subgroup G) (hV : Nat.card V = 4)
    (hDV : D ≤ normalizer (V : Set G))
    (d : G) (hdD : d ∈ D) (hd3 : d ^ 3 = 1)
    (hdC : d ∉ centralizer (V : Set G))
    (u : G) (huV : u ∈ V) (hu : u ≠ 1) :
    componentOrbit (zpowers u) D = V := by
  have hOV : componentOrbit (zpowers u) D ≤ V := by
    apply iSup_le
    intro a
    rintro _ ⟨x, hx, rfl⟩
    exact ((hDV a.property) x).mp ((zpowers_le.mpr huV) hx)
  obtain hb | he := invariant_ambient_subgroup V hV d (hDV hdD) hd3 hdC
    (componentOrbit (zpowers u) D) hOV
    (le_normalizer_componentOrbit (zpowers u) D hdD)
  · exact (hu (show u ∈ (⊥ : Subgroup G) from
      hb ▸ le_componentOrbit (zpowers u) D (mem_zpowers u))).elim
  · exact he

end Theory.GroupAction.CardFourCubic
