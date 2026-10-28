module

public import CFSG.Quasithin.Chapter16.Section01To02.SourceHypothesis
public import CFSG.Quasithin.ChapterI.Section06To08.TightPGroup.Intersection
public import Theory.GroupTheory.PrimeRankElementary

/-!
# Inputs and conjugation geometry for 16.2.11–16.2.12

The inputs below are the actual local configuration and the preceding
16.2.5–16.2.10 conclusions. They do not assert tight embedding, triviality of
the two-core, or control of the Sylow conjugacy class. In particular `H` and
`L₀` are the normalizer and local component closure already defined in §16.2.

Conjugation is left conjugation. Thus the book's `L^g` is represented by
`conjSubgroup L g⁻¹`. The symmetric version of 16.2.8(3) for `⟨z⟩L` is obtained
from its printed version for `⟨z⟩Lᵘ` by conjugating with the swapping element.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
pp.1174–1176. These are conditional interfaces, not proofs of those inputs.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter16.CoverAndSylowElimination

open Subgroup Theory.GroupTheory ChapterI.Section06To08

variable {G : Type*} [Group G]

/-- The first omega subgroup of the actual component Sylow, in ambient `G`. -/
def sylowOmega (T : Sylow 2 G) (L : Subgroup G) : Subgroup G :=
  (omega₁ (componentSylow T L) (p := 2)).map (componentSylow T L).subtype

/-- The center of the actual component, in ambient `G`. -/
def componentCenter (L : Subgroup G) : Subgroup G := (center L).map L.subtype

/-- The earlier local conclusions consumed by the two elimination arguments.
The assembly owner must derive these from the genuine nonnormal-component
counterexample; none is an elimination conclusion. -/
structure EarlierConclusions (T : Sylow 2 G) (z u : G) (L : Subgroup G) : Prop where
  localSetup : CentralComponentSetup T z L
  not_normal : ¬ (L.subgroupOf (involutionCentralizer z)).Normal
  u_mem : u ∈ T
  u_not_normalizer : u ∉ normalizer (L : Set G)
  closure_eq : localComponentClosure z L = L ⊔ conjSubgroup L u
  sylow_le : (T : Subgroup G) ≤ localComponentNormalizer z L
  commuting : L ≤ centralizer (conjSubgroup L u : Set G)
  permutes : ∀ g ∈ localComponentNormalizer z L,
    conjSubgroup L g = L ∨ conjSubgroup L g = conjSubgroup L u
  index_sylow : (normalizer (L : Set G)).relIndex (T : Subgroup G) = 2
  index_local : (normalizer (L : Set G)).relIndex (localComponentNormalizer z L) = 2
  intersection_le_center : L ⊓ conjSubgroup L u ≤ componentCenter L
  normalizer_control : ∀ X : Subgroup G, IsPGroup 2 X → X ≠ ⊥ →
    X ≤ zpowers z ⊔ L → normalizer (X : Set G) ≤ localComponentNormalizer z L
  noncontainment : ∀ g ∉ localComponentNormalizer z L,
    ¬ localComponentClosure z L ≤ conjSubgroup (localComponentNormalizer z L) g
  external_involution : ∃ g ∉ localComponentNormalizer z L, ∃ i : G,
    orderOf i = 2 ∧ i ∈ conjSubgroup L g ∧
      i ∈ localComponentNormalizer z L ⊓ normalizer (L : Set G)

variable {T : Sylow 2 G} {z u : G} {L : Subgroup G}

theorem sylowOmega_le : sylowOmega T L ≤ componentSylow T L := map_subtype_le _

theorem componentCenter_le : componentCenter L ≤ L := map_subtype_le _

theorem componentCenter_eq_bot (hc : center L = ⊥) : componentCenter L = ⊥ := by
  simp only [componentCenter, hc, Subgroup.map_bot]

namespace EarlierConclusions
variable (h : EarlierConclusions T z u L)
include h

/-- Transport normalizer control to every conjugate of `⟨z⟩L`. -/
theorem conjugate_normalizer_control (g : G) {X : Subgroup G}
    (hp : IsPGroup 2 X) (hne : X ≠ ⊥)
    (hle : X ≤ conjSubgroup (zpowers z ⊔ L) g) :
    normalizer (X : Set G) ≤ conjSubgroup (localComponentNormalizer z L) g := by
  have hback : conjSubgroup X g⁻¹ ≤ zpowers z ⊔ L := by
    simpa only [conjSubgroup_inv] using conjSubgroup_mono hle g⁻¹
  have hbackne : conjSubgroup X g⁻¹ ≠ ⊥ := by
    intro he
    have := congrArg (fun Y => conjSubgroup Y g) he
    rw [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one] at this
    exact hne (by simpa only [conjSubgroup, Subgroup.map_bot] using this)
  have hn := h.normalizer_control _ (hp.map _) hbackne hback
  have hn' := conjSubgroup_mono hn g
  have he : conjSubgroup (normalizer (conjSubgroup X g⁻¹ : Set G)) g =
      normalizer (X : Set G) := by
    rw [conjSubgroup, map_equiv_normalizer_eq]
    change normalizer (conjSubgroup (conjSubgroup X g⁻¹) g : Set G) = _
    rw [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one]
  exact he.symm.le.trans hn'

/-- Centralizers of the same nontrivial two-subgroups satisfy the same bound. -/
theorem conjugate_centralizer_control (g : G) {X : Subgroup G}
    (hp : IsPGroup 2 X) (hne : X ≠ ⊥)
    (hle : X ≤ conjSubgroup (zpowers z ⊔ L) g) :
    centralizer (X : Set G) ≤ conjSubgroup (localComponentNormalizer z L) g :=
  (centralizer_le_normalizer _).trans (h.conjugate_normalizer_control g hp hne hle)

/-- The reverse containment is excluded too; this is the orientation needed
at the end of 16.2.12. -/
theorem conjugate_noncontainment {g : G} (hg : g ∉ localComponentNormalizer z L) :
    ¬ conjSubgroup (localComponentClosure z L) g ≤ localComponentNormalizer z L := by
  intro hle
  have hg' : g⁻¹ ∉ localComponentNormalizer z L := by
    simpa only [inv_mem_iff] using hg
  apply h.noncontainment g⁻¹ hg'
  simpa only [conjSubgroup_inv] using conjSubgroup_mono hle g⁻¹

/-- The swapped component has precisely the conjugate Sylow intersection. -/
theorem swapped_sylow : conjSubgroup (componentSylow T L) u =
    componentSylow T (conjSubgroup L u) := by
  have ht : conjSubgroup (T : Subgroup G) u = T :=
    mem_normalizer_iff_map_conj_eq.mp ((T : Subgroup G).le_normalizer h.u_mem)
  change ((T : Subgroup G) ⊓ L).map (MulAut.conj u).toMonoidHom = _
  rw [map_inf _ _ _ (MulAut.conj u).injective]
  change conjSubgroup (T : Subgroup G) u ⊓ conjSubgroup L u = _
  rw [ht]
  rfl

end EarlierConclusions
end CFSG.Quasithin.Chapter16.CoverAndSylowElimination
