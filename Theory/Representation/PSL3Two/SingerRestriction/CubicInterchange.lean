module

public import Theory.Representation.PSL3Two.SingerRestriction.CubicInterchange.Canonical
public import Theory.Representation.PSL3Two.SingerRestriction.CubicInterchange.Conjugacy
public import Theory.Representation.PSL3Two.SingerRestriction.CubicInterchange.Transport

/-!
# Interchanging the cubic fixed lines of Singer moving constituents

Simultaneous conjugacy aligns an arbitrary Singer–cubic pair with the explicit
matrices. Pulling back the moving subspace preserves Singer invariance,
disjointness from the fixed plane, and transitivity off zero. The checked
canonical calculation constructs an outer involution normalizing the Singer
group and centralizing the cubic group, together with a commuting inner
involution that swaps the same fixed vectors. The action equality uses the
actual steinbergAut extension and SteinbergStructure.autEquiv.

The five-space specialization applies this result to the literal displacement
span. The Chapter J adapter supplies its hypotheses from centralizer geometry.

Source: Aschbacher–Smith J.2.3(7), printed p.434 (PDF p.445),
combined manuscript of 1 March 2004.
-/

public section

open Representation Representation.BinaryOffender Representation.RegularCyclicNormalClosure
open Subgroup
namespace BinaryLinearThree.SingerRestriction.CubicInterchange
open Matrix.PSL3Two.OuterInvolutionSinger FiveSpace.Certificate
noncomputable section
local instance : AddCommGroup Steinberg := inferInstance
local instance : Module (ZMod 2) Steinberg := inferInstance

/-- The source's outer involution and a commuting inner involution exchange
both cubic fixed lines of the Singer moving constituents. -/
theorem exists_interchange (H D : Subgroup Group) (hH : Nat.card H = 7)
    (hD : Nat.card D = 3) (hDH : D ≤ normalizer H)
    (M : Submodule (ZMod 2) Steinberg)
    (hM : ∀ h ∈ H, ∀ v ∈ M, S h v ∈ M)
    (hd : fixedSpace S H ⊓ M = ⊥)
    (ht : ∀ v ∈ M, v ≠ 0 → ∀ w ∈ M, w ≠ 0 → ∃ h ∈ H, S h v = w) :
    ∃ (j : MulAut Group) (g : Group),
      j ^ 2 = 1 ∧ j ∉ MulAut.innerSubgroup Group ∧ H.map j.toMonoidHom = H ∧
      (∀ d ∈ D, j d = d) ∧ g ^ 2 = 1 ∧ g ≠ 1 ∧ g ∈ normalizer D ∧ j g = g ∧
      (∀ v ∈ M, v ≠ 0 → v ∈ fixedSpace S D →
        S g v = SteinbergStructure.autEquiv j v ∧ S g v ≠ v) := by
  obtain ⟨t,heH,heD⟩ := pair_conjugacy H D hH hD hDH
  have hc (N : Submodule (ZMod 2) Steinberg)
      (hN : ∀ h ∈ zpowers singer, ∀ u ∈ N, S h u ∈ N)
      (hdN : fixedSpace S (zpowers singer) ⊓ N = ⊥)
      (htN : ∀ u ∈ N, u ≠ 0 → ∀ w ∈ N, w ≠ 0 → ∃ h ∈ zpowers singer, S h u = w)
      (u : Steinberg) (hu : u ∈ N) (hu0 : u ≠ 0)
      (huC : u ∈ fixedSpace S (zpowers cubic)) :
      S inner u = AutomorphismAction.steinbergAut outer u ∧ S inner u ≠ u := by
    have hh := canonical_interchange N hN hdN htN u hu hu0 huC
    exact ⟨hh.1.trans (autEquiv_action outer u),hh.2⟩
  obtain ⟨j,g,h1,h2,h3,h4,h5,h6,h7,h8,hm⟩ := transport_interchange
    S AutomorphismAction.steinbergAut AutomorphismAction.steinbergAut_comp_conj
    (zpowers singer) (zpowers cubic) H D t heH heD outer inner
    outer_sq outer_not_inner outer_normalizes outer_centralizes
    inner_sq inner_ne_one inner_normalizes outer_inner hc M hM hd ht
  refine ⟨j,g,h1,h2,h3,h4,h5,h6,h7,h8,?_⟩
  intro v hv hv0 hvD
  have hh := hm v hv hv0 hvD
  exact ⟨hh.1.trans (autEquiv_action j v).symm,hh.2⟩

/-- Every nonzero cubic fixed vector in a Singer moving constituent is moved
by an element of the actual cubic normalizer. -/
theorem exists_moving_normalizer (H D : Subgroup Group) (hH : Nat.card H = 7)
    (hD : Nat.card D = 3) (hDH : D ≤ normalizer H)
    (M : Submodule (ZMod 2) Steinberg)
    (hM : ∀ h ∈ H, ∀ v ∈ M, S h v ∈ M)
    (hd : fixedSpace S H ⊓ M = ⊥)
    (ht : ∀ v ∈ M, v ≠ 0 → ∀ w ∈ M, w ≠ 0 → ∃ h ∈ H, S h v = w)
    (v : Steinberg) (hv : v ∈ M) (hv0 : v ≠ 0) (hvD : v ∈ fixedSpace S D) :
    ∃ g : Group, g ∈ normalizer D ∧ S g v ≠ v := by
  obtain ⟨j,g,_,_,_,_,_,_,hg,_,hm⟩ := exists_interchange H D hH hD hDH M hM hd ht
  exact ⟨g,hg,(hm v hv hv0 hvD).2⟩

/-- The literal displacement-span formulation for an invariant five-space. -/
theorem fiveSpace_movement (H D : Subgroup Group) (hH : Nat.card H = 7)
    (hD : Nat.card D = 3) (hDH : D ≤ normalizer H)
    (A : Submodule (ZMod 2) Steinberg) (hA5 : Module.finrank (ZMod 2) A = 5)
    (hFA : fixedSpace S H ≤ A) (hA : ∀ h ∈ H, ∀ a ∈ A, S h a ∈ A)
    (v : Steinberg) (hv : v ∈ displacementSpan S H A) (hv0 : v ≠ 0)
    (hvD : v ∈ fixedSpace S D) : ∃ g : Group, g ∈ normalizer D ∧ S g v ≠ v :=
  exists_moving_normalizer H D hH hD hDH _ (FiveSpace.moved_mem H A hA)
    (FiveSpace.decomposition H hH A hA5 hFA hA).2.2
    (FiveSpace.transitive H hH A hA5 hFA hA) v hv hv0 hvD
end
end BinaryLinearThree.SingerRestriction.CubicInterchange
