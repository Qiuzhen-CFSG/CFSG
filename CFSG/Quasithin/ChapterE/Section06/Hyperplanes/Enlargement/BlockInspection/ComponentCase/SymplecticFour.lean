module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.ComponentCase.ModelExclusions
public import Theory.SpecificGroups.SymplecticFour.RootSubgroup.ElementCentralizer


/-!
# Excluding the parameter-four symplectic root action in E.6.23

The fixed space A has corank two, so a hyperplane U contains an element
acting nontrivially on X. The actual root-action isomorphism expresses this
as conjugation by a nonidentity root matrix on the derived symplectic carrier.
The matrix calculation shows that every element of X centralizing this actor
centralizes the entire root action, and hence V. Thus C_X(U) lies in C_G(V),
which lies in M by E.6.1. An escaping small block cannot lie in C_X(U).

This stronger centralizer containment handles every possible subnormal block
at once. It requires neither normality of the small block nor an identification
of the distinct A₅ and SL₂(4) modules. The comparison with the full matrix group
is the actual derived-subgroup inclusion in `derived_fixed_of_ne_zero`.
All fields, equivalences and root parameters come from SymplecticRootAction.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.23,
printed p.254 (PDF p.265), and E.6.8(2b), printed p.247 (PDF p.258).
-/

public section

open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.SymplecticFour
open Representation.OneCohomology.SymplecticFour
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.ComponentCase
open Components
variable {G : Type*} [Group G] [Finite G] {M V : Subgroup G}

/-- A hyperplane acting nontrivially through a symplectic root has the same
centralizer inside X as the whole acting subgroup V. The containment below
is the direction needed to exclude every escaping subgroup of C_X(U). -/
theorem symplectic_root_centralizer_le [IsElementaryAbelian 2 V]
    {U A X : Subgroup G} {n : ℕ}
    (hUh : IsHyperplane V U) (hc : subgroupCorank V A = 2)
    (hfixed : V ⊓ centralizer (X : Set G) = A)
    (hroot : SymplecticRootAction X V n) :
    X ⊓ centralizer (U : Set G) ≤ centralizer (V : Set G) := by
  have hnUA : ¬ U ≤ A := by
    intro hh
    have := subgroupCorank_antitone (V := V) hh
    rw [hc, hUh.2] at this
    omega
  obtain ⟨u, hu, huA⟩ := Set.not_subset.mp hnUA
  have huV := hUh.1 hu
  have huC : u ∉ centralizer (X : Set G) := by
    intro hh
    exact huA (hfixed ▸ (show u ∈ V ⊓ centralizer (X : Set G) from ⟨huV, hh⟩))
  obtain ⟨hVN, F, _, _, _, e, r, haction⟩ := hroot
  have parameter (v : G) (hv : v ∈ V) :
      ∃ t : F, ∀ x : X,
        e (X.normalizerMonoidHom ⟨v, hVN hv⟩ x) =
          (MulAut.conjNormal (H := commutator (Sp F)) (rootElement r t)) (e x) := by
    have hm : (MulAut.congr e) (X.normalizerMonoidHom ⟨v, hVN hv⟩) ∈
        (RootSubgroup.group r).map (MulAut.conjNormal (H := commutator (Sp F))) := by
      rw [RootSubgroup.group, ← haction]
      exact ⟨_, ⟨_, ⟨⟨v, hVN hv⟩, hv, rfl⟩, rfl⟩, rfl⟩
    obtain ⟨g, hg, he⟩ := hm
    obtain ⟨t, rfl⟩ := (RootSubgroup.mem_group_iff r g).mp hg
    refine ⟨t, fun x => ?_⟩
    have hh := congrArg (fun a : MulAut (commutator (Sp F)) => a (e x)) he
    change (MulAut.conjNormal (H := commutator (Sp F)) (rootElement r t)) (e x) =
      e (X.normalizerMonoidHom ⟨v, hVN hv⟩ (e.symm (e x))) at hh
    simpa only [e.symm_apply_apply] using hh.symm
  obtain ⟨t, ht⟩ := parameter u huV
  have ht0 : t ≠ 0 := by
    intro hz
    apply huC
    apply mem_centralizer_iff.mpr
    intro x hx
    have he := ht ⟨x, hx⟩
    simp only [hz, RootSubgroup.element_zero, map_one, MulAut.one_apply] at he
    have hh := congrArg (fun y : X => (y : G)) (e.injective he)
    change u * x * u⁻¹ = x at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  intro l hl
  let x : X := ⟨l, hl.1⟩
  have huFix : X.normalizerMonoidHom ⟨u, hVN huV⟩ x = x := by
    apply Subtype.ext
    change u * l * u⁻¹ = l
    rw [mem_centralizer_iff.mp hl.2 u hu, mul_inv_cancel_right]
  have htFix : (MulAut.conjNormal (H := commutator (Sp F))
      (rootElement r t)) (e x) = e x := by
    rw [← ht x, huFix]
  apply mem_centralizer_iff.mpr
  intro v hv
  obtain ⟨s, hs⟩ := parameter v hv
  have hvFix := (hs x).trans (RootSubgroup.derived_fixed_of_ne_zero r ht0 (e x) htFix s)
  have hh := congrArg (fun y : X => (y : G)) (e.injective hvFix)
  change v * l * v⁻¹ = l at hh
  exact mul_inv_eq_iff_eq_mul.mp hh

/-- The parameter-four root action cannot contain an escaping small block. -/
theorem symplecticFour_exclusion {K : GroupClass} {T : Sylow 2 G}
    (h : HypothesisE61 K T M V) : SymplecticFourExclusion M V := by
  let _ := h.elementary
  intro U _ hUh L hL he A _ _ hc X hLX _ hfixed _ _ hroot
  exact he ((le_inf hLX.le hL.1).trans
    ((symplectic_root_centralizer_le hUh hc hfixed hroot).trans h.centralizer_le))

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.ComponentCase
