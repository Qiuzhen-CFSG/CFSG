module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SurvivingIntersections.Local
public import CFSG.Quasithin.FermatMersenne
public import Theory.SpecificGroups.PSL2.PrimeSylowMaximal

/-!
# The surviving Fermat–Mersenne linear intersection

For a Fermat or Mersenne prime p > 7, one of p − 1 and p + 1 is a
power of two at least sixteen. Dickson's subgroup classification then
makes every Sylow two-subgroup of the actual PSL₂(p) model maximal.
The component Sylow subgroup supplied by the local setup is S ∩ L;
it lies in the proper subgroup L ∩ M, which must therefore equal it.

The source's inner-action hypothesis is retained in the assembly theorem.
The subgroup calculation already follows from the model and the Sylow
containment. The smaller parameters are handled separately by SmallLinear.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
1.1.5(3)(e) and 2.3.9(7)(e), printed pp.502 and 525–526.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter2.ComponentRefinement
open Subgroup
open scoped MatrixGroups

private theorem large_fermatMersenne_adjacent_power {p : ℕ}
    (hp : IsFermatOrMersennePrime p) (hbig : 7 < p) :
    ∃ k : ℕ, 4 ≤ k ∧ (p - 1 = 2 ^ k ∨ p + 1 = 2 ^ k) := by
  rcases hp.2 with ⟨a, ha⟩ | ⟨a, ha⟩
  · have ha2 : 2 ≤ a := by
      by_contra! h
      interval_cases a <;> norm_num at ha <;> omega
    refine ⟨2 ^ a, ?_, Or.inl (by omega)⟩
    exact (show 2 ^ 2 ≤ 2 ^ a from Nat.pow_le_pow_right (by omega) ha2)
  · have ha4 : 4 ≤ a := by
      by_contra! h
      interval_cases a <;> norm_num at ha <;> omega
    exact ⟨a, ha4, Or.inr ha⟩

/-- Sylow maximality alone identifies the intersection in the large
prime-field branch, without additional restrictions on the inner action. -/
theorem LocalSetup.linearPrime_intersection {G : Type*} [Group G]
    {H L M : Subgroup G} {S : Sylow 2 H} {z : G}
    (h : LocalSetup H L M S z) (p : ℕ) [Fact p.Prime]
    (hp : IsFermatOrMersennePrime p) (hbig : 7 < p)
    (e : L ≃* PSL(2,ZMod p)) :
    L ⊓ M = ((S : Subgroup H).map H.subtype) ⊓ L := by
  let := h.finite
  obtain ⟨k, hk, hpk⟩ := large_fermatMersenne_adjacent_power hp hbig
  obtain ⟨R, hR⟩ := h.component_sylow
  have hmax : IsCoatom (R : Subgroup L) := by
    apply (OrderIso.isCoatom_iff e.mapSubgroup (R : Subgroup L)).mp
    change IsCoatom ((R : Subgroup L).map e.toMonoidHom)
    exact Matrix.ProjectiveSpecialLinearGroup.sylow_two_isCoatom_of_adjacent_power
      hk hpk (R.mapSurjective (f := e.toMonoidHom) e.surjective)
  have hle : (R : Subgroup L) ≤ M.subgroupOf L := by
    rw [hR]
    intro x hx
    exact h.sylow_le hx
  have hproper : M.subgroupOf L ≠ ⊤ :=
    fun he => h.outside (subgroupOf_eq_top.mp he)
  have heq := (hmax.le_iff_eq hproper).mp hle
  have he := congrArg (fun U : Subgroup L => U.map L.subtype) (heq.trans hR)
  simpa only [subgroupOf_map_subtype, inf_comm M L] using he

/-- The large-parameter PSL₂ branch of 2.3.9(7)(e), with the literal inner
action from 1.1.5(3)(e) and the actual matrix-model equivalence. -/
theorem linearTwo_intersection {G : Type*} [Group G]
    {H L M : Subgroup G} {S : Sylow 2 H} {z : G}
    (h : LocalSetup H L M S z) (p : ℕ) [Fact p.Prime]
    (hp : IsFermatOrMersennePrime p) (hbig : 7 < p)
    (e : L ≃* PSL(2,ZMod p)) (α : MulAut L)
    (_hα : ∀ x : L, (α x : G) = z * (x : G) * z⁻¹)
    (_hinner : α ∈ (MulAut.conj (G := L)).range) :
    L ⊓ M = ((S : Subgroup H).map H.subtype) ⊓ L :=
  h.linearPrime_intersection p hp hbig e

end CFSG.Quasithin.Chapter2.ComponentRefinement

end
