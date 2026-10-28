module

public import Theory.Representation.BinaryCoprimeDegree
public import Theory.Representation.BinaryCoprimeDegree.PerfectCentral
public import Theory.GroupTheory.CoprimeQuotientSubgroups.PrimeLift
public import Theory.ElementaryAbelian.ExtraspecialEquiv

/-!
# Extraspecial degree bounds through central quotients

Let a finite perfect group act faithfully and irreducibly over F₂, and let a
central quotient contain an extraspecial subgroup of order p³ for an odd prime
p. If p divides the central kernel, the Schur-field and determinant argument
already gives degree at least p * ordₚ(2). Otherwise the extraspecial subgroup
lifts isomorphically through the coprime kernel, and its binary degree bound
applies to the restricted original action.

This retains arbitrary central covers; no Schur multiplier computation or
splitting of the full central extension is assumed. The concrete consumer is
the J₄ exclusion in Aschbacher–Smith K.4, printed p.457, using G.7.1(2).
-/

public section
namespace Representation.BinaryCoprimeDegree
open Subgroup

/-- The extraspecial binary bound survives arbitrary central quotients of a
perfect group when the original representation is faithful and irreducible. -/
theorem extraspecial_central_quotient_degree
    {G H V : Type*} [Group G] [Finite G] [Group H] [Finite H]
    [Group.IsPerfect G] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) [ρ.IsIrreducible]
    (hρ : Function.Injective ρ) (f : G →* H) (hf : Function.Surjective f)
    (hc : f.ker ≤ center G) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (P : Subgroup H) [IsExtraspecial p P] (hP : Nat.card P = p ^ 3) :
    p * orderOf (2 : ZMod p) ≤ Module.finrank (ZMod 2) V := by
  by_cases hd : p ∣ Nat.card f.ker
  · exact perfect_central_prime_degree ρ hρ Fact.out hp2
      (hd.trans (Subgroup.card_dvd_of_le hc))
  · have hcop : Nat.Coprime p (Nat.card f.ker) :=
      (Fact.out : p.Prime).coprime_iff_not_dvd.mpr hd
    obtain ⟨A, _hA, ⟨e⟩⟩ := exists_prime_subgroup_equiv_of_surjective_coprime
      f hf hcop P (IsPGroup.of_card hP)
    let : IsExtraspecial p A := IsExtraspecial.of_mulEquiv e.symm inferInstance
    exact extraspecial_finrank_le hp2 (ρ.comp A.subtype)
      (hρ.comp A.subtype_injective) ((Nat.card_congr e.toEquiv).trans hP)

end Representation.BinaryCoprimeDegree
