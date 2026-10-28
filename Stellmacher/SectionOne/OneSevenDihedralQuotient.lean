module
public import Stellmacher.SectionOne.OneSevenSmallSylow
public import Theory.GroupTheory.SpecificGroups.DihedralQuotientSylow

/-!
# One-seven actions which are odd-dihedral quotients

Under Section 1's exact action hypotheses, a quotient of an odd dihedral
group with nontrivial J(V,S) is SL₂(2). This is the action-theoretic part of
the faithful local quotient consequence of (6.3) used in Stellmacher (8.2),
Journal of Algebra 190 (1997), p.37.

The pure dihedral quotient theorem gives |S|≤2 and normal generation by S.
Since the nontrivial J lies in S, both have order two and J=S. Thus its
normal closure E is the whole group, and the proved small-Sylow consequence
of the global (1.7) factor product identifies that group as SL₂(2).
The surjection and nontrivial J are explicit inputs: no pending local
classification theorem or implicit quotient-kernel property is used.
-/

namespace Stellmacher.SectionOne
universe u

public theorem isSL2Two_of_odd_dihedral_quotient
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) (S : Sylow 2 G)
    (hJ : oneJ (V := V) (S : Subgroup G) ≠ ⊥)
    (n : ℕ) (hn : Odd n) (q : DihedralGroup n →* G) (hq : Function.Surjective q) :
    IsSL2Two G := by
  have hSylow := odd_dihedral_quotient_sylow n hn q hq S
  let J := oneJ (V := V) (S : Subgroup G)
  have hJS : J ≤ (S : Subgroup G) := sSup_le fun A hA => hA.1
  have hJcard : 1 < Nat.card J := (Subgroup.one_lt_card_iff_ne_bot J).mpr hJ
  have hS2 : Nat.card S = 2 := by
    have hle := Subgroup.card_le_of_le hJS
    omega
  have hJeq : J = (S : Subgroup G) :=
    Subgroup.eq_of_le_of_card_ge hJS (by omega)
  have hEtop : oneE (V := V) (S : Subgroup G) = ⊤ := by
    change Subgroup.normalClosure (J : Set G) = ⊤
    rw [hJeq]
    exact hSylow.2
  exact isSL2Two_of_oneE_eq_top_of_sylow_card_two h S hS2 hEtop

end Stellmacher.SectionOne
