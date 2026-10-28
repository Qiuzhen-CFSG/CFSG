module
public import CFSG.Quasithin.ChapterH.Section05To09.NaturalDual.SourceFourActors.Parameters
public import Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals.TreeWreathModel
public import Theory.GroupTheory.WreathTwoElementaryRank
public import Theory.GroupTheory.PrimeRankDihedral
public import Theory.GroupTheory.PrimeRankSylow
public import Theory.GroupTheory.GeneralizedFitting.ComponentLayerStructure
public import Theory.Representation.BinaryOffender.PermutationConjugacy

/-!
# Offenders preserve the original dimension-four summands

An elementary subgroup of the actual automorphism group has rank at most
four, by the dihedral wreath model of its Sylow subgroup. An outer involution
fixes exactly four dimensions of the doubled-natural module. The offender
inequality would therefore force an outer offender to have rank four and
fixed dimension four. H.9.3's three actual elementary-sixteen classes exclude
this: the two outer classes fix dimensions one and two, while the remaining
class lies in the layer. Thus every offender preserves the natural summand.

`Thompson` applies this to the literal normalizer action quotient of the
chosen doubled branch. This gives the containment used after C.1.34 in
12.1.4 independently of the MS classification. The remaining ambient Sylow
and component arguments belong to `qt-d-double-natural-pure-fusion`;
`qt-d-double-natural-centralizers` retains the final source assembly.
Source: Aschbacher--Smith, 12.1.4, printed p.790, and H.9.3, pp.391--392.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterH.NaturalDual.SourceSetup
open SourceFourActors
variable {M E : Type*} [Group M] [AddCommGroup E] [Module (ZMod 2) E]
  (S : SourceSetup 4 M E)

include S in
private theorem elementary_rank_le_four (A : Subgroup M) (hA : IsElementaryAbelian 2 A) :
    rank A ≤ 4 := by
  let := S.finite_group
  let P : Sylow 2 M := Classical.choice inferInstance
  let e := permutation S P
  have hr : primeRank 2 (Equiv.Perm (Fin 8)) ≤ 4 := by
    rw [Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals.treeSylow.primeRank_eq]
    rw [Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals.treeSylow_coe,
      primeRank_equiv 2 Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals.treeWreathEquiv]
    exact WreathTwoElementaryRank.rank_bound (dihedral_rank_le_two 2) (by decide)
  have hrM : primeRank 2 M ≤ 4 := (primeRank_equiv 2 e).le.trans hr
  have hc : Nat.card A ≤ 16 := (primeRank_le_iff_elementary_card_le M).mp hrM A hA
  exact (Nat.log_mono_right hc).trans_eq (by decide : Nat.log 2 16 = 4)

/-- Every offender of the actual eight-dimensional doubled-natural action
preserves the original natural and dual summands. -/
theorem four_offender_le_layer (A : Subgroup M) (hA : IsOffender S.representation A) :
    A ≤ componentLayer M := by
  let := S.finite_group
  let : FiniteDimensional (ZMod 2) E := S.model.coordinates.symm.finiteDimensional
  let := hA.1.2
  let P : Sylow 2 M := Classical.choice inferInstance
  have hd : Module.finrank (ZMod 2) E = 8 := by
    rw [S.model.coordinates.finrank_eq]
    simp [BinaryNaturalDual.CoordinateSpace, BinaryNaturalDual.Space,
      BinaryLinear.OuterCyclic.Space, Module.finrank_prod, Subspace.dual_finrank_eq]
  have hr := S.elementary_rank_le_four A hA.1.2
  by_contra hout
  obtain ⟨a,ha,han⟩ := SetLike.not_le_iff_exists.mp hout
  have ha1 : a ≠ 1 := fun he => han (he ▸ one_mem _)
  have ha2 : orderOf a = 2 := by
    exact orderOf_eq_prime (by simpa using elemPow_eq_one_of_isElementaryAbelian (p := 2) a ha) ha1
  have hsub : fixedSpace S.representation A ≤ elementFixed S a := by
    intro v hv
    exact (mem_elementFixed S a v).mpr (hv ⟨a,ha⟩)
  have hf : Module.finrank (ZMod 2) (fixedSpace S.representation A) ≤ 4 :=
    (Submodule.finrank_mono hsub).trans_eq (outer_fixed_finrank S P a ha2 han)
  have hsum := fixedCodim_add_finrank S.representation A
  have hoff := hA.2
  have heq : Module.finrank (ZMod 2) (fixedSpace S.representation A) = 4 := by omega
  have hr4 : rank A = 4 := by omega
  have hc : Nat.card A = 16 := by
    obtain ⟨k,hk⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_card_eq
    have hkr : rank A = k := by rw [rank,hk,Nat.log_pow (by decide : 1 < 2)]
    rw [hk,←hkr,hr4]
    rfl
  obtain ⟨i,⟨g,hg⟩,_⟩ := actor_exhaustion S P A hA.1.2 hc
  have hdim : Module.finrank (ZMod 2) (S.fixed (actor S P i)) = 4 := by
    rw [←hg]
    exact (fixedSpaceConjEquiv S.representation A g).finrank_eq.symm.trans heq
  fin_cases i
  · apply hout
    intro x hx
    have hh := A0_le_layer S P (hg ▸ mem_map_of_mem (MulAut.conj g).toMonoidHom hx)
    have hn : g ∈ normalizer (componentLayer M : Set M) := by
      rw [normalizer_eq_top]; trivial
    exact (hn x).mpr hh
  · have hh := (A1_parameters S P).1
    change Module.finrank (ZMod 2) (S.fixed (A1 S P)) = 4 at hdim
    omega
  · obtain ⟨b,hb,hbn⟩ := SetLike.not_le_iff_exists.mp (outer_actors S P).2
    have hh := (A2_parameters S P b hb (fun h => hbn h.2)).2.1
    change Module.finrank (ZMod 2) (S.fixed (A2 S P)) = 4 at hdim
    omega
end CFSG.Quasithin.ChapterH.NaturalDual.SourceSetup
