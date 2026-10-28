module

public import Theory.SpecificGroups.PSL2.PrimeCardInnerIndex
public import Theory.SpecificGroups.PGL2.PerfectCentralizer
public import GorensteinWalter.PGL2DihedralSylow
public import Theory.GroupTheory.PrimeRankDihedral
public import Theory.GroupTheory.PrimeRankSylow
public import Theory.GroupTheory.PrimeRankElementary
public import Theory.GroupTheory.PerfectSmallTwoAction
public import Theory.GroupTheory.PGroup.ElementaryNormalizer

/-!
# Two-signalizers in prime-field PSL₂ automorphism groups

The full automorphism group is the actual PGL₂(p), of two-rank at most
two. A nontrivial two-signalizer has a nontrivial characteristic elementary
subgroup of order at most four. Every perfect normalizing actor centralizes
that subgroup. But a nontrivial perfect subgroup of PGL₂ has trivial
centralizer, a contradiction. This proves vanishing in the full automorphism
group, including outer involutions, for every prime p > 3.

The model transport retains an actual equivalence with the original radical
quotient. It covers p = 5 as well as the surviving primes p ≥ 11.
Source: Aschbacher--Smith, 11.4.1(3), printed p.776.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Radical

private theorem signalizer_eq_bot_of_rank_two
    {J : Type*} [Group J] [Finite J] (D U : Subgroup J) [Group.IsPerfect D]
    (hr : primeRank 2 J ≤ 2) (hc : centralizer (D : Set J) = ⊥)
    (hu : IsPGroup 2 U) (hn : D ≤ normalizer (U : Set J)) : U = ⊥ := by
  by_contra hU
  obtain ⟨E, hE, _, he, hNE⟩ := exists_nontrivial_elementary_with_normalizer_le U hu hU
  have hnE := hn.trans hNE
  have hcard : Nat.card E ≤ 4 := (primeRank_le_iff_elementary_card_le J).mp hr E he
  let N := normalizer (E : Set J)
  let B := D.subgroupOf N
  let C := E.subgroupOf N
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hnE).symm.toMonoidHom)
    (subgroupOfEquivOfLe hnE).symm.surjective
  let : C.Normal := normal_in_normalizer
  have hCcard : Nat.card C ≤ 4 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe E.le_normalizer).toEquiv]
    exact hcard
  have hBC := le_centralizer_of_isPerfect_of_card_le_four B C hCcard
  have hDE : D ≤ centralizer (E : Set J) := by
    intro d hd e he
    exact congrArg N.subtype
      (hBC (show (⟨d, hnE hd⟩ : N) ∈ B from hd)
        ⟨e, E.le_normalizer he⟩ he)
  exact hE (bot_unique ((le_centralizer_iff.mp hDE).trans_eq hc))

/-- Every nontrivial perfect subgroup of PGL₂ over an odd finite field
has trivial normalized two-subgroups. -/
theorem pgl_two_signalizer_eq_bot
    (F : Type) [Field F] [Finite F]
    (hodd : GorensteinWalter.IsOddPrimePower (Nat.card F))
    (D U : Subgroup (PGL(2, F))) [Group.IsPerfect D] (hD : D ≠ ⊥)
    (hU : IsPGroup 2 U) (hn : D ≤ normalizer (U : Set _)) : U = ⊥ := by
  let : Finite (PGL(2, F)) := Finite.of_surjective
    Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  let P : Sylow 2 (PGL(2, F)) := default
  obtain ⟨m, _, ⟨e⟩⟩ := GorensteinWalter.pgl2_odd_hasDihedralSylowTwo_model F hodd P
  have hr : primeRank 2 (PGL(2, F)) ≤ 2 :=
    (P.primeRank_eq.trans (primeRank_equiv 2 e)).le.trans (dihedral_rank_le_two m)
  exact signalizer_eq_bot_of_rank_two D U hr
    (Theory.PGL2.centralizer_eq_bot_of_perfect D hD) hU hn

/-- Prime-field coverage supplies vanishing in the full automorphism group
of the literal PSL₂ model. -/
theorem prime_psl_automorphism_two_signalizer_eq_bot
    {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    (F : Type) [Field F] [Finite F] (hF : Nat.card F = p)
    (D U : Subgroup (MulAut PSL(2, F))) [Group.IsPerfect D] (hD : D ≠ ⊥)
    (hU : IsPGroup 2 U) (hn : D ≤ normalizer (U : Set _)) : U = ⊥ := by
  have ho : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  let hodd : GorensteinWalter.IsOddPrimePower (Nat.card F) :=
    ⟨p, 1, Fact.out, ho, by decide, by simpa using hF⟩
  have hc : 3 < Nat.card F := by omega
  let e : GorensteinWalter.PGL2 F ≃* MulAut PSL(2, F) :=
    MulEquiv.ofBijective (GorensteinWalter.pgl2InnerAutPSL2 F hodd hc)
      ⟨GorensteinWalter.pgl2InnerAutPSL2_injective F hodd hc,
        Theory.PSL2.prime_card_pgl_coverage F hF hodd hc⟩
  let : Group.IsPerfect (D.map e.symm.toMonoidHom) := Group.IsPerfect.map _
  apply (U.map_eq_bot_iff_of_injective (f := e.symm.toMonoidHom) e.symm.injective).mp
  exact pgl_two_signalizer_eq_bot F hodd _ _
    (fun he => hD ((D.map_eq_bot_iff_of_injective (f := e.symm.toMonoidHom) e.symm.injective).mp he))
    (hU.map e.symm.toMonoidHom)
    ((map_mono hn).trans (U.le_normalizer_map e.symm.toMonoidHom))

/-- Transport to the actual radical quotient by a supplied group isomorphism. -/
theorem prime_model_two_signalizer_eq_bot
    {Q : Type*} [Group Q] {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    (F : Type) [Field F] [Finite F] (hF : Nat.card F = p) (e : Q ≃* PSL(2, F))
    (D U : Subgroup (MulAut Q)) [Group.IsPerfect D] (hD : D ≠ ⊥)
    (hU : IsPGroup 2 U) (hn : D ≤ normalizer (U : Set _)) : U = ⊥ := by
  let a := MulAut.congr e
  let : Group.IsPerfect (D.map a.toMonoidHom) := Group.IsPerfect.map _
  apply (U.map_eq_bot_iff_of_injective (f := a.toMonoidHom) a.injective).mp
  exact prime_psl_automorphism_two_signalizer_eq_bot hp F hF _ _
    (fun he => hD ((D.map_eq_bot_iff_of_injective (f := a.toMonoidHom) a.injective).mp he))
    (hU.map a.toMonoidHom) ((map_mono hn).trans (U.le_normalizer_map a.toMonoidHom))

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Radical
