module
public import CFSG.Quasithin.Chapter4.Section04.OddActorOddCore
public import Theory.Representation.G2Natural

open Subgroup
open scoped IsMulCommutative
/-!
# The unitary six-dimensional specialization

The natural G₂(2)' module has dimension six over F₂, hence order 64 for the
chosen elementary subgroup. This adapter applies the odd-core centralization
and genuine uniqueness reductions to the actual module chart supplied by the
unitary source, preserving all subgroup maps and the original actor A.

Source: Aschbacher--Smith, Theorem 4.4.3(i.c) and Lemma 4.4.8,
printed pp.619--620.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter4.Section04
variable {G:Type*} [Group G] [Finite G]

private theorem unitary_card {V:Subgroup G} [IsElementaryAbelian 2 V]
    (E:Additive V≃ₗ[ZMod 2]Atlas.G2.Natural.Space (ZMod 2)) : Nat.card V=64 := by
  have hd:Module.finrank (ZMod 2) (Additive V)=6:=
    E.finrank_eq.trans (Atlas.G2.Natural.finrank_space (ZMod 2))
  have hc:=Module.natCard_eq_pow_finrank (K:=ZMod 2) (V:=Additive V)
  rw [Nat.card_zmod,hd] at hc
  exact hc

theorem chosen_unitary_oddNormalizer_oddCore
    {K:GroupClass} {T:Sylow 2 G} {L V M:Subgroup G} [IsElementaryAbelian 2 V]
    (h:Chapter12.Section02.Hypothesis1221 K T L)
    (D:Chapter12.Section02.ChosenModule T L V)
    (E:Additive V≃ₗ[ZMod 2]Atlas.G2.Natural.Space (ZMod 2))
    {p:ℕ} [Fact p.Prime] (hp:3<p) (A:Subgroup G) (hA:IsPGroup p A)
    (hAN:A≤normalizer (L:Set G)) (hcomm:⁅A,L⁆≤L.pCoreIn 2)
    (hAV:A≤centralizer (V:Set G))
    (hunique:UniqueMaximalOvergroup (oddActorResidual L A) M) :
    ⁅V,(pPrimeCore 2 (normalizer (A:Set G))).map (normalizer (A:Set G)).subtype⁆=⊥ ∧
    (pPrimeCore 2 (normalizer (A:Set G))).map (normalizer (A:Set G)).subtype≤M := by
  have hodd:Odd (Nat.card A):=by
    obtain ⟨n,hn⟩:=hA.exists_card_eq
    rw [hn]
    exact ((Fact.out:p.Prime).odd_of_ne_two (by omega)).pow
  exact ⟨chosen_oddNormalizer_centralizes_oddCore h D (unitary_card E) A hAN hcomm hodd hAV,
    chosen_oddNormalizer_oddCore_le_of_uniqueness h D (unitary_card E) A hAN hcomm hodd hAV hunique⟩
end CFSG.Quasithin.Chapter4.Section04
