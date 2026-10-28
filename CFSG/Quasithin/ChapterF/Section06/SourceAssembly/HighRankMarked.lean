module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.MarkedCases
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.MixedEight
public import CFSG.Quasithin.ChapterF.Section06.Amalgams.SmallBound
public import CFSG.Quasithin.ChapterF.Section06.Elementary.PrimeToThree.Core
public import Theory.SpecificGroups.G2Even.TwoRank
public import Theory.Mathieu.SmallModuleRanks.M12
public import Theory.Representation.BinaryNaturalDual.FiveActors.ModuleGeometry.Rank
public import Theory.GroupTheory.PrimeRankDihedral
public import Theory.GroupTheory.PrimeRankProduct

/-!
# The marked Aut(M₁₂) alternative from a rank-four subgroup

A Goldschmidt triple with trivial two-core and two-rank at least four has
both local groups of characteristic two. A bad local group gives the opposite local group a faithful action on
six cosets, while the symmetric group on six letters has two-rank at most
three. The marked F.6.5 enumeration then leaves four concrete amalgams.
The G₂(2)′, G₂(2), and M₁₂ markings are excluded by the two-rank bounds of
their literal overlap subgroups, leaving the marked Aut(M₁₂) amalgam.

The elementary-local wrapper supplies the rank hypothesis used in
14.6.10(4), and retains the literal local inclusions needed by its consumer.
The earlier source premise `CharacteristicTwoMarkedAmalgamInput` is supplied
by `characteristicTwoMarked_of_large_nonabelian`.

Source: Aschbacher–Smith F.6.5 and 14.6.10(4), printed pp.305, 1028–1029.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF
open SourceAssembly
universe u
variable {G : Type u} [Group G] [Finite G] {A B : Subgroup G}

private theorem overlap_rank (h : IsGoldschmidtTriple A B) :
    primeRank 2 G = primeRank 2 (A ⊓ B : Subgroup G) := by
  obtain ⟨S, hS⟩ := h.intersection_sylow
  rw [hS]
  exact S.primeRank_eq

private theorem local_rank (h : IsGoldschmidtTriple A B) :
    primeRank 2 G = primeRank 2 B := by
  obtain ⟨S, hS⟩ := h.intersection_sylow
  have hSB : (S : Subgroup G) ≤ B := hS.symm.le.trans inf_le_right
  rw [S.primeRank_eq, (S.subtype hSB).primeRank_eq]
  exact (primeRank_equiv 2 (subgroupOfEquivOfLe hSB)).symm

private theorem opposite_index_six (h : IsGoldschmidtTriple A B) :
    (((pCore 2 A).map A.subtype).subgroupOf B).index = 6 := by
  let S := A ⊓ B
  let Q := (pCore 2 A).map A.subtype
  have hBS : Nat.card B = 3 * Nat.card S := by
    simpa only [S, inf_comm B A] using h.symm.local_card_eq_three_mul_intersection
  have hQS : Nat.card Q * 2 = Nat.card S := by
    have hm := (Q.subgroupOf S).card_mul_index
    have he : Nat.card (Q.subgroupOf S) = Nat.card Q :=
      Nat.card_congr (subgroupOfEquivOfLe h.local_twoCore_le_intersection).toEquiv
    change Nat.card (Q.subgroupOf S) * Q.relIndex S = Nat.card S at hm
    rw [he, h.left_core_index] at hm
    exact hm
  have hQP : Nat.card (Q.subgroupOf B) = Nat.card Q :=
    Nat.card_congr (subgroupOfEquivOfLe (h.local_twoCore_le_intersection.trans inf_le_right)).toEquiv
  have hm := (Q.subgroupOf B).card_mul_index
  rw [hQP, hBS, ← hQS] at hm
  have hp : 0 < Nat.card Q := Nat.card_pos
  change (Q.subgroupOf B).index = 6
  nlinarith

private theorem characteristic_two_of_high_rank (h : IsGoldschmidtTriple A B)
    (hcore : pCore 2 G = ⊥) (hr : 4 ≤ primeRank 2 G) :
    generalizedFitting A = pCore 2 A := by
  by_contra hbad
  let P := ((pCore 2 A).map A.subtype).subgroupOf B
  have hk : P.normalCore = ⊥ :=
    h.opposite_core_normalCore_eq_bot hcore (h.local_core_centralizes_residual hbad)
  let f := MulAction.toPermHom B (B ⧸ P)
  have hf : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, ← normalCore_eq_ker]
    exact hk
  let e := Finite.equivFinOfCardEq (show Nat.card (B ⧸ P) = 6 from opposite_index_six h)
  have hb := primeRank_le_of_injective 2 f hf
  rw [primeRank_equiv 2 (Equiv.permCongrHom e)] at hb
  have hu := BinaryNaturalDual.FiveActors.ModuleGeometry.symmetric_six_rank_le_three
  rw [local_rank h] at hr
  omega

private theorem split_sixteen_rank :
    primeRank 2 (Multiplicative (ZMod 2) × DihedralGroup 4) ≤ 3 := by
  rw [primeRank_prod_eq_add]
  have h2 : primeRank 2 (Multiplicative (ZMod 2)) ≤ 1 :=
    primeRank_le_of_card_le_prime_pow (by simp)
  have h8 : primeRank 2 (DihedralGroup 4) ≤ 2 := by
    simpa using dihedral_rank_le_two 2
  omega

private theorem g2_rank : primeRank 2 (Atlas.G2.Model (ZMod 2)) ≤ 3 := by
  simpa using (Atlas.G2.EvenTwoRank.two_rank (ZMod 2) (n := 1) (by simp)).le

private theorem marked_aut_of_exceptional (h : IsGoldschmidtTriple A B)
    (hr : 4 ≤ primeRank 2 G) (hm : ExceptionalMarkedAmalgam A B) :
    GreenBook.AutMathieuTwelve.IsAutM12Amalgam
      (RankTwoAmalgam.ofSubgroups A (A ⊓ B) B inf_le_left inf_le_right) := by
  rcases hm with hm | hm | hm | hm
  · obtain ⟨e⟩ := hm
    have h₁ : primeRank 2 Atlas.G2.BinaryParabolicPair.derivedSylow ≤
        primeRank 2 (commutator (Atlas.G2.Model (ZMod 2))) :=
      primeRank_le_of_injective 2
        (Atlas.G2.BinaryParabolicPair.derivedSylow :
          Subgroup Atlas.G2.BinaryParabolicPair.DerivedModel).subtype
        Subtype.val_injective
    have h₂ := primeRank_le_of_injective 2
      (commutator (Atlas.G2.Model (ZMod 2))).subtype Subtype.val_injective
    rw [overlap_rank h, primeRank_equiv 2 e.middle] at hr
    change 4 ≤ primeRank 2 Atlas.G2.BinaryParabolicPair.derivedSylow at hr
    have hg := g2_rank
    omega
  · obtain ⟨e⟩ := hm
    have h₁ := primeRank_le_of_injective 2
      (Atlas.G2.unipotent (K := ZMod 2)).subtype Subtype.val_injective
    rw [overlap_rank h, primeRank_equiv 2 e.middle] at hr
    change 4 ≤ primeRank 2 (Atlas.G2.unipotent (K := ZMod 2)) at hr
    have hg := g2_rank
    omega
  · obtain ⟨e⟩ := hm
    let f := e.trans GreenBook.MathieuTwelve.concreteIso
    have h₁ := primeRank_le_of_injective 2
      Sporadic.Mathieu.M12SmallPair.sylowCandidate.subtype Subtype.val_injective
    rw [overlap_rank h, primeRank_equiv 2 f.middle] at hr
    change 4 ≤ primeRank 2 Sporadic.Mathieu.M12SmallPair.sylowCandidate at hr
    have hg := Sporadic.Mathieu.m12_twoRank_le_three
    omega
  · exact hm

/-- Rank at least four selects the Aut(M₁₂) marking in one of the two orientations. -/
theorem IsGoldschmidtTriple.aut_mathieu_marked_of_high_rank
    (hF1 : CharacteristicTwoMarkedAmalgamInput.{u})
    (h : IsGoldschmidtTriple A B) (hcore : pCore 2 G = ⊥)
    (hr : 4 ≤ primeRank 2 G) :
    GreenBook.AutMathieuTwelve.IsAutM12Amalgam
        (RankTwoAmalgam.ofSubgroups A (A ⊓ B) B inf_le_left inf_le_right) ∨
      GreenBook.AutMathieuTwelve.IsAutM12Amalgam
        (RankTwoAmalgam.ofSubgroups B (B ⊓ A) A inf_le_left inf_le_right) := by
  obtain ⟨S, hS⟩ := h.intersection_sylow
  have hrS : 4 ≤ primeRank 2 S := by rwa [S.primeRank_eq] at hr
  have hc : 8 < Nat.card S := by
    by_contra! hc
    have hu : primeRank 2 S ≤ 3 := primeRank_le_of_card_le_prime_pow hc
    omega
  have hn : ¬ Nonempty (S ≃* (Multiplicative (ZMod 2) × DihedralGroup 4)) := by
    rintro ⟨e⟩
    rw [primeRank_equiv 2 e] at hrS
    have hu := split_sixteen_rank
    omega
  rcases hF1 G A B S h hcore (characteristic_two_of_high_rank h hcore hr)
    (characteristic_two_of_high_rank h.symm hcore hr) hS hc hn with hm | hm
  · exact .inl (marked_aut_of_exceptional h hr hm)
  · exact .inr (marked_aut_of_exceptional h.symm hr hm)

/-- The marked alternative on a prime-to-three-core-free quotient containing
a local elementary abelian subgroup of rank at least four. -/
theorem IsGoldschmidtTriple.aut_mathieu_marked_of_elementary_local
    (hF1 : CharacteristicTwoMarkedAmalgamInput.{u})
    (h : IsGoldschmidtTriple A B) (hn3 : pPrimeCore 3 G = ⊥)
    (E : Subgroup G) (hE : IsElementaryAbelian 2 E) (_hEB : E ≤ B)
    (hr : 4 ≤ Group.rank E) :
    GreenBook.AutMathieuTwelve.IsAutM12Amalgam
        (RankTwoAmalgam.ofSubgroups A (A ⊓ B) B inf_le_left inf_le_right) ∨
      GreenBook.AutMathieuTwelve.IsAutM12Amalgam
        (RankTwoAmalgam.ofSubgroups B (B ⊓ A) A inf_le_left inf_le_right) := by
  let := hE
  apply h.aut_mathieu_marked_of_high_rank hF1
  · exact bot_unique (twoCore_le_primeToThreeCore.trans hn3.le)
  · exact hr.trans (Subgroup.rank_le_primeRank_of_abelian_pGroup 2 E
      (IsElementaryAbelian.isPGroup 2 E) inferInstance)

end CFSG.Quasithin.ChapterF
