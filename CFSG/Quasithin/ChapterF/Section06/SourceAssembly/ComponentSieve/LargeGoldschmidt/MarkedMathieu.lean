module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentSieve.LargeGoldschmidt.Models
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.QuasisimpleCases.Mathieu.InnerResidual
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentModels
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentExclusions.Janko
public import Theory.GroupTheory.SylowCoprimeEquivalence
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.QuasisimpleCases.DegreeThree.ExponentBounds

/-!
# The component quotient of the marked Mathieu amalgam

The inner Mathieu marking places the entire common Sylow subgroup in the
actual two-residual. Hence that residual is the whole ambient group. Its
center is a three-group, so the literal central projection preserves its
Sylow two-subgroup. The marked Sylow has order 64 and exponent eight, and
contains an element of order eight. The complete Theorem C catalogue sieve
and the prime degree-three exponent bound therefore identify the original
component quotient with M₁₂.

The inputs are the genuine earlier A/C statements, the SQTK quotient and
the original embedded Goldschmidt amalgam; no model or Sylow-size premise
is added. Source: Aschbacher–Smith F.6.18(12), printed pp.309–310.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.SourceAssembly
universe u
variable {G H : Type u} [Group G] [Finite G] [Group H] [Finite H]
  {κ : GroupClass.{u}} {G₁ G₂ : Subgroup G}

theorem residual_quotient_sylow_of_marked_mathieu
    (e : G ≃* (H ⧸ pPrimeCore 3 H)) (h : IsGoldschmidtTriple G₁ G₂)
    (hM : GreenBook.MathieuTwelve.IsM12Amalgam
      (RankTwoAmalgam.ofSubgroups G₁ (G₁ ⊓ G₂) G₂ inf_le_left inf_le_right))
    (hq : IsQuasisimple (pResidual 2 G))
    (P : Sylow 2 (pResidual 2 G ⧸ center (pResidual 2 G))) :
    Nonempty (P ≃* Sporadic.Mathieu.M12SmallPair.sylowCandidate) := by
  let K := pResidual 2 G
  have hK : IsComponent G K := ⟨(inferInstance : K.Normal).isSubnormal,hq⟩
  have htop := Mathieu.residual_eq_top_of_m12_amalgam h hM
  let j : K ≃* G := (MulEquiv.subgroupCongr htop).trans topEquiv
  obtain ⟨T,hT⟩ := h.intersection_sylow
  let R := T.mapSurjective (f := j.symm.toMonoidHom) j.symm.surjective
  let eTR : T ≃* R := (T : Subgroup G).equivMapOfInjective j.symm.toMonoidHom j.symm.injective
  have hk : Nat.Coprime 2 (Nat.card (QuotientGroup.mk' (center K)).ker) := by
    rw [QuotientGroup.ker_mk']
    obtain ⟨n,hn⟩ := (component_center_is_three_group e hK).exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 2 3).pow_right n
  let eRP := Sylow.equivOfSurjectiveCoprime (QuotientGroup.mk' (center K))
    (QuotientGroup.mk'_surjective _) hk R P
  obtain ⟨m⟩ := hM
  let v : T ≃* Sporadic.Mathieu.M12SmallPair.sylowCandidate :=
    (MulEquiv.subgroupCongr hT).symm.trans (m.trans GreenBook.MathieuTwelve.concreteIso).middle
  exact ⟨(eTR.trans eRP).symm.trans v⟩

theorem residual_quotient_degree_three_or_mathieu_of_marked_mathieu
    (hA : ChapterA.Section02.TheoremA κ H)
    (hC : ChapterA.Section02.TheoremC κ (pResidual 2 G ⧸ center (pResidual 2 G)))
    (hH : IsSQTK κ H) (e : G ≃* (H ⧸ pPrimeCore 3 H))
    (h : IsGoldschmidtTriple G₁ G₂)
    (hM : GreenBook.MathieuTwelve.IsM12Amalgam
      (RankTwoAmalgam.ofSubgroups G₁ (G₁ ⊓ G₂) G₂ inf_le_left inf_le_right))
    (hq : IsQuasisimple (pResidual 2 G)) :
    (∃ p : ℕ, p.Prime ∧ Odd p ∧
      (ClassicalGroup.IsPSL (pResidual 2 G ⧸ center (pResidual 2 G)) 3 p ∨
        ClassicalGroup.IsPSU (pResidual 2 G ⧸ center (pResidual 2 G)) 3 p)) ∨
      Nonempty ((pResidual 2 G ⧸ center (pResidual 2 G)) ≃* Sporadic.Mathieu.M12) := by
  let K := pResidual 2 G
  have hK : IsComponent G K := ⟨(inferInstance : K.Normal).isSubnormal,hq⟩
  let P : Sylow 2 (K ⧸ center K) := default
  obtain ⟨j⟩ := residual_quotient_sylow_of_marked_mathieu e h hM hq P
  have hP : Nat.card P = 64 := (Nat.card_congr j.toEquiv).trans
    Sporadic.Mathieu.M12SmallPair.card_sylowCandidate
  have hexp : ∀ x : P, x ^ 8 = 1 := fun x => j.injective (by
    rw [map_pow,map_one]
    exact Mathieu.m12_sylow_pow_eight (j x))
  let x := j.symm (Sporadic.Mathieu.M12SmallPair.SylowAutomorphismGroup.generator 2)
  have hx : orderOf x = 8 := by
    simpa only [x,MulEquiv.orderOf_eq] using Mathieu.m12_sylow_generator_order_eight
  have hm := component_central_quotient_model hA hC hH
    (e.symm.toMonoidHom.comp (QuotientGroup.mk' _))
    (e.symm.surjective.comp (QuotientGroup.mk'_surjective _)) hK
  exact ComponentSieve.LargeGoldschmidt.theoremC_degree_three_or_mathieu_of_sylow64 P hP hexp x hx hm
theorem residual_quotient_mathieu_of_marked_mathieu
    (hA : ChapterA.Section02.TheoremA κ H)
    (hC : ChapterA.Section02.TheoremC κ (pResidual 2 G ⧸ center (pResidual 2 G)))
    (hH : IsSQTK κ H) (e : G ≃* (H ⧸ pPrimeCore 3 H))
    (h : IsGoldschmidtTriple G₁ G₂)
    (hM : GreenBook.MathieuTwelve.IsM12Amalgam
      (RankTwoAmalgam.ofSubgroups G₁ (G₁ ⊓ G₂) G₂ inf_le_left inf_le_right))
    (hq : IsQuasisimple (pResidual 2 G)) :
    Nonempty ((pResidual 2 G ⧸ center (pResidual 2 G)) ≃* Sporadic.Mathieu.M12) := by
  rcases residual_quotient_degree_three_or_mathieu_of_marked_mathieu hA hC hH e h hM hq
    with ⟨p, hp, ho, hm⟩ | hm
  · let P : Sylow 2 (pResidual 2 G ⧸ center (pResidual 2 G)) := default
    obtain ⟨j⟩ := residual_quotient_sylow_of_marked_mathieu e h hM hq P
    have hP : Nat.card P = 64 := (Nat.card_congr j.toEquiv).trans
      Sporadic.Mathieu.M12SmallPair.card_sylowCandidate
    have hexp : ∀ x : P, x ^ 8 = 1 := fun x => j.injective (by
      rw [map_pow, map_one]
      exact Mathieu.m12_sylow_pow_eight (j x))
    have hb : Nat.card P ≤ 32 := hm.elim
      (linear_three_model_sylow_card_le_32 P hexp hp ho)
      (unitary_three_model_sylow_card_le_32 P hexp hp ho)
    omega
  · exact hm

end CFSG.Quasithin.ChapterF.SourceAssembly
