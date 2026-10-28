module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentProduct.Source
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentSieve.SourceComponent
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.Rigidity.Complete
public import Theory.GroupTheory.PResidual.PrimeToQuotientLift
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF
variable {G : Type*} [Group G] [Finite G] {A B : Subgroup G}

private theorem local_three_generated {L : Type*} [Group L] [Finite L]
    (e : (L ⧸ pCore 2 L) ≃* Equiv.Perm (Fin 3)) :
    primeToResidual 3 (pResidual 2 L) = ⊤ := by
  have hc := residual_core_quotient_card_of_sylow_index_three (default : Sylow 2 L)
    (SymmetricThreeTwoCore.sylow_index_three e _)
  let : IsSimpleGroup (pResidual 2 L ⧸ pCore 2 (pResidual 2 L)) :=
    isSimpleGroup_of_prime_card hc
  exact primeToResidual_eq_top_of_simple_quotient 3 2 _ pCore_isPGroup
    (isPPerfect_pResidual 2) (by rw [hc])

theorem IsGoldschmidtTriple.twoResidual_eq_primeToThreeResidual
    (h : IsGoldschmidtTriple A B) : pResidual 2 G = primeToResidual 3 G := by
  apply le_antisymm
  · rw [h.twoResidual_eq_sup]
    apply sup_le
    · apply le_primeToResidual_of_eq_top 3
      have hm := map_primeToResidual (p := 3)
        ((pResidual 2 A).equivMapOfInjective A.subtype A.subtype_injective)
      rw [local_three_generated h.quotient_left.some,map_top_of_surjective _
        (equivMapOfInjective _ _ A.subtype_injective).surjective] at hm
      exact hm.symm
    · apply le_primeToResidual_of_eq_top 3
      have hm := map_primeToResidual (p := 3)
        ((pResidual 2 B).equivMapOfInjective B.subtype B.subtype_injective)
      rw [local_three_generated h.quotient_right.some,map_top_of_surjective _
        (equivMapOfInjective _ _ B.subtype_injective).surjective] at hm
      exact hm.symm
  · apply primeToResidual_le
    rw [index_eq_card]
    obtain ⟨n,hn⟩ := (isPGroup_quotient_pResidual (G := G) 2).exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n

namespace SourceAssembly
universe u
variable {D H : Type u} [Group D] [Finite D] [Group H] [Finite H]
    {κ : GroupClass.{u}} {D₁ D₂ : Subgroup D}

private theorem SingleResidualComponent.not_quasisimple_fitting
    (d : SingleResidualComponent D₁ D₂)
    (hA : ChapterA.Section02.TheoremA κ H)
    (hC : ChapterA.Section02.TheoremC κ (d.component ⧸ center d.component))
    (hH : IsSQTK κ H) (e : D ≃* (H ⧸ pPrimeCore 3 H))
    (h : IsGoldschmidtTriple D₁ D₂)
    (hf : IsQuasisimple (generalizedFitting D)) : False := by
  have hz : pCore 2 D = ⊥ := le_bot_iff.mp
    (twoCore_le_primeToThreeCore.trans (Noncyclic.primeToThreeCore_eq_bot_of_quotient e).le)
  have hb := d.left_not_characteristic_two h hz
  obtain ⟨p,hp,ho,_,hm⟩ := d.prime_psl2_of_either_exceptional hA hC hH e h hz (Or.inl hb)
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨hN,hcard,_,hdisj,_⟩ := d.prime_product e h ho hm
  let N := pResidual 2 D ⊓ centralizer (d.component : Set D)
  have hcardN : Nat.card N = 3 := by simpa [N] using hcard
  let : N.Normal := hN
  let : Group.IsNilpotent N := (IsPGroup.of_card (p := 3) (n := 1) hcardN).isNilpotent
  have hNF : N ≤ generalizedFitting D :=
    (show N ≤ fittingSubgroup D from le_sSup ⟨inferInstance,inferInstance⟩).trans (fitting_le_generalizedFitting D)
  have hcf : d.component = generalizedFitting D :=
    d.isComponent.eq_of_le ⟨(inferInstance : (generalizedFitting D).Normal).isSubnormal,hf⟩
      (component_le_generalizedFitting D _ d.isComponent)
  have hbot : N = ⊥ := le_bot_iff.mp (hdisj.eq_bot ▸
    (le_inf (hNF.trans_eq hcf.symm) le_rfl : N ≤ d.component ⊓ N))
  have hcardbot : Nat.card N = 1 := by rw [hbot]; simp
  omega

theorem twoResidual_eq_fitting_of_quasisimple_fitting
    (hA : ChapterA.Section02.TheoremA κ H)
    (hC : ∀ (L : Type u) [Group L] [Finite L], ChapterA.Section02.TheoremC κ L)
    (hH : IsSQTK κ H) (e : D ≃* (H ⧸ pPrimeCore 3 H))
    (h : IsGoldschmidtTriple D₁ D₂) (hc : IsCyclic (pCore 3 D))
    (hf : IsQuasisimple (generalizedFitting D)) :
    pResidual 2 D = generalizedFitting D := by
  rcases source_F_6_17_reduction hA hH e h hc with hr | hd | hd
  · exact hr.1
  · obtain ⟨d⟩ := hd
    exact (SingleResidualComponent.not_quasisimple_fitting d hA (hC _) hH e h hf).elim
  · obtain ⟨d⟩ := hd
    exact (SingleResidualComponent.not_quasisimple_fitting d hA (hC _) hH e h.symm hf).elim

end SourceAssembly
end CFSG.Quasithin.ChapterF
