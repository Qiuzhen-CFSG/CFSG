module

public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceOppositeRootComplement
public import Theory.SpecificGroups.SL2.OppositeRootsComplement

/-!
# Recognition of the original opposite-root join

The simultaneous complement retains the original whole Cartan and both
specified roots. Their two distinct full Sylow images generate PSL₂(8), so
their literal join is that complement. The isomorphism retains the original
full-core quotient marking pointwise.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceOppositeRootJoin
open ChapterF.Source ChapterF.Source.SuzukiContainment ChapterF.Source.DGS85.OriginalExtension
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.ReducedCartan
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (eR : (pResidual 2 H ⧸ pCore 2 (pResidual 2 H)) ≃* Theory.PSL2.BinaryGroup 3)
include hG hempty hM hu hmany hcard e hH eR

/-- The literal original root join is a full-core complement with its original
PSL₂(8) quotient marking and the same whole Cartan. -/
theorem source_opposite_root_join
    (c : CompatibleCartans ![locals T M Mc H 1,locals T M Mc H 0]
      (reducedSylow ![locals T M Mc H 1,locals T M Mc H 0] (T : Subgroup G)))
    (R S : Subgroup G) (hRH : R ≤ H) (hSH : S ≤ H)
    (hR : IsPGroup 2 R) (hS : IsPGroup 2 S) (hR8 : Nat.card R = 8) (hS8 : Nat.card S = 8)
    (hkR : Disjoint R (H.pCoreIn 2)) (hkS : Disjoint S (H.pCoreIn 2))
    (hCR : c.D 0 ⊔ c.D 1 ≤ normalizer (R : Set G))
    (hCS : c.D 0 ⊔ c.D 1 ≤ normalizer (S : Set G))
    (hne : (R.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H)) ≠
      (S.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))) :
    (pCore 2 H).IsComplement' ((R ⊔ S).subgroupOf H) ∧
      c.D 0 ⊔ c.D 1 ≤ R ⊔ S ∧
      ∃ f : (R ⊔ S : Subgroup G) ≃* Theory.PSL2.BinaryGroup 3,
        ∀ x, f x = (sourceFirstCoreQuotientEquiv hG T hempty hM hu hmany hcard e H hH eR)
          (QuotientGroup.mk' (pCore 2 H) (inclusion (sup_le hRH hSH) x)) := by
  obtain ⟨K,hK,hCK,hRK,hSK,f,hf⟩ :=
    SourceOppositeRootComplement.source_opposite_root_cartan_complement
      hG T hempty hM hu hmany hcard e H hH eR c R S hRH hSH
      hR hS hR8 hS8 hkR hkS hCR hCS hne
  let R₁ := R.subgroupOf H
  let S₁ := S.subgroupOf H
  let ε := (sourceFirstCoreQuotientEquiv hG T hempty hM hu hmany hcard e H hH eR).trans
    (Theory.PSL2.sl2QuotientEquiv (GaloisField 2 3)).symm
  let q := ε.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  have hq : q.ker = pCore 2 H := by
    rw [MonoidHom.ker_comp_of_injective _ _ ε.injective,QuotientGroup.ker_mk']
  have hle (U : Subgroup G) (hu : U ≤ K.map H.subtype) : U.subgroupOf H ≤ K := by
    intro x hx
    obtain ⟨k,hk,he⟩ := hu hx
    exact (Subtype.ext he : k = x) ▸ hk
  have hn : R₁.map q ≠ S₁.map q := by
    intro he
    apply hne
    apply Subgroup.map_injective (f := ε.toMonoidHom) ε.injective
    simpa only [Subgroup.map_map] using he
  obtain ⟨hjoin,_⟩ := Matrix.SpecialLinearGroup.opposite_roots_eq_complement q K
    (hq.symm ▸ hK) R₁ S₁ (hle R hRK) (hle S hSK)
    (hR.of_equiv (subgroupOfEquivOfLe hRH).symm)
    (hS.of_equiv (subgroupOfEquivOfLe hSH).symm)
    (by rw [Nat.card_congr (subgroupOfEquivOfLe hRH).toEquiv,hR8,
      GaloisField.card 2 3 (by decide)]; decide)
    (by rw [Nat.card_congr (subgroupOfEquivOfLe hSH).toEquiv,hS8,
      GaloisField.card 2 3 (by decide)]; decide) hn
  have hJK : (R ⊔ S).subgroupOf H = K := by
    rw [subgroupOf_sup hRH hSH]
    exact hjoin
  have hmap : K.map H.subtype = R ⊔ S := by
    rw [←hJK,map_subgroupOf_eq_of_le (sup_le hRH hSH)]
  let j : (R ⊔ S : Subgroup G) ≃* K :=
    (subgroupOfEquivOfLe (sup_le hRH hSH)).symm.trans (MulEquiv.subgroupCongr hJK)
  refine ⟨hJK.symm ▸ hK,hmap ▸ hCK,j.trans f,?_⟩
  intro x
  exact hf (j x)

end CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceOppositeRootJoin
