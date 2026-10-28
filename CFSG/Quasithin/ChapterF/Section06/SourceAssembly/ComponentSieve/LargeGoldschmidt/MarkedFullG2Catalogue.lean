module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentSieve.LargeGoldschmidt.MarkedFullG2
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentSieve.LargeGoldschmidt.Models
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentModels
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.QuasisimpleCases.DegreeThree.ExponentBounds
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.QuasisimpleCases.DegreeThree.WreathedModels
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.QuasisimpleCases.Mathieu.Component
public import Theory.GroupTheory.SylowSectionExponent

/-!
# The component Sylow in the full binary G₂ source branch

The marked derived overlap embeds into the actual two-residual. Its image
survives the odd central kernel, bounding the component-quotient Sylow from
below by 32 and supplying an order-eight element and noncommutativity.
The full common Sylow bounds the order by 64 and the exponent by eight.
The complete earlier Theorem C catalogue then leaves odd prime degree three
or M₁₂. The concrete marked first-vertex obstruction excludes M₁₂, while
the degree-three exponent bound forces order 32. Comparing with the ambient
Sylow order 64 also proves that the two-residual is proper.

All Sylow invariants and the component-family choice are derived from the
original A/C, SQTK quotient, generalized-Fitting and full amalgam marking.
Source: Aschbacher–Smith F.6.18(11), printed pp.309–310.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.SourceAssembly
open Atlas.G2 Atlas.G2.BinaryParabolicPair
open ChapterA.Section02
universe u
variable {G H : Type u} [Group G] [Finite G] [Group H] [Finite H]
  {κ : GroupClass.{u}} {G₁ G₂ : Subgroup G}

private theorem models_of_sylow_between_32_64
    {Q : Type*} [Group Q] [Finite Q]
    (P : Sylow 2 Q) (hlo : 32 ≤ Nat.card P) (hhi : Nat.card P ≤ 64)
    (he : ∀ x : P, x ^ 8 = 1) (x : P) (hx : orderOf x = 8)
    (hm : IsTheoremCModel Q) :
    (∃ p : ℕ, p.Prime ∧ Odd p ∧ (ClassicalGroup.IsPSL Q 3 p ∨ ClassicalGroup.IsPSU Q 3 p)) ∨
      Nonempty (Q ≃* Sporadic.Mathieu.M12) := by
  have hn128 : ¬ 128 ∣ Nat.card Q := by
    intro hd
    have hh := Nat.le_of_dvd (Nat.card_pos (α := P))
      (P.pow_dvd_card_of_pow_dvd_card (n := 7) hd)
    norm_num at hh
    omega
  rcases ComponentSieve.LargeGoldschmidt.theoremC_models_of_large_sylow_exponent_eight
    P hlo (by omega) he x hx hm with hd | h12 | h22 | h23 | hj2
  · exact .inl hd
  · exact .inr h12
  · obtain ⟨e⟩ := h22
    apply (hn128 _).elim
    rw [Nat.card_congr e.toEquiv,Sporadic.Mathieu.m22_order]
    norm_num
  · obtain ⟨e⟩ := h23
    apply (hn128 _).elim
    rw [Nat.card_congr e.toEquiv,Sporadic.Mathieu.m23_order]
    norm_num
  · obtain ⟨e⟩ := hj2
    apply (hn128 _).elim
    rw [Nat.card_congr e.toEquiv,Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.card_carrier]
    norm_num

theorem full_g2_source_component_sylow
    (hA : TheoremA κ H)
    (hC : TheoremC κ (pResidual 2 G ⧸ center (pResidual 2 G)))
    (hH : IsSQTK κ H) (eG : G ≃* (H ⧸ pPrimeCore 3 H))
    (hFstar : pResidual 2 G = generalizedFitting G)
    (hq : IsQuasisimple (pResidual 2 G))
    (h : IsGoldschmidtTriple G₁ G₂)
    (hM : GreenBook.ExceptionalModels.G2.IsFullAmalgam
      (RankTwoAmalgam.ofSubgroups G₁ (G₁ ⊓ G₂) G₂ inf_le_left inf_le_right)) :
    pResidual 2 G ≠ ⊤ ∧
      ∃ P : Sylow 2 (pResidual 2 G ⧸ center (pResidual 2 G)),
        Nat.card P = 32 ∧ (∀ x : P, x ^ 8 = 1) ∧ ¬ IsMulCommutative P := by
  let K := pResidual 2 G
  have hK : IsComponent G K := ⟨(inferInstance : K.Normal).isSubnormal,hq⟩
  obtain ⟨T,hT⟩ := h.intersection_sylow
  have hMarked := hM
  obtain ⟨m⟩ := hM
  let eT : T ≃* commonSylow := (MulEquiv.subgroupCongr hT).symm.trans m.middle
  have hTc : Nat.card T = 64 := (Nat.card_congr eT.toEquiv).trans card_unipotent_binary
  have heT : ∀ x : T, x ^ 8 = 1 := fun x => eT.injective (by
    simpa only [map_pow,map_one] using commonSylow_pow_eight (eT x))
  let q := QuotientGroup.mk' (center K)
  have hqc : Nat.Coprime 2 (Nat.card q.ker) := by
    rw [QuotientGroup.ker_mk']
    exact (component_center_odd_of_primeToThree_quotient eG hK).coprime_two_left
  obtain ⟨f,hf,_,hfK⟩ := full_g2_marked_inner_sylow_embedding hMarked
  let fK : derivedSylow →* K := f.codRestrict K (fun x => hfK ⟨x,rfl⟩)
  have hiK : Function.Injective fK := fun _ _ he => hf (congrArg Subtype.val he)
  have hS : IsPGroup 2 derivedSylow := derivedSylow.isPGroup'
  have hR : IsPGroup 2 fK.range := hS.of_surjective fK.rangeRestrict fK.rangeRestrict_surjective
  have hqi := injective_comp_subtype_of_coprime_ker q hqc fK.range hR
  let g := q.comp fK
  have hgi : Function.Injective g := by
    intro a b he
    apply hiK
    have hh : (⟨fK a,⟨a,rfl⟩⟩ : fK.range) = ⟨fK b,⟨b,rfl⟩⟩ := hqi he
    exact congrArg Subtype.val hh
  have hgR : IsPGroup 2 g.range := hS.of_surjective g.rangeRestrict g.rangeRestrict_surjective
  obtain ⟨P,hP⟩ := hgR.exists_le_sylow
  let i : derivedSylow →* P := (Subgroup.inclusion hP).comp g.rangeRestrict
  have hi : Function.Injective i := fun _ _ he => hgi (congrArg Subtype.val he)
  have hlo : 32 ≤ Nat.card P := by
    simpa only [card_derivedSylow] using Nat.card_le_card_of_injective i hi
  have hhi : Nat.card P ≤ 64 := (sylow_card_section_le T K q
    (QuotientGroup.mk'_surjective _) P).trans_eq hTc
  have hexp : ∀ x : P, x ^ 8 = 1 := sylow_section_pow_eq_one T heT K q
    (QuotientGroup.mk'_surjective _) P
  obtain ⟨s,hs⟩ := derivedSylow_order_eight
  have hx : orderOf (i s) = 8 := (orderOf_injective i hi _).trans hs
  have hnc : ¬ IsMulCommutative P := by
    intro hcomm
    apply derivedSylow_not_commutative
    exact isMulCommutative_iff.mpr fun a b => hi (by
      simpa only [map_mul] using (isMulCommutative_iff.mp hcomm) (i a) (i b))
  have hm := component_central_quotient_model hA hC hH
    (eG.symm.toMonoidHom.comp (QuotientGroup.mk' _))
    (eG.symm.surjective.comp (QuotientGroup.mk'_surjective _)) hK
  have h32 : Nat.card P = 32 := by
    rcases models_of_sylow_between_32_64 P hlo hhi hexp (i s) hx hm with hd | hm
    · obtain ⟨p,hp,ho,hm⟩ := hd
      have hb : Nat.card P ≤ 32 := hm.elim
        (linear_three_model_sylow_card_le_32 P hexp hp ho)
        (unitary_three_model_sylow_card_le_32 P hexp hp ho)
      omega
    · obtain ⟨j⟩ := hm
      obtain ⟨_,⟨e⟩⟩ := Mathieu.ambient_m12_of_sylow_sixty_four eG hFstar hq j T hTc
      exact (not_mathieu_of_full_g2_amalgam h hMarked e).elim
  refine ⟨?_,P,h32,hexp,hnc⟩
  intro htop
  have hh := component_quotient_sylow_card_of_top eG hK htop T P
  omega
end CFSG.Quasithin.ChapterF.SourceAssembly
