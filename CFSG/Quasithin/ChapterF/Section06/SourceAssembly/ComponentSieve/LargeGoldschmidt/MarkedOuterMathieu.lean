module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentSieve.LargeGoldschmidt.OuterSylow
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentSieve.LargeGoldschmidt.MarkedMathieu
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.QuasisimpleCases.Mathieu.OuterExponent
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.QuasisimpleCases.Mathieu.OuterResidual
public import Theory.GroupTheory.SylowSectionExponent
public import Theory.GroupTheory.WreathedThirtyTwo

/-!
# The component quotient of the marked outer Mathieu amalgam

The exact outer marking supplies an inner Sylow of order 64 in the actual
two-residual. The central projection is injective on this two-group because
the residual component center is a three-group. The quotient Sylow therefore
has order between 64 and 128, exponent eight and an element of order eight.
If its order is 128, both section maps are isomorphisms, carrying the marked
unique elementary sixteen into this same quotient Sylow. The full catalogue
and concrete sporadic obstructions then leave only M₁₂.

All section maps, the original Goldschmidt pair and its full amalgam marking
are retained. The only earlier classification inputs are the genuine A/C
statements. Source: Aschbacher–Smith F.6.18(13), printed pp.309–310.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.SourceAssembly
open Sporadic.Mathieu
universe u
variable {G H : Type u} [Group G] [Finite G] [Group H] [Finite H]
  {κ : GroupClass.{u}} {G₁ G₂ : Subgroup G}

theorem residual_quotient_mathieu_of_marked_aut_mathieu
    (hA : ChapterA.Section02.TheoremA κ H)
    (hC : ChapterA.Section02.TheoremC κ (pResidual 2 G ⧸ center (pResidual 2 G)))
    (hH : IsSQTK κ H) (e : G ≃* (H ⧸ pPrimeCore 3 H))
    (h : IsGoldschmidtTriple G₁ G₂)
    (hM : GreenBook.AutMathieuTwelve.IsAutM12Amalgam
      (RankTwoAmalgam.ofSubgroups G₁ (G₁ ⊓ G₂) G₂ inf_le_left inf_le_right))
    (hq : IsQuasisimple (pResidual 2 G)) :
    Nonempty ((pResidual 2 G ⧸ center (pResidual 2 G)) ≃* M12) := by
  let K := pResidual 2 G
  have hK : IsComponent G K := ⟨(inferInstance : K.Normal).isSubnormal,hq⟩
  obtain ⟨T,hT⟩ := h.intersection_sylow
  have hMarked := hM
  obtain ⟨m⟩ := hM
  let em := ((m.trans GreenBook.AutMathieuTwelve.ambientIso.symm).trans
    GreenBook.AutMathieuTwelve.concreteIso).middle
  let eT : T ≃* M12ExceptionalExtension.overlap :=
    (MulEquiv.subgroupCongr hT).symm.trans em
  have hTc : Nat.card T = 128 := (Nat.card_congr eT.toEquiv).trans
    (M12ExceptionalExtension.SecondCoordinates.card_overlap M12ExceptionalExtension.innerModel)
  have heT : ∀ x : T, x ^ 8 = 1 := fun x => eT.injective (by
    simpa only [map_pow,map_one] using Mathieu.aut_m12_sylow_pow_eight (eT x))
  have huT : ∃! E : Subgroup T, IsElementaryAbelian 2 E ∧ Nat.card E = 16 :=
    existsUnique_elementary_subgroup_of_equiv eT.symm aut_m12_sylow_unique_elementary_sixteen
  let q := QuotientGroup.mk' (center K)
  have hqc : Nat.Coprime 2 (Nat.card q.ker) := by
    rw [QuotientGroup.ker_mk']
    obtain ⟨n,hn⟩ := (component_center_is_three_group e hK).exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 2 3).pow_right n
  obtain ⟨f,hf,_,hfK⟩ := Mathieu.outer_marked_inner_sylow_embedding hMarked
  let fK : M12SmallPair.sylowCandidate →* K := f.codRestrict K (fun x => hfK ⟨x,rfl⟩)
  have hiK : Function.Injective fK := fun _ _ he => hf (congrArg Subtype.val he)
  have hS : IsPGroup 2 M12SmallPair.sylowCandidate := M12SmallPair.commonSylow.isPGroup'
  have hR : IsPGroup 2 fK.range := hS.of_surjective fK.rangeRestrict fK.rangeRestrict_surjective
  have hqi := injective_comp_subtype_of_coprime_ker q hqc fK.range hR
  let g := q.comp fK
  have hgi : Function.Injective g := by
    intro a b he
    apply hiK
    have hh : (⟨fK a, ⟨a,rfl⟩⟩ : fK.range) = ⟨fK b, ⟨b,rfl⟩⟩ := hqi he
    exact congrArg Subtype.val hh
  have hgR : IsPGroup 2 g.range := hS.of_surjective g.rangeRestrict g.rangeRestrict_surjective
  obtain ⟨P,hP⟩ := hgR.exists_le_sylow
  let i : M12SmallPair.sylowCandidate →* P := (Subgroup.inclusion hP).comp g.rangeRestrict
  have hi : Function.Injective i := fun _ _ he => hgi (congrArg Subtype.val he)
  have hlo : 64 ≤ Nat.card P := by
    simpa only [M12SmallPair.card_sylowCandidate] using Nat.card_le_card_of_injective i hi
  have hhi : Nat.card P ≤ 128 := (sylow_card_section_le T K q
    (QuotientGroup.mk'_surjective _) P).trans_eq hTc
  have hexp : ∀ x : P, x ^ 8 = 1 := sylow_section_pow_eq_one T heT K q
    (QuotientGroup.mk'_surjective _) P
  let x := i (M12SmallPair.SylowAutomorphismGroup.generator 2)
  have hx : orderOf x = 8 := (orderOf_injective i hi _).trans
    Mathieu.m12_sylow_generator_order_eight
  have hu (hc : Nat.card P = 128) :
      ∃! E : Subgroup P, IsElementaryAbelian 2 E ∧ Nat.card E = 16 := by
    obtain ⟨j⟩ := sylow_equiv_of_section_card_eq T K q
      (QuotientGroup.mk'_surjective _) P (hc.trans hTc.symm)
    exact existsUnique_elementary_subgroup_of_equiv j huT
  have hm := component_central_quotient_model hA hC hH
    (e.symm.toMonoidHom.comp (QuotientGroup.mk' _))
    (e.symm.surjective.comp (QuotientGroup.mk'_surjective _)) hK
  exact ComponentSieve.LargeGoldschmidt.theoremC_mathieu_of_outer_sylow_invariants
    P hlo hhi hexp x hx hu hm
end CFSG.Quasithin.ChapterF.SourceAssembly
