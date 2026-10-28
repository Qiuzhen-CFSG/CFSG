module
public import CFSG.Quasithin.Chapter14.Section06.SourceTransitiveFactors
public import CFSG.Quasithin.Chapter14.Section06.SourceCyclicStructure
public import CFSG.Quasithin.ChapterD.Section02.RatioDecomposition.SingletonSupport
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.KernelResidual
public import Theory.ElementaryAbelian.Injective

/-!
# The cyclic-star singleton in the original plane branch

The unique factor is the actual minimum-actor subgroup in J/O₂(J).
The image of its endpoint kernel is a nontrivial normal subgroup of the
primitive elementary residual, and hence is that entire residual. This
excludes the extraspecial endpoint and leaves a cyclic residual or the
literal elementary-nine residual on a four-dimensional moved space. In the
nine case the endpoint involution is starred and has fixed codimension two,
so transport through the actual factor gives ambient cubic minimum two.

These results retain the full original ambient hypotheses and the original
quotient and factor embeddings. They do not exclude elementary nine or
prove cyclicity of the starred actors in a general singleton.

Source: Aschbacher--Smith 14.6.11--12, printed pp.1030--1031, and
D.2.17(1)--(4), printed p.188.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam
variable {G : Type*} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
include hG hempty hM hu hmany hcard e hab

/-- The endpoint kernel maps onto the literal primitive odd residual. -/
theorem source_ratio_singleton_kernel_eq_residual
    (J : Subgroup G) (hJ : J ∈ Chapter3.HStar (T : Subgroup G) M)
    (hs : Group.IsSolvable J)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)]
    (a : LocalQuotientAction J (conjugateSpanBy (localModule T M) J) (centralInvolutions T))
    (f : ChapterD.RatioDecomposition.FactorData a.representation
      (ChapterD.Jhat a.representation)
      (subspaceCommutator a.representation ⊤ (pResidual 2 (J ⧸ pCore 2 J))))
    (d : ChapterD.RatioDecomposition.Decomposition f.representation)
    (i : d.Index) (hi : ∀ j : d.Index, j = i)
    (l : ChapterD.CyclicSource.LocalGeneration (d.factor i).action) :
    l.kernel.map (f.ambientFactor d i).embedding.groupMap =
      pResidual 2 (J ⧸ pCore 2 J) := by
  let K := ChapterD.Jhat a.representation
  let P := pResidual 2 (J ⧸ pCore 2 J)
  let g : (d.factor i).Carrier →* (J ⧸ pCore 2 J) :=
    (ChapterD.Jhat a.representation).subtype.comp (d.factor i).embedding.groupMap
  have hg : Function.Injective g :=
    (ChapterD.Jhat a.representation).subtype_injective.comp (d.factor i).embedding.group_injective
  let B := l.kernel.map g
  let : K.Normal := ChapterD.Jhat_normal a.representation
  have hrange : g.range = K := f.unique_factor_actor d i hi
  let q : (d.factor i).Carrier →* K := g.codRestrict K (fun x => hrange ▸ (show g x ∈ g.range from ⟨x,rfl⟩))
  have honto : Function.Surjective q := by
    intro x
    obtain ⟨y,hy⟩ := (show (x : J ⧸ pCore 2 J) ∈ g.range from hrange.symm ▸ x.property)
    exact ⟨y,Subtype.ext hy⟩
  have hB : B = (pResidual 2 K).map K.subtype := by
    rw [show B = l.kernel.map g from rfl, l.kernel_eq_twoResidual]
    have he := map_pResidual_of_surjective 2 q honto
    calc
      _ = ((pResidual 2 (d.factor i).Carrier).map q).map K.subtype := by
        rw [map_map]
        rfl
      _ = _ := by rw [he]
  have hBn : B.Normal := by rw [hB]; infer_instance
  have hBP : B ≤ P := by rw [hB]; exact map_pResidual_le 2 K.subtype
  have hBne : B ≠ ⊥ := fun hz => l.nontrivial
    ((map_eq_bot_iff_of_injective _ hg).mp hz)
  obtain ⟨_,_,_,_,_,hmin⟩ := source_solvable_minimal_elementary_residual
    hG T hempty hM hu hmany hcard e hab J hJ hs
  exact (hmin B hBn hBP).resolve_left hBne

/-- The cyclic-star singleton leaves only the cyclic and elementary-nine endpoints. -/
theorem source_ratio_singleton_cyclicStar_alternatives
    (J : Subgroup G) (hJ : J ∈ Chapter3.HStar (T : Subgroup G) M)
    (hs : Group.IsSolvable J)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)]
    (a : LocalQuotientAction J (conjugateSpanBy (localModule T M) J) (centralInvolutions T))
    (f : ChapterD.RatioDecomposition.FactorData a.representation
      (ChapterD.Jhat a.representation)
      (subspaceCommutator a.representation ⊤ (pResidual 2 (J ⧸ pCore 2 J))))
    (d : ChapterD.RatioDecomposition.Decomposition f.representation) (hd : d.FittingFull)
    (i : d.Index) (hi : ∀ j : d.Index, j = i)
    (hc : ∀ A ∈ ChapterD.QhatStar (d.factor i).action, IsCyclic A) :
    IsCyclic (pResidual 2 (J ⧸ pCore 2 J)) ∨
      (IsElementaryAbelian 3 (pResidual 2 (J ⧸ pCore 2 J)) ∧
        Nat.card (pResidual 2 (J ⧸ pCore 2 J)) = 9 ∧
        Module.finrank (ZMod 2)
          (subspaceCommutator a.representation ⊤ (pResidual 2 (J ⧸ pCore 2 J))) = 4) := by
  let := hs
  let : (ChapterD.Jhat a.representation).Normal := ChapterD.Jhat_normal a.representation
  obtain ⟨_,_,_,hcover,_,_⟩ := Section02.source_lemma_14_2_2_8_minimal
    hG T hempty hM hu hmany hcard e J hJ
  have hq : cubicRatio a.representation ≤ 2 := (cubicRatio_le_quadraticRatio _).trans
    (source_rankTwo_quadratic_bound_of_action hG T hempty hM hu hmany hcard e hab J hJ.1 a)
  obtain ⟨l⟩ := f.factor_cyclic_localGeneration d (pCore_quotient_pCore_eq_bot 2)
    hq hd hcover (QuotientGroup.mk' (pCore 2 J)) (QuotientGroup.mk'_surjective _) i hc
  have he := source_ratio_singleton_kernel_eq_residual hG T hempty hM hu hmany hcard e hab
    J hJ hs a f d i hi l
  let g : (d.factor i).Carrier →* (J ⧸ pCore 2 J) :=
    (ChapterD.Jhat a.representation).subtype.comp (d.factor i).embedding.groupMap
  have hg : Function.Injective g :=
    (ChapterD.Jhat a.representation).subtype_injective.comp (d.factor i).embedding.group_injective
  let P := pResidual 2 (J ⧸ pCore 2 J)
  change l.kernel.map g = P at he
  have hcyc (hl : IsCyclic l.kernel) : IsCyclic P := by
    let := hl
    have hh : IsCyclic (l.kernel.map g) :=
      isCyclic_of_surjective (g.subgroupMap l.kernel) (g.subgroupMap_surjective l.kernel)
    exact he ▸ hh
  let := Representation.BinaryGroupAction.action (d.factor i).action
  let : Finite (d.factor i).Space := Module.finite_of_finite (ZMod 2)
  let : IsElementaryAbelian 2 (Multiplicative (d.factor i).Space) :=
    Representation.BinaryGroupAction.elementary
  let := l.normal
  rcases l.endpoints (d.factor i).faithful with h3 | h5 | h9 | h27
  · exact Or.inl (hcyc (h3.kernel_equiv.some.isCyclic.mpr inferInstance))
  · exact Or.inl (hcyc (h5.kernel_equiv.some.isCyclic.mpr inferInstance))
  · let := h9.kernel_elementary
    refine Or.inr ⟨?_,?_,?_⟩
    · change IsElementaryAbelian 3 P
      have hh : IsElementaryAbelian 3 (l.kernel.map g) := IsElementaryAbelian.map g
      exact he ▸ hh
    · change Nat.card P = 9
      have hh : Nat.card (l.kernel.map g) = 9 :=
        (card_map_of_injective hg).trans h9.card_kernel
      exact he ▸ hh
    · rw [f.unique_factor_finrank d i hi]
      have hcV : Nat.card (d.factor i).Space = 16 :=
        (Nat.card_congr Multiplicative.toAdd).symm.trans h9.card_module
      have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := (d.factor i).Space)
      rw [hcV,Nat.card_zmod] at hh
      exact Nat.pow_right_injective (by decide : 1 < 2) hh.symm
  · obtain ⟨p,_,hP,_,_,_⟩ := source_solvable_minimal_elementary_residual
      hG T hempty hM hu hmany hcard e hab J hJ hs
    let : IsElementaryAbelian p P := hP
    let j : l.kernel →* P := (g.comp l.kernel.subtype).codRestrict P (fun x => by
      exact he.le (mem_map_of_mem g x.property))
    let : IsElementaryAbelian p l.kernel := IsElementaryAbelian.of_injective j (by
      intro x y hxy
      apply Subtype.ext
      have hh : g (x : (d.factor i).Carrier) = g (y : (d.factor i).Carrier) :=
        congrArg (fun z : P => (z : J ⧸ pCore 2 J)) hxy
      exact hg hh)
    let := h27.kernel_extraspecial
    have hz := IsExtraspecial.center_order_p 3 l.kernel
    rw [center_eq_top,card_top,h27.card_kernel] at hz
    omega

/-- The elementary-nine endpoint has cubic minimum exactly two in the literal quotient action. -/
theorem source_ratio_singleton_nine_ratio_two
    (J : Subgroup G) (hJ : J ∈ Chapter3.HStar (T : Subgroup G) M)
    (hs : Group.IsSolvable J)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)]
    (a : LocalQuotientAction J (conjugateSpanBy (localModule T M) J) (centralInvolutions T))
    (f : ChapterD.RatioDecomposition.FactorData a.representation
      (ChapterD.Jhat a.representation)
      (subspaceCommutator a.representation ⊤ (pResidual 2 (J ⧸ pCore 2 J))))
    (d : ChapterD.RatioDecomposition.Decomposition f.representation) (hd : d.FittingFull)
    (i : d.Index) (hi : ∀ j : d.Index, j = i)
    (hc : ∀ A ∈ ChapterD.QhatStar (d.factor i).action, IsCyclic A)
    (hnine : Nat.card (pResidual 2 (J ⧸ pCore 2 J)) = 9) :
    cubicRatio a.representation = 2 := by
  let := hs
  let : (ChapterD.Jhat a.representation).Normal := ChapterD.Jhat_normal a.representation
  obtain ⟨_,_,_,hcover,_,_⟩ := Section02.source_lemma_14_2_2_8_minimal
    hG T hempty hM hu hmany hcard e J hJ
  have hq : cubicRatio a.representation ≤ 2 := (cubicRatio_le_quadraticRatio _).trans
    (source_rankTwo_quadratic_bound_of_action hG T hempty hM hu hmany hcard e hab J hJ.1 a)
  obtain ⟨l⟩ := f.factor_cyclic_localGeneration d (pCore_quotient_pCore_eq_bot 2)
    hq hd hcover (QuotientGroup.mk' (pCore 2 J)) (QuotientGroup.mk'_surjective _) i hc
  have he := source_ratio_singleton_kernel_eq_residual hG T hempty hM hu hmany hcard e hab
    J hJ hs a f d i hi l
  let g : (d.factor i).Carrier →* (J ⧸ pCore 2 J) :=
    (ChapterD.Jhat a.representation).subtype.comp (d.factor i).embedding.groupMap
  have hg : Function.Injective g :=
    (ChapterD.Jhat a.representation).subtype_injective.comp (d.factor i).embedding.group_injective
  change l.kernel.map g = pResidual 2 (J ⧸ pCore 2 J) at he
  have hk : Nat.card l.kernel = 9 := by
    rw [←he,card_map_of_injective hg] at hnine
    exact hnine
  have htotal : Nat.card (d.factor i).Carrier = 18 := by
    have hh := l.kernel.card_mul_index
    rw [hk,l.kernel_index_two] at hh
    omega
  have ht : Nat.card (zpowers l.involution) = 2 := by
    rw [Nat.card_zpowers,l.order_two]
  have hindex : (zpowers l.involution).index = 9 := by
    have hh := (zpowers l.involution).card_mul_index
    rw [ht,htotal] at hh
    omega
  let S := (IsPGroup.of_card (p := 2) (n := 1) (by simpa using ht)).toSylow
    (show ¬ 2 ∣ (zpowers l.involution).index by rw [hindex]; decide)
  have hstar : zpowers l.involution ∈ ChapterD.QhatStar (d.factor i).action :=
    (source_ratio_factor_starred_sylow hG T hempty hM hu hmany hcard e hab
      J hJ hs a f d hd i _).mpr ⟨S,rfl⟩
  have hr : Representation.BinaryOffender.rank (zpowers l.involution) = 1 := by
    rw [Representation.BinaryOffender.rank,ht]
    decide
  have hcod := ChapterD.CyclicSource.starred_codimension (d.factor i).action hstar hr
  let := Representation.BinaryGroupAction.action (d.factor i).action
  let : Finite (d.factor i).Space := Module.finite_of_finite (ZMod 2)
  let : IsElementaryAbelian 2 (Multiplicative (d.factor i).Space) :=
    Representation.BinaryGroupAction.elementary
  let := l.normal
  rcases l.endpoints (d.factor i).faithful with h3 | h5 | h9 | h27
  · have hh := Nat.card_congr h3.kernel_equiv.some.toEquiv
    change Nat.card l.kernel = Nat.card (ZMod 3) at hh
    rw [Nat.card_zmod] at hh
    omega
  · have hh := Nat.card_congr h5.kernel_equiv.some.toEquiv
    change Nat.card l.kernel = Nat.card (ZMod 5) at hh
    rw [Nat.card_zmod] at hh
    omega
  · have hfcard : Nat.card (FixedPoints.subgroup (zpowers l.involution)
        (Multiplicative (d.factor i).Space)) = 4 := by
      have hh := (FixedPoints.subgroup (zpowers l.involution)
        (Multiplicative (d.factor i).Space)).card_mul_index
      rw [h9.fixed_index,h9.card_module] at hh
      omega
    rw [Representation.BinaryGroupAction.fixedPoints_eq,
      Representation.BinaryGroupAction.card_submoduleEquivSubgroup] at hfcard
    have hdim : Module.finrank (ZMod 2) (d.factor i).Space = 4 := by
      have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := (d.factor i).Space)
      have hv : Nat.card (d.factor i).Space = 16 := h9.card_module
      rw [hv,Nat.card_zmod] at hh
      exact Nat.pow_right_injective (by decide : 1 < 2) hh.symm
    have hfixdim : Module.finrank (ZMod 2)
        (fixedSpace (d.factor i).action (zpowers l.involution)) = 2 := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hfcard
      exact Nat.pow_right_injective (by decide : 1 < 2) hfcard
    have hcd : fixedCodim (d.factor i).action (zpowers l.involution) = 2 := by
      have hh := fixedCodim_add_finrank (d.factor i).action (zpowers l.involution)
      omega
    rw [hcd,(d.factor i).embedding.ratio,f.ratio] at hcod
    exact hcod.symm
  · have hh := h27.card_kernel
    omega


end CFSG.Quasithin.Chapter14.Section06
