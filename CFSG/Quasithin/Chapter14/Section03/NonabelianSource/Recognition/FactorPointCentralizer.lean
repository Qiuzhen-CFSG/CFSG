module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.FactorFullAutomorphism
public import Theory.SpecificGroups.AlternatingSix.NaturalSplit.DeletedPointCentralizer
public import Theory.GroupAction.NormalizerFixedCentralizer
public import Theory.SpecificGroups.AlternatingSix.NaturalSplit.DeletedPointAmbient

/-!
# The marked deleted-point involution in the original source supplement

Strict enlargement of C_G(A) forces the actual supplement D to fill the
pointwise fixer of U. The preimage of the sixth deleted coordinate class
therefore lies in D. Its marked action fixes A, has order two, and is not
inner conjugation by any element of A. The same marking identifies its
centralizer in the natural A₆ block, of order 960, with quotient A₅ by A.
The full normalizer centralizer has order 3840 and quotient S₅ by the
original C_G(A); both denominator containments are proved explicitly.

Source: Aschbacher–Smith 14.3.20, second paragraph, printed pp.997–998.
-/

public noncomputable section
open Subgroup Module Theory.GroupTheory
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open BinaryPermutation.SixNaturalSplit
variable {G:Type*} [Group G] [Finite G]

theorem source_factor_point_of_strict_centralizer
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)]
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g∈F.P (sourceResidual M Mc)) (hgH : g∉F.H)
    (hs : Group.IsSolvable F.TerminalHdot)
    (A:Subgroup G) [IsElementaryAbelian 2 A]
    (hAR:A≤(F.I₂ (sourceResidual M Mc)).pCoreIn 2)
    (hVA:rankTwoSeed T M≤A) (hAc:Nat.card A=16)
    (hc8:Nat.card (A⊓F.U:Subgroup G)=8)
    (hAN:F.I₂ (sourceResidual M Mc)⊔F.H.pCoreIn 2≤normalizer (A:Set G))
    (hlt:A<centralizer (A:Set G)) :
    let N:=F.H⊓normalizer (A:Set G)
    let Y:=(pResidual 2 N).map N.subtype
    let K:=sourceResidual M Mc⊔Y
    let D:=F.H.pCoreIn 2⊓centralizer (F.U:Set G)
    ∃ f:K≃*Model,
      (A.subgroupOf K).map f.toMonoidHom=translations ∧
      (F.U.subgroupOf K).map f.toMonoidHom=canonicalCore ∧
      ∃ d:normalizer (K:Set G),
        (d:G)∈D ∧ (d:G)∈centralizer (A:Set G) ∧ (d:G)∉A ∧
        d^2=1 ∧ MulAut.congr f (K.normalizerMonoidHom d)=pointAutomorphism ∧
        Nat.card (K⊓centralizer ({(d:G)}:Set G):Subgroup G)=960 := by
  intro N Y K D
  obtain ⟨f,hA,hU,j,hj,hact,⟨eFix⟩,_⟩:=source_factor_block_supplement_action_of_solvable
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs A hAR hVA hAc hc8 hAN
  obtain ⟨eD⟩:=source_factor_supplement_dihedral_of_strict_centralizer
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs A hAR hVA hAc hc8 hAN hlt
  have hsurj:Function.Surjective j :=
    (hj.bijective_of_nat_card_le (by
      rw [Nat.card_congr eFix.toEquiv,Nat.card_congr eD.toEquiv])).2
  let eU : fixingSubgroup (MulAut K) (F.U.subgroupOf K : Set K) ≃* canonicalFixer :=
    ((MulAut.congr f).subgroupMap _).trans (MulEquiv.subgroupCongr
      ((MulAut.map_fixingSubgroup_congr f (F.U.subgroupOf K)).trans (by rw [hU]; rfl)))
  let p:canonicalFixer:=⟨pointAutomorphism,pointAutomorphism_fixes_core⟩
  obtain ⟨d0,hd0⟩:=hsurj (eU.symm p)
  have hN:normalizer (K:Set G)=K⊔D :=
    (source_factor_block_normalizer_of_solvable
      hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs A hAR hVA hAc hc8 hAN).1
  have hDN:D≤normalizer (K:Set G) := hN ▸ le_sup_right
  let d:normalizer (K:Set G):=⟨d0,hDN d0.property⟩
  have hjd:K.normalizerMonoidHom d=(j d0:MulAut K) := by
    apply MulEquiv.ext
    intro k
    exact Subtype.ext (hact d0 k).symm
  have hmark:MulAut.congr f (K.normalizerMonoidHom d)=pointAutomorphism := by
    rw [hjd]
    have he:=congrArg (fun a:canonicalFixer=>(a:MulAut Model))
      ((congrArg eU hd0).trans (eU.apply_symm_apply p))
    exact he
  have hb:= (source_factor_full_automorphism_of_strict_centralizer
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs A hAR hVA hAc hc8 hAN hlt).1
  have hd2:d^2=1 := by
    apply hb.1
    apply (MulAut.congr f).injective
    change (MulAut.congr f) (K.normalizerMonoidHom (d^2))=
      (MulAut.congr f) (K.normalizerMonoidHom 1)
    rw [map_pow,map_one,map_pow,map_one,hmark,pointAutomorphism_square]
  have hAK:A≤K := (source_factor_block_split_model_of_solvable
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs A hAR hVA hAc hc8 hAN).1
  have hdC:(d:G)∈centralizer (A:Set G) := by
    intro a ha
    let aK:K:=⟨a,hAK ha⟩
    have hfa:f aK∈translations := hA ▸ mem_map_of_mem f.toMonoidHom ha
    obtain ⟨v,hv⟩:=hfa
    have hp:pointAutomorphism (f aK)=f aK :=
      (MulAut.mem_fixedSubgroup _ _).mp ((pointAutomorphism_fixed_iff _).mpr (by rw [←hv]; rfl))
    have he:=congrArg (fun b:MulAut Model=>b (f aK)) hmark
    change f ((K.normalizerMonoidHom d) (f.symm (f aK)))=pointAutomorphism (f aK) at he
    rw [f.symm_apply_apply,hp] at he
    have heG:=congrArg Subtype.val (f.injective he)
    change (d:G)*a*(d:G)⁻¹=a at heG
    exact (mul_inv_eq_iff_eq_mul.mp heG).symm
  have hdA:(d:G)∉A := by
    intro ha
    let a:K:=⟨d,hAK ha⟩
    have hf:f a∈translations := hA ▸ mem_map_of_mem f.toMonoidHom ha
    obtain ⟨v,hv⟩:=hf
    have hconj:K.normalizerMonoidHom d=MulAut.conj a := by ext k; rfl
    have he:pointAutomorphism=MulAut.conj (SemidirectProduct.inl v) := by
      rw [←hmark,hconj,MulAut.congr_conj,←hv]
    exact pointAutomorphism_not_inner_translation v he
  let ec: (K⊓centralizer ({(d:G)}:Set G):Subgroup G)≃*pointAutomorphism.fixedSubgroup :=
    (normalizerFixedEquivCentralizer K d).symm.trans
      ((MulAut.fixedSubgroupCongr f (K.normalizerMonoidHom d)).trans
        (MulEquiv.subgroupCongr (congrArg MulAut.fixedSubgroup hmark)))
  refine ⟨f,hA,hU,d,d0.property,hdC,hdA,hd2,hmark,?_⟩
  exact (Nat.card_congr ec.toEquiv).trans pointAutomorphism_fixed_card


/-- The same marked involution has both literal source centralizer quotients. -/
theorem source_factor_point_centralizers_of_strict_centralizer
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)]
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g∈F.P (sourceResidual M Mc)) (hgH : g∉F.H)
    (hs : Group.IsSolvable F.TerminalHdot)
    (A:Subgroup G) [IsElementaryAbelian 2 A]
    (hAR:A≤(F.I₂ (sourceResidual M Mc)).pCoreIn 2)
    (hVA:rankTwoSeed T M≤A) (hAc:Nat.card A=16)
    (hc8:Nat.card (A⊓F.U:Subgroup G)=8)
    (hAN:F.I₂ (sourceResidual M Mc)⊔F.H.pCoreIn 2≤normalizer (A:Set G))
    (hlt:A<centralizer (A:Set G)) :
    let N:=F.H⊓normalizer (A:Set G)
    let Y:=(pResidual 2 N).map N.subtype
    let K:=sourceResidual M Mc⊔Y
    let D:=F.H.pCoreIn 2⊓centralizer (F.U:Set G)
    ∃ f:K≃*Model,
      (A.subgroupOf K).map f.toMonoidHom=translations ∧
      (F.U.subgroupOf K).map f.toMonoidHom=canonicalCore ∧
      ∃ d:normalizer (K:Set G),
        (d:G)∈D ∧ (d:G)∈centralizer (A:Set G) ∧ (d:G)∉A ∧
        orderOf (d:G)=2 ∧ MulAut.congr f (K.normalizerMonoidHom d)=pointAutomorphism ∧
        Nat.card (K⊓centralizer ({(d:G)}:Set G):Subgroup G)=960 ∧
        A≤K⊓centralizer ({(d:G)}:Set G) ∧
        (∃ hn:(A.subgroupOf (K⊓centralizer ({(d:G)}:Set G))).Normal,
          letI:=hn
          Nonempty (((K⊓centralizer ({(d:G)}:Set G):Subgroup G) ⧸
            A.subgroupOf (K⊓centralizer ({(d:G)}:Set G)))≃*alternatingGroup (Fin 5))) ∧
        Nat.card (normalizer (A:Set G)⊓centralizer ({(d:G)}:Set G):Subgroup G)=3840 ∧
        centralizer (A:Set G)≤normalizer (A:Set G)⊓centralizer ({(d:G)}:Set G) ∧
        (let C:=normalizer (A:Set G)⊓centralizer ({(d:G)}:Set G)
          ∃ hn:((centralizer (A:Set G)).subgroupOf C).Normal,
            letI:=hn
            Nonempty ((C ⧸ (centralizer (A:Set G)).subgroupOf C)≃*Equiv.Perm (Fin 5))) := by
  intro N Y K D
  obtain ⟨f,hA,hU,d,hdD,hdC,hdA,hd2,hmark,hc⟩:=source_factor_point_of_strict_centralizer
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs A hAR hVA hAc hc8 hAN hlt
  have hAK:A≤K := (source_factor_block_split_model_of_solvable
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs A hAR hVA hAc hc8 hAN).1
  have hnorm:normalizer (A:Set G)=normalizer (K:Set G) :=
    (source_factor_block_normalizer_of_solvable
      hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs A hAR hVA hAc hc8 hAN).2
  have hb:= (source_factor_full_automorphism_of_strict_centralizer
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs A hAR hVA hAc hc8 hAN hlt).1
  have hdo:orderOf (d:G)=2 := orderOf_eq_prime (congrArg Subtype.val hd2) (by
    intro hh
    exact hdA (hh.symm ▸ A.one_mem))
  have hAC:A≤K⊓centralizer ({(d:G)}:Set G) := by
    intro a ha
    exact ⟨hAK ha,mem_centralizer_singleton_iff.mpr (hdC a ha)⟩
  have hEA: IsElementaryAbelian 2 (centralizer (A:Set G)) :=
    (source_factor_centralizer_elementary_of_solvable
      hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs A hAR hVA hAc hc8 hAN).1
  let :=hEA
  have hCC:centralizer (A:Set G)≤normalizer (A:Set G)⊓centralizer ({(d:G)}:Set G) := by
    intro c hc
    refine ⟨_root_.centralizer_le_normalizer A hc,mem_centralizer_singleton_iff.mpr ?_⟩
    exact congrArg Subtype.val (mul_comm (⟨c,hc⟩:centralizer (A:Set G)) ⟨d,hdC⟩)
  refine ⟨f,hA,hU,d,hdD,hdC,hdA,hdo,hmark,hc,hAC,?_,?_,hCC,?_⟩
  · exact pointBlockCentralizer_quotient K A f hA d hmark
  · rw [hnorm]
    exact pointNormalizerCentralizer_card K f d hmark natural_block_normalizer hb
  · rw [hnorm]
    exact pointNormalizerCentralizer_quotient K A hAK f hA d hmark natural_block_normalizer hb


end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
