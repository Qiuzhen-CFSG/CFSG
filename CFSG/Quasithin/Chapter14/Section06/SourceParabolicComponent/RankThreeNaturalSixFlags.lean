module
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicComponent.RankThreeNaturalSixResidual
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.InnerMarking
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.SylowGeometry
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.IndexTwo.Intersections
/-!
# The original natural-six flag from its Sylow action

For an actual four-dimensional natural A6 block, pass the original source
point and plane through the same block coordinates. A Sylow subgroup of the
component fixes both spaces. The concrete six-letter flag theorem supplies
one conjugator in A6; inner relabelling of the original BlockModuleModel then
identifies both source images with the canonical flag and preserves the
literal conjugation intertwining.

The source applications derive the Sylow placement, invariance and dimensions
from the original local hypotheses. The residual application also derives
placement, normalization and module containment. The genuine alternating
block identification and the actual order-sixteen branch remain explicit:
the source separately treats the rank-five central cover.

Source: Aschbacher--Smith B.3, C.2.7(3), and 14.6.10(5), printed p.1029.
-/

public noncomputable section
open Subgroup BinaryPermutation Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06.RankThreeNaturalSix
open ChapterC Theory.SpecificGroups.SymmetricSix.BinaryFlags NaturalGeometry
variable {G : Type*} [Group G] [Finite G] (K : Subgroup G)

private def imageSpace (m : BlockModuleModel K action)
    (hW : Nat.card (sourceModule K) = 16) (B : Subgroup G) :
    Submodule (ZMod 2) (natural (Fin 6)) :=
  AddSubgroup.toZModSubmodule 2
    ((B.subgroupOf (sourceModule K)).map (sourceCoordinatesOfCard K m hW).toMonoidHom).toAddSubgroup'

private theorem imageSpace_card (m : BlockModuleModel K action)
    (hW : Nat.card (sourceModule K) = 16) (B : Subgroup G) (hB : B ≤ sourceModule K) :
    Nat.card (imageSpace K m hW B) = Nat.card B := by
  let q := sourceCoordinatesOfCard K m hW
  let E := (B.subgroupOf (sourceModule K)).map q.toMonoidHom
  have he : Nat.card (imageSpace K m hW B) = Nat.card E := by
    exact Nat.card_congr {
      toFun v := ⟨Multiplicative.ofAdd v.val,v.property⟩
      invFun v := ⟨v.val.toAdd,v.property⟩
      left_inv _ := rfl
      right_inv _ := rfl }
  exact he.trans ((card_map_of_injective q.injective).trans
    (Nat.card_congr (subgroupOfEquivOfLe hB).toEquiv))

private theorem coordinates_conjugate (m : BlockModuleModel K action)
    (hW : Nat.card (sourceModule K) = 16) (k : K) (v : sourceModule K)
    (hv : (k : G) * v.val * (k : G)⁻¹ ∈ sourceModule K) :
    sourceCoordinatesOfCard K m hW ⟨(k : G) * v.val * (k : G)⁻¹,hv⟩ =
      action (m.quotientIso (QuotientGroup.mk' (pCore 2 K) k))
        (sourceCoordinatesOfCard K m hW v) := by
  let a := ((blockU K).equivMapOfInjective K.subtype K.subtype_injective).symm v
  have he : ((blockU K).equivMapOfInjective K.subtype K.subtype_injective).symm
      ⟨(k : G) * v.val * (k : G)⁻¹,hv⟩ = blockConjugate K k a := by
    apply ((blockU K).equivMapOfInjective K.subtype K.subtype_injective).injective
    rw [MulEquiv.apply_symm_apply]
    apply Subtype.ext
    change (k : G) * v.val * (k : G)⁻¹ = (k : G) * (a.val : G) * (k : G)⁻¹
    congr 2
    exact (congrArg Subtype.val
      (((blockU K).equivMapOfInjective K.subtype K.subtype_injective).apply_symm_apply v)).symm
  change m.moduleIso (QuotientGroup.mk' _ (_)) = _
  exact (congrArg (fun x => m.moduleIso (QuotientGroup.mk' (blockFixed K) x)) he).trans
    (m.intertwining k a)

private theorem imageSpace_invariant (m : BlockModuleModel K action)
    (hW : Nat.card (sourceModule K) = 16) (B : Subgroup G)
    (S : Sylow 2 K) (hSB : (S : Subgroup K).map K.subtype ≤ normalizer (B : Set G)) :
    ∀ x ∈ ((S : Subgroup K).map
      (m.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K)))).map
        (alternatingGroup (Fin 6)).subtype,
      move x (imageSpace K m hW B) = imageSpace K m hW B := by
  have hi : ∀ k ∈ (S : Subgroup K), ∀ v ∈ imageSpace K m hW B,
      naturalRepresentation (Fin 6)
        (m.quotientIso (QuotientGroup.mk' (pCore 2 K) k)).val v ∈ imageSpace K m hW B := by
    intro k hk v hv
    change Multiplicative.ofAdd v ∈ (B.subgroupOf (sourceModule K)).map
      (sourceCoordinatesOfCard K m hW).toMonoidHom at hv
    obtain ⟨w,hw,he⟩ := hv
    have hw' : (k : G) * w.val * (k : G)⁻¹ ∈ sourceModule K :=
      le_normalizer_iff.mp (normalizer_le_normalizer_characteristic_image K (blockU K))
        k (K.le_normalizer k.property) w w.property
    refine ⟨⟨(k : G) * w.val * (k : G)⁻¹,hw'⟩,
      le_normalizer_iff.mp hSB k (mem_map_of_mem _ hk) w hw,?_⟩
    exact (coordinates_conjugate K m hW k w hw').trans
      (congrArg (action (m.quotientIso (QuotientGroup.mk' (pCore 2 K) k))) he)
  rintro _ ⟨a,⟨k,hk,rfl⟩,rfl⟩
  apply Submodule.eq_of_le_of_finrank_eq ?_ (move_finrank _ _)
  rintro _ ⟨v,hv,rfl⟩
  exact hi k hk v hv



private theorem imageSpace_innerMarking (m : BlockModuleModel K action)
    (hW : Nat.card (sourceModule K) = 16) (B : Subgroup G)
    (a : alternatingGroup (Fin 6)) :
    imageSpace K (m.innerMarking a) hW B = move a.val (imageSpace K m hW B) := by
  apply le_antisymm
  · rintro v ⟨w,hw,he⟩
    refine ⟨(sourceCoordinatesOfCard K m hW w).toAdd,⟨w,hw,rfl⟩,?_⟩
    exact congrArg Multiplicative.toAdd he
  · rintro v ⟨w,⟨u,hu,he⟩,rfl⟩
    refine ⟨u,hu,?_⟩
    exact congrArg (action a) he

/-- One inner marking of the original block identifies both actual Sylow-invariant
source subgroups. No separately chosen point or plane coordinates are required. -/
theorem exists_source_flag_marking (m : BlockModuleModel K action)
    (hW : Nat.card (sourceModule K) = 16) (B Z : Subgroup G)
    (hB : B ≤ sourceModule K) (hZ : Z ≤ sourceModule K)
    (hBc : Nat.card B = 4) (hZc : Nat.card Z = 2)
    (S : Sylow 2 K)
    (hSB : (S : Subgroup K).map K.subtype ≤ normalizer (B : Set G))
    (hSZ : (S : Subgroup K).map K.subtype ≤ normalizer (Z : Set G)) :
    ∃ m' : BlockModuleModel K action,
      (B.subgroupOf (sourceModule K)).map (sourceCoordinatesOfCard K m' hW).toMonoidHom =
        canonicalPlane.toAddSubgroup.toSubgroup ∧
      (Z.subgroupOf (sourceModule K)).map (sourceCoordinatesOfCard K m' hW).toMonoidHom =
        canonicalLine.toAddSubgroup.toSubgroup := by
  let f := m.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  let S' := S.mapSurjective (f := f)
    (m.quotientIso.surjective.comp (QuotientGroup.mk'_surjective _))
  have hd (E : Subgroup G) (hE : E ≤ sourceModule K) (n : ℕ)
      (hc : Nat.card E = 2 ^ n) : Module.finrank (ZMod 2) (imageSpace K m hW E) = n := by
    apply Nat.pow_right_injective (by decide : 2 ≤ 2)
    have he := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := imageSpace K m hW E)
    rw [Nat.card_zmod] at he
    exact he.symm.trans ((imageSpace_card K m hW E hE).trans hc)
  obtain ⟨a,haZ,haB⟩ := sylow_flag_of_between (alternatingGroup (Fin 6)) le_rfl S'
    (imageSpace K m hW Z) (imageSpace K m hW B)
    (hd Z hZ 1 hZc) (hd B hB 2 hBc)
    (imageSpace_invariant K m hW Z S hSZ)
    (imageSpace_invariant K m hW B S hSB)
  refine ⟨m.innerMarking a⁻¹,?_,?_⟩
  · have he : imageSpace K (m.innerMarking a⁻¹) hW B = canonicalPlane := by
      rw [imageSpace_innerMarking,haB]
      exact move_inv a.val canonicalPlane
    exact congrArg (fun U : Submodule (ZMod 2) (natural (Fin 6)) =>
      U.toAddSubgroup.toSubgroup) he
  · have he : imageSpace K (m.innerMarking a⁻¹) hW Z = canonicalLine := by
      rw [imageSpace_innerMarking,haZ]
      exact move_inv a.val canonicalLine
    exact congrArg (fun U : Submodule (ZMod 2) (natural (Fin 6)) =>
      U.toAddSubgroup.toSubgroup) he

omit [Finite G] in
/-- Unpack the genuine alternating block definition into the literal action
used by the rank-three consumer. -/
theorem model_of_alternatingBlock (h : IsAlternatingBlock K 6) :
    Nonempty (BlockModuleModel K action) := by
  obtain ⟨rho,⟨m⟩,he⟩ := h.2.2
  have hr : rho = action := by
    ext a v : 2
    exact Multiplicative.toAdd.injective (he a v)
  exact hr ▸ ⟨m⟩

end CFSG.Quasithin.Chapter14.Section06.RankThreeNaturalSix

namespace CFSG.Quasithin.Chapter14.Section06
open ChapterC SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open RankThreeNaturalSix
variable {G : Type*} [Group G] [Finite G]

/-- In the actual four-dimensional natural-six branch the source Sylow
subgroup determines the flag, so no additional coordinate marks are inputs. -/
theorem source_parabolic_naturalSix_rank_three_of_sylow
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (I I2 K : Subgroup G) (hKI : K ≤ I) (hKN : (K.subgroupOf I).Normal)
    (hSyl : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ I) I)
    (hI2I : I2 ≤ I) (hI2H : I2 ≤ H) (hI2M : ¬ I2 ≤ M)
    (hblock : IsAlternatingBlock K 6)
    (hW : Nat.card (RankThreeNaturalSix.sourceModule K) = 16)
    (hVW : localModule T M ≤ RankThreeNaturalSix.sourceModule K) :
    IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) I2) ∧
      Nat.card (conjugateSpanBy (localModule T M) I2) = 8 ∧
      primeRank 2 (conjugateSpanBy (localModule T M) I2) = 3 := by
  obtain ⟨m⟩ := model_of_alternatingBlock K hblock
  obtain ⟨S,hS⟩ := Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal hSyl hKI
    hKN.isSubnormal
  have hST : (S : Subgroup K).map K.subtype ≤ (T : Subgroup G) :=
    hS.le.trans (inf_le_left.trans inf_le_left)
  have hTV : (T : Subgroup G) ≤ normalizer (localModule T M : Set G) :=
    hM.1.2.trans (le_normalizer_conjugateSpanBy _ _)
  have hTZ : (T : Subgroup G) ≤ normalizer (centralInvolutions T : Set G) :=
    (le_centralizer_iff.mpr (centralInvolutions_le_centralizer_sylow T)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hZV : centralInvolutions T ≤ localModule T M := le_conjugateSpanBy _ _
  obtain ⟨m',hp,hz⟩ := exists_source_flag_marking K m hW
    (localModule T M) (centralInvolutions T) hVW (hZV.trans hVW) hcard
    (plane_centralInvolutions_card T M hM.1.2 hcard e) S (hST.trans hTV) (hST.trans hTZ)
  exact source_parabolic_naturalSix_rank_three hG T hempty hM hunique hmany hcard e H hH
    I I2 K hKI hKN hI2I hI2H hI2M m' hW hVW hp hz

end CFSG.Quasithin.Chapter14.Section06
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open ChapterC RankThreeNaturalSix
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry
variable {G : Type*} [Group G] [Finite G]

variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (u : G) (hu : u ∈ conjugateSpanBy (localModule T M) H)
    (hindex : (suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u).relIndex
        (T : Subgroup G) = 2)
    (hmove : ¬ Mc.pCoreIn 2 ≤ centralizer ({u} : Set G))
    (hproduct : ∀ t ∈ (T : Subgroup G), t ∉ suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u →
        ¬ Mc.pCoreIn 2 ≤ centralizer ({u * (MulAut.conj t⁻¹) u} : Set G))
    (hU3 : Mc ⊓ normalizer (suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u : Set G) =
        (T : Subgroup G))
    (hlocal : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({u} : Set G))
      (H ⊓ centralizer ({u} : Set G)))
include hG hempty hM hunique hmany hcard e hab H hH hu hindex hmove hproduct hU3 hlocal

/-- The residual and Sylow producers discharge placement, normalization, module
containment and both flag marks in the literal four-dimensional natural-six branch. -/
theorem source_parabolic_residual_naturalSix_rank_three_of_block
    (hrank : 4 ≤ Nat.log 2 ((centralizer (H.pCoreIn 2 : Set G)).relIndex
      (conjugateSpanBy (localModule T M) H)))
    (I I2 : Subgroup G)
    (hI : I ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M))
    (hSI2 : (T : Subgroup G) ⊓ I ≤ I2) (hI2H : I2 ≤ H)
    (hquot2 : Nonempty ((I2 ⧸ pCore 2 I2) ≃* Equiv.Perm (Fin 3)))
    (hout : ¬ I ⊓ M ≤ Mc)
    (hgen : ((pResidual 2 (sourceResidual M Mc ⊓ I : Subgroup G)).map
      (sourceResidual M Mc ⊓ I).subtype ⊔ ((T : Subgroup G) ⊓ I)) ⊔ I2 = I)
    (K : Subgroup I) (hKr : K = pResidual 2 I)
    (hblock : IsAlternatingBlock (K.map I.subtype) 6)
    (hW : Nat.card (RankThreeNaturalSix.sourceModule (K.map I.subtype)) = 16) :
    IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) I2) ∧
      Nat.card (conjugateSpanBy (localModule T M) I2) = 8 ∧
      primeRank 2 (conjugateSpanBy (localModule T M) I2) = 3 := by
  let C := K.map I.subtype
  have hI2I : I2 ≤ I := le_sup_right.trans hgen.le
  have hI2M : ¬ I2 ≤ M := by
    intro hh
    apply hI.1.2.2.2
    rw [←hgen]
    exact sup_le (sup_le (((map_subtype_le _).trans inf_le_left).trans
      (sourceResidual_le M Mc)) (inf_le_left.trans hM.1.2)) hh
  let : K.Normal := by rw [hKr]; infer_instance
  have hn : (C.subgroupOf I).Normal := by
    change ((K.map I.subtype).comap I.subtype).Normal
    rw [comap_map_eq_self_of_injective I.subtype_injective K]
    infer_instance
  have hmod := source_parabolic_span_le_component_module hG T hempty hM hunique hmany
    hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal hrank I I2 hI hSI2 hI2H
    hquot2 hout hgen K hKr
  have hSyl := (source_suitable_intersection_sylow hG T hempty hM hunique hmany
    hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal I hI.1).1
  exact source_parabolic_naturalSix_rank_three_of_sylow hG T hempty hM hunique hmany hcard e H hH
    I I2 C (map_subtype_le _) hn hSyl hI2I hI2H hI2M hblock hW
    ((le_conjugateSpanBy _ _).trans hmod.2)

end CFSG.Quasithin.Chapter14.Section06
