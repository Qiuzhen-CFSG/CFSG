module
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingSelectedCentralizerSource
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingFullNormalizerSource
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingSylowSource
public import Theory.SpecificGroups.BinaryFiveAffine.ResidualSylowGeometry
public import Theory.GroupTheory.ConjugateAxisMovement
public import Theory.GroupTheory.ConjugatePairInternalLift
public import Theory.GroupTheory.Commutator.NormalizedIndexTwo
public import Mathlib.GroupTheory.IndexNormal

/-!
# Residual four-group movement in the original alternating-five branch

The residual four-group and its factor-interchanged conjugate span the
natural sixteen-group. An element of Tᵤ outside J preserves J and the
commutator axis, but escapes H=N_G(U). If its conjugate four-group
centralized the original one, the marked Sylow-base calculation would
place both spanning axes in U, a contradiction. Index-two normality
supplies the commutator controlling the two orders of conjugation.

Source: Aschbacher–Smith, 2.4.29, printed pp.545–546.
-/

public section
open Subgroup Stellmacher
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter2
open ChapterC ChapterC.Section05.ConjugateSource ChapterC.Section05.BlockAnalysis
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem MinimalBlockSetup.single_alternating_residual_noncentral_movement_of_marks
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block)
    (hA : IsAlternatingBlock (d.block.map d.H.subtype) 5)
    (hD : (T : Subgroup G) ⊓ centralizer (d.block.map d.H.subtype : Set G) = ⊥)
    (eH : d.H ≃* BinaryFiveAffine.W)
    (hU : ((blockU d.block).map d.block.subtype).map eH.toMonoidHom = BinaryFiveAffine.vectorGroup)
    (hS : (d.S : Subgroup d.H).map eH.toMonoidHom = (BinaryFiveAffine.standardSylow : Subgroup BinaryFiveAffine.W))
    (hSJ : ((d.S : Subgroup d.H).map d.H.subtype) ⊓
      centralizer ({d.affineInvolution eH} : Set G) =
      elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype))
    (hZT : zpowers (d.affineCentralVector eH) ≤ (center (T : Subgroup G)).map (T : Subgroup G).subtype)
    (hTu : ((T : Subgroup G) ⊓ centralizer ({d.affineInvolution eH} : Set G)).relIndex (T : Subgroup G) = 2) :
    ∀ x : G, x ∈ (T : Subgroup G) ⊓ centralizer ({d.affineInvolution eH} : Set G) →
      x ∉ elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) →
      ¬ ((d.affineCentralizerResidual eH).pCoreIn 2).conjBy x⁻¹ ≤
        centralizer ((d.affineCentralizerResidual eH).pCoreIn 2 : Set G) := by
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let J := elementaryAbelianMaxJ S
  let U := sourceModule (d.block.map d.H.subtype)
  let E := (d.affineCentralizerResidual eH).pCoreIn 2
  let u := d.affineInvolution eH
  let z := d.affineCentralVector eH
  let Tu := (T : Subgroup G) ⊓ centralizer ({u} : Set G)
  change S ⊓ centralizer ({u} : Set G) = J at hSJ
  let f : BinaryFiveAffine.W →* G := d.H.subtype.comp eH.symm.toMonoidHom
  have hf : Function.Injective f := d.H.subtype_injective.comp eH.symm.injective
  have hcomp : f.comp eH.toMonoidHom = d.H.subtype := by ext a; simp [f]
  have hfU : BinaryFiveAffine.vectorGroup.map f = U := by
    rw [←hU,map_map,hcomp]
    exact (moduleLayer_map d.H.subtype d.H.subtype_injective d.block).symm
  have hfS : (BinaryFiveAffine.standardSylow : Subgroup BinaryFiveAffine.W).map f = S := by
    rw [←hS,map_map,hcomp]
  have hfJ : BinaryFiveAffine.sylowBase.map f = J := by
    rw [←BinaryFiveAffine.thompson_standardSylow,
      ←elementaryAbelianMaxJ_map_injective f hf,hfS]
  have hfL : BinaryFiveAffine.residualImage.map f = d.affineCentralizerResidual eH := by
    rw [←BinaryFiveAffine.markedResidualImage_map eH,map_map,hcomp]
    exact BinaryFiveAffine.markedResidualImage_ambient_map d.H eH
  have hfE : (BinaryFiveAffine.residualImage.pCoreIn 2).map f = E := by
    rw [map_pCoreIn_of_injective 2 _ f hf,hfL]
  have hfz : f (BinaryFiveAffine.t*BinaryFiveAffine.standardZ) = u*z := by
    rw [map_mul,BinaryFiveAffine.standardZ_eq_centralSingular]; rfl
  have hEJ : E ≤ J := by
    rw [←hfE,←hfJ]
    exact map_mono BinaryFiveAffine.residual_core_le_sylowBase
  have hJE : J ≤ normalizer (E : Set G) := by
    rw [←hfJ,←hfE]
    exact (map_mono BinaryFiveAffine.sylowBase_le_normalizer_residual_core).trans
      ((BinaryFiveAffine.residualImage.pCoreIn 2).le_normalizer_map f)
  have hcomm : ⁅E,J⁆ ≤ zpowers (u*z) := by
    have hh := map_mono (f := f) BinaryFiveAffine.residual_core_commutator_base_le
    simpa only [map_commutator,hfE,hfJ,MonoidHom.map_zpowers,hfz] using hh
  have hcriterion : ∀ B : Subgroup G, B ≤ J → ⁅B,J⁆ ≤ zpowers (u*z) →
      B ≤ centralizer (E : Set G) → B ≤ U := by
    intro B hBJ hBA hBC
    rw [←hfU]
    exact BinaryFiveAffine.le_vectorGroup_map_of_base_centralizes_residual_core_of_commutator
      f hf B (hfJ.symm ▸ hBJ) (hfE.symm ▸ hBC) (by simpa only [hfJ,hfz] using hBA)
  let s := f BinaryFiveAffine.standardSwap
  have hspan : U = E ⊔ E.conjBy s := by
    have hh := congrArg (fun B : Subgroup BinaryFiveAffine.W => B.map f)
      BinaryFiveAffine.residual_core_sup_swap_eq
    simpa only [Subgroup.map_sup,map_conjBy_hom,hfE,hfU] using hh.symm
  obtain ⟨hcore,_,hNU⟩ := d.single_alternating_full_normalizer_of_centralizer_bot
    hG T hM hTM hu hST hsingle hA hD
  have hsS : s ∈ S := hfS ▸ mem_map_of_mem f BinaryFiveAffine.standardSwap_mem
  have hsU : s ∈ normalizer (U : Set G) := by
    rw [hNU]
    exact (map_subtype_le (d.S : Subgroup d.H)) hsS
  obtain ⟨hi,_,hJT⟩ := d.single_alternating_sylow_index_source hG T hM hTM hu hST hsingle hA
  change elementaryAbelianMaxJ (T : Subgroup G) = J at hJT
  have hSN : (S.subgroupOf (T : Subgroup G)).Normal := normal_of_index_eq_two hi
  have hTN : (T : Subgroup G) ≤ normalizer (S : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hST.le).mp hSN
  have hTuN : (Tu.subgroupOf (T : Subgroup G)).Normal := normal_of_index_eq_two hTu
  have hTNu : (T : Subgroup G) ≤ normalizer (Tu : Set G) :=
    (normal_subgroupOf_iff_le_normalizer inf_le_left).mp hTuN
  have hderived : ⁅(T : Subgroup G),(T : Subgroup G)⁆ ≤ J := by
    rw [←hSJ]
    have h1 := commutator_le_of_normalized_index_two (T : Subgroup G) S (T : Subgroup G)
      hST.le hi (T : Subgroup G).le_normalizer hTN
    have h2 := commutator_le_of_normalized_index_two (T : Subgroup G) Tu (T : Subgroup G)
      inf_le_left hTu (T : Subgroup G).le_normalizer hTNu
    exact le_inf h1 (h2.trans inf_le_right)
  have hTJ : (T : Subgroup G) ≤ normalizer (J : Set G) := by
    rw [←hJT]
    exact (T : Subgroup G).le_normalizer.trans
      (normalizer_le_normalizer_elementaryAbelianMaxJ _)
  intro x hx hxJ
  have hxin : x⁻¹ ∈ Tu := Tu.inv_mem hx
  have hxinvJ : x⁻¹ ∉ J := fun hh => hxJ (J.inv_mem_iff.mp hh)
  have hxinvS : x⁻¹ ∉ S := by
    intro hh
    apply hxinvJ
    rw [←hSJ]
    exact ⟨hh,hxin.2⟩
  have hxinvH : x⁻¹ ∉ d.H := by
    intro hh
    let Ti := (T : Subgroup G).comap d.H.subtype
    have hSi : (d.S : Subgroup d.H) ≤ Ti := by
      intro a ha
      exact hST.le (mem_map_of_mem d.H.subtype ha)
    have hTi : Ti = (d.S : Subgroup d.H) :=
      d.S.is_maximal' T.isPGroup'.comap_subtype hSi
    apply hxinvS
    exact mem_map_of_mem d.H.subtype (hTi ▸ (show (⟨x⁻¹,hh⟩ : d.H) ∈ Ti from hxin.1))
  have hxinvU : x⁻¹ ∉ normalizer (U : Set G) := by rwa [hNU]
  have hzx : x⁻¹*z=z*x⁻¹ := by
    obtain ⟨a,ha,he⟩ := hZT (mem_zpowers z)
    have hh := congrArg Subtype.val (mem_center_iff.mp ha (⟨x⁻¹,hxin.1⟩ : (T : Subgroup G)))
    change (a : G) = z at he
    simpa only [coe_mul,he] using hh
  have hux : x⁻¹*u=u*x⁻¹ := mem_centralizer_singleton_iff.mp hxin.2
  have hfix : (MulAut.conj x⁻¹) (u*z) = u*z := by
    change x⁻¹*(u*z)*(x⁻¹)⁻¹=u*z
    calc
      x⁻¹*(u*z)*(x⁻¹)⁻¹ = (x⁻¹*u)*z*(x⁻¹)⁻¹ := by rw [mul_assoc x⁻¹ u z]
      _ = (u*x⁻¹)*z*(x⁻¹)⁻¹ := by rw [hux]
      _ = u*(x⁻¹*z)*(x⁻¹)⁻¹ := by rw [mul_assoc u x⁻¹ z]
      _ = u*(z*x⁻¹)*(x⁻¹)⁻¹ := by rw [hzx]
      _ = u*z := by simp only [mul_assoc,mul_inv_cancel,mul_one]
  have hAx : (zpowers (u*z)).conjBy x⁻¹ = zpowers (u*z) := by
    exact (MonoidHom.map_zpowers _ _).trans (congrArg zpowers hfix)
  exact not_conjBy_le_centralizer_of_span E J U (zpowers (u*z)) x⁻¹ s
    hEJ (hTJ hxin.1) hAx hcomm hcriterion hspan hsU hJE
    (hderived (commutator_mem_commutator ((T : Subgroup G).inv_mem hxin.1)
      ((T : Subgroup G).inv_mem (hST.le hsS)))) hxinvU

theorem MinimalBlockSetup.single_alternating_residual_noncentral_movement_source
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block)
    (hA : IsAlternatingBlock (d.block.map d.H.subtype) 5)
    (hD : (T : Subgroup G) ⊓ centralizer (d.block.map d.H.subtype : Set G) = ⊥) :
    ∃ eH : d.H ≃* BinaryFiveAffine.W,
      ((blockU d.block).map d.block.subtype).map eH.toMonoidHom = BinaryFiveAffine.vectorGroup ∧
      (d.S : Subgroup d.H).map eH.toMonoidHom = (BinaryFiveAffine.standardSylow : Subgroup BinaryFiveAffine.W) ∧
      ∀ x : G, x ∈ (T : Subgroup G) ⊓ centralizer ({d.affineInvolution eH} : Set G) →
        x ∉ elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) →
        ¬ ((d.affineCentralizerResidual eH).pCoreIn 2).conjBy x⁻¹ ≤
          centralizer ((d.affineCentralizerResidual eH).pCoreIn 2 : Set G) := by
  obtain ⟨eH,hU,hS,_,_,_,_,_,_,_,hSJ,hZ,_,_,hZT,_,_,_,_,_,hi,_,_⟩ :=
    d.single_alternating_selected_centralizer_packet hG T hM hTM hu hST hsingle hA hD
  have hzT : zpowers (d.affineCentralVector eH) ≤
      (center (T : Subgroup G)).map (T : Subgroup G).subtype := by
    simpa only [hZ,BinaryFiveAffine.standardZ_eq_centralSingular] using hZT
  exact ⟨eH,hU,hS,d.single_alternating_residual_noncentral_movement_of_marks
    hG T hM hTM hu hST hsingle hA hD eH hU hS hSJ hzT hi⟩

end CFSG.Quasithin.Chapter2
