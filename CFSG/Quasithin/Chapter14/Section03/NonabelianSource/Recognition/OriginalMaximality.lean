module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.BlockMaximality
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.QuaternionClosure
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.ParabolicOrthogonal
public import Theory.Representation.BinaryConjugationSection.ImageDimensions
public import Theory.Representation.InvertedCubicTensor.NaturalTensorFree

/-!
# Maximal elementary factors from the original orthogonal action

The original marked natural quotient is reconstructed on the literal
parabolic section. Cubic cross pairing and the actual quaternion involution
centralizer prove that its two elementary factors contain every elementary
subgroup of the two-core.

Source: Aschbacher--Smith 14.3.18(4), printed p.996.
-/

@[expose] public noncomputable section
open Subgroup InvertedCubicTensor Theory.GroupTheory
open scoped TensorProduct IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

theorem maximal_elementary_factors_of_full_orthogonal
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
    (dg : ClosureGeometry F) (hZ : F.ZU=F.Vi 1) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g∈F.P (sourceResidual M Mc)) (hgH : g∉F.H)
    (hr : ChapterG.Section09.FittingRecognition.OrthogonalRealization F.terminalRepresentation ⊤) :
    ∃ A B : Subgroup G,
      A≤(F.I₂ (sourceResidual M Mc)).pCoreIn 2 ∧ B≤(F.I₂ (sourceResidual M Mc)).pCoreIn 2 ∧
      rankTwoSeed T M≤A ∧ rankTwoSeed T M≤B ∧
      IsElementaryAbelian 2 A ∧ IsElementaryAbelian 2 B ∧
      Nat.card A=16 ∧ Nat.card B=16 ∧ A⊓B=rankTwoSeed T M ∧
      A⊔B=(F.I₂ (sourceResidual M Mc)).pCoreIn 2 ∧
      Nat.card ((F.I₂ (sourceResidual M Mc)).pCoreIn 2)=64 ∧
      F.I₂ (sourceResidual M Mc)⊔F.H.pCoreIn 2≤normalizer (A:Set G) ∧
      F.I₂ (sourceResidual M Mc)⊔F.H.pCoreIn 2≤normalizer (B:Set G) ∧
      ∀E:Subgroup G,IsElementaryAbelian 2 E→E≤(F.I₂ (sourceResidual M Mc)).pCoreIn 2→E≤A ∨ E≤B := by
  let h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  let L := sourceResidual M Mc
  let : Fact (IsPGroup 2 F.U) := ⟨dg.two⟩
  have hPhi : (frattini F.U).map F.U.subtype=F.Vi 1 := by
    rw [dg.frattini_point]
    exact map_subgroupOf_eq_of_le ((F.le_seed 1).trans (le_conjugateSpanBy _ _))
  have hcomm : ⁅F.U,F.U⁆≤F.Vi 1 := by
    rw [←F.U.map_subtype_commutator]
    exact (map_mono (f:=F.U.subtype) (commutator_le_frattini_of_isPGroup (p:=2))).trans hPhi.le
  have hsquare : ∀u∈F.U,u^2∈F.Vi 1 := fun u hu=>
    hPhi ▸ mem_map_of_mem F.U.subtype (pth_power_mem_frattini_of_isPGroup (p:=2) (⟨u,hu⟩:F.U))
  have hspan : F.U=conjugateSpanBy (F.Vi 2) F.H := by rw [F.last]; rfl
  obtain ⟨e₀,_,hgen,_,hIG,hIN,_,_,hfactor,hPH,hcore,hindex,_⟩ :=
    F.binary_generation (by decide) L h.L_normalizes_seed (h.binarySeedAction_surjective F)
      h.centralizer hcomm hsquare hspan hne g hgP hgH
  obtain ⟨e',u,b,huU,huw,hX,hmarkU,hmarkX⟩ :=
    F.binary_marked_quotient L g hgP hgH hfactor hPH hgen.symm e₀ hcore hindex
  let α : S₃ ≃* S₃ := MulAut.conj (Equiv.swap 0 2)
  let e'' := e'.trans α
  have huMark : F.binaryCoreProjection L e'' u = inverter := by
    rw [F.binaryCoreProjection_apply]
    change α (e' (QuotientGroup.mk' (pCore 2 (F.I₂ L)) u)) = inverter
    rw [←F.binaryCoreProjection_apply L e' u]
    rw [hmarkU u huU huw]
    decide +kernel
  have hsplit := F.binary_core_factorization L g hgP hfactor hPH hgen.symm e'' hcore hindex
  let := F.binary_source_E_normal_in_core L h.L_normalizes_seed g hgP hgen.symm hcomm
  let := F.binary_source_quotient_elementary L h.L_normalizes_seed g hgP hgen.symm hcore
    (F.binary_core_normalizes_U L hfactor hPH) hsplit hcomm hsquare
  obtain ⟨σ,d,_,hfinite,⟨j,hj⟩,hfixed⟩ :=
    F.binary_natural_quotient L h.L_normalizes_seed g hgP hfactor hPH hgen.symm e'' hcore hindex hcomm hsquare
  let := hfinite
  have hmark : d.imageSpace F.W=multiplicitySpace σ := by
    have hf := (hfixed u huU huw).1
    rw [huMark] at hf
    change d.imageSpace F.W = LinearMap.ker (σ inverter - 1)
    exact hf.symm
  have hE : F.E g=rankTwoSeed T M :=
    intersection_eq_seed_of_full_orthogonal hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr
  obtain ⟨dU⟩ := quaternion_closure_of_full_orthogonal F dg hZ hne hr
  have hU : Nat.card F.U=32 := dU.card
  have hWc : Nat.card F.W=16 := by
    have hh := relIndex_mul_card_of_le (show F.W≤F.U from inf_le_left)
    rw [hindex,hU] at hh
    omega
  have hEc : Nat.card (F.E g)=4 := by
    rw [hE]
    simpa only [F.last,show (2:ℕ)^2=4 from rfl] using F.card 2 le_rfl
  have hEW : F.E g≤F.W := inf_le_left
  have hidx : (F.E g).relIndex F.W=2^2 := by
    have hh := relIndex_mul_card_of_le hEW
    rw [hWc,hEc] at hh
    norm_num at *
    omega
  have hW : F.W≤(F.I₂ L).pCoreIn 2 := le_sup_left.trans hsplit.ge
  have hdim : Module.finrank (ZMod 2) (multiplicitySpace σ)=2 := by
    rw [←hmark]
    exact d.imageSpace_finrank_of_index F.W hW 2 hidx
  exact block_maximal_elementary_factors_of_center_point F dU dg hZ L g e'' hIG hIN σ d hE hcore hW hmark
    (cubic_fixed_zero_of_natural_tensor σ j hj) hdim
    (W_involution_generated_of_full_orthogonal F dg hZ hne hr)
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
