module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialNormalizerComplement
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialNormalizerFrattini
public import Theory.GroupTheory.NormalComplementSylowFactorization

/-!
# The original Sylow factorization with the inner kernel retained

The normal three-complement of C_K R₁ allows a three-Sylow of C_K to
be chosen inside N_{C_K R₁}(R₁). Extend it inside M₁ = N_N(R₁), where
N = N_G(K). Since K and C_K are normal in N and N = K C_K M₁,
normal-product Sylow indices give a Sylow B of N with the exact product
B = B_K B_M, where B_K = B ∩ K and B_M = N_B(R₁). Moreover
B ∩ C_K ≤ B_M. The original Baumann-normalizer theorem places B_M
in N_G(L).

This proves the normal-complement/Frattini step in Aschbacher–Smith
14.7.21(1), printed pp.1049–1050, with the full inner-action kernel
retained. The later m₃ contradiction, centralizer control and N = H
remain separate source obligations; no conclusion record is assumed.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source Chapter1
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- Choose a three-Sylow of C_K in the literal R₁ normalizer. -/
theorem extraspecial_centralizer_sylow_in_point_normalizer
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    ∃ S : Sylow 3 (normalizerResidualCentralizer F),
      (S : Subgroup _).map (normalizerResidualCentralizer F).subtype ≤
        normalizer (K F : Set G) ⊓ normalizer (F.Ri L 1 : Set G) := by
  let C := normalizerResidualCentralizer F
  let D := C ⊔ F.Ri L 1
  have hDY : D ≤ normalizerPointCentralizer F L := sup_le
    (extraspecial_normalizer_residualCentralizer_le_pointCentralizer h hab structural previous faithful he)
    (isSylowIn_iff.mp (extraspecial_normalizer_point_sylow h hab structural previous faithful he)).2.1
  obtain ⟨R,hR⟩ := (extraspecial_normalizer_point_sylow h hab structural previous faithful he).restrict
    (show F.Ri L 1 ≤ D from le_sup_right) hDY
  obtain ⟨S,hS⟩ := R.exists_le_normalizer_of_normal_complement (by decide : 3 ≠ 2)
    (extraspecial_centralizer_point_normal_complement d h hab structural previous faithful he)
  have hSC := (extraspecial_centralizer_point_sylow_cyclic d h hab structural previous faithful he S).1
  obtain ⟨S',hS'⟩ := (show IsSylowIn 3 ((S : Subgroup D).map D.subtype) D from ⟨S,rfl⟩).restrict
    hSC le_sup_left
  refine ⟨S',?_⟩
  rw [hS']
  refine le_inf ((map_subtype_le _).trans (hDY.trans inf_le_left)) ?_
  have hn := (map_mono hS).trans ((R : Subgroup D).le_normalizer_map D.subtype)
  rwa [hR] at hn

/-- The repaired Sylow factorization in the original normalizer, together
with the actual Baumann-normalizer containment of its second factor. -/
theorem extraspecial_normalizer_three_sylow_factorization
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    ∃ B : Sylow 3 (normalizer (K F : Set G)),
      let B₀ := (B : Subgroup _).map (normalizer (K F : Set G)).subtype
      let B_K := B₀ ⊓ K F
      let B_M := B₀ ⊓ normalizer (F.Ri L 1 : Set G)
      B₀ = B_K ⊔ B_M ∧ (B₀ : Set G) = (B_K : Set G) * (B_M : Set G) ∧
        B₀ ⊓ normalizerResidualCentralizer F ≤ B_M ∧
        B_M ≤ normalizer (L : Set G) := by
  let N := normalizer (K F : Set G)
  let C := normalizerResidualCentralizer F
  let M := N ⊓ normalizer (F.Ri L 1 : Set G)
  have hKN : K F ≤ N := (K F).le_normalizer
  have hCN : C ≤ N := map_subtype_le _
  have hMN : M ≤ N := inf_le_left
  let K' := (K F).subgroupOf N
  let C' := C.subgroupOf N
  let M' := M.subgroupOf N
  let : K'.Normal := normal_subgroupOf_of_le_normalizer (le_rfl : N ≤ normalizer (K F : Set G))
  let : C'.Normal := normal_subgroupOf_of_le_normalizer normalizerResidualCentralizer_normalizes
  obtain ⟨hgen,hML⟩ := extraspecial_normalizer_inner_frattini_source d h hab structural previous faithful earlier he
  have hgen' : K' ⊔ C' ⊔ M' = ⊤ := by
    rw [←subgroupOf_sup hKN hCN,←subgroupOf_sup (sup_le hKN hCN) hMN,hgen,subgroupOf_self]
  obtain ⟨S,hS⟩ := extraspecial_centralizer_sylow_in_point_normalizer d h hab structural previous faithful he
  let e := (subgroupOfEquivOfLe hCN).symm
  let S' := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hSM : (S' : Subgroup C').map C'.subtype ≤ M' := by
    rintro x ⟨y,⟨z,hz,rfl⟩,rfl⟩
    exact hS (mem_map_of_mem C.subtype hz)
  obtain ⟨B,hB,hBC⟩ := Sylow.exists_factor_of_normal_sylow_containment K' C' M' hgen' S' hSM
  let B₀ := (B : Subgroup N).map N.subtype
  have hBN : B₀ ≤ N := map_subtype_le _
  have hBM : B₀ ⊓ M = B₀ ⊓ normalizer (F.Ri L 1 : Set G) := by
    dsimp [M]
    rw [←inf_assoc,inf_of_le_left hBN]
  have hf : B₀ = (B₀ ⊓ K F) ⊔ (B₀ ⊓ normalizer (F.Ri L 1 : Set G)) := by
    have hm := congrArg (Subgroup.map N.subtype) hB
    rw [Subgroup.map_sup,Subgroup.map_inf _ _ _ N.subtype_injective,
      Subgroup.map_inf _ _ _ N.subtype_injective,map_subgroupOf_eq_of_le hKN,
      map_subgroupOf_eq_of_le hMN] at hm
    exact hm.trans (congrArg (fun A => (B₀ ⊓ K F) ⊔ A) hBM)
  have hbc : B₀ ⊓ C ≤ B₀ ⊓ normalizer (F.Ri L 1 : Set G) := by
    have hm := map_mono (f := N.subtype) hBC
    rw [Subgroup.map_inf _ _ _ N.subtype_injective,Subgroup.map_inf _ _ _ N.subtype_injective,
      map_subgroupOf_eq_of_le hCN,map_subgroupOf_eq_of_le hMN] at hm
    exact hm.trans hBM.le
  refine ⟨B,hf,?_,hbc,?_⟩
  · rw [←coe_mul_of_right_le_normalizer_left,←hf]
    exact (le_inf (inf_le_left.trans B₀.le_normalizer) (inf_le_left.trans hBN)).trans
      (inf_normalizer_le_normalizer_inf)
  · exact (le_inf (inf_le_left.trans hBN) inf_le_right).trans hML

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
