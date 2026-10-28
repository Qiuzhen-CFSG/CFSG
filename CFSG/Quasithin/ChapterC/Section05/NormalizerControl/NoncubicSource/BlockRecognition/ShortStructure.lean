module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.Kernel
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.Commutation.Quotient
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.LargerSource
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore
/-!
# The short-block structure of the actual auxiliary span

The original source identities identify U(L) with the moved elementary
subgroup. Perfectness passes from K to its conjugate span; the inherited
characteristic-two property gives F*(L)=O₂(L). The actual action kernel
identifies L/O₂(L) with its A₇ image. Together with the intrinsic invariant
interval, these give all fields of IsShort for the literal L.
Source: Aschbacher–Smith C.5.13, printed p.163.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl
open ConjugateSource.RankOne Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]
private theorem perfect_twoPerfect {A : Type*} [Group A] [Finite A]
    [Group.IsPerfect A] : IsPPerfect 2 A := by
  intro H hH hq
  let : H.Normal := hH
  by_contra hne
  let : Nontrivial (A ⧸ H) := QuotientGroup.nontrivial_iff.mpr hne
  let : Group.IsPerfect (A ⧸ H) := Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective H)
  let : Group.IsNilpotent (A ⧸ H) := hq.isNilpotent
  exact Group.IsPerfect.not_isSolvable (A ⧸ H) inferInstance

theorem source_short_of_interval (K T X : Subgroup G)
    (hK : IsChiZeroBlock K) (h3 : ¬ IsAlternatingBlock K 3)
    (hT : IsPGroup 2 T) (hUT : U K ≤ T) (hTK : T ≤ normalizer (K : Set G))
    (P : Sylow 2 (K ⊔ T : Subgroup G))
    (hP : (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T)
    (hA : K ⊔ T ∈ Chapter1.He G) (hAX : K ⊔ T ≤ X) (hX : X ∈ Chapter1.He G)
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = T)
    (hmodel : let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
      let V := conjugateSpanBy (omegaOneCenterAmbient T) N
      let hs := noncubic_source_span K T X hK h3 hT hUT hTK P hP hA hAX S hS
      let : (V.subgroupOf N).Normal := (normal_subgroupOf_iff_le_normalizer hs.2.1).mpr hs.2.2.1
      IsAlternating (DualOffender.closureImage (V.subgroupOf N) (K.subgroupOf N)) 7)
    (hirr : BlockModuleIrreducible (conjugateSpanBy K
      (X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)))) :
    IsShort (conjugateSpanBy K (X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G))) := by
  let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
  let V := conjugateSpanBy (omegaOneCenterAmbient T) N
  let L := conjugateSpanBy K N
  have hs := noncubic_source_span K T X hK h3 hT hUT hTK P hP hA hAX S hS
  let : (V.subgroupOf N).Normal := (normal_subgroupOf_iff_le_normalizer hs.2.1).mpr hs.2.2.1
  let : IsElementaryAbelian 2 V := hs.1
  have hf := noncubic_auxiliary_local_family K T X hK h3 hTK hAX hX S hS
  have hKN : K ≤ N := hf.1.1
  have hLN : L ≤ N := conjugateSpanBy_le_self hKN
  let : (L.subgroupOf N).Normal := DualOffender.source_span_normal K N hKN
  have hcore := DualOffender.noncubic_source_moved_core K T X hK h3 hT hUT hTK P hP hA hAX S hS
  have hULV : U L ≤ V := hcore.2.2.2.2.symm.le.trans
    (le_normalizer_iff_commutator_le_left.mp (hLN.trans hs.2.2.1))
  let i : blockU L →* V := (L.subtype.comp (blockU L).subtype).codRestrict V
    (fun u => hULV (mem_map_of_mem L.subtype u.property))
  have hi : Function.Injective i := by
    intro a b hab
    exact Subtype.ext (Subtype.ext (congrArg (fun x : V => (x : G)) hab))
  have helem : IsElementaryAbelian 2 (blockU L) := {
    toIsMulCommutative := IsMulCommutative.of_comm (fun a b => hi (by rw [map_mul, map_mul]; exact mul_comm (i a) (i b)))
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun u => hi (by
      rw [map_pow,map_one]
      exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 V) (i u))) }
  have hshortK := hK.chi.short
  let : IsQuasisimple (K ⧸ pCore 2 K) := noncubic_quotient_quasisimple hK h3
  let : Group.IsPerfect K := BlockCommutation.perfect_of_quasisimple_quotient hshortK
  let : Group.IsPerfect L := conjugateSpanBy_isPerfect K N
  have hfit : generalizedFitting L = pCore 2 L :=
    generalizedFitting_eq_pCore_of_selfCentralizing 2 (Chapter1.mem_He_iff.mp
      (pCoreIn_selfCentralizing_of_subnormal hf.2.1 hLN
        (inferInstance : (L.subgroupOf N).Normal).isSubnormal))
  have hLC : L.pCoreIn 2 ≤ N.pCoreIn 2 :=
    pCoreIn_mono_of_normalizes hLN (le_normalizer_conjugateSpanBy K N)
  have hVC : V ≤ centralizer (N.pCoreIn 2 : Set G) := by
    intro v hv c hc
    obtain ⟨c,hc,rfl⟩ := hc
    exact congrArg N.subtype (hs.2.2.2.2.2.2.1.le_centralizer_pCore (show (⟨v,hs.2.1 hv⟩ : N) ∈ V.subgroupOf N from hv) c hc)
  have hcentral : blockU L ≤ centralizer (pCore 2 L : Set L) := by
    intro u hu c hc
    apply Subtype.ext
    exact hVC (hULV (mem_map_of_mem L.subtype hu)) c
      (hLC (mem_map_of_mem L.subtype hc))
  have hq : IsQuasisimple (L ⧸ pCore 2 L) := by
    let C := DualOffender.closureImage (V.subgroupOf N) (K.subgroupOf N)
    let : IsSimpleGroup C := EmbeddingSelection.AlternatingSevenMaximal.simple_of_model hmodel
    let : Group.IsPerfect C := EmbeddingSelection.AlternatingSevenMaximal.perfect_of_model hmodel
    let : IsQuasisimple C := {
      toIsPerfect := inferInstance
      simple := by
        let e := (QuotientGroup.quotientMulEquivOfEq
          (EmbeddingSelection.AlternatingSevenMaximal.center_of_model hmodel)).trans QuotientGroup.quotientBot
        exact e.isSimpleGroup }
    obtain ⟨e⟩ := (EmbeddingSelection.source_component_kernel K T X hK h3 hT hUT hTK P hP hA hAX hX S hS).2.1
    let f := subgroupOfEquivOfLe hLN
    let e' := QuotientGroup.congr _ _ f (pCore_map_iso 2 f)
    exact IsQuasisimple.of_mulEquiv (e.symm.trans e')
  exact ⟨inferInstance,perfect_twoPerfect,hfit,helem,hcentral,Or.inl hq,hirr⟩
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl
