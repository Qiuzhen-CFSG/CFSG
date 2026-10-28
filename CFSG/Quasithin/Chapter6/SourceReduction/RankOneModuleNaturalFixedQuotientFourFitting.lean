module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientFourOvergroups
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientFourComponentEscape
public import Theory.GroupTheory.Fitting.OutsideComponent

/-!
# Trapping the ordinary Fitting preimage

Once O₂(M₁) lies in the original S=(T∩L)O₂(LT), S is Sylow in its join
with O₂,F(M₁), since F(M₁/O₂(M₁)) has odd order. That join is solvable,
so the actual E.6.26 overgroup theorem places its Fitting preimage in M.
Together with escape of O₂,F*(M₁), this yields an actual outside component.

The core containment is the separate quintic-core calculation, not a
generation or trapping assumption. Source: Aschbacher--Smith 6.1.4, p.665.
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open OrthogonalFourMinus.FiniteModel RankOneGeneric
variable {G : Type*} [Group G] [Finite G]

private theorem fitting_join_sylow (R : Subgroup G) (hp : IsPGroup 2 R)
    (hQR : pCore 2 G ≤ R) : Chapter1.IsSylowIn 2 R (twoFittingCore G ⊔ R) := by
  let Q := pCore 2 G
  let F := twoFittingCore G
  let q := QuotientGroup.mk' Q
  let f := q.comp F.subtype
  have hk : f.ker = Q.subgroupOf F := by
    ext x
    exact QuotientGroup.eq_one_iff (x : G)
  have hr : f.range = fittingSubgroup (G ⧸ Q) := by
    rw [MonoidHom.range_comp,range_subtype]
    exact map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _
  have hc : Nat.Coprime 2 (Nat.card (fittingSubgroup (G ⧸ Q))) :=
    (pPrimeCore_coprime_card (p := 2) (G := G ⧸ Q)).of_dvd_right
      (card_dvd_of_le (fitting_le_pPrimeCore_of_pCore_eq_bot 2
        (pCore_quotient_pCore_eq_bot 2)))
  have hi : ¬ 2 ∣ (Q.subgroupOf F).index := by
    rw [←hk,index_ker,hr]
    exact Nat.prime_two.coprime_iff_not_dvd.mp hc
  apply IsPGroup.exists_sylow_sup_of_coprime_index F R hp le_normalizer_of_normal
    (Q.subgroupOf F) hi
  rw [map_subgroupOf_eq_of_le (show Q ≤ F from twoCore_le_twoFittingCore)]
  exact hQR

variable {T : Sylow 2 G} {L M V M₁ : Subgroup G} {n s : ℕ} [NeZero s]
local instance fittingFixedAlgebra : Algebra (ZMod 2) (fixedField s) := ZMod.algebra _ 2
local instance fittingBinaryModule : Module (ZMod 2) (Space s) :=
  Module.compHom (Space s) (algebraMap (ZMod 2) (fixedField s))

/-- The ordinary two-Fitting preimage is trapped once the literal quintic
core S contains O₂(M₁). The E-generation and Sylow conclusions are proved. -/
theorem full_reduced_hermitian_fitting_le_of_core_le
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hm : IsConjugationModel L (reducedSubgroup (L ⊔ (T : Subgroup G)))
      (SL2.BinarySmall.hermitian s)) (hs : 1 < s)
    (hM₁ : IsMaximalTwoLocal M₁) (hTM₁ : (T : Subgroup G) ≤ M₁)
    (hQ₁ : M₁.pCoreIn 2 ≤
      ((T : Subgroup G) ⊓ L) ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2) :
    (twoFittingCore M₁).map M₁.subtype ≤ M := by
  let S := ((T : Subgroup G) ⊓ L) ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2
  let F := (twoFittingCore M₁).map M₁.subtype
  let H := F ⊔ S
  have hQT : (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le
      (show (T : Subgroup G) ≤ L ⊔ (T : Subgroup G) from le_sup_right)] using
      pCoreIn_le_sylow (L ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
  have hST : S ≤ (T : Subgroup G) := sup_le inf_le_left hQT
  have hSM₁ := hST.trans hTM₁
  let R := S.subgroupOf M₁
  let D := twoFittingCore M₁ ⊔ R
  have hp : IsPGroup 2 R := (T.isPGroup'.to_le hST).comap_subtype
  have hQR : pCore 2 M₁ ≤ R := fun x hx => hQ₁ (mem_map_of_mem M₁.subtype hx)
  have hDm : D.map M₁.subtype = H := by
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hSM₁]
  have hSyl : Chapter1.IsSylowIn 2 S H := by
    have hh := (Chapter1.IsSylowIn.map_iff M₁.subtype M₁.subtype_injective).mpr
      (fitting_join_sylow R hp hQR)
    rwa [hDm,map_subgroupOf_eq_of_le hSM₁] at hh
  let : Group.IsSolvable D := twoFittingCore_sup_solvable R hp
  let : Group.IsSolvable H := by
    rw [←hDm]
    exact Group.isSolvable_of_surjective
      (f := (D.equivMapOfInjective M₁.subtype M₁.subtype_injective).toMonoidHom)
      (D.equivMapOfInjective M₁.subtype M₁.subtype_injective).surjective
  have hHM₁ : H ≤ M₁ := sup_le (map_subtype_le _) hSM₁
  exact (show F ≤ H from le_sup_left).trans
    (full_reduced_hermitian_inner_sylow_overgroup_le h hout hm hs hM₁ hHM₁ hSyl
      ChapterE.generationParameter_le_one_of_solvable).1

/-- An outside literal C-component of M₁ exists once its ordinary Fitting
preimage is trapped. Quasisimplicity is on its actual two-core quotient. -/
theorem full_reduced_hermitian_exists_component_outside_of_core_le
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hm : IsConjugationModel L (reducedSubgroup (L ⊔ (T : Subgroup G)))
      (SL2.BinarySmall.hermitian s)) (hs : 1 < s)
    (hM₁ : IsMaximalTwoLocal M₁) (hCM₁ : omegaCentralizer T ≤ M₁)
    (hQ₁ : M₁.pCoreIn 2 ≤
      ((T : Subgroup G) ⊓ L) ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2) :
    ∃ K : Subgroup M₁, K.IsCComponent ∧ IsQuasisimple (K ⧸ pCore 2 K) ∧
      ¬ K.map M₁.subtype ≤ M := by
  have hf := full_reduced_hermitian_fitting_le_of_core_le h hout hm hs hM₁
    (sylow_le_omegaCentralizer.trans hCM₁) hQ₁
  have hg := full_reduced_hermitian_component_escape h hout hm hs hM₁ hCM₁
  obtain ⟨K,hK,hq,hnot⟩ := exists_cComponent_outside_of_fitting_preimage_le
    (M.subgroupOf M₁) (map_le_iff_le_comap.mp hf) (fun hh => hg (map_le_iff_le_comap.mpr hh))
  exact ⟨K,hK,hq,fun hh => hnot (map_le_iff_le_comap.mp hh)⟩

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
