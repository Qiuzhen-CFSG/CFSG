module

public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.CentralizerRestriction.CoverCalculations
public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.CentralizerRestriction.CoverAction
public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.CentralizerRestriction.KernelContainment
public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.NormalizerModule.AbelianSection
public import Theory.GroupTheory.NormalizedSupCard
public import Mathlib.GroupTheory.SpecificGroups.KleinFour

/-!
# Assembly of the two-central HS cover restriction

All local conclusions use the given central quotient map. Conjugating that
marking handles any two-central involution; the cover groups X and R remain
literally embedded in K. The common commutator and Frattini line is central,
and adjoining the ambient center gives a Klein four-group. The normalizer's
four centralizer premises are constructed and applied to its abelian-core
consumer. Only that consumer's independent concrete normalizer data remain
explicit, with their existing producer in `NormalizerModule/ModelGeometry`.

Source: Aschbacher–Smith I.2.2(5), printed pp.411–412 / PDF pp.422–423.
The unrestricted HS covering theorem is assembled by the parent HS task.
-/

public section
open Subgroup Theory.GroupTheory
open Theory.GroupTheory.DoubleCoverCentralizer
open Sporadic.LeechRelated.HS Sporadic.LeechRelated.HS.EvenLocalCandidates
open Sporadic.LeechRelated.HS.EvenLocalCandidates.CentralInvolutionCore
open CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSInner.CoreStructure
namespace CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.CentralizerRestriction
variable {K : Type*} [Group K] [Finite K]

/-- Transport for the original modelMap, without changing its marking. -/
theorem twoCentral_residual_image_and_perfect
    (e : (K ⧸ center K) ≃* Carrier) (hZ : Nat.card (center K) = 2)
    (u : K) (hu : orderOf (modelMap e u) = 2) (hc : TwoCentral (modelMap e u)) :
    (centralizerTwoResidual u).map (modelMap e) = centralizerTwoResidual (modelMap e u) ∧
      Group.IsPerfect (centralizerTwoResidual u) := by
  obtain ⟨g,hg⟩ := isConj_iff.mp ((twoCentral_iff_isConj_e0 _ hu).mp hc).symm
  have h := cover_residual_image_and_perfect (e.trans (MulAut.conj g)) hZ u hg
  refine ⟨?_,h.2⟩
  apply map_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective
  rw [map_map,map_centralizerTwoResidual,MulAut.conj_apply,hg]
  exact h.1

/-- The original quotient map identifies the actual cover and model cores. -/
theorem twoCentral_core_image
    (e : (K ⧸ center K) ≃* Carrier) (hZ : Nat.card (center K) = 2)
    (u : K) (hu : orderOf (modelMap e u) = 2) (hc : TwoCentral (modelMap e u)) :
    (centralizerCore u).map (modelMap e) = centralizerCore (modelMap e u) := by
  have hk : IsPGroup 2 (modelMap e).ker :=
    IsPGroup.of_card (n := 1) (by rw [modelMap_ker,hZ,pow_one])
  change ((centralizerTwoResidual u).pCoreIn 2).map (modelMap e) = _
  rw [map_pCoreIn_of_ker_isPGroup _ hk,(twoCentral_residual_image_and_perfect e hZ u hu hc).1]
  rfl

/-- The source's core commutator-generation equation modulo the central kernel. -/
theorem cover_core_residual_commutator_mod_center
    (e : (K ⧸ center K) ≃* Carrier) (hZ : Nat.card (center K) = 2)
    (u : K) (hu : modelMap e u = e0) :
    ⁅centralizerCore u,centralizerTwoResidual u⁆ ⊔ center K =
      centralizerCore u ⊔ center K := by
  have he : (⁅centralizerCore u,centralizerTwoResidual u⁆).map (modelMap e) =
      (centralizerCore u).map (modelMap e) := by
    rw [map_commutator,cover_core_image e hZ u hu,
      (cover_residual_image_and_perfect e hZ u hu).1,marked_centralizer_core_commutator]
  have he' := congrArg (fun S : Subgroup Carrier => S.comap (modelMap e)) he
  simpa only [comap_map_eq,modelMap_ker] using he'

private theorem marked_mem_coreCenter : e0 ∈ coreCenter e0 := by
  have hc : commonInvolution ∈ center core := by
    rw [← cyclicGenerator_square]
    exact (center core).pow_mem cyclicGenerator_mem_center 2
  refine mem_map.mpr ⟨markedCoreEquiv commonInvolution,?_,commonInvolution_eq_e0⟩
  rw [← map_center_equiv markedCoreEquiv]
  exact mem_map_of_mem _ hc

/-- The upstairs core has nilpotence class at most two, literally in K. -/
theorem twoCentral_core_derived_central
    (e : (K ⧸ center K) ≃* Carrier) (hZ : Nat.card (center K) = 2)
    (u : K) (hu : orderOf (modelMap e u) = 2) (hc : TwoCentral (modelMap e u)) :
    ⁅centralizerCore u,centralizerCore u⁆ ≤ coreCenter u := by
  obtain ⟨g,hg⟩ := isConj_iff.mp ((twoCentral_iff_isConj_e0 _ hu).mp hc).symm
  let e' := e.trans (MulAut.conj g)
  have hm : modelMap e' u = e0 := hg
  obtain ⟨v,_,hv,hd,_,_⟩ := cover_core_square_structure e' hZ u hm
  have hcentral : v ∈ center (centralizerCore u) :=
    cover_core_central_of_image e' hZ u hm v (hv.symm ▸ marked_mem_coreCenter)
  rw [← map_subtype_commutator]
  apply map_mono
  rw [hd]
  exact zpowers_le.mpr hcentral

private theorem involution_zpowers {G : Type*} [Group G] [Finite G]
    {u x : G} (hu : orderOf u = 2) (hx : x ∈ zpowers u) : x = 1 ∨ x = u := by
  classical
  rw [mem_zpowers_iff_mem_range_orderOf,hu] at hx
  obtain ⟨n,hn,he⟩ := Finset.mem_image.mp hx
  have hn2 := Finset.mem_range.mp hn
  have hn01 : n = 0 ∨ n = 1 := by omega
  rcases hn01 with rfl | rfl
  · exact Or.inl (by simpa only [pow_zero] using he.symm)
  · exact Or.inr (by simpa only [pow_one] using he.symm)

/-- The source group ⟨u⟩Z is the actual elementary four-group. -/
theorem twoCentral_central_four
    (e : (K ⧸ center K) ≃* Carrier) (hZ : Nat.card (center K) = 2)
    (u : K) (hu : orderOf (modelMap e u) = 2) (hc : TwoCentral (modelMap e u)) :
    IsKleinFour (zpowers u ⊔ center K : Subgroup K) := by
  have huorder := order_two_of_twoCentral_image e hZ u hu hc
  have hu2 : u ^ 2 = 1 := by rw [← huorder,pow_orderOf_eq_one]
  have huZ : u ∉ center K := by
    intro hz
    have he : modelMap e u = 1 := by
      apply MonoidHom.mem_ker.mp
      rwa [modelMap_ker]
    rw [he,orderOf_one] at hu
    omega
  have hd : Disjoint (zpowers u) (center K) := by
    apply Subgroup.disjoint_def.mpr
    intro x hx hz
    rcases involution_zpowers huorder hx with h | h
    · exact h
    · exact (huZ (h ▸ hz)).elim
  have hcard : Nat.card (zpowers u ⊔ center K : Subgroup K) = 4 := by
    rw [card_sup_eq_mul_of_normalizes_of_disjoint _ _
      ((center_le_centralizer _).trans (centralizer_le_normalizer _)) hd,
      Nat.card_zpowers,huorder,hZ]
  have hsq (x : (zpowers u ⊔ center K : Subgroup K)) : x ^ 2 = 1 := by
    obtain ⟨a,ha,z,hz,he⟩ := mem_sup_of_normal_right.mp x.property
    have ha2 : a ^ 2 = 1 := by
      rcases involution_zpowers huorder ha with rfl | rfl
      · simp
      · exact hu2
    have hz2 : z ^ 2 = 1 := by
      have hh := pow_card_eq_one' (x := (⟨z,hz⟩ : center K))
      rw [hZ] at hh
      exact congrArg Subtype.val hh
    apply Subtype.ext
    change (x : K) ^ 2 = 1
    rw [← he,(show Commute a z from mem_center_iff.mp hz a).mul_pow,ha2,hz2,one_mul]
  let : Nontrivial (zpowers u ⊔ center K : Subgroup K) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard]; decide)
  exact ⟨hcard,(Monoid.exponent_eq_prime_iff Nat.prime_two).mpr
    (fun x hx => orderOf_eq_prime (hsq x) hx)⟩

/-- The completed two-central cover restriction for an actual double cover.
Ambient perfection is supplied in particular by the source quasisimple hypothesis. -/
theorem twoCentral_cover_restriction [Group.IsPerfect K]
    (e : (K ⧸ center K) ≃* Carrier) (hZ : Nat.card (center K) = 2)
    (u : K) (hu : orderOf (modelMap e u) = 2) (hc : TwoCentral (modelMap e u)) :
    orderOf u = 2 ∧ HasUniqueCoreSquareLift u ∧
      center K ≤ centralizerTwoResidual u ∧
      centralizerTwoResidual u ≤ centralizer (coreCenter u : Set K) := by
  obtain ⟨g,hg⟩ := isConj_iff.mp ((twoCentral_iff_isConj_e0 _ hu).mp hc).symm
  exact ⟨order_two_of_twoCentral_image e hZ u hu hc,
    twoCentral_hasUniqueCoreSquareLift e hZ u hu hc,
    cover_center_le_residual (e.trans (MulAut.conj g)) hZ u hg,
    cover_residual_centralizes_coreCenter (e.trans (MulAut.conj g)) hZ u hg⟩

/-- All four earlier centralizer premises of the normalizer branch are discharged. -/
theorem normalizerCentralizerInput [Group.IsPerfect K]
    (e : (K ⧸ center K) ≃* Carrier) (hZ : Nat.card (center K) = 2)
    (u : K) (hu : modelMap e u = e0) : AbelianSection.CentralizerInput e u where
  center_le := cover_center_le_residual e hZ u hu
  residual_image := (cover_residual_image_and_perfect e hZ u hu).1
  center_image := cover_coreCenter_image e hZ u hu
  centralizes := cover_residual_centralizes_coreCenter e hZ u hu

/-- Actual normalizer consumer: only its independent model geometry remains
explicit; no lifting, centrality, core purity, or square premise is retained. -/
theorem normalizer_core_abelian_of_model [Group.IsPerfect K]
    (e : (K ⧸ center K) ≃* Carrier) (hZ : Nat.card (center K) = 2)
    (u : K) (hu : modelMap e u = e0) (m : AbelianSection.ModelInput) :
    IsMulCommutative (Q e) :=
  (AbelianSection.core_incidence_and_abelian e hZ u
    (normalizerCentralizerInput e hZ u hu) m).2.2.2

end CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.CentralizerRestriction
