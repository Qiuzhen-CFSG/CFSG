module

public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.CentralizerRestriction.CoverResidual
public import Theory.GroupTheory.Commutator.CentralCoprimeIndexTransfer

/-!
# The ambient center lies in the HS centralizer residual

The model residual has order 3840 and its full centralizer order 7680.
The centralizer preimage in a double cover has order 15360. Its quotient by
the two-residual therefore has order at most four, so is abelian. Central
transfer at the odd-index preimage puts the ambient center in its derived
subgroup, hence in the residual. This proves the instance of source restriction
(i) required by the normalizer argument, from perfection of the ambient cover.

Source: Aschbacher–Smith I.2.2, restriction (i), printed p.410, and (5),
printed pp.411–412 / PDF pp.421–423.
-/

public section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory
open Sporadic.LeechRelated.HS Sporadic.LeechRelated.HS.EvenLocalCandidates
open Sporadic.LeechRelated.HS.EvenLocalCandidates.CentralInvolutionCore
open CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSInner
open CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSInner.CoreStructure
namespace CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.CentralizerRestriction

private theorem commutative_of_card_le_four {G : Type*} [Group G] [Finite G]
    (h : Nat.card G ≤ 4) : IsMulCommutative G := by
  have hp : 0 < Nat.card G := Nat.card_pos
  have hc : Nat.card G = 1 ∨ Nat.card G = 2 ∨ Nat.card G = 3 ∨ Nat.card G = 4 := by omega
  rcases hc with h1 | h2 | h3 | h4
  · let : Subsingleton G := (Nat.card_eq_one_iff_unique.mp h1).1
    exact ⟨⟨fun _ _ => Subsingleton.elim _ _⟩⟩
  · let : IsCyclic G := isCyclic_of_prime_card h2
    infer_instance
  · let : IsCyclic G := isCyclic_of_prime_card h3
    infer_instance
  · exact IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) h4

theorem model_residual_card : Nat.card modelResidual = 3840 := by
  have hc : Nat.card core = 64 := le_antisymm core_card_le core_card_ge
  have hk : Nat.card (core.subgroupOf modelResidual) = 64 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe model_core_le_residual).toEquiv,hc]
  have hq : Nat.card (modelResidual ⧸ core.subgroupOf modelResidual) = 60 := by
    rw [Nat.card_congr modelResidualQuotient.toEquiv, nat_card_alternatingGroup]
    norm_num
  have hh := (core.subgroupOf modelResidual).card_mul_index
  rw [index_eq_card,hk,hq] at hh
  exact hh.symm

variable {K : Type*} [Group K] [Finite K]

omit [Finite K] in
private theorem center_le_model_preimage
    (e : (K ⧸ center K) ≃* Carrier) (u : K) : center K ≤ preimage e u := by
  rw [← modelMap_ker e]
  exact MonoidHom.ker_le_comap _ _

omit [Finite K] in
theorem cover_preimage_card
    (e : (K ⧸ center K) ≃* Carrier) (hZ : Nat.card (center K) = 2)
    (u : K) (hu : modelMap e u = e0) : Nat.card (preimage e u) = 15360 := by
  let P := preimage e u
  let f := (modelMap e).subgroupMap P
  have hker : f.ker = (center K).subgroupOf P := by
    rw [ker_subgroupMap,modelMap_ker]
  have hkcard : Nat.card f.ker = 2 := by
    rw [hker,Nat.card_congr (subgroupOfEquivOfLe (center_le_model_preimage e u)).toEquiv,hZ]
  have hh := f.ker.card_mul_index
  rw [index_ker,f.range_eq_top_of_surjective ((modelMap e).subgroupMap_surjective P),
    card_top,hkcard] at hh
  change 2 * Nat.card (P.map (modelMap e)) = Nat.card P at hh
  rw [preimage_map,hu,centralizer_card] at hh
  exact hh.symm

/-- Restriction (i) for this actual centralizer preimage, with its transfer
premise proved from ambient perfection and the two-central marking. -/
theorem cover_center_le_residual [Group.IsPerfect K]
    (e : (K ⧸ center K) ≃* Carrier) (hZ : Nat.card (center K) = 2)
    (u : K) (hu : modelMap e u = e0) : center K ≤ centralizerTwoResidual u := by
  let P := preimage e u
  let N := pResidual 2 P
  have hPN : centralizerTwoResidual u = N.map P.subtype :=
    cover_residual_eq_preimage_residual e hZ u hu
  have hP : Nat.card P = 15360 := cover_preimage_card e hZ u hu
  have hN : 3840 ≤ Nat.card N := by
    have hd := (centralizerTwoResidual u).card_map_dvd (modelMap e)
    rw [(cover_residual_image_and_perfect e hZ u hu).1,
      marked_centralizer_residual_eq,card_map_of_injective (localGroup 0).subtype_injective,
      model_residual_card] at hd
    have hncard : Nat.card (centralizerTwoResidual u) = Nat.card N := by
      rw [hPN,card_map_of_injective P.subtype_injective]
    rw [hncard] at hd
    exact Nat.le_of_dvd Nat.card_pos hd
  have hsmall : Nat.card (P ⧸ N) ≤ 4 := by
    have hh := N.card_mul_index
    rw [index_eq_card,hP] at hh
    nlinarith
  let : IsMulCommutative (P ⧸ N) := commutative_of_card_le_four hsmall
  let : CommGroup (P ⧸ N) := { (inferInstance : Group (P ⧸ N)) with
    mul_comm := fun x y => mul_comm x y }
  have hd : _root_.commutator P ≤ N := by
    simpa using Abelianization.commutator_subset_ker (QuotientGroup.mk' N)
  have hodd : ¬ 2 ∣ P.index := by
    have hpidx : P.index = (centralizer ({e0} : Set Carrier)).index := by
      change (preimage e u).index = _
      rw [preimage,index_comap_of_surjective _
        (e.surjective.comp (QuotientGroup.mk'_surjective (center K))),hu]
    rw [hpidx]
    exact e0_twoCentral.not_dvd_centralizer_index
  have hz := central_le_mapped_commutator_of_coprime_index P (center K) le_rfl
    (center_le_model_preimage e u) (by rw [hZ]; exact Nat.prime_two.coprime_iff_not_dvd.mpr hodd)
  rw [hPN]
  exact hz.trans (map_mono hd)

end CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.CentralizerRestriction
