module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.LinearOvergroupCentralizer
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.LinearCentralizerFF

/-!
# Equality and the full supplement for linear overgroups

The unequal-omega branch supplies a nontrivial rank-one FF action in the
centralizer of the original component. The same component remains PSL₃(2)
in the larger faithful quotient and has no fixed vectors there. The complete
B.5 classification therefore excludes this branch. Equality of the omega
modules gives the literal supplement by the full overgroup centralizer.

The residual commutator premise is precisely the extra assumption in
13.4.7(2); its proof when K₂=L₂ remains part of clause (4).
Source: Aschbacher–Smith 13.4.7(2), printed pp.899,902.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Section03.Noncentrality.SupercriticalSource NoncentralChiefRefinement
open Representation.BinaryOffender
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V A B : Subgroup G}
variable (h₀ : Hypothesis1331 T L) (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Source1332OneTwo T)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hindexA : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (A : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexB : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (K : Subgroup (A ⊔ B : Subgroup G)) (hK : K.IsCComponent)
    (hres : let X := A ⊔ B
      let Z := omegaOneCenterAmbient (T : Subgroup G)
      let K₁ := (pResidual 2 A).map A.subtype
      let K₂ := (pResidual 2 B).map B.subtype
      let C₁ := X ⊓ centralizer ((Z ⊓ centralizer (K₁ : Set G) : Subgroup G) : Set G)
      let C₂ := X ⊓ centralizer ((Z ⊓ centralizer (K₂ : Set G) : Subgroup G) : Set G)
      (primeToResidual 3 C₁).map C₁.subtype = K₁ ∨
        (primeToResidual 3 C₂).map C₂.subtype = K₂)
    (eK : ((K.map (A ⊔ B).subtype) ⧸ pCore 2 (K.map (A ⊔ B).subtype)) ≃*
      Matrix.PSL3Two.PSL)
include h₀ D m h1332 hTA hTB eA eB hne hindexA hindexB hK hres eK

/-- The linear source overgroup formula, with the residual commutator
premise and the full literal action kernel retained. -/
theorem original_pair_linear_overgroup_formula
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (hout : ¬ A ⊔ B ≤ normalizer (L : Set G))
    (hindexL : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hcomm : let K₂ := (pResidual 2 B).map B.subtype
      ⁅K₂,ChapterB.thompsonJ (T : Subgroup G) 1⁆ = K₂)
    (Y : Subgroup G) (hY : Y ∈ Chapter1.HOver G ((A ⊔ B : Subgroup G) : Set G)) :
    conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) Y =
      conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) (A ⊔ B) ∧
    (Y : Set G) = ((A ⊔ B : Subgroup G) : Set G) *
      (Y ⊓ centralizer (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G))
        (A ⊔ B) : Set G) : Subgroup G) := by
  let C := K.map (A ⊔ B).subtype
  let W := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) Y
  let U := W.subgroupOf Y
  have hCY : C ≤ Y := (map_subtype_le K).trans hY.2
  have hTY : (T : Subgroup G) ≤ Y := (hTA.trans le_sup_left).trans hY.2
  have hWY : W ≤ Y := conjugateSpanBy_le
    (fun z hz => hTY ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1) Y.le_normalizer
  by_cases he : W = conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) (A ⊔ B)
  · exact ⟨he,original_pair_linear_overgroup_supplement_of_omega_eq h₀ D m h1332
      hTA hTB eA eB hne hindexA hindexB K hK hres h structural hout hindexL eK Y hY he⟩
  exfalso
  obtain ⟨hr,hneF,hrank,hFF⟩ := original_pair_linear_overgroup_centralizer_FF_hypothesis
    h₀ D m h1332 hTA hTB eA eB hne hindexA hindexB K hK hres eK
    h structural hout hindexL hcomm Y hY he
  let := hr.normal
  let := hr.elementary
  let N := centralizer (U : Set Y)
  let q := QuotientGroup.mk' N
  let ρ := Representation.NormalElementaryQuotient.representation U q
    (QuotientGroup.mk'_surjective N) (QuotientGroup.ker_mk' N)
  let S := (C.subgroupOf Y).map q
  let F := centralizer (S : Set (Y ⧸ N))
  let σ := ρ.comp F.subtype
  let E := offenderSubgroup σ
  let : Nontrivial E := (nontrivial_iff_ne_bot E).mpr hneF
  let f := F.subtype.comp E.subtype
  obtain ⟨hN,e,heq⟩ := original_pair_overgroup_component_quotient h₀ D m h1332
    hTA hTB eA eB hne hindexA hindexB K hK hres Y hY
  have hrange : (q.comp (inclusion hCY)).range = S := by
    rw [MonoidHom.range_comp,inclusion_range]
  let eS : S ≃* Matrix.PSL3Two.PSL :=
    (MulEquiv.subgroupCongr hrange.symm).trans (e.symm.trans eK)
  have hfree : fixedSpace ρ S = ⊥ := by
    apply bot_unique
    intro v hv
    have hc := (Representation.NormalElementaryQuotient.mem_fixedSpace_image U q
      (QuotientGroup.mk'_surjective N) (QuotientGroup.ker_mk' N) (C.subgroupOf Y) v).mp hv
    have hz : v.toMul.val.val ∈ W ⊓ centralizer (C : Set G) := by
      refine ⟨v.toMul.property,?_⟩
      intro c hcC
      exact congrArg Subtype.val (hc ⟨c,hCY hcC⟩ hcC)
    have hzero := original_pair_overgroup_component_fixed_free h₀ D m h1332
      hTA hTB eA eB hne hindexA hindexB K hK hres h structural hout hindexL Y hY
    rw [hzero] at hz
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Subtype.ext
    exact hz
  exact no_rank_one_FF_of_commuting_linearThree ρ S eS hfree f
    (by rintro _ ⟨a,rfl⟩; exact a.val.property) hrank hFF

/-- The final clause of source 13.4.7(2): a Sylow centralizer of the seed
leaves no proper local overgroup of the original linear join. -/
theorem original_pair_linear_overgroup_eq_of_seed_centralizer
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (hout : ¬ A ⊔ B ≤ normalizer (L : Set G))
    (hindexL : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hcomm : let K₂ := (pResidual 2 B).map B.subtype
      ⁅K₂,ChapterB.thompsonJ (T : Subgroup G) 1⁆ = K₂)
    (Y : Subgroup G) (hY : Y ∈ Chapter1.HOver G ((A ⊔ B : Subgroup G) : Set G))
    (hcent : Y ⊓ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) = T) :
    Y = A ⊔ B := by
  have hf := (original_pair_linear_overgroup_formula h₀ D m h1332
    hTA hTB eA eB hne hindexA hindexB K hK hres eK
    h structural hout hindexL hcomm Y hY).2
  have hker : Y ⊓ centralizer (conjugateSpanBy
      (omegaOneCenterAmbient (T : Subgroup G)) (A ⊔ B) : Set G) ≤ A ⊔ B := by
    exact (inf_le_inf_left Y (centralizer_le (le_conjugateSpanBy _ _))).trans
      (hcent.le.trans (hTA.trans le_sup_left))
  refine le_antisymm ?_ hY.2
  intro y hy
  have hm : y ∈ ((A ⊔ B : Subgroup G) : Set G) *
      (Y ⊓ centralizer (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G))
        (A ⊔ B) : Set G) : Subgroup G) := by
    rw [←hf]
    exact hy
  obtain ⟨x,hx,c,hc,rfl⟩ := hm
  exact (A ⊔ B).mul_mem hx (hker hc)

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
