module

public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.CenterFrattiniSource
public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Theory.GroupTheory.SolvableRadical.SolvableKernel
public import Theory.GroupTheory.PPrimeCoreSurjection
public import Theory.GroupTheory.CComponent.RadicalFree

/-!
# Intrinsic structure of the higher-exponent candidate

Conditional only on an isomorphism of the published complement with `SL₂(5)`
and its order 120, the published semidirect product is a C-component satisfying
both the nilpotent alternative and every common assertion of A.3.6. Its
solvable radical is the inverse image of the complement's center. The radical
has the vector kernel as its derived subgroup, and that kernel has index two
in the radical. The odd core and Fitting subgroup are the same vector kernel.

Quasisimplicity of the complement follows from the matrix SL₂ perfectness and
PSL₂ simplicity theorems. The solvable-kernel theorem identifies the radical;
inversion supplies each vector as a commutator. Subnormal minimality follows
from the quasisimple subnormal dichotomy and the solvable-supplement theorem.
We transport the characteristic subgroups and quotient isomorphisms to the
intrinsic top-subgroup carrier before applying the Frattini obstruction.

Thus the candidate fails every alternative of `Proposition121Four`, including
the extra center–Frattini equality in (4d). These are conditional intrinsic
certificates. Constructing the complement isomorphism and establishing SQTK
belong to the parent assembly; no QTKE ambient realization is asserted.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, A.3.6 and its proof,
printed pp.43–45, and Proposition 1.2.1(4), printed p.504. The higher-exponent
homocyclic possibility is explicitly retained on p.45.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
noncomputable section
namespace CFSG.Quasithin.Chapter1.Section02.CenterFrattiniSource

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private theorem sl5_quasisimple : IsQuasisimple SL5 where
  toIsPerfect := ⟨Matrix.SL2.commutator_eq_top (a := (2 : ZMod 5)) (by decide) (by decide)⟩
  simple := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (F := ZMod 5) (by norm_num)

private instance sl5_nontrivial : Nontrivial SL5 := by
  let := sl5_quasisimple.simple
  exact (QuotientGroup.mk'_surjective (center SL5)).nontrivial

private theorem complement_quasisimple (e : complement ≃* SL5) :
    IsQuasisimple complement := by
  let := sl5_quasisimple
  exact IsQuasisimple.of_mulEquiv e.symm

private theorem complement_center_card (e : complement ≃* SL5) :
    Nat.card (center complement) = 2 := by
  rw [Nat.card_congr (centerCongr e).toEquiv,
    Nat.card_congr (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity'
      (R := ZMod 5) (n := Fin 2) 0).toEquiv]
  exact (IsPrimitiveRoot.neg_one (R := ZMod 5) 5 (by decide)).card_rootsOfUnity

private theorem complement_radical (e : complement ≃* SL5) :
    solvableRadical complement = center complement := by
  let := complement_quasisimple e
  apply le_antisymm
  · rcases IsQuasisimple.normal_le_center_or_eq_top (solvableRadical complement) with h | h
    · exact h
    · let : Group.IsSolvable (⊤ : Subgroup complement) := h ▸ inferInstance
      let : Group.IsSolvable complement := Group.isSolvable_of_surjective
        (f := (topEquiv : (⊤ : Subgroup complement) ≃* complement).toMonoidHom)
        topEquiv.surjective
      let : Nontrivial complement := e.surjective.nontrivial
      exact (Group.IsPerfect.not_isSolvable complement inferInstance).elim
  · exact le_solvableRadical _ inferInstance inferInstance

private theorem kernel_card : Nat.card kernel = 11 ^ 4 := by
  rw [Nat.card_congr kernelEquiv.toEquiv]
  norm_num [Vector, Nat.card_eq_fintype_card]

private theorem kernel_solvable : Group.IsSolvable kernel :=
  Group.isSolvable_of_isSolvable_injective (f := kernelEquiv.toMonoidHom) kernelEquiv.injective

/-- The solvable radical is exactly the inverse image of the complement center. -/
theorem radical_eq_preimage (e : complement ≃* SL5) :
    solvableRadical Candidate = (center complement).comap SemidirectProduct.rightHom := by
  let : Group.IsSolvable (SemidirectProduct.rightHom : Candidate →* complement).ker := kernel_solvable
  rw [← comap_solvableRadical_eq_of_solvable_ker
    (SemidirectProduct.rightHom : Candidate →* complement)
    (fun g => ⟨SemidirectProduct.inr g, rfl⟩), complement_radical e]

private theorem kernel_le_radical : kernel ≤ solvableRadical Candidate :=
  le_solvableRadical _ inferInstance kernel_solvable

private theorem inverter_mem_radical (e : complement ≃* SL5) :
    inverter ∈ solvableRadical Candidate := by
  rw [radical_eq_preimage e]
  change inverter.right ∈ center complement
  apply mem_center_iff.mpr
  intro g
  apply action_injective
  apply MulEquiv.ext
  intro v
  simp only [map_mul, MulAut.mul_apply]
  rw [inverter_action, inverter_action, map_inv]

private theorem kernel_commutator_witness (g : Candidate) (hg : g ∈ kernel) :
    ∃ v : kernel, ⁅inverter, (v : Candidate)⁆ = g := by
  let v : Vector := Multiplicative.ofAdd (fun i => 60 * g.left.toAdd i)
  refine ⟨⟨SemidirectProduct.inl v, by simp [kernel_mem]⟩, ?_⟩
  change inverter * SemidirectProduct.inl v * inverter⁻¹ * (SemidirectProduct.inl v)⁻¹ = g
  rw [inverter_conjugates, ← map_inv (SemidirectProduct.inl : Vector →* Candidate),
    ← map_mul (SemidirectProduct.inl : Vector →* Candidate)]
  apply Eq.trans (congrArg (SemidirectProduct.inl : Vector →* Candidate) ?_)
    (kernel_eq_inl ⟨g, hg⟩).symm
  apply congrArg Multiplicative.ofAdd
  ext i
  change -(60 * g.left.toAdd i) + -(60 * g.left.toAdd i) = g.left.toAdd i
  calc
    _ = (-120 : ZMod 121) * g.left.toAdd i := by ring
    _ = _ := by rw [show (-120 : ZMod 121) = 1 from by decide, one_mul]

private theorem kernel_le_commutator_of_inverter {R : Subgroup Candidate}
    (hK : kernel ≤ R) (hi : inverter ∈ R) : kernel ≤ ⁅R, R⁆ := by
  intro g hg
  obtain ⟨v, hv⟩ := kernel_commutator_witness g hg
  exact hv ▸ commutator_mem_commutator hi (hK v.property)

/-- Inversion makes the vector kernel the full derived subgroup of the radical. -/
theorem radical_derived_eq_kernel (e : complement ≃* SL5) :
    ⁅solvableRadical Candidate, solvableRadical Candidate⁆ = kernel := by
  apply le_antisymm
  · rw [radical_eq_preimage e]
    apply commutator_le.mpr
    intro g hg h hh
    change (SemidirectProduct.rightHom : Candidate →* complement) ⁅g, h⁆ = 1
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact (mem_center_iff.mp hg _).symm
  · exact kernel_le_commutator_of_inverter kernel_le_radical (inverter_mem_radical e)

/-- The vector kernel is generated by its commutators with the candidate. -/
theorem kernel_commutator_eq :
    ⁅kernel, (⊤ : Subgroup Candidate)⁆ = kernel := by
  apply le_antisymm (commutator_le_left _ _)
  intro g hg
  obtain ⟨v, hv⟩ := kernel_commutator_witness g hg
  rw [commutator_comm]
  exact hv ▸ commutator_mem_commutator (mem_top _) v.property

/-- The radical contains the vector kernel with relative index two. -/
theorem kernel_radical_index (e : complement ≃* SL5) :
    kernel.relIndex (solvableRadical Candidate) = 2 := by
  change (SemidirectProduct.rightHom : Candidate →* complement).ker.relIndex _ = _
  rw [relIndex_ker, radical_eq_preimage e,
    map_comap_eq_self_of_surjective (f := (SemidirectProduct.rightHom : Candidate →* complement))
      (fun g => ⟨SemidirectProduct.inr g, rfl⟩), complement_center_card e]

private theorem complement_oddCore (e : complement ≃* SL5) (hc : Nat.card complement = 120) :
    pPrimeCore 2 complement = ⊥ := by
  let := complement_quasisimple e
  have hcop := pPrimeCore_coprime_card (p := 2) (G := complement)
  rcases IsQuasisimple.normal_le_center_or_eq_top (pPrimeCore 2 complement) with h | h
  · have hd := card_dvd_of_le h
    rw [complement_center_card e] at hd
    apply card_eq_one.mp
    exact Nat.eq_one_of_dvd_coprimes hcop.symm (dvd_refl _) hd
  · have he : Nat.card (pPrimeCore 2 complement) = 120 := by
      rw [h, Nat.card_congr (topEquiv : (⊤ : Subgroup complement) ≃* complement).toEquiv, hc]
    rw [he] at hcop
    exact (by decide : ¬ Nat.Coprime 2 120) hcop |>.elim

/-- The vector kernel is precisely the odd core. -/
theorem oddCore_eq_kernel (e : complement ≃* SL5) (hc : Nat.card complement = 120) :
    pPrimeCore 2 Candidate = kernel := by
  have hker : Nat.Coprime 2 (Nat.card (SemidirectProduct.rightHom : Candidate →* complement).ker) := by
    change Nat.Coprime 2 (Nat.card kernel)
    rw [kernel_card]
    decide
  rw [← pPrimeCore_comap_eq_of_surjective_coprime 2
    (SemidirectProduct.rightHom : Candidate →* complement)
    (fun g => ⟨SemidirectProduct.inr g, rfl⟩) hker, complement_oddCore e hc]
  rfl

/-- The candidate is perfect once its actual complement is identified. -/
theorem candidate_perfect (e : complement ≃* SL5) : Group.IsPerfect Candidate := by
  let := complement_quasisimple e
  exact perfect_of_complement_perfect inferInstance

/-- Minimality among nontrivial perfect subnormal subgroups is proved using
quasisimplicity of the complement and the solvable vector kernel. -/
theorem candidate_isCComponent (e : complement ≃* SL5) :
    (⊤ : Subgroup Candidate).IsCComponent := by
  let := candidate_perfect e
  let := complement_quasisimple e
  let : Nontrivial complement := e.surjective.nontrivial
  let : Nontrivial Candidate := (show Function.Surjective
    (SemidirectProduct.rightHom : Candidate →* complement) from
      fun g => ⟨SemidirectProduct.inr g, rfl⟩).nontrivial
  let : Group.IsSolvable kernel := kernel_solvable
  refine ⟨top_ne_bot, inferInstance, IsSubnormal.top, ?_⟩
  intro N _ hN hp hs
  let := hp
  let : Nontrivial N := (nontrivial_iff_ne_bot N).mpr hN
  let f : Candidate →* complement := SemidirectProduct.rightHom
  have hf : Function.Surjective f := fun g => ⟨SemidirectProduct.inr g, rfl⟩
  rcases IsQuasisimple.subnormal_le_center_or_eq_top (N.map f) (hs.map hf) with h | h
  · have hNR : N ≤ solvableRadical Candidate := by
      rw [radical_eq_preimage e]
      exact map_le_iff_le_comap.mp h
    let : Group.IsSolvable N := Group.isSolvable_of_isSolvable_injective
      (f := inclusion hNR) (inclusion_injective hNR)
    exact (Group.IsPerfect.not_isSolvable N inferInstance).elim
  · have hsup : N ⊔ kernel = ⊤ := by
      simpa only [comap_map_eq, comap_top, f, kernel] using congrArg (Subgroup.comap f) h
    simpa only [solvableResidual_eq_top] using hs.solvableResidual_le_of_sup_eq_top kernel hsup

/-- The quotient by the Fitting subgroup is the specified matrix group. -/
noncomputable def fittingQuotientEquiv (e : complement ≃* SL5)
    (hc : Nat.card complement = 120) : Candidate ⧸ fittingSubgroup Candidate ≃* SL5 :=
  (QuotientGroup.quotientMulEquivOfEq (fitting_eq_kernel_of_coprime
    (by rw [hc]; decide))).trans (quotientKernelEquiv.trans e)

/-- Every displayed nilpotent-case clause of A.3.6 holds for the candidate. -/
theorem candidate_a36Nilpotent (e : complement ≃* SL5) (hc : Nat.card complement = 120) :
    A36Nilpotent Candidate := by
  have hcop : Nat.Coprime 11 (Nat.card complement) := by rw [hc]; decide
  have hF := generalizedFitting_eq_kernel_of_coprime hcop
  refine ⟨generalizedFitting_eq_fitting, ?_, ?_, ?_⟩
  · rw [generalizedFitting_eq_fitting]
    infer_instance
  · refine ⟨ZMod 5, inferInstance, inferInstance, by simp, ⟨?_⟩⟩
    exact (QuotientGroup.quotientMulEquivOfEq generalizedFitting_eq_fitting).trans
      (fittingQuotientEquiv e hc)
  · intro p hp hd
    have hcard : Nat.card (generalizedFitting Candidate) = 11 ^ 4 := by rw [hF, kernel_card]
    rw [hcard] at hd
    have he : p = 11 := (Nat.prime_dvd_prime_iff_eq hp (by decide)).mp (hp.dvd_of_dvd_pow hd)
    subst p
    refine ⟨Or.inl (Or.inl (by decide)), Or.inr ⟨2, by decide, ⟨?_⟩⟩⟩
    have hcore : pCore 11 Candidate = kernel :=
      fitting_eq_elevenCore.symm.trans (fitting_eq_kernel_of_coprime hcop)
    exact (MulEquiv.subgroupCongr hcore).trans kernelEquiv

/-- All common assertions after A.3.6(1)–(4), including both quotient
quasisimplicity clauses and the radical-derived identity. -/
theorem candidate_a36Common (e : complement ≃* SL5) (hc : Nat.card complement = 120) :
    A36Common Candidate := by
  have hcop : Nat.Coprime 11 (Nat.card complement) := by rw [hc]; decide
  have hF := fitting_eq_kernel_of_coprime hcop
  let := sl5_quasisimple
  refine ⟨hF.trans (oddCore_eq_kernel e hc).symm,
    IsQuasisimple.of_mulEquiv (fittingQuotientEquiv e hc).symm,
    Or.inl ⟨generalizedFitting_eq_fitting.symm, ?_, ?_⟩, ?_, ?_⟩
  · rw [hF]; exact kernel_le_radical
  · rw [hF]; exact kernel_radical_index e
  · rw [hF, radical_derived_eq_kernel e, kernel_commutator_eq]
  · exact IsQuasisimple.of_mulEquiv ((QuotientGroup.quotientMulEquivOfEq
      (radical_derived_eq_kernel e)).trans (quotientKernelEquiv.trans e)).symm

section Transport
variable {G H : Type*} [Group G] [Group H]

-- The Fitting transport argument also appears in ChapterB/Section01/QuasisimpleSections/Group.
private theorem fitting_map_le (e : G ≃* H) :
    (fittingSubgroup G).map e.toMonoidHom ≤ fittingSubgroup H := by
  apply map_le_iff_le_comap.mpr
  apply sSup_le
  rintro N ⟨hN, hnil⟩
  apply map_le_iff_le_comap.mp
  let := hnil
  exact le_sSup ⟨hN.map _ e.surjective, Group.nilpotent_of_mulEquiv (e.subgroupMap N)⟩

private theorem fitting_map (e : G ≃* H) :
    (fittingSubgroup G).map e.toMonoidHom = fittingSubgroup H := by
  apply le_antisymm (fitting_map_le e)
  have h := map_mono (f := e.toMonoidHom) (fitting_map_le e.symm)
  simpa [map_map] using h

private theorem layer_map_le (e : G ≃* H) :
    (componentLayer G).map e.toMonoidHom ≤ componentLayer H := by
  apply map_le_iff_le_comap.mpr
  apply sSup_le
  intro L hL
  exact map_le_iff_le_comap.mp (le_sSup (hL.map_equiv e))

private theorem layer_map (e : G ≃* H) :
    (componentLayer G).map e.toMonoidHom = componentLayer H := by
  apply le_antisymm (layer_map_le e)
  have h := map_mono (f := e.toMonoidHom) (layer_map_le e.symm)
  simpa [map_map] using h

private theorem generalizedFitting_map (e : G ≃* H) :
    (generalizedFitting G).map e.toMonoidHom = generalizedFitting H := by
  rw [generalizedFitting, generalizedFitting, Subgroup.map_sup, fitting_map, layer_map]

end Transport

private abbrev TopCandidate := ↥(⊤ : Subgroup Candidate)
private def topCandidateEquiv : TopCandidate ≃* Candidate := topEquiv

private theorem top_generalizedFitting_eq_fitting :
    generalizedFitting TopCandidate = fittingSubgroup TopCandidate := by
  apply map_injective (f := topCandidateEquiv.toMonoidHom) topCandidateEquiv.injective
  rw [generalizedFitting_map, fitting_map, generalizedFitting_eq_fitting]

private noncomputable def topGeneralizedFittingKernelEquiv (hc : Nat.card complement = 120) :
    generalizedFitting TopCandidate ≃* kernel :=
  (topCandidateEquiv.subgroupMap _).trans (MulEquiv.subgroupCongr
    ((generalizedFitting_map topCandidateEquiv).trans
      (generalizedFitting_eq_kernel_of_coprime (by rw [hc]; decide))))

private theorem top_kernel_inversion (hc : Nat.card complement = 120)
    (v : generalizedFitting TopCandidate) :
    (⟨inverter, mem_top _⟩ : TopCandidate) * (v : TopCandidate) *
      (⟨inverter, mem_top _⟩ : TopCandidate)⁻¹ = (v : TopCandidate)⁻¹ := by
  apply Subtype.ext
  have hv : (v.val.val : Candidate) ∈ kernel := by
    rw [← generalizedFitting_eq_kernel_of_coprime (by rw [hc]; decide),
      ← generalizedFitting_map topCandidateEquiv]
    exact mem_map_of_mem topCandidateEquiv.toMonoidHom v.property
  exact inverter_conjugates_kernel ⟨v.val.val, hv⟩

/-- A.3.6(4) on the intrinsic top-subgroup carrier, with the exact published definitions. -/
theorem top_a36Nilpotent (e : complement ≃* SL5) (hc : Nat.card complement = 120) :
    A36Nilpotent (⊤ : Subgroup Candidate) := by
  have hcop : Nat.Coprime 11 (Nat.card complement) := by rw [hc]; decide
  refine ⟨top_generalizedFitting_eq_fitting, ?_, ?_, ?_⟩
  · rw [top_generalizedFitting_eq_fitting]
    infer_instance
  · refine ⟨ZMod 5, inferInstance, inferInstance, by simp, ⟨?_⟩⟩
    exact (QuotientGroup.congr _ _ topCandidateEquiv
      (generalizedFitting_map topCandidateEquiv)).trans
        ((QuotientGroup.quotientMulEquivOfEq generalizedFitting_eq_fitting).trans
          (fittingQuotientEquiv e hc))
  · intro p hp hd
    have hcard : Nat.card (generalizedFitting TopCandidate) = 11 ^ 4 :=
      (Nat.card_congr (topGeneralizedFittingKernelEquiv hc).toEquiv).trans kernel_card
    rw [hcard] at hd
    have he : p = 11 := (Nat.prime_dvd_prime_iff_eq hp (by decide)).mp (hp.dvd_of_dvd_pow hd)
    subst p
    refine ⟨Or.inl (Or.inl (by decide)), Or.inr ⟨2, by decide, ⟨?_⟩⟩⟩
    have hcore : pCore 11 Candidate = kernel :=
      fitting_eq_elevenCore.symm.trans (fitting_eq_kernel_of_coprime hcop)
    exact (topCandidateEquiv.subgroupMap (pCore 11 TopCandidate)).trans
      ((MulEquiv.subgroupCongr ((pCore_map_iso 11 topCandidateEquiv).trans hcore)).trans kernelEquiv)

/-- Every common clause of A.3.6 transported to the intrinsic top carrier. -/
theorem top_a36Common (e : complement ≃* SL5) (hc : Nat.card complement = 120) :
    A36Common (⊤ : Subgroup Candidate) := by
  have hcop : Nat.Coprime 11 (Nat.card complement) := by rw [hc]; decide
  have hF := fitting_eq_kernel_of_coprime hcop
  obtain ⟨hO, hq, _, hd, hq'⟩ := candidate_a36Common e hc
  have hD : (⁅solvableRadical TopCandidate, solvableRadical TopCandidate⁆).map
      topCandidateEquiv.toMonoidHom = ⁅solvableRadical Candidate, solvableRadical Candidate⁆ := by
    rw [map_commutator, map_solvableRadical_equiv]
  refine ⟨?_, ?_, Or.inl ⟨top_generalizedFitting_eq_fitting.symm, ?_, ?_⟩, ?_, ?_⟩
  · apply map_injective (f := topCandidateEquiv.toMonoidHom) topCandidateEquiv.injective
    rw [fitting_map, pPrimeCore_map_iso, hO]
  · let := hq
    exact IsQuasisimple.of_mulEquiv (QuotientGroup.congr _ _ topCandidateEquiv
      (fitting_map topCandidateEquiv)).symm
  · apply (map_le_map_iff_of_injective (f := topCandidateEquiv.toMonoidHom) topCandidateEquiv.injective).mp
    rw [fitting_map, map_solvableRadical_equiv, hF]
    exact kernel_le_radical
  · rw [← relIndex_map_map_of_injective (f := topCandidateEquiv.toMonoidHom)
      (fittingSubgroup TopCandidate) (solvableRadical TopCandidate) topCandidateEquiv.injective,
      fitting_map, map_solvableRadical_equiv, hF]
    exact kernel_radical_index e
  · apply map_injective (f := topCandidateEquiv.toMonoidHom) topCandidateEquiv.injective
    rw [hD, map_commutator, fitting_map, map_top_of_surjective _ topCandidateEquiv.surjective]
    exact hd
  · let := hq'
    exact IsQuasisimple.of_mulEquiv (QuotientGroup.congr _ _ topCandidateEquiv hD).symm

/-- The extra equality fails on the intrinsic top subgroup as well as on Candidate. -/
theorem top_not_centerFrattini (hc : Nat.card complement = 120) :
    ¬ CenterFrattini (⊤ : Subgroup Candidate) :=
  not_centerFrattini_of_homocyclic_121_inversion
    ((topGeneralizedFittingKernelEquiv hc).trans kernelEquiv)
    ⟨inverter, mem_top _⟩ (top_kernel_inversion hc)

/-- All four Chapter 1 alternatives are excluded, with intrinsic subgroup transport. -/
theorem top_not_proposition121Four (hc : Nat.card complement = 120) :
    ¬ Proposition121Four (⊤ : Subgroup Candidate) :=
  not_proposition121Four_of_homocyclic_121_inversion
    ((topGeneralizedFittingKernelEquiv hc).trans kernelEquiv)
    ⟨inverter, mem_top _⟩ (top_kernel_inversion hc)

/-- The complete conditional intrinsic certificate, retaining every common clause.
The parent supplies the complement witnesses and any additional source hypotheses. -/
theorem intrinsic_structure (e : complement ≃* SL5) (hc : Nat.card complement = 120) :
    (⊤ : Subgroup Candidate).IsCComponent ∧
      A36Nilpotent (⊤ : Subgroup Candidate) ∧
      A36Common (⊤ : Subgroup Candidate) ∧
      ¬ CenterFrattini (⊤ : Subgroup Candidate) ∧
      ¬ Proposition121Four (⊤ : Subgroup Candidate) :=
  ⟨candidate_isCComponent e, top_a36Nilpotent e hc, top_a36Common e hc,
    top_not_centerFrattini hc, top_not_proposition121Four hc⟩

end CFSG.Quasithin.Chapter1.Section02.CenterFrattiniSource
