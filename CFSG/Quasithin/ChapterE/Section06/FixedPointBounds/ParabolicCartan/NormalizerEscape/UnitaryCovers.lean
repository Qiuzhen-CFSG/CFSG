module

public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.NormalizerEscape.Unitary
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Inverted.Source
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.BenderHall.Reduction
public import Theory.SpecificGroups.PSU3.EvenOddCenterCover
public import Theory.GroupTheory.CComponent.QuotientLifting

/-!
# Unitary source escape away from the scalar prime

The source component modulo its two-core is quasisimple. The proved scalar
SU₃ covering theorem shows that the kernel of its actual map to the marked
PSU₃ component has order dividing three. Thus every odd-primary subgroup
away from three has coprime source kernel. Combining this with full-Borel
escape retains the original subgroup and removes the kernel premise.

Source: Aschbacher–Smith E.2.2(2a), A.2.12(I), A.2.18, and 4.4.13(1).
The actual A₅ Hall-kernel consumer has prime-to-fifteen order; the general
prime-three source branch is not claimed here.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.NormalizerEscape
open MarkedModels MarkedModels.DiagramHall ChapterB
open BenderSuzuki.MatrixGroups HermitianForm HermitianForm.UniversalCover
variable {X : Type*} [Group X] [Finite X]

/-- The literal source comparison kernel in the unitary row divides three. -/
theorem unitary_comparison_kernel_card_dvd_three
    (S : Sylow 2 X) (hP : IsMinimalParabolicOver S ⊤) (K : Subgroup X)
    (hK : K.IsCComponent) (hqK : IsQuasisimple (K ⧸ pCore 2 K)) {f : ℕ}
    (hm : UnitaryModel (minimalParabolicMax S hP) K f) :
    Nat.card (linearSourceComparison S hP K).ker ∣ 3 := by
  obtain ⟨F,hfield,hfin,hchar,J,hJ,hf,hF,hconj,_,e,_⟩ := hm
  let := hfield
  let := hfin
  let := hchar
  let := hqK
  let : IsQuasisimple (actorImage K) :=
    IsQuasisimple.of_mulEquiv (cComponentTwoCoreQuotientEquiv hK)
  have hsub : (actorImage K).IsSubnormal :=
    hK.subnormal.map (QuotientGroup.mk'_surjective (pCore 2 X))
  have hcore : pCore 2 (actorImage K) = ⊥ := by
    rw [pCore_subnormal_eq_comap 2 hsub, pCore_quotient_pCore_eq_bot]
    exact (actorImage K).subtype.ker_eq_bot (actorImage K).subtype_injective
  let r := e.toMonoidHom.comp (linearSourceComparison S hP K)
  have hr : Function.Surjective r := e.surjective.comp (linearSourceComparison_surjective S hP K)
  obtain ⟨k,hks,hk⟩ := OddPartDescent.exists_lift_even J hf hF hconj
    (fun p hp hp3 => EvenKernelBound.LargePrimary.not_dvd_universal_kernel J hf hp hp3 hF hconj)
    (fun hodd => EvenKernelBound.ThreePrimary.not_nine_dvd_universal_kernel J hf hodd hF hconj)
    r hr hcore
  have hd := kernel_card_dvd_of_surjective_factor J.specialToProjective r k hks hk
  rw [UniversalCover.card_kernel J hF hconj,
    MonoidHom.ker_comp_of_injective _ e.toMonoidHom e.injective] at hd
  exact hd.trans (Nat.gcd_dvd_left 3 (2^f+1))

/-- In the actual unitary source row, odd primes different from three are
coprime to the original component projection's kernel. -/
theorem unitary_source_kernel_coprime
    (S : Sylow 2 X) (hP : IsMinimalParabolicOver S ⊤) (K : Subgroup X)
    (hK : K.IsCComponent) (hqK : IsQuasisimple (K ⧸ pCore 2 K)) {f : ℕ}
    (hm : UnitaryModel (minimalParabolicMax S hP) K f)
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (hp3 : p ≠ 3) :
    Nat.Coprime p (Nat.card
      ((QuotientGroup.mk' (sourceKernel (minimalParabolicMax S hP))).subgroupMap K).ker) := by
  let q : K →* actorImage K := (QuotientGroup.mk' (pCore 2 X)).subgroupMap K
  let r := linearSourceComparison S hP K
  let s : K →* sourceImage (minimalParabolicMax S hP) K :=
    (QuotientGroup.mk' (sourceKernel (minimalParabolicMax S hP))).subgroupMap K
  have hq : Function.Surjective q := (QuotientGroup.mk' (pCore 2 X)).subgroupMap_surjective K
  have hr : Function.Surjective r := linearSourceComparison_surjective S hP K
  have hfac : r.comp q = s := by ext; rfl
  have hqker : q.ker = pCore 2 K := by
    have he := ker_subgroupMap K (QuotientGroup.mk' (pCore 2 X))
    rw [QuotientGroup.ker_mk'] at he
    exact he.trans (pCore_subnormal_eq_comap 2 hK.subnormal).symm
  have hqc : Nat.Coprime p (Nat.card q.ker) := by
    rw [hqker]
    obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := K)).exists_card_eq
    rw [hn]
    exact hp.coprime_two_right.pow_right n
  have hrc : Nat.Coprime p (Nat.card r.ker) :=
    ((Nat.coprime_primes (Fact.out : p.Prime) Nat.prime_three).mpr hp3).of_dvd_right
      (unitary_comparison_kernel_card_dvd_three S hP K hK hqK hm)
  change Nat.Coprime p (Nat.card s.ker)
  rw [kernel_card_eq_mul_of_surjective_factor s r q hr hq hfac]
  exact hqc.mul_right hrc

/-- The original unitary source row gives escape for every prescribed
odd-primary subgroup away from three; no torus or kernel premise remains. -/
theorem unitary_original_escape
    (S : Sylow 2 X) (hP : IsMinimalParabolicOver S ⊤) (K : Subgroup X)
    (hK : K.IsCComponent) (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (hc : SingleClauses (minimalParabolicMax S hP) K S) {f : ℕ}
    (hm : UnitaryModel (minimalParabolicMax S hP) K f)
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (hp3 : p ≠ 3)
    (A : Subgroup X) (hA : IsPGroup p A) (hAM : A ≤ minimalParabolicMax S hP) :
    ¬ normalizer (A : Set X) ≤ minimalParabolicMax S hP := by
  have hAK : A ≤ K := by
    rw [BenderHall.SingleClauses.component_eq_residual hc hK]
    intro a ha
    apply mem_pResidual_of_orderOf_coprime
    simpa only [Subgroup.orderOf_mk] using
      (hA.orderOf_coprime hp.coprime_two_right (⟨a,ha⟩ : A)).symm
  exact unitary_original_escape_of_coprime_kernel hm hp A hA hAM hAK
    (unitary_source_kernel_coprime S hP K hK hqK hm hp hp3)

end CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.NormalizerEscape
