module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial.Natural.Splitting.Recognition
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial.Natural.Splitting.Lift
public import Theory.GroupAction.FixedCoatomDisplacement

/-!
# A split natural section from a small fixed index

Let H/N be an elementary binary section of a finite group A with a specified
surjection onto the actual SL₃(2). If the projection kernel centralizes H/N,
the radical preimage N[H,ker π] is exactly N. The resulting quotient action
is faithful whenever [H,A] is not contained in N, by simplicity of SL₃(2).

A fixed preimage of relative index at most two gives an involution whose
displacement has order at most two. The earlier three-transvection recognition
then splits the quotient into its intrinsic fixed and moving subgroups and
provides natural coordinates with an automorphism marking. Lifting this
splitting constructs every field of SingleNaturalSection, including the exact
intersection and equivariant coordinates. Normality of N supplies the triple
bound. No geometric or later flag hypotheses are used.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), the notation c(U) on p.881 and the inference in (4.6.8), claim (2),
p.906, specialized to the binary case.
-/

public section

open Subgroup
open scoped commutatorElement
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open Escape.Initial.Natural.Splitting

namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Propagation.Generation.Detection.Recognition

variable {A : Type*} [Group A] [Finite A]

/-- A nontrivial elementary section centralized by the projection kernel is
a split single natural section if a nonidentity quotient involution has fixed
preimage of relative index at most two. -/
theorem singleNaturalSection_of_small_fixed_index (π : A →* SL)
    (hπ : Function.Surjective π) (H N : Subgroup A) [H.Normal] [N.Normal]
    (hNH : N ≤ H) (hE : IsElementaryAbelian 2 (H ⧸ N.subgroupOf H))
    (hkernel : ⁅H, π.ker⁆ ≤ N) (hnontrivial : ¬ ⁅H, (⊤ : Subgroup A)⁆ ≤ N)
    (a : A) (ha : π a ≠ 1) (ha2 : (π a) ^ 2 = 1)
    (hindex : (centralizerModulo H (zpowers a) N).relIndex H ≤ 2) :
    Nonempty (Escape.SingleNaturalSection π π.ker (pResidual 2 A) H N) := by
  let := hE
  let B := Escape.radicalPreimage π.ker H N
  have hBN : B = N := sup_eq_left.mpr hkernel
  let E := H ⧸ B.subgroupOf H
  let q : H →* E := QuotientGroup.mk' (B.subgroupOf H)
  let ρ := headAction H N π.ker π hπ rfl
  let : IsElementaryAbelian 2 E := radical_elementary H N π.ker
  have hfaithful : Function.Injective ρ := by
    let : IsSimpleGroup SL := Atlas.Comparisons.Exceptional.sl3Two_simple
    apply ρ.ker_eq_bot_iff.mp
    rcases (MonoidHom.normal_ker ρ).eq_bot_or_eq_top with hk | hk
    · exact hk
    · exfalso
      apply hnontrivial
      rw [commutator_comm]
      apply commutator_le.mpr
      intro g _ x hx
      have hg : ρ (π g) = 1 := MonoidHom.mem_ker.mp (hk ▸ mem_top (π g))
      have hformula := headAction_apply H N π.ker π hπ rfl g ⟨x, hx⟩
      change ρ (π g) (q ⟨x, hx⟩) = q _ at hformula
      rw [hg] at hformula
      have hc := QuotientGroup.eq_iff_div_mem.mp hformula.symm
      change g * x * g⁻¹ / x ∈ B at hc
      rw [hBN] at hc
      simpa only [commutatorElement_def, div_eq_mul_inv, coe_subtype] using hc
  have hsmall : HasSmallInvolution ρ := by
    refine ⟨π a, ha, ha2, ?_⟩
    let C := centralizerModulo H (zpowers a) N
    let F := FixedPoints.subgroup (zpowers (ρ (π a))) E
    have hCfixed : (C.subgroupOf H).map q ≤ F := by
      rintro _ ⟨x, hx, rfl⟩ mover
      have hfixed : ρ (π a) (q x) = q x := by
        rw [headAction_apply]
        apply QuotientGroup.eq_iff_div_mem.mpr
        change a * (x : A) * a⁻¹ / (x : A) ∈ B
        rw [hBN]
        have hc := (mem_centralizerModulo_iff.mp hx).2 a (mem_zpowers a)
        simpa only [commutatorElement_def, div_eq_mul_inv, coe_subtype] using hc
      exact smul_eq_self_of_mem_zpowers mover.property hfixed
    have hdiv : C.relIndex H ∣ 2 := by
      have hpos : C.relIndex H ≠ 0 := (C.subgroupOf H).index_ne_zero_of_finite
      apply (Nat.dvd_prime Nat.prime_two).mpr
      change C.relIndex H ≤ 2 at hindex
      omega
    have hFindex : F.index ∣ 2 :=
      (index_dvd_of_le hCfixed).trans
        (((C.subgroupOf H).index_map_dvd (QuotientGroup.mk'_surjective _)).trans hdiv)
    exact MulAut.commutatorAction_card_le_two_of_fixed_index_dvd_two (ρ (π a)) hFindex
  obtain ⟨s⟩ := naturalActionSplitting_of_small_involution ρ hfaithful hsmall
  exact singleNaturalSection_of_head_splitting H N π.ker (pResidual 2 A) π hπ rfl
    hNH hE ((commutator_mono hkernel le_rfl).trans (commutator_le_left N _)) s

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Propagation.Generation.Detection.Recognition
