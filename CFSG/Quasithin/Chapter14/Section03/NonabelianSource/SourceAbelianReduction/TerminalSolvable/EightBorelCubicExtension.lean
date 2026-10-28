module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.EightBorelFieldAction
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.CubicExtension

/-!
# The exact L₂(8) partner quotient and its actual cubic supplement

Apply the trivial core-action centralizer to the original ComponentLift and
EightImageRow. The rank-one action kernel is exactly O₂(Mc); the partner
quotient is PSL₂(8) or its actual automorphism group. In the proper-extension
case an ambient element of order three lies in the original M intersect Mc,
supplements K, and acts by a coefficient automorphism after the displayed
inner change of quotient marking.

All original source inputs and the independent marked amalgam remain explicit.
Identification of the extended amalgam, ambient recognition and Borel
exclusion remain with this owner.
Source: Aschbacher--Smith 14.2.18 and its 14.3.15 application, pp.987,994.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    {F : InvariantFlag T (rankTwoSeed T M) 2} {g : G} {K : Subgroup G}
include hG hempty hM hu hmany hcard e


/-- The literal kernel in G has no odd remainder. -/
theorem source_eight_marked_rankOne_kernel_eq
    (hK : ComponentLift F g K) (h8 : EightImageRow F K)
    (r : EightLargeParabolic.MarkedTriality T M Mc (K ⊔ (T : Subgroup G))) :
    pCoreActionKernelIn 2 K Mc = Mc.pCoreIn 2 := by
  have hjoin := source_eight_marked_join_eq hG T hempty hM hu hmany hcard e hK h8 r
  have hH : K ∈ Chapter3.HStar (T : Subgroup G) M := by
    simpa only [hjoin] using
      (source_eight_join_minimal hG T hempty hM hu hmany hcard e hK h8).1
  have rK : EightLargeParabolic.MarkedTriality T M Mc K := hjoin ▸ r
  rw [←EightLargeParabolic.source_rankOneAction_kernel_map hG hempty hM hu hmany hcard e hH rK,
    EightLargeParabolic.source_rankOneAction_kernel_eq hG hempty hM hu hmany hcard e hH rK]
  rfl

/-- The exact partner quotient, with the previous centralizer premise discharged. -/
theorem source_eight_marked_partner_quotient
    (hK : ComponentLift F g K) (h8 : EightImageRow F K)
    (r : EightLargeParabolic.MarkedTriality T M Mc (K ⊔ (T : Subgroup G))) :
    Nonempty ((Mc ⧸ pCore 2 Mc) ≃* Theory.PSL2.BinaryGroup 3) ∨
      Nonempty ((Mc ⧸ pCore 2 Mc) ≃* MulAut (Theory.PSL2.BinaryGroup 3)) :=
  EightLargeParabolic.source_partner_quotient hG hempty hM hu hmany hcard e
    (source_eight_join_minimal hG T hempty hM hu hmany hcard e hK h8).1 r

/-- The actual action and cubic supplement retain the quotient-conjugation square
on the original K. No containment T ≤ K is assumed. -/
theorem source_eight_marked_cubic_structure
    (hK : ComponentLift F g K) (h8 : EightImageRow F K)
    (r : EightLargeParabolic.MarkedTriality T M Mc (K ⊔ (T : Subgroup G))) :
    ∃ (hn : Mc ≤ normalizer (K : Set G))
      (b : (K ⧸ pCore 2 K) ≃* Theory.PSL2.BinaryGroup 3)
      (a : Mc →* MulAut (Theory.PSL2.BinaryGroup 3)),
      (∀ (x : Mc) (k : K), a x (b (QuotientGroup.mk' (pCore 2 K) k)) =
        b (QuotientGroup.mk' (pCore 2 K) (K.normalizerMonoidHom (inclusion hn x) k))) ∧
      a.ker = pCore 2 Mc ∧
      (Mc = K ∨ ∃ (σ : Theory.PSL2.BinaryField 3 ≃+* Theory.PSL2.BinaryField 3) (x : Mc)
        (j : Theory.PSL2.BinaryGroup 3),
        orderOf σ = 3 ∧ orderOf x = 3 ∧
        a x = MulAut.congr (MulAut.conj j) (Theory.PSL2.fieldAut σ) ∧
        zpowers (x : G) ≤ M ⊓ Mc ∧ Nat.card (zpowers (x : G)) = 3 ∧
        Mc = K ⊔ zpowers (x : G) ∧ M ⊓ Mc = (M ⊓ K) ⊔ zpowers (x : G)) := by
  have hjoin := source_eight_marked_join_eq hG T hempty hM hu hmany hcard e hK h8 r
  have hH : K ∈ Chapter3.HStar (T : Subgroup G) M := by
    simpa only [hjoin] using
      (source_eight_join_minimal hG T hempty hM hu hmany hcard e hK h8).1
  have rK : EightLargeParabolic.MarkedTriality T M Mc K := hjoin ▸ r
  refine ⟨EightLargeParabolic.source_partner_le_first_normalizer hG hempty hM hu hmany hcard e hH rK,
    EightLargeParabolic.firstQuotientEquiv rK,
    EightLargeParabolic.sourceRankOneAction hG hempty hM hu hmany hcard e hH rK,
    EightLargeParabolic.source_rankOneAction_mk hG hempty hM hu hmany hcard e hH rK,
    EightLargeParabolic.source_rankOneAction_kernel_eq hG hempty hM hu hmany hcard e hH rK,?_⟩
  by_cases he : Mc = K
  · exact Or.inl he
  · obtain ⟨σ,x,j,hσ,hx,hact,hfield,hAN,hA,hcardA,hMc,hI⟩ :=
      EightLargeParabolic.source_cubic_overlap_supplement hG hempty hM hu hmany hcard e hH rK he
    exact Or.inr ⟨σ,x,j,hσ,hx,hact,hA,hcardA,hMc,hI⟩

/-- Both literal source endpoints have the same cubic supplement. -/
theorem source_eight_marked_endpoint_factorizations
    (hK : ComponentLift F g K) (h8 : EightImageRow F K)
    (r : EightLargeParabolic.MarkedTriality T M Mc (K ⊔ (T : Subgroup G))) :
    Mc = K ∨ ∃ A : Subgroup G,
      A ≤ M ⊓ Mc ∧ Nat.card A = 3 ∧
      Mc = K ⊔ A ∧ M ⊓ Mc = (M ⊓ K) ⊔ A ∧
      M = EightLargeParabolic.secondParabolic T M Mc K ⊔ A := by
  have hjoin := source_eight_marked_join_eq hG T hempty hM hu hmany hcard e hK h8 r
  have hH : K ∈ Chapter3.HStar (T : Subgroup G) M := by
    simpa only [hjoin] using
      (source_eight_join_minimal hG T hempty hM hu hmany hcard e hK h8).1
  have rK : EightLargeParabolic.MarkedTriality T M Mc K := hjoin ▸ r
  rcases EightLargeParabolic.source_cubic_endpoint_factorizations
    hG hempty hM hu hmany hcard e hH rK with he | ⟨A,hA,hcardA,hMc,hI,hMsecond,hAn,hp,hpM⟩
  · exact Or.inl he
  · exact Or.inr ⟨A,hA,hcardA,hMc,hI,hMsecond⟩
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
