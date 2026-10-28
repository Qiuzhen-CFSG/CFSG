module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddCriticalPair.OrthogonalSource.Recognition
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddCriticalPair.Alternatives.Sylow
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddCriticalPair.Parabolic
public import Theory.GroupAction.BinaryWreathPlaneGeometry

/-!
# The original second factor in the orthogonal coordinates

The actual H₂ fixes the first covering plane modulo Z. In the full wreath
action its image therefore lies in the second matrix factor; both have order
six, so the images agree. Their common kernel O₂(H) gives equality of the
literal preimages. Consequently H₂ has index two in the full quotient
centralizer P of the same u, and their embedded two-residuals agree.

The source recognition consumer preserves the original H,M,Mc and both
factor markings. Dimension four remains conditional here; its endpoint
construction stays with the original 14.6.13 assembly.
Source: Aschbacher--Smith 14.6.12--17, printed pp.1031--1036.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section06.OddCriticalPair
open Chapter15.Section03 OddNormalizer
open Chapter15.Section03.AbelianAmalgam
open Chapter15.Section03.AbelianAmalgam.GenerationOne
variable {G : Type*} [Group G] [Finite G]
variable {H U Z : Subgroup G} [IsElementaryAbelian 2 U]
attribute [local instance] orthogonalAction

omit [Finite G] in
/-- The original H₂ is exactly the preimage of the other matrix factor.
Pointwise fixation gives containment; both quotient factors have order six. -/
theorem original_second_factor_eq
    (a : LocalQuotientAction H U Z) (T H0 H1 H2 : Subgroup G)
    (d : ExchangedFactorSetup a T 3 H0 H1 H2)
    (o : SourceOrthogonalFourAction H U Z (H.pCoreIn 2))
    (i : OrthogonalPlaneIndex) (hi : o.plane i = firstSupport a H1) :
    H2 = o.secondFactor i := by
  have h2H := d.second_le.trans d.zero_le
  have hfix := second_factor_fixes_first_support a T 3 H0 H1 H2 d
  have himage : (H2.subgroupOf H).map o.actor ≤ BinaryWreathPointStabilizer.secondFactor i := by
    rintro _ ⟨x,hx,rfl⟩
    apply (BinaryWreathPointStabilizer.mem_secondFactor_iff i (o.actor x)).mpr
    intro v hv
    obtain ⟨w,rfl⟩ := o.surjective v
    have hw : (w : G) ∈ firstSupport a H1 := hi ▸ (o.mem_plane_iff i w).mpr hv
    exact (o.fixed_iff_commutator_mem x w).mpr
      (hfix (commutator_mem_commutator hw hx))
  have hcard : Nat.card ((H2.subgroupOf H).map o.actor) = 6 := by
    have hk : o.actor.ker = (QuotientGroup.mk' (pCore 2 H)).ker := by
      rw [o.actor_kernel,QuotientGroup.ker_mk']
      exact comap_map_eq_self_of_injective H.subtype_injective _
    rw [←relIndex_ker,hk,relIndex_ker]
    change Nat.card (actorImage H H2) = 6
    rw [Nat.card_congr d.second_model.some.toEquiv,DihedralGroup.nat_card]
  have he : (H2.subgroupOf H).map o.actor = BinaryWreathPointStabilizer.secondFactor i :=
    eq_of_le_of_card_ge himage (by rw [hcard,BinaryWreathPointStabilizer.card_secondFactor])
  have hker : o.actor.ker ≤ H2.subgroupOf H := by
    rw [o.actor_kernel]
    exact subgroupOf_mono H d.core_le_second
  have hpre := congrArg (fun B => B.comap o.actor) he
  rw [comap_map_eq_self hker] at hpre
  have hm := congrArg (fun B : Subgroup H => B.map H.subtype) hpre
  rw [map_subgroupOf_eq_of_le h2H] at hm
  exact hm

end CFSG.Quasithin.Chapter14.Section06.OddCriticalPair

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.OddCriticalPair
open Chapter15.Section03 OddNormalizer
open Chapter15.Section03.AbelianAmalgam
open Chapter15.Section03.AbelianAmalgam.GenerationOne
variable {G : Type*} [Group G] [Finite G]

/-- The literal original factor and full quotient centralizer have the same
embedded two-residual; neither their equality nor the index is an input. -/
theorem original_second_factor_residual
    {D : ChapterF.Section09.Setup G} (h : D.Hypothesis)
    [IsElementaryAbelian 2 D.UH]
    (a : LocalQuotientAction D.H D.UH D.V₁) (H0 H1 H2 : Subgroup G)
    (d : ExchangedFactorSetup a (D.T : Subgroup G) 3 H0 H1 H2)
    (o : SourceOrthogonalFourAction D.H D.UH D.V₁ D.QH)
    (i : OrthogonalPlaneIndex) (hi : o.plane i = firstSupport a H1)
    (u : (⁅D.UH,D.H⁆ : Subgroup G))
    (hu : (u : G) ∈ o.plane i) (huz : (u : G) ∉ D.V₁) :
    H2 ≤ h.kernel (zpowers (u : G)) ∧ H2.relIndex (h.kernel (zpowers (u : G))) = 2 ∧
      (pResidual 2 H2).map H2.subtype =
        (pResidual 2 (h.kernel (zpowers (u : G)))).map (h.kernel (zpowers (u : G))).subtype := by
  have huU : (u : G) ∈ D.UH :=
    (le_normalizer_iff_commutator_le_left.mp o.normalized) u.property
  have hu2 : (u : G)^2 = 1 := elemPow_eq_one_of_isElementaryAbelian (p := 2) (u : G) huU
  exact second_factor_residual h o i H2
    (original_second_factor_eq a (D.T : Subgroup G) H0 H1 H2 d o i hi) u hu2 hu huz

end CFSG.Quasithin.Chapter14.Section06.OddCriticalPair

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.OddCriticalPair
open OddNormalizer SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
variable {G : Type*} [Group G] [Finite G]

/-- Rank-four recognition with the original second factor identified in the
same matrix marking. This removes the factor-identification premise of the
parabolic and residual consumer. The endpoint geometry remains separate. -/
theorem source_rankFour_orthogonal_marked_factors
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)]
    (a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T))
    (p : ℕ) (H0 H1 H2 : Subgroup G)
    (d : ExchangedFactorSetup a (T : Subgroup G) p H0 H1 H2)
    (hdim : Module.finrank (ZMod 2) (subspaceCommutator a.representation ⊤ ⊤) = 4) :
    p = 3 ∧ ∃ o : SourceOrthogonalFourAction H (conjugateSpanBy (localModule T M) H)
      (centralInvolutions T) (H.pCoreIn 2),
      ∃ i : OrthogonalPlaneIndex, o.plane i = firstSupport a H1 ∧ H2 = o.secondFactor i := by
  obtain ⟨hp,o,i,hi⟩ := source_rankFour_orthogonal_action hG T hempty hM hunique hmany
    hcard e hab H hH a p H0 H1 H2 d hdim
  subst p
  exact ⟨rfl,o,i,hi,original_second_factor_eq a (T : Subgroup G) H0 H1 H2 d o i hi⟩

end CFSG.Quasithin.Chapter14.Section06.OddCriticalPair
