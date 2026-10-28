module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.SourceNormalizer.Sextet.Quotient

/-!
# The original Mathieu three-space normalizer extension

Transport the 45-point classification through the checked marking interchange.
The kernel is defined from the actual action on the six literal four-subgroups
of A₂. It has order three, is normal in N_G(A₂)/A₂, and its quotient is S₆.
Membership is characterized by ambient normalization of each of the six fours,
so the extension retains the original local geometry and quotient maps.

Source: Aschbacher, *Sporadic Groups* (1994), 40.4(1), 40.5(2), pp.218–219.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory.TransvectionFive.UniquenessMathieu.SourceNormalizer
open UniquenessLinear
variable {G : Type*} [Group G] [Finite G] {z : G} (F : MarkedCentralizer z)

/-- The cubic subgroup is the kernel of the action on the six literal
four-subgroups inside the original oriented A₂. -/
def threeSpaceCubicKernel (hcounts : MathieuFusionOrientation F) :
    Subgroup (threeSpaceQuotient F) := (threeSpaceSextetAction F hcounts).ker

instance threeSpaceCubicKernel_normal (hcounts : MathieuFusionOrientation F) :
    (threeSpaceCubicKernel F hcounts).Normal := MonoidHom.normal_ker _

theorem threeSpaceSextetAction_surjective (hcounts : MathieuFusionOrientation F) :
    Function.Surjective (threeSpaceSextetAction F hcounts) := by
  rw [threeSpaceSextetAction_eq]
  have hc : ((oppositeMarking F).fusion (oppositeMarking F).plane).ncard = 45 := by
    simpa only [MarkedCentralizer.fusion, oppositeMarking_plane] using hcounts.2
  intro p
  obtain ⟨q, hq⟩ := (planeSextetAction_structure (oppositeMarking F) hc).2 p
  refine ⟨(threeSpacePlaneQuotientEquiv F).symm q, ?_⟩
  change planeSextetAction (oppositeMarking F) hc
    (threeSpacePlaneQuotientEquiv F ((threeSpacePlaneQuotientEquiv F).symm q)) = p
  rw [MulEquiv.apply_symm_apply]
  exact hq

theorem threeSpace_quotient_card (hcounts : MathieuFusionOrientation F) :
    Nat.card (threeSpaceQuotient F) = 2160 := by
  rw [Nat.card_congr (threeSpacePlaneQuotientEquiv F).toEquiv]
  exact planeSextet_quotient_card (oppositeMarking F) (by
    simpa only [MarkedCentralizer.fusion, oppositeMarking_plane] using hcounts.2)

/-- Source 40.4(1) identifies an extension by C₃, with the original
normalizer quotient and the actual six-point permutation map. -/
def threeSpaceCubicQuotientEquiv (hcounts : MathieuFusionOrientation F) :
    (threeSpaceQuotient F ⧸ threeSpaceCubicKernel F hcounts) ≃* Equiv.Perm (Fin 6) :=
  QuotientGroup.quotientKerEquivOfSurjective (threeSpaceSextetAction F hcounts)
    (threeSpaceSextetAction_surjective F hcounts)

theorem threeSpaceCubicKernel_card (hcounts : MathieuFusionOrientation F) :
    Nat.card (threeSpaceCubicKernel F hcounts) = 3 := by
  have hm := card_eq_card_quotient_mul_card_subgroup (threeSpaceCubicKernel F hcounts)
  rw [threeSpace_quotient_card F hcounts,
    Nat.card_congr (threeSpaceCubicQuotientEquiv F hcounts).toEquiv,
    Nat.card_eq_fintype_card, Fintype.card_perm] at hm
  norm_num at hm
  omega

theorem threeSpaceCubicQuotientEquiv_mk (hcounts : MathieuFusionOrientation F)
    (q : threeSpaceQuotient F) :
    threeSpaceCubicQuotientEquiv F hcounts (QuotientGroup.mk q) =
      threeSpaceSextetAction F hcounts q := by
  unfold threeSpaceCubicQuotientEquiv
  rfl

/-- An element lies in the cubic kernel precisely when its ambient lift
normalizes every one of the six marked four-subgroups. -/
theorem mem_threeSpaceCubicKernel_iff (hcounts : MathieuFusionOrientation F)
    (n : threeSpaceNormalizer F) :
    QuotientGroup.mk n ∈ threeSpaceCubicKernel F hcounts ↔
      ∀ i : Fin 6, n.val ∈ normalizer (planeFour (oppositeMarking F) i : Set G) := by
  change threeSpaceSextetAction F hcounts (QuotientGroup.mk n) = 1 ↔ _
  constructor
  · intro h i
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (planeFour (oppositeMarking F) i).map (MulAut.conj (n : G)).toMonoidHom = _
    rw [threeSpaceSextetAction_conjugation F hcounts, h, Equiv.Perm.one_apply]
  · intro h
    apply Equiv.ext
    intro i
    apply planeFour_injective (oppositeMarking F)
    change planeFour (oppositeMarking F)
      (threeSpaceSextetAction F hcounts (QuotientGroup.mk n) i) = planeFour (oppositeMarking F) i
    rw [← threeSpaceSextetAction_conjugation F hcounts]
    exact mem_normalizer_iff_map_conj_eq.mp (h i)

end Theory.GroupTheory.TransvectionFive.UniquenessMathieu.SourceNormalizer
