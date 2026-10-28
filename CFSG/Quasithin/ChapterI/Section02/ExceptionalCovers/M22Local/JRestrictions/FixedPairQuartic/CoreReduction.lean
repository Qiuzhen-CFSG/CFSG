module

public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M22Local.JRestrictions.FixedPairQuartic

/-!
# The actual pair-core Frattini quotient under quartic reduction

Restrict the quotient by central squares to the literal local two-core.
The p-group-kernel theorem proves surjectivity on cores, and the previously
proved source-J Frattini equality identifies its kernel. Thus the quartic
core modulo Frattini is the actual binary-cover core, with the ambient
quotient-map equation retained.

Source: Aschbacher–Smith I.2.2(6a), printed pp.410 and 412. This supplies
quotient coordinates; it does not recognize the quartic central product.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M22Local.FixedPairQuartic
open Subgroup Sporadic.Mathieu Sporadic.Mathieu.M22CentralCover
open CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M22Local
variable {K : Type*} [Group K] [Finite K] [IsCyclic (center K)]

/-- Restriction of the actual square quotient to the local two-core. -/
noncomputable def coreReduction (e : (K ⧸ center K) ≃* M22)
    (hZ : Nat.card (center K) = 4) (H : Subgroup M22) :
    pCore 2 (preimage e H) →* pCore 2 (preimage (quarticReductionEquiv e) H) where
  toFun x := ⟨quarticReductionLocal e H x.val,
    (localProjection_comap_twoCore (quarticReductionEquiv e)
      (IsPGroup.of_card (n := 1) (by simpa using quarticReduction_center_card e hZ)) H).le
      ((localProjection_comap_twoCore e
        (IsPGroup.of_card (n := 2) (by simpa using hZ)) H).ge x.property)⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem coreReduction_surjective (e : (K ⧸ center K) ≃* M22)
    (hZ : Nat.card (center K) = 4) (H : Subgroup M22) :
    Function.Surjective (coreReduction e hZ H) := by
  intro y
  obtain ⟨x, hx⟩ := quarticReductionLocal_surjective e H y.val
  have hm : x ∈ pCore 2 (preimage e H) := by
    apply (localProjection_comap_twoCore e
      (IsPGroup.of_card (n := 2) (by simpa using hZ)) H).le
    have hy := (localProjection_comap_twoCore (quarticReductionEquiv e)
      (IsPGroup.of_card (n := 1) (by simpa using quarticReduction_center_card e hZ)) H).ge
        y.property
    change localProjection (quarticReductionEquiv e) H (quarticReductionLocal e H x) ∈
      pCore 2 H
    rwa [hx]
  exact ⟨⟨x, hm⟩, Subtype.ext hx⟩

theorem coreReduction_ker (e : (K ⧸ center K) ≃* M22)
    (hZ : Nat.card (center K) = 4) (H : Subgroup M22) (hH : IsSourceJ H) :
    (coreReduction e hZ H).ker = frattini (pCore 2 (preimage e H)) := by
  ext x
  have hx : x ∈ frattini (pCore 2 (preimage e H)) ↔
      (x.val : K) ∈ centerSquares K := by
    rw [← sourceJ_quartic_frattini e hZ H hH]
    change x ∈ frattini (pCore 2 (preimage e H)) ↔
      (preimage e H).subtype ((pCore 2 (preimage e H)).subtype x) ∈ _
    rw [mem_map_iff_mem (preimage e H).subtype_injective,
      mem_map_iff_mem (pCore 2 (preimage e H)).subtype_injective]
  rw [hx]
  change coreReduction e hZ H x = 1 ↔ (x.val : K) ∈ centralSquares K
  rw [Subtype.ext_iff, Subtype.ext_iff]
  exact QuotientGroup.eq_one_iff _

/-- The quotient by the proved Frattini kernel is the literal binary core. -/
noncomputable def coreReductionEquiv (e : (K ⧸ center K) ≃* M22)
    (hZ : Nat.card (center K) = 4) (H : Subgroup M22) (hH : IsSourceJ H) :
    (pCore 2 (preimage e H) ⧸ frattini (pCore 2 (preimage e H))) ≃*
      pCore 2 (preimage (quarticReductionEquiv e) H) :=
  (QuotientGroup.quotientMulEquivOfEq (coreReduction_ker e hZ H hH).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (coreReduction_surjective e hZ H))

/-- The equivalence induces precisely the original ambient square quotient. -/
@[simp] theorem coreReductionEquiv_mk (e : (K ⧸ center K) ≃* M22) (hZ : Nat.card (center K) = 4)
    (H : Subgroup M22) (hH : IsSourceJ H) (x : pCore 2 (preimage e H)) :
    ((coreReductionEquiv e hZ H hH (QuotientGroup.mk x)).val : K ⧸ centralSquares K) =
      QuotientGroup.mk' (centralSquares K) (x.val : K) := rfl

/-- Fixed-pair application, with no source-J premise left over. -/
noncomputable def fixedPairCoreReductionEquiv (e : (K ⧸ center K) ≃* M22)
    (hZ : Nat.card (center K) = 4) :
    (pCore 2 (preimage e m22DisjointPairStabilizer) ⧸
      frattini (pCore 2 (preimage e m22DisjointPairStabilizer))) ≃*
        pCore 2 (preimage (quarticReductionEquiv e) m22DisjointPairStabilizer) :=
  coreReductionEquiv e hZ _ fixed_pair_isSourceJ

@[simp] theorem fixedPairCoreReductionEquiv_mk (e : (K ⧸ center K) ≃* M22)
    (hZ : Nat.card (center K) = 4) (x : pCore 2 (preimage e m22DisjointPairStabilizer)) :
    ((fixedPairCoreReductionEquiv e hZ (QuotientGroup.mk x)).val :
      K ⧸ centralSquares K) = QuotientGroup.mk' (centralSquares K) (x.val : K) := rfl

theorem fixed_pair_frattini_quotient_card (e : (K ⧸ center K) ≃* M22)
    (hZ : Nat.card (center K) = 4) :
    Nat.card (pCore 2 (preimage e m22DisjointPairStabilizer) ⧸
      frattini (pCore 2 (preimage e m22DisjointPairStabilizer))) = 32 := by
  have h := (frattini (pCore 2 (preimage e m22DisjointPairStabilizer))).card_mul_index
  rw [fixed_pair_frattini_card e hZ, fixed_pair_core_card e hZ, index_eq_card] at h
  omega

end CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M22Local.FixedPairQuartic
