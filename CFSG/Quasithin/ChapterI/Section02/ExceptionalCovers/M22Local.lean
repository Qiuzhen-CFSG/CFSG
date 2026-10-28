module

public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.Definitions
public import Theory.GroupTheory.CentralizerResidualRestriction
public import Theory.Mathieu.M22.CentralCoverPrelude
public import Theory.Mathieu.M22.Properties.HexadExtension
public import Theory.GroupTheory.PCoreFrattiniTransport
public import Theory.SpecificGroups.SymmetricFive.AutomorphismRank
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# The actual local pullbacks in the M₂₂ covering argument

For the literal central quotient of K, construct the hexad-stabilizer
preimage I and the pointwise-kernel preimage R. The six-point action identifies
I/R with A₆, and R is exactly O₂(I) when the center is a two-group.
The native fixed hexad places each noncentral involution centralizer inside
one of these actual subgroups I.

For an arbitrary S₅/E₁₆ subgroup of M₂₂, its elementary kernel is its two-core.
The double-cover lifting argument therefore proves the Frattini assertion
in I.2.2(6a) for its literal full preimage, without a representative choice.
The complement, module recognition, central residual placement and unique
square clause are not asserted here.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, I.2.2(6),
printed pp.410 and 412 / PDF pp.421 and 423.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M22Local
open Subgroup Sporadic.Mathieu Sporadic.Mathieu.M22CentralCover
open scoped Pointwise
variable {K : Type*} [Group K]

/-- The actual full hexad-stabilizer preimage in K. -/
noncomputable def hexadPreimage (e : (K ⧸ center K) ≃* M22) (B : Finset (Fin 22)) :
    Subgroup K := preimage e (MulAction.stabilizer M22 B)

/-- The full pointwise-kernel preimage; its normality is relative to I. -/
noncomputable def hexadRadical (e : (K ⧸ center K) ≃* M22) (B : Finset (Fin 22)) :
    Subgroup K := preimage e (m22HexadPointwiseKernel B)

theorem center_le_hexadRadical (e : (K ⧸ center K) ≃* M22) (B : Finset (Fin 22)) :
    center K ≤ hexadRadical e B := center_le_preimage e _

theorem hexadRadical_le (e : (K ⧸ center K) ≃* M22) (B : Finset (Fin 22)) :
    hexadRadical e B ≤ hexadPreimage e B :=
  comap_mono (m22HexadPointwiseKernel_le B)

/-- Intrinsic coordinates on the same radical, with the specified quotient map. -/
theorem hexadRadical_subgroupOf (e : (K ⧸ center K) ≃* M22) (B : Finset (Fin 22)) :
    (hexadRadical e B).subgroupOf (hexadPreimage e B) =
      (m22SetAction B).ker.comap (localProjection e (MulAction.stabilizer M22 B)) := by
  ext x
  change projection e x ∈ m22HexadPointwiseKernel B ↔
    localProjection e (MulAction.stabilizer M22 B) x ∈ (m22SetAction B).ker
  constructor
  · rintro ⟨y, hy, he⟩
    exact (show y = localProjection e (MulAction.stabilizer M22 B) x from
      Subtype.ext he) ▸ hy
  · intro hx
    exact ⟨localProjection e (MulAction.stabilizer M22 B) x, hx, rfl⟩

instance hexadRadical_normal (e : (K ⧸ center K) ≃* M22) (B : Finset (Fin 22)) :
    ((hexadRadical e B).subgroupOf (hexadPreimage e B)).Normal := by
  rw [hexadRadical_subgroupOf]
  exact (inferInstance : (m22SetAction B).ker.Normal).comap _

/-- This is the quotient isomorphism induced by the actual six-point action. -/
noncomputable def hexadQuotientEquiv (e : (K ⧸ center K) ≃* M22)
    {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    (hexadPreimage e B ⧸ (hexadRadical e B).subgroupOf (hexadPreimage e B)) ≃*
      alternatingGroup (Fin 6) := by
  letI := hexadRadical_normal e B
  exact (@QuotientGroup.equivOfSurjectiveComap
    (hexadPreimage e B) (MulAction.stabilizer M22 B) _ _
    (localProjection e (MulAction.stabilizer M22 B)) (localProjection_surjective e _)
    ((hexadRadical e B).subgroupOf (hexadPreimage e B)) (m22SetAction B).ker
    (hexadRadical_normal e B) inferInstance (hexadRadical_subgroupOf e B).symm).trans
      (m22HexadQuotientAlternatingEquiv hB)

@[simp] theorem hexadQuotientEquiv_mk (e : (K ⧸ center K) ≃* M22)
    {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) (x : hexadPreimage e B) :
    (hexadQuotientEquiv e hB (QuotientGroup.mk x) : Equiv.Perm (Fin 6)) =
      m22HexadAction hB (localProjection e (MulAction.stabilizer M22 B) x) := rfl

theorem hexadRadical_card (e : (K ⧸ center K) ≃* M22)
    {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    Nat.card (hexadRadical e B) = 16 * Nat.card (center K) := by
  rw [hexadRadical, preimage_card, m22HexadPointwiseKernel_card hB]

/-- The source odd-index condition is 77 for every chosen hexad. -/
theorem hexadPreimage_index (e : (K ⧸ center K) ≃* M22)
    {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    (hexadPreimage e B).index = 77 := by
  change ((MulAction.stabilizer M22 B).comap (projection e)).index = 77
  rw [(MulAction.stabilizer M22 B).index_comap_of_surjective (projection_surjective e)]
  have hc := (MulAction.stabilizer M22 B).card_mul_index
  rw [m22Hexad_stabilizer_card hB, m22_order] at hc
  omega

private theorem alternatingSix_twoCore : pCore 2 (alternatingGroup (Fin 6)) = ⊥ := by
  rcases alternatingGroup.normal_subgroup_eq_bot_or_eq_top (by simp : 5 ≤ Nat.card (Fin 6))
      (N := pCore 2 (alternatingGroup (Fin 6))) with h | h
  · exact h
  · have hc : Nat.card (pCore 2 (alternatingGroup (Fin 6))) = 360 := by
      rw [h, Subgroup.card_top, nat_card_alternatingGroup, Nat.card_fin]
      decide
    obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := alternatingGroup (Fin 6))).exists_card_eq
    have hd : 3 ∣ 2 ^ n := hn ▸ hc.symm ▸ (by decide : 3 ∣ 360)
    exact False.elim ((by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd))

private theorem core_eq_of_quotient {A Q : Type*} [Group A] [Finite A] [Group Q] [Finite Q]
    (N : Subgroup A) [N.Normal] (hN : IsPGroup 2 N) (a : (A ⧸ N) ≃* Q)
    (hQ : pCore 2 Q = ⊥) : pCore 2 A = N := by
  let f := a.toMonoidHom.comp (QuotientGroup.mk' N)
  have hk : f.ker = N := (MonoidHom.ker_mulEquiv_comp (QuotientGroup.mk' N) a).trans
    (QuotientGroup.ker_mk' N)
  have hc := f.comap_pCore_of_ker_isPGroup
    (a.surjective.comp (QuotientGroup.mk'_surjective N)) (hk.symm ▸ hN)
  rw [hQ, MonoidHom.comap_bot, hk] at hc
  exact hc.symm

/-- The genuine native hexad kernel, not an arbitrary E16, is the two-core. -/
theorem native_hexad_twoCore {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    pCore 2 (MulAction.stabilizer M22 B) = (m22SetAction B).ker :=
  core_eq_of_quotient _ (IsPGroup.of_card (n := 4) (by simpa using m22HexadKernel_card hB))
    (m22HexadQuotientAlternatingEquiv hB) alternatingSix_twoCore

variable [Finite K]

/-- The source radical R is exactly O₂(I), embedded back in K. -/
theorem hexadRadical_eq_twoCore (e : (K ⧸ center K) ≃* M22)
    (hZ : IsPGroup 2 (center K)) {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    hexadRadical e B = (pCore 2 (hexadPreimage e B)).map (hexadPreimage e B).subtype := by
  have h := preimage_twoCore e hZ (MulAction.stabilizer M22 B)
  rw [native_hexad_twoCore hB] at h
  exact h

/-- In the double cover the actual hexad radical is elementary abelian. -/
theorem hexadRadical_elementary (e : (K ⧸ center K) ≃* M22)
    (hZ : Nat.card (center K) = 2) {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    IsElementaryAbelian 2 (hexadRadical e B) := by
  let := m22HexadPointwiseKernel_elementaryAbelian hB
  exact elementary_preimage e hZ _

omit [Finite K] in
/-- Every noncentral cover involution selects a genuine local subgroup I
containing its entire centralizer, by its native fixed hexad. -/
theorem centralizer_le_fixedHexad (e : (K ⧸ center K) ≃* M22) (u : K)
    (hu : orderOf u = 2) (hun : u ∉ center K) :
    m22FixedPoints (projection e u) ∈ m22Blocks ∧
      u ∈ hexadRadical e (m22FixedPoints (projection e u)) ∧
      centralizer ({u} : Set K) ≤ hexadPreimage e (m22FixedPoints (projection e u)) := by
  have hq : orderOf (projection e u) = 2 := by
    apply orderOf_eq_prime_iff.mpr
    refine ⟨?_, fun h => hun (projection_ker e ▸ h)⟩
    rw [← map_pow, show u ^ 2 = 1 from hu ▸ pow_orderOf_eq_one u, map_one]
  refine ⟨m22FixedPoints_mem_blocks _ hq, m22_mem_fixedPoints_kernel _, ?_⟩
  intro x hx
  change projection e x ∈ MulAction.stabilizer M22 (m22FixedPoints (projection e u))
  apply m22_centralizer_le_fixedPoints_stabilizer (projection e u)
  apply mem_centralizer_singleton_iff.mpr
  simpa only [map_mul] using congrArg (projection e) (mem_centralizer_singleton_iff.mp hx)

omit [Finite K] in
/-- The same element of K, now in its fixed-point stabilizer preimage. -/
noncomputable def fixedHexadElement (e : (K ⧸ center K) ≃* M22) (u : K) :
    hexadPreimage e (m22FixedPoints (projection e u)) :=
  ⟨u, hexadRadical_le e _ (m22_mem_fixedPoints_kernel _)⟩

/-- A local square calculation uses precisely the full ambient centralizer core. -/
theorem fixedHexadCore_map (e : (K ⧸ center K) ≃* M22) (u : K)
    (hu : orderOf u = 2) (hun : u ∉ center K) :
    (centralizerCore (fixedHexadElement e u)).map
      (hexadPreimage e (m22FixedPoints (projection e u))).subtype = centralizerCore u := by
  change (Theory.GroupTheory.centralizerResidualCore (fixedHexadElement e u)).map _ =
    Theory.GroupTheory.centralizerResidualCore u
  exact Theory.GroupTheory.map_centralizerResidualCore_subtype _ _
    (centralizer_le_fixedHexad e u hu hun).2.2

/-- The source notation S₅/E₁₆, with normality relative to the subgroup. -/
def IsSourceJ (H : Subgroup M22) : Prop :=
  ∃ N : Subgroup H, ∃ _ : N.Normal, IsElementaryAbelian 2 N ∧ Nat.card N = 16 ∧
    Nonempty ((H ⧸ N) ≃* Equiv.Perm (Fin 5))

/-- The source E16 kernel is intrinsic, even when no representative was chosen. -/
theorem sourceJ_twoCore (H : Subgroup M22) (hH : IsSourceJ H) :
    IsElementaryAbelian 2 (pCore 2 H) ∧ Nat.card (pCore 2 H) = 16 := by
  obtain ⟨N, hN, hE, hc, ⟨a⟩⟩ := hH
  let := hN
  let := hE
  rw [core_eq_of_quotient N (IsElementaryAbelian.isPGroup 2 N) a
    Theory.SpecificGroups.SymmetricFive.pCore_two_eq_bot]
  exact ⟨hE, hc⟩

/-- I.2.2(6a), the Frattini assertion for every source J when the center has order two. -/
theorem sourceJ_doubleCover_frattini (e : (K ⧸ center K) ≃* M22)
    (hZ : Nat.card (center K) = 2) (H : Subgroup M22) (hH : IsSourceJ H) :
    frattini (pCore 2 (preimage e H)) = ⊥ := by
  let := (sourceJ_twoCore H hH).1
  exact local_twoCore_frattini e hZ H

/-- The order-two-center source two-core is an actual elementary abelian group. -/
theorem sourceJ_doubleCover_elementary (e : (K ⧸ center K) ≃* M22)
    (hZ : Nat.card (center K) = 2) (H : Subgroup M22) (hH : IsSourceJ H) :
    IsElementaryAbelian 2 (pCore 2 (preimage e H)) := by
  let : Fact (IsPGroup 2 (pCore 2 (preimage e H))) := ⟨pCore_isPGroup⟩
  exact (frattini_eq_bot_iff_isElementaryAbelian (p := 2)).mp
    (sourceJ_doubleCover_frattini e hZ H hH)

/-- The actual two-core order is 32 or 64 in the two respective center cases. -/
theorem sourceJ_core_card (e : (K ⧸ center K) ≃* M22)
    (hZ : IsPGroup 2 (center K)) (H : Subgroup M22) (hH : IsSourceJ H) :
    Nat.card (pCore 2 (preimage e H)) = Nat.card (center K) * 16 := by
  have hk : IsPGroup 2 (localProjection e H).ker := by
    rw [localProjection_ker]
    exact hZ.comap_subtype
  rw [(localProjection e H).card_pCore_of_ker_isPGroup (localProjection_surjective e H) hk,
    localProjection_ker_card, (sourceJ_twoCore H hH).2]

end CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M22Local
