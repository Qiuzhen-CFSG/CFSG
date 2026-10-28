module

public import CFSG.Quasithin.ChapterE.Section04.GenerationSetup
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.Representation.BinaryOffender.IrreducibleMovedGeneration
public import Theory.GroupTheory.PrimeRankElementary
public import Theory.GroupTheory.PResidual.SylowSupplement

/-!
# Commutators and corank intersections for E.4.2

A weak subgroup normalized by T cannot centralize the normal quasisimple
factor L: it would then be a normal two-subgroup of LT. Sylow conjugacy
supplies its nontriviality. In a local overgroup, passage to H/O₂(H) bounds
the rank lost by intersecting a corank-family member with O₂(H).

The final lemma carries out the invariant fixed-space calculation assuming
the stated residual commutator identity. It does not derive that identity
from the local generalized-Fitting condition. All two-cores and residuals
of overgroups are formed intrinsically and then embedded in G.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, E.4.2,
printed p.241 (PDF p.252).
-/

public section
open Subgroup Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.ValueBound
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]

omit [Finite G] in
/-- A nontrivial two-subgroup normalized by T generates the normal quasisimple factor by commutators: otherwise LT normalizes that two-subgroup, contradicting the trivial two-core. -/
theorem commutator_eq_component_of_normalized_two_subgroup
    (L T W : Subgroup G) [L.Normal] [IsQuasisimple L]
    (hcore : pCore 2 G = ⊥) (hgen : L ⊔ T = ⊤)
    (hW : IsPGroup 2 W) (hne : W ≠ ⊥)
    (hn : T ≤ normalizer (W : Set G)) : ⁅L, W⁆ = L := by
  have hcomp : IsComponent G L := ⟨(inferInstance : L.Normal).isSubnormal, inferInstance⟩
  rcases hcomp.commutator_dichotomy W with hc | hc
  · have hLn : L ≤ normalizer (W : Set G) :=
      le_normalizer_iff_commutator_le_right.mpr (by rw [hc]; exact bot_le)
    have ht : normalizer (W : Set G) = ⊤ := top_unique (hgen ▸ sup_le hLn hn)
    let : W.Normal := normalizer_eq_top_iff.mp ht
    have hWcore : W ≤ pCore 2 G := le_sSup ⟨inferInstance, hW⟩
    exact (hne (le_bot_iff.mp (hcore ▸ hWcore))).elim
  · rw [hc]
    apply le_antisymm
    · apply iSup_le
      intro w x hx
      obtain ⟨y, hy, rfl⟩ := hx
      exact (inferInstance : L.Normal).conj_mem y hy w
    · exact (le_iSup_conjugates L W)

/-- Sylow conjugacy places a member of the nonempty fixed-space family inside the specified Sylow subgroup. -/
theorem fixedSpaceFamily_exists_le_sylow (ρ : Representation (ZMod 2) G V)
    (T : Sylow 2 G) {k : ℕ} (hΩ : (fixedSpaceFamily ρ k).Nonempty) :
    ∃ A ∈ fixedSpaceFamily ρ k, A ≤ (T : Subgroup G) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨A, hA⟩ := hΩ
  let : IsElementaryAbelian 2 A := hA.2.1.2
  obtain ⟨S, hAS⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S T
  refine ⟨A.map (MulAut.conj g).toMonoidHom,
    fixedSpaceFamily_conjugationInvariant ρ k A hA g, ?_⟩
  rw [← hg]
  exact map_mono hAS

/-- The actual W_j generates L by commutators. Nonemptiness of the original family suffices for every j. -/
theorem commutator_weakSubgroup_eq_component
    (ρ : Representation (ZMod 2) G V) (T : Sylow 2 G)
    (L : Subgroup G) [L.Normal] [IsQuasisimple L]
    (hcore : pCore 2 G = ⊥) (hgen : L ⊔ (T : Subgroup G) = ⊤)
    {k : ℕ} (hΩ : (fixedSpaceFamily ρ (k + 1)).Nonempty) (j : ℕ) :
    ⁅L, weakSubgroup (fixedSpaceFamily ρ (k + 1)) j T⁆ = L := by
  obtain ⟨A, hA, hAT⟩ := fixedSpaceFamily_exists_le_sylow ρ T hΩ
  apply commutator_eq_component_of_normalized_two_subgroup L T _ hcore hgen
    (T.isPGroup'.of_injective (inclusion (weakSubgroup_le _ _ _))
      (inclusion_injective _)) (weakSubgroup_ne_bot ρ hA hAT)
  exact T.toSubgroup.le_normalizer.trans (weakSubgroup_normalizer ρ (k + 1) j T)

/-- If W_j(T) lies in the local two-core, conjugacy invariance identifies it with W_j of that core, so the whole overgroup normalizes it. -/
theorem weakSubgroup_normalized_of_le_core (ρ : Representation (ZMod 2) G V)
    (T : Sylow 2 G) (H : Subgroup G) {k j : ℕ}
    (hW : weakSubgroup (fixedSpaceFamily ρ k) j T ≤ (pCore 2 H).map H.subtype) :
    H ≤ normalizer (weakSubgroup (fixedSpaceFamily ρ k) j T : Set G) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have he := SubgroupFamily.span_eq_in_p_overgroup
    (corankFamily_conjugationInvariant (fixedSpaceFamily_conjugationInvariant ρ k) j)
    T ((pCore 2 H).map H.subtype) (pCore_isPGroup.map H.subtype) hW
  change weakSubgroup (fixedSpaceFamily ρ k) j T =
    weakSubgroup (fixedSpaceFamily ρ k) j ((pCore 2 H).map H.subtype) at he
  rw [he]
  apply le_trans _ (weakSubgroup_normalizer ρ k j _)
  simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using
    (le_normalizer_map (H := pCore 2 H) H.subtype)

/-- The elementary abelian image of B in H/O₂(H) bounds the corank of its intersection with the embedded two-core. -/
theorem core_intersection_corank_le (H B : Subgroup G) (hBH : B ≤ H)
    [IsElementaryAbelian 2 B] :
    Nat.log 2 ((B ⊓ (pCore 2 H).map H.subtype).relIndex B) ≤
      primeRank 2 (H ⧸ pCore 2 H) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let q := QuotientGroup.mk' (pCore 2 H)
  let C := B.subgroupOf H
  let : IsElementaryAbelian 2 C := IsElementaryAbelian.subgroupOf hBH
  have hcard := (primeRank_le_iff_elementary_card_le
    (H ⧸ pCore 2 H)).mp le_rfl (C.map q) (IsElementaryAbelian.map (p := 2) q)
  have hidx : ((pCore 2 H).map H.subtype).relIndex B = Nat.card (C.map q) := by
    have ht := relIndex_map_map_of_injective (pCore 2 H) C H.subtype_injective
    have hC : C.map H.subtype = B := map_subgroupOf_eq_of_le hBH
    rw [hC] at ht
    calc
      _ = (pCore 2 H).relIndex C := ht
      _ = Nat.card (C.map q) := by
        simpa only [q, QuotientGroup.ker_mk'] using (relIndex_ker C q)
  rw [inf_relIndex_left, hidx]
  exact (Nat.log_mono_right hcard).trans_eq (Nat.log_pow (by decide) _)

/-- Logarithmic coranks add in a tower inside a finite two-group. -/
theorem corank_add_of_le (A B D : Subgroup G) (hBA : B ≤ A) (hDB : D ≤ B)
    (hA : IsPGroup 2 A) :
    Nat.log 2 (D.relIndex A) = Nat.log 2 (D.relIndex B) + Nat.log 2 (B.relIndex A) := by
  have hB := hA.of_injective (inclusion hBA) (inclusion_injective hBA)
  obtain ⟨a, ha⟩ := hA.exists_card_eq
  obtain ⟨b, hb⟩ := hB.exists_card_eq
  obtain ⟨r, _, hr⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    (ha ▸ relIndex_dvd_card B A)
  obtain ⟨s, _, hs⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    (hb ▸ relIndex_dvd_card D B)
  rw [← relIndex_mul_relIndex _ _ _ hDB hBA, hr, hs, ← pow_add]
  simp only [Nat.log_pow (by decide : 1 < 2)]

/-- Intersecting B with O₂(H) costs at most the local quotient rank and preserves the original containing family member A; A need not lie in H. -/
theorem core_intersection_corank_witness (ρ : Representation (ZMod 2) G V)
    (H : Subgroup G) {k j : ℕ} {B : Subgroup G}
    (hB : B ∈ corankFamily (fixedSpaceFamily ρ k) j) (hBH : B ≤ H) :
    ∃ A ∈ fixedSpaceFamily ρ k, B ≤ A ∧
      Nat.log 2 ((B ⊓ (pCore 2 H).map H.subtype).relIndex A) ≤
        j + primeRank 2 (H ⧸ pCore 2 H) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨A, hA, hBA, hj⟩ := hB
  let : IsElementaryAbelian 2 A := hA.2.1.2
  let : IsElementaryAbelian 2 B :=
    { toIsMulCommutative := IsMulCommutative.of_setLike_mul_comm
        (fun _ ha _ hb => setLike_mul_comm (hBA ha) (hBA hb))
      exponent_dvd_p := Monoid.exponent_dvd_of_monoidHom (inclusion hBA) (inclusion_injective hBA) |>.trans
        (IsElementaryAbelian.exponent_dvd_p 2 A) }
  refine ⟨A, hA, hBA, ?_⟩
  rw [corank_add_of_le A B _ hBA inf_le_left (IsElementaryAbelian.isPGroup 2 A)]
  exact (Nat.add_le_add (core_intersection_corank_le H B hBH) hj).trans_eq (Nat.add_comm _ _)

omit [Finite G] in
/-- The intrinsic two-core of an overgroup of T embeds into T. -/
theorem core_le_sylow (T : Sylow 2 G) (H : Subgroup G) (hTH : (T : Subgroup G) ≤ H) :
    (pCore 2 H).map H.subtype ≤ T := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := map_mono (f := H.subtype) (pCore_isPGroup.le_sylow_of_normal (T.subtype hTH))
  simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH] using h

/-- The source local fixed-space calculation, with the residual commutator identity explicit. The normal weak subgroup inside O₂(H) supplies an invariant fixed space. -/
theorem fixedSpace_weakSubgroup_le_residual_of_commutator
    (ρ : Representation (ZMod 2) G V) (T : Sylow 2 G) (H : Subgroup G)
    (hTH : (T : Subgroup G) ≤ H) {k j : ℕ}
    (hm : j + primeRank 2 (H ⧸ pCore 2 H) ≤ k)
    {B : Subgroup G} (hB : B ∈ corankFamily (fixedSpaceFamily ρ (k + 1)) j)
    (hBT : B ≤ T)
    (hc : ⁅(pResidual 2 H).map H.subtype, B⁆ = (pResidual 2 H).map H.subtype) :
    fixedSpace ρ (weakSubgroup (fixedSpaceFamily ρ (k + 1))
      (j + primeRank 2 (H ⧸ pCore 2 H)) T) ≤
      fixedSpace ρ ((pResidual 2 H).map H.subtype) := by
  let m := j + primeRank 2 (H ⧸ pCore 2 H)
  let Q := (pCore 2 H).map H.subtype
  let W := weakSubgroup (fixedSpaceFamily ρ (k + 1)) m Q
  have hD := core_intersection_corank_witness ρ H hB (hBT.trans hTH)
  obtain ⟨A, hA, hBA, hcorank⟩ := hD
  have hDA : B ⊓ Q ≤ A := inf_le_left.trans hBA
  have hDW : B ⊓ Q ≤ W :=
    SubgroupFamily.le_span ⟨A, hA, hDA, hcorank⟩ inf_le_right
  have hfix : fixedSpace ρ W ≤ fixedSpace ρ B := by
    have he := hA.2.2 (B ⊓ Q) hDA (by dsimp only [Q]; omega)
    exact (fixedSpace_antitone ρ hDW).trans
      (he ▸ fixedSpace_antitone ρ hBA)
  have hHn : H ≤ normalizer (Q : Set G) := by
    simpa only [Q, normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using
      (le_normalizer_map (H := pCore 2 H) H.subtype)
  have hHst : H ≤ subspaceStabilizer ρ (fixedSpace ρ W) :=
    fixedSpace_invariant_normalizer ρ
      (hHn.trans (weakSubgroup_normalizer ρ (k + 1) m Q))
  have hRst := (map_subtype_le (pResidual 2 H)).trans hHst
  have hRfix := le_fixedSpace_commutator_of_invariant ρ hRst hfix
  rw [hc] at hRfix
  exact (fixedSpace_antitone ρ (SubgroupFamily.span_mono
    (corankFamily (fixedSpaceFamily ρ (k + 1)) m) (core_le_sylow T H hTH))).trans hRfix

end CFSG.Quasithin.ChapterE.ValueBound
