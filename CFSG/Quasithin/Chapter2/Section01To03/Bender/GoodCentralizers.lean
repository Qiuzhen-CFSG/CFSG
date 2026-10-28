module

public import CFSG.Quasithin.Chapter2.Section01To03.Bender.BadCentralizers
public import Theory.GroupTheory.TightlyEmbedded.ProductDisconnected
public import BenderSuzuki.SE.Interfaces
public import CFSG.Quasithin.Chapter2.Section01To03.Bender.GoodCentralizers.Geometry

/-!
# The good-centralizer branch of Proposition 2.2.2

The original elementary subgroup U and its fusion in M construct the literal
product-disconnected set I(U)^G. Simple Corollary ZD then recognizes G itself
and identifies the original M as a Borel subgroup. This avoids the covering
classification needed by Shult's theorem for a general ambient group.

The empty-delta application constructs U and discharges all its centralizer
containments using the completed bad-centralizer argument. The three universal
earlier-source implications remain explicit for the Bender parent to discharge:
1.1.5, ordinary I.3.1 balance, and simple Corollary ZD. No strong-embedding
conclusion is assumed or asserted before recognition.

Source: Aschbacher--Smith, Proposition 2.2.2, printed pp.519--520, and
GLS4, Chapter 2, Corollary ZD following Theorem ZD, printed pp.20--21.
-/

public section
open Subgroup Theory.GroupTheory
open BenderSuzuki.PFAppendixIII

namespace CFSG.Quasithin.Chapter2.BenderFusion
universe u

namespace GoodCentralizers

/-- The genuine universal simple Corollary ZD. Its producer is the existing
product-disconnected/ZD source family; this definition asserts no theorem. -/
@[expose] def SimpleCorollaryZD : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (Z : Set G) (M : Subgroup G),
    IsSimpleGroup G → ¬ IsMulCommutative G → IsProductDisconnected Z M →
      BenderSuzuki.IsSimpleBenderGroup G ∧ BenderSuzuki.IsBorelSubgroup M

end GoodCentralizers

variable {G : Type u} [Group G] {T : Sylow 2 G} {M : Subgroup G}

/-- The original normalizer is proper in the nonabelian simple application. -/
theorem LocalControlWitness.normalizer_ne_top
    (w : LocalControlWitness T M) (hs : IsSimpleGroup G)
    (hna : ¬ IsMulCommutative G) : M ≠ ⊤ := by
  intro hM
  let : IsSimpleGroup G := hs
  have hn : w.U.Normal := normalizer_eq_top_iff.mp (w.normalizer_eq.trans hM)
  rcases hs.eq_bot_or_eq_top_of_normal w.U hn with hb | ht
  · exact w.ne_bot hb
  · let : IsElementaryAbelian 2 w.U := w.elementary
    have hc : IsMulCommutative (⊤ : Subgroup G) := ht ▸
      (inferInstance : IsMulCommutative w.U)
    exact hna ⟨⟨fun x y => congrArg Subtype.val
      (@mul_comm' (⊤ : Subgroup G) _ hc ⟨x, mem_top x⟩ ⟨y, mem_top y⟩)⟩⟩

/-- Fusion identifies exactly the original nonidentity U-elements in M. -/
theorem LocalControlWitness.involutionConjugates_inter
    (w : LocalControlWitness T M) (hTM : (T : Subgroup G) ≤ M) :
    involutionConjugates w.U ∩ (M : Set G) = {x : G | x ∈ w.U ∧ x ≠ 1} := by
  ext x
  constructor
  · rintro ⟨⟨g, y, hy, hi, rfl⟩, hxM⟩
    have hf := Set.ext_iff.mp (w.conjugates_in_M y hy) (MulAut.conj g y)
    obtain ⟨m, hm, he⟩ := hf.mp ⟨isConj_iff.mpr ⟨g, rfl⟩, hxM⟩
    refine ⟨?_, (involutionConjugates_isInvolution ⟨g, y, hy, hi, rfl⟩).ne_one⟩
    rw [← he]
    simpa only [inv_inv] using
      (mem_normalizer_iff.mp (w.normalizes (M.inv_mem hm)) y).mp hy
  · rintro ⟨hx, hx1⟩
    let : IsElementaryAbelian 2 w.U := w.elementary
    exact ⟨mem_involutionConjugates hx ⟨hx1, elemPow_eq_one_of_isElementaryAbelian x hx⟩,
      hTM (w.le_sylow hx)⟩

private theorem returning_conjugator_mem (w : LocalControlWitness T M)
    (hg : ∀ u ∈ w.U, u ≠ 1 → centralizer ({u} : Set G) ≤ M)
    {x g : G} (hx : x ∈ w.U) (hx1 : x ≠ 1)
    (hr : MulAut.conj g x ∈ M) : g ∈ M := by
  obtain ⟨m, hm, he⟩ := (Set.ext_iff.mp (w.conjugates_in_M x hx)
    (MulAut.conj g x)).mp ⟨isConj_iff.mpr ⟨g, rfl⟩, hr⟩
  have hc : m * g ∈ centralizer ({x} : Set G) := by
    apply mem_centralizer_singleton_iff.mpr
    have hf : (m * g) * x * (m * g)⁻¹ = x := by
      calc
        _ = m * (g * x * g⁻¹) * m⁻¹ := by group
        _ = m * (m⁻¹ * x * m) * m⁻¹ := by
          change m * (MulAut.conj g x) * m⁻¹ = _
          rw [← he]
        _ = x := by group
    exact mul_inv_eq_iff_eq_mul.mp hf
  have hmgg := M.mul_mem (M.inv_mem hm) (hg x hx hx1 hc)
  simpa only [inv_mul_cancel_left] using hmgg

/-- Good centralizers construct Definition ZD on the actual I(U)^G and M. -/
theorem LocalControlWitness.productDisconnected_of_centralizers_le
    (w : LocalControlWitness T M) (hs : IsSimpleGroup G)
    (hna : ¬ IsMulCommutative G) (hTM : (T : Subgroup G) ≤ M)
    (hg : ∀ u ∈ w.U, u ≠ 1 → centralizer ({u} : Set G) ≤ M) :
    IsProductDisconnected (involutionConjugates w.U) M := by
  have hinter := w.involutionConjugates_inter hTM
  have hmem {x : G} (hx : x ∈ involutionConjugates w.U) (hxM : x ∈ M) :
      x ∈ w.U ∧ x ≠ 1 := (Set.ext_iff.mp hinter x).mp ⟨hx, hxM⟩
  refine ⟨fun _ hz => involutionConjugates_isInvolution hz,
    fun g _ hz => involutionConjugates_invariant g hz,
    w.normalizer_ne_top hs hna, ?_, ?_, ?_⟩
  · refine ⟨w.z, ?_, hTM (w.le_sylow w.z_mem)⟩
    exact mem_involutionConjugates w.z_mem
      ⟨w.z_ne_one, (orderOf_eq_prime_iff.mp w.z_order).1⟩
  · intro x hx hxM g
    constructor
    · exact returning_conjugator_mem w hg (hmem hx hxM).1 (hmem hx hxM).2
    · intro hgm
      exact M.mul_mem (M.mul_mem hgm hxM) (M.inv_mem hgm)
  · intro x hx y hy hi hxyM
    have hxi := involutionConjugates_isInvolution hx
    have hyi := involutionConjugates_isInvolution hy
    have hc : Commute x y := by
      have he := hi.inv_eq_self
      rw [mul_inv_rev, hxi.inv_eq_self, hyi.inv_eq_self] at he
      exact he.symm
    obtain ⟨g, a, ha, hai, hga⟩ := hx
    let b := MulAut.conj g⁻¹ y
    have hgb : MulAut.conj g b = y := by simp [b, MulAut.conj_apply, mul_assoc]
    have hab : Commute a b := by
      apply (MulAut.conj g).injective
      simpa only [map_mul, hga, hgb] using hc.eq
    have hbZ : b ∈ involutionConjugates w.U := involutionConjugates_invariant _ hy
    have hbM : b ∈ M := hg a ha hai.ne_one
      (mem_centralizer_singleton_iff.mpr hab.eq.symm)
    have hbU := (hmem hbZ hbM).1
    have hab1 : a * b ≠ 1 := by
      intro he
      apply hi.ne_one
      have hh := congrArg (MulAut.conj g) he
      simpa only [map_mul, hga, hgb, map_one] using hh
    have hprod : x * y ∈ involutionConjugates w.U := by
      refine ⟨g, a * b, w.U.mul_mem ha hbU, ?_, ?_⟩
      · refine ⟨hab1, ?_⟩
        rw [hab.mul_pow, hai.sq_eq_one,
          (involutionConjugates_isInvolution hbZ).sq_eq_one, one_mul]
      · rw [map_mul, hga, hgb]
    exact hg _ (hmem hprod hxyM).1 hi.ne_one

variable [Finite G]

/-- Simple Corollary ZD recognizes G and the original M from the constructed
product-disconnected set. The earlier theorem is the only recognition input. -/
theorem LocalControlWitness.bender_borel_of_centralizers_le
    (w : LocalControlWitness T M) (hs : IsSimpleGroup G)
    (hna : ¬ IsMulCommutative G) (hTM : (T : Subgroup G) ≤ M)
    (hg : ∀ u ∈ w.U, u ≠ 1 → centralizer ({u} : Set G) ≤ M)
    (sourceZD : GoodCentralizers.SimpleCorollaryZD.{u}) :
    BenderSuzuki.IsSimpleBenderGroup G ∧ BenderSuzuki.IsBorelSubgroup M :=
  sourceZD G (involutionConjugates w.U) M hs hna
    (w.productDisconnected_of_centralizers_le hs hna hTM hg)

/-- The empty-delta source application retains the constructed U, original
T and M, and the full known-simple induction class. -/
theorem source_bender_borel_of_delta_empty
    (hG : IsSimpleQTKE CFSG.KnownSimple.IsKnownSimple G) (T : Sylow 2 G) (M : Subgroup G)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hdelta : delta (Chapter1.He G) M = ∅)
    (source115 : BadCentralizers.ComponentSource115 G)
    (source13 : BadCentralizers.OrdinaryBalance13.{u} CFSG.KnownSimple.IsKnownSimple)
    (sourceZD : GoodCentralizers.SimpleCorollaryZD.{u}) :
    ∃ w : LocalControlWitness T M,
      IsProductDisconnected (involutionConjugates w.U) M ∧
      BenderSuzuki.IsSimpleBenderGroup G ∧ BenderSuzuki.IsBorelSubgroup M := by
  obtain ⟨w, hg⟩ := source_local_control_with_centralizers_of_delta_empty
    hG T M hM hTM hunique hdelta source115 source13
  exact ⟨w, w.productDisconnected_of_centralizers_le hG.simple hG.nonabelian hTM hg,
    w.bender_borel_of_centralizers_le hG.simple hG.nonabelian hTM hg sourceZD⟩

/-- The Borel obtained from simple Corollary ZD is the normalizer of the
original Sylow, and its original U is exactly the first omega of that Sylow. -/
theorem LocalControlWitness.markings_of_bender_borel
    (w : LocalControlWitness T M) (hTM : (T : Subgroup G) ≤ M)
    (hB : BenderSuzuki.IsSimpleBenderGroup G) (hM : BenderSuzuki.IsBorelSubgroup M) :
    ClassificationModels.IsBenderModel G ∧
      M = normalizer (T : Set G) ∧
      ∃ n : ℕ, 2 ≤ n ∧ BenderSuzuki.IsSimpleBenderGroupAtExponent n G ∧
        w.U = omegaOneAmbient (T : Subgroup G) ∧
        w.U = (center T).map (T : Subgroup G).subtype ∧ Nat.card w.U = 2 ^ n := by
  obtain ⟨S, hMS⟩ := hM.2
  have hST : (S : Subgroup G) ≤ T :=
    S.isPGroup'.le_sylow_of_normalized T (hTM.trans hMS.le)
  have he : (T : Subgroup G) = S := S.is_maximal' T.isPGroup' hST
  have hMT : M = normalizer (T : Set G) := by
    change M = normalizer ((T : Subgroup G) : Set G)
    rw [he]
    exact hMS
  have hm := GoodCentralizers.classificationModel_of_simpleBender hB
  obtain ⟨n, hn, hnG, hw, hc⟩ := GoodCentralizers.exponent_and_omega_of_simpleBender hB T
  have hNM : normalizer (omegaOneAmbient (T : Subgroup G) : Set G) = M :=
    (GoodCentralizers.normalizer_omega_eq hB T hw).trans hMT.symm
  let : IsElementaryAbelian 2 w.U := w.elementary
  have hU : w.U ≤ omegaOneAmbient (T : Subgroup G) := by
    rw [← omegaOneAmbient_eq_self w.U]
    exact omegaOneAmbient_mono w.le_sylow
  have hf := OmegaNormalizerModels.of_bender_model hm T
  have hUeq : w.U = omegaOneAmbient (T : Subgroup G) := by
    apply le_antisymm hU
    intro x hx
    by_cases hx1 : x = 1
    · simpa only [hx1] using w.U.one_mem
    obtain ⟨g, hg, hgx⟩ := hf.transitive w.z (hU w.z_mem) w.z_ne_one x hx hx1
    have hgM : g ∈ M := hNM ▸ hg
    exact hgx ▸ (mem_normalizer_iff.mp (w.normalizes hgM) w.z).mp w.z_mem
  exact ⟨hm, hMT, n, hn, hnG, hUeq, hUeq.trans hw, hUeq.symm ▸ hc⟩

/-- The good-centralizer branch with the actual model, exponent and U
markings; the only recognition input remains universal simple Corollary ZD. -/
theorem LocalControlWitness.marked_bender_of_centralizers_le
    (w : LocalControlWitness T M) (hs : IsSimpleGroup G)
    (hna : ¬ IsMulCommutative G) (hTM : (T : Subgroup G) ≤ M)
    (hg : ∀ u ∈ w.U, u ≠ 1 → centralizer ({u} : Set G) ≤ M)
    (sourceZD : GoodCentralizers.SimpleCorollaryZD.{u}) :
    BenderSuzuki.IsBorelSubgroup M ∧ ClassificationModels.IsBenderModel G ∧
      M = normalizer (T : Set G) ∧
      ∃ n : ℕ, 2 ≤ n ∧ BenderSuzuki.IsSimpleBenderGroupAtExponent n G ∧
        w.U = omegaOneAmbient (T : Subgroup G) ∧
        w.U = (center T).map (T : Subgroup G).subtype ∧ Nat.card w.U = 2 ^ n := by
  obtain ⟨hB, hM⟩ := w.bender_borel_of_centralizers_le hs hna hTM hg sourceZD
  exact ⟨hM, w.markings_of_bender_borel hTM hB hM⟩

/-- Proposition 2.2.2's empty-delta branch, with all source markings and
the full known-simple class, from its three genuine earlier implications. -/
theorem source_marked_bender_of_delta_empty
    (hG : IsSimpleQTKE CFSG.KnownSimple.IsKnownSimple G) (T : Sylow 2 G) (M : Subgroup G)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hdelta : delta (Chapter1.He G) M = ∅)
    (source115 : BadCentralizers.ComponentSource115 G)
    (source13 : BadCentralizers.OrdinaryBalance13.{u} CFSG.KnownSimple.IsKnownSimple)
    (sourceZD : GoodCentralizers.SimpleCorollaryZD.{u}) :
    ∃ w : LocalControlWitness T M,
      IsProductDisconnected (involutionConjugates w.U) M ∧
      BenderSuzuki.IsBorelSubgroup M ∧ ClassificationModels.IsBenderModel G ∧
      M = normalizer (T : Set G) ∧
      ∃ n : ℕ, 2 ≤ n ∧ BenderSuzuki.IsSimpleBenderGroupAtExponent n G ∧
        w.U = omegaOneAmbient (T : Subgroup G) ∧
        w.U = (center T).map (T : Subgroup G).subtype ∧ Nat.card w.U = 2 ^ n := by
  obtain ⟨w, hz, hB, hM⟩ := source_bender_borel_of_delta_empty
    hG T M hM hTM hunique hdelta source115 source13 sourceZD
  exact ⟨w, hz, hM, w.markings_of_bender_borel hTM hB hM⟩

end CFSG.Quasithin.Chapter2.BenderFusion
