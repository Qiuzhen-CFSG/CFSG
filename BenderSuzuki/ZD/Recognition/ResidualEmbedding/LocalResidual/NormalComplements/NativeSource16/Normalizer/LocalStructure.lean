module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Counting.SectionFive.MaximalFixed.NormalizerStructure
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Counting.SectionThree
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.TwoCoreSplitting.NativeSource.LocalConfiguration.FixedPair

/-!
# The contrary local normalizer in source 16.7

Theorem 4 at any literal fixed coset shows that a distinguished involution
normalizing an odd subgroup with at least three fixed cosets centralizes that
subgroup whenever it fixes one of those cosets. A noncentral normalizing
involution is therefore free on the fixed set. Section 5 supplies rank one,
conjugacy and the odd-core factorization of its normalizer. Conjugacy also
makes the distinguished circle of its centralizer trivial.

Source: GLS IV, Chapter 2, Lemma 16.7, first paragraph.
-/

noncomputable section
namespace BenderSuzuki.ZD.Section16.NativeSource
open Subgroup Theory.GroupTheory PFAppendixIII PFchapter1section1
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

omit [Finite G] in
private theorem fixes_mk_iff (x b : G) :
    x • (QuotientGroup.mk b : G ⧸ M) = QuotientGroup.mk b ↔ b⁻¹ * x * b ∈ M := by
  rw [MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq]
  constructor <;> intro hh <;>
    simpa only [mul_inv_rev, inv_inv, mul_assoc] using M.inv_mem hh

omit [Finite G] in
/-- Theorem 4 at an arbitrary fixed coset, using the original odd subgroup. -/
public theorem centralizes_of_common_fixed
    (h : IsProductDisconnected Z M) (ha : ResidualAction Z M)
    (Y : Subgroup G) (hodd : Odd (Nat.card Y))
    (hthree : 3 ≤ Nat.card (theorem4bFixedPoints M Y))
    {s : G} (hs : s ∈ Z) (hsN : s ∈ normalizer (Y : Set G))
    {beta : G ⧸ M} (hsbeta : s • beta = beta)
    (hYbeta : beta ∈ fixedPointsOfSubgroup G (G ⧸ M) Y) :
    s ∈ centralizer (Y : Set G) := by
  induction beta using Quotient.inductionOn with
  | h b =>
    let e := MulAut.conj b⁻¹
    let Q := Y.map e.toMonoidHom
    have hQM : Q ≤ M := by
      rintro _ ⟨y, hy, rfl⟩
      simpa only [e, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using
        (fixes_mk_iff y b).mp (hYbeta y hy)
    have hsM : e s ∈ M := by
      simpa only [e, MulAut.conj_apply, inv_inv] using (fixes_mk_iff s b).mp hsbeta
    have hsQ : e s ∈ normalizer (Q : Set G) :=
      le_normalizer_map (H := Y) e.toMonoidHom (mem_map_of_mem _ hsN)
    rcases ha.odd_normalizer (e s) (h.invariant _ _ hs) hsM Q
      (by rw [card_map_of_injective e.injective]; exact hodd) hQM hsQ with hc | hf
    · rw [mem_centralizer_iff]
      intro y hy
      apply e.injective
      simpa only [map_mul, MulEquiv.coe_toMonoidHom] using
        mem_centralizer_singleton_iff.mp (hc (mem_map_of_mem e.toMonoidHom hy))
    · have hcard : Nat.card (theorem4bFixedPoints M Y) = 1 := by
        apply Nat.card_eq_one_iff_exists.mpr
        refine ⟨⟨QuotientGroup.mk b, hYbeta⟩, ?_⟩
        rintro ⟨a, ha⟩
        apply Subtype.ext
        have hQa : Q ≤ MulAction.stabilizer G (b⁻¹ • a) := by
          rintro _ ⟨y, hy, rfl⟩
          apply MulAction.mem_stabilizer_iff.mpr
          simp only [e, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
          rw [mul_smul, mul_smul, smul_inv_smul, ha y hy]
        have he := congrArg (fun c : G ⧸ M => b • c) (hf _ hQa)
        simpa only [smul_inv_smul, MulAction.Quotient.smul_mk, smul_eq_mul, mul_one] using he
      omega

omit [Finite G] in
/-- A noncentral distinguished normalizer is free on the subgroup fixed set. -/
public theorem normalizer_involution_free
    (h : IsProductDisconnected Z M) (ha : ResidualAction Z M)
    (Y : Subgroup G) (hodd : Odd (Nat.card Y))
    (hthree : 3 ≤ Nat.card (theorem4bFixedPoints M Y))
    {s : G} (hs : s ∈ Z) (hsN : s ∈ normalizer (Y : Set G))
    (hsC : s ∉ centralizer (Y : Set G)) :
    ∀ beta : theorem4bFixedPoints M Y, s • (beta : G ⧸ M) ≠ beta := by
  intro beta hfix
  exact hsC (centralizes_of_common_fixed h ha Y hodd hthree hs hsN hfix beta.property)

/-- The source normalizer structure and trivial centralizer circle for the
same noncentral distinguished involution. -/
public theorem contrary_normalizer_structure
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) (Y : Subgroup G) (hodd : Odd (Nat.card Y))
    (hthree : 3 ≤ Nat.card (theorem4bFixedPoints M Y))
    {s : G} (hs : s ∈ Z) (hsN : s ∈ normalizer (Y : Set G))
    (hsC : s ∉ centralizer (Y : Set G)) :
    SectionFiveNormalizerStructure Z Y ∧ localCircleIn Z (centralizer (Y : Set G)) = ⊥ := by
  obtain ⟨z, hz, hzM⟩ := h.disconnected.nonempty
  obtain ⟨g, hg⟩ := isConj_iff.mp (r.one_class z hz s hs)
  have hzfix : z • (QuotientGroup.mk 1 : G ⧸ M) = QuotientGroup.mk 1 := by
    change z ∈ MulAction.stabilizer G (QuotientGroup.mk 1 : G ⧸ M)
    rwa [baseCoset_stabilizer]
  have hsfix : s • (g • (QuotientGroup.mk 1 : G ⧸ M)) =
      g • (QuotientGroup.mk 1 : G ⧸ M) := by
    rw [← hg, mul_smul, mul_smul, inv_smul_smul, hzfix]
  have hstr := sectionFive_normalizerStructure_of_not_fixed h r Y hodd hs hsN hsfix
    (fun hh => hsC (centralizes_of_common_fixed h.disconnected ha Y hodd hthree hs hsN
      hsfix (fun y hy => MulAction.mem_stabilizer_iff.mp (hh hy))))
  refine ⟨hstr, ?_⟩
  rw [localCircleIn_eq_closure]
  apply le_antisymm ?_ bot_le
  apply (closure_le _).mpr
  rintro v ⟨hvZ, hvC⟩
  have hvN := centralizer_le_normalizer (Y : Set G) hvC
  obtain ⟨g, hg⟩ := hstr.one_class v hvZ hvN s hs hsN
  have hc := (inferInstance : ((centralizer (Y : Set G)).subgroupOf
    (normalizer (Y : Set G))).Normal).conj_mem ⟨v, hvN⟩ hvC g
  change (g : G) * v * (g : G)⁻¹ ∈ centralizer (Y : Set G) at hc
  exact (hsC (hg ▸ hc)).elim

end BenderSuzuki.ZD.Section16.NativeSource
