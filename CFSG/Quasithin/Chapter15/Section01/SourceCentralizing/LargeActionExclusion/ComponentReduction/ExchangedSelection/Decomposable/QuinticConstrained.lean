module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.ResidualControl
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Alternatives
public import Theory.GroupTheory.PResidual.PrimeToMonotone
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.RankOne.Source

/-!
# Cubic residual obstruction at the original prime-five component

The literal quotient C_M(Z₁)/C_M(V) has order five times a power of two.
Its prime-to-three residual is trivial. Functoriality therefore makes the
embedded O^{3′}(M ∩ L) centralize V. The original moving subgroup lies in
S and acts nontrivially on L, so the constrained cubic-centralizer identity
cannot hold. This excludes the A₆ and G₂ rows without exchanged-plane or
later index conclusions.

The actual eight-dimensional consumer retains the same component, marking
and pre-exclusion witness. Source: Aschbacher--Smith 15.1.20--23, printed
pp.1094--1100; the residual convention is literally primeToResidual 3.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}
variable {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}

/-- The original prime-five quotient kills the literal cubic residual. -/
theorem PreExclusionSource.cubic_residual_centralizes_of_prime_five (s : d.PreExclusionSource h.normalized 5) :
    (primeToResidual 3 (M ⊓ d.L : Subgroup G)).map (M ⊓ d.L).subtype ≤
      centralizer (V : Set G) := by
  let C := M ⊓ d.G1
  let K := (M ⊓ centralizer (V : Set G)).subgroupOf C
  let : K.Normal := caseI_module_centralizer_normal (Z1 := d.Z1) h.normalized
  have hc : Nat.Coprime 3 (Nat.card (C ⧸ K)) := by
    obtain ⟨n,hn⟩ := (isPGroup_quotient_pResidual (G := C ⧸ K) 2).exists_card_eq
    rw [← (pResidual 2 (C ⧸ K)).card_mul_index, s.residual_card, index_eq_card, hn]
    exact (by decide : Nat.Coprime 3 5).mul_right ((by decide : Nat.Coprime 3 2).pow_right n)
  have hk : primeToResidual 3 C ≤ K := by
    simpa only [QuotientGroup.ker_mk'] using primeToResidual_le_ker (QuotientGroup.mk' K) hc
  have hr : (primeToResidual 3 C).map C.subtype ≤ centralizer (V : Set G) := by
    rintro x ⟨y,hy,rfl⟩
    exact (hk hy).2
  exact (embedded_primeToResidual_mono 3 (inf_le_inf_left M d.L_component.1)).trans hr

/-- The moving subgroup contradicts the constrained cubic-centralizer identity. -/
theorem PreExclusionSource.not_constrainedCentralizerIdentity_of_prime_five (s : d.PreExclusionSource h.normalized 5)
    (hTM : (T : Subgroup G) ≤ M) : ¬ d.ConstrainedCentralizerIdentity := by
  intro hc
  have hmoveV : ⁅V,(pResidual 2 (M ⊓ d.G1 : Subgroup G)).map
      (M ⊓ d.G1).subtype⁆ ≤ V :=
    le_normalizer_iff_commutator_le_left.mp
      (((map_subtype_le _).trans inf_le_left).trans h.normalized)
  have hmoveC := hmoveV.trans (le_centralizer_iff.mp (s.cubic_residual_centralizes_of_prime_five (h := h)))
  have hmoveL := ((le_inf (s.moving_le_sylow (h := h) hTM) hmoveC).trans hc.le).trans
    inf_le_right
  apply s.moving_noncentral
  rw [commutator_comm]
  exact commutator_eq_bot_iff_le_centralizer.mpr hmoveL


/-- Only the actual A₇ and binary linear rows remain in the constrained
catalogue at source prime five. The same quotient and parabolics are retained. -/
theorem PreExclusionSource.constrained_reduction_of_prime_five
    (s : d.PreExclusionSource h.normalized 5)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (a : d.ConstrainedAlternatives) :
    d.ConstrainedA7Alternative ∨
      ∃ (n : ℕ) (e : (d.L ⧸ pCore 2 d.L) ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)),
        (n = 4 ∨ n = 5) ∧ d.ConstrainedLinearParabolic e d.ML ∧
        d.ConstrainedLinearParabolic e (M ⊓ d.L) ∧ (M ⊓ d.L) ⊔ d.ML = d.L := by
  cases a with
  | rankOne ha => exact (s.no_constrained_rankOne (h := h) (.inr rfl) hG hM hJ ha).elim
  | linearThree ha =>
      exact (s.not_constrainedCentralizerIdentity_of_prime_five (h := h) hM.1.2 ha.centralizers).elim
  | alternatingSeven ha => exact .inl ha
  | alternatingSix _ hc =>
      exact (s.not_constrainedCentralizerIdentity_of_prime_five (h := h) hM.1.2 hc).elim
  | g2 _ hc =>
      exact (s.not_constrainedCentralizerIdentity_of_prime_five (h := h) hM.1.2 hc).elim
  | linear n hn e hm hs hg => exact .inr ⟨n,e,hn,hm,hs,hg⟩

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
