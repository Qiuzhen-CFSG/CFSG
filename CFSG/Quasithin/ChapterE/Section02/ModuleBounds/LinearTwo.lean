module

public import CFSG.Quasithin.ChapterE.Section02.ModuleBounds.QuotientCentralizer
public import Theory.Representation.SL2.CoreQuotientDegree
public import Theory.GroupTheory.NoncentralChiefRefinement.UniqueResidualLayer
public import Theory.GroupTheory.PResidual.Quotient
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.ElementaryAbelian.BinaryQuotientRank
/-!
# The genuine linear-two degree and actor bound in E.2.13

Every chief series on the original P/Z has a noncentral factor. Otherwise
the two-residual centralizes P/Z, and the proved source kernel bound would
make X a two-group, contradicting proper conjugate generation by V.

When the actual two-core quotient is SL₂(2^m), that noncentral factor has
binary dimension at least 2m by highest-weight descent. Its dimension is
at most that of P/Z. The literal complementary summands B/Z and A/Z have
equal order, giving dim(P/Z)=2 dim(A/Z) and hence dim(A/Z)≥m.

Source: Aschbacher–Smith E.2.13(4), printed pp.224–225. The quotient marking
is an actual group equivalence. The proof descends only the actual chief
factor through O₂, and never assumes that the whole P/Z is an X/O₂-module.
The earlier E.2.11 family producer supplies the marking from its original
maximal-core quotient.
-/

@[expose] public section
open Subgroup Theory.GroupTheory NoncentralChiefRefinement
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.ChapterE.TwoConjugate.Hypotheses
variable {X : Type*} [Group X] [Finite X]
  {T : Sylow 2 X} {V M : Subgroup X} {g : X}

private theorem isPGroup_of_core_quotient {H : Type*} [Group H]
    (hp : IsPGroup 2 (H ⧸ pCore 2 H)) : IsPGroup 2 H := by
  have ht : IsPGroup 2 (⊤ : Subgroup H) := by
    have hh := (hp.to_subgroup ⊤).comap_of_ker_isPGroup
      (QuotientGroup.mk' (pCore 2 H)) (by
        rw [QuotientGroup.ker_mk']; exact pCore_isPGroup)
    exact hh.of_equiv (MulEquiv.subgroupCongr (Subgroup.comap_top _))
  exact ht.of_equiv topEquiv

theorem quotient_core_noncentral_chief_exists (h : Hypotheses T V M g)
    (hproper : V ≠ ⊤) (hfit : generalizedFitting X = pCore 2 X) :
    letI := h.Z_normal
    let q := QuotientGroup.mk' (Z V g)
    letI := h.core_geometry.1
    ∀ (s : SeriesOn ((P V M g).map q)), ∃ i, ¬ s.Central i := by
  let := h.Z_normal
  let := h.core_geometry.1
  let q := QuotientGroup.mk' (Z V g)
  let U := (P V M g).map q
  let := h.quotient_direct_sum.1
  dsimp only
  intro s
  by_contra! hn
  have hp : IsPGroup 2 U := IsElementaryAbelian.isPGroup 2 U
  have hpLast : IsPGroup 2 s.series.last.val := hp.of_equiv
    (MulEquiv.subgroupCongr (congrArg Subtype.val s.last_eq)).symm
  have hc := s.series.residual_commutator_le_head_of_central_steps hpLast hn
  rw [s.head_eq, s.last_eq] at hc
  have hcR : pResidual 2 (X ⧸ Z V g) ≤ centralizer (U : Set (X ⧸ Z V g)) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp (le_bot_iff.mp hc))
  have hk := h.quotient_core_centralizer_le hfit
  have hcentral : centralizer (U : Set (X ⧸ Z V g)) ≤ pCore 2 (X ⧸ Z V g) := by
    have hm := map_mono (f := q) hk
    rw [map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)] at hm
    exact hm.trans (le_sSup ⟨Normal.map inferInstance q (QuotientGroup.mk'_surjective _), pCore_isPGroup.map q⟩)
  have hpbar : IsPGroup 2 (X ⧸ Z V g) := isPGroup_of_core_quotient
    ((pResidual_le_iff_isPGroup_quotient 2 _).mp (hcR.trans hcentral))
  have hZtwo : IsPGroup 2 q.ker := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup.to_le ((h.core_geometry.2.2.trans inf_le_left).trans h.P_le_twoCore)
  have hXtop : IsPGroup 2 (⊤ : Subgroup X) := by
    exact ((hpbar.to_subgroup ⊤).comap_of_ker_isPGroup q hZtwo).of_equiv
      (MulEquiv.subgroupCongr (Subgroup.comap_top _))
  have hcore : (⊤ : Subgroup X) ≤ pCore 2 X := le_sSup ⟨inferInstance, hXtop⟩
  exact h.V_not_le_twoCore hproper (le_top.trans hcore)

/-- The SL₂ binary minimum degree on the original P/Z, obtained through
an actual noncentral chief factor rather than a splitting assumption. -/
theorem quotient_core_finrank_ge_linear_two
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (h : Hypotheses T V M g) (hproper : V ≠ ⊤)
    (hfit : generalizedFitting X = pCore 2 X)
    (m : ℕ) (hm : m ≠ 0) (hcard : Nat.card F = 2 ^ m) :
    letI := h.Z_normal
    let q := QuotientGroup.mk' (Z V g)
    letI := h.quotient_direct_sum.1
    ∀ _e : ((X ⧸ Z V g) ⧸ pCore 2 (X ⧸ Z V g)) ≃* SL(2,F),
      2 * m ≤ Module.finrank (ZMod 2) (Additive ((P V M g).map q)) := by
  let := h.Z_normal
  let := h.core_geometry.1
  let q := QuotientGroup.mk' (Z V g)
  let U := (P V M g).map q
  let := h.quotient_direct_sum.1
  dsimp only
  intro e
  obtain ⟨s⟩ := SeriesOn.exists_series U
  obtain ⟨i, hi⟩ := h.quotient_core_noncentral_chief_exists hproper hfit s
  have hd := s.noncentral_factor_finrank_ge_sl2 e i hi m hm hcard
  have hle := LinearMap.finrank_le_finrank_of_surjective (s.factorProjection_surjective i)
  exact hd.trans (hle.trans (Submodule.finrank_le (s.linearTerm i.succ).toSubmodule))
/-- The actual core quotient has twice the dimension of the actual actor
quotient. Both summands and both quotient maps are the source ones. -/
theorem quotient_core_finrank_eq_twice_actor (h : Hypotheses T V M g) :
    letI := h.Z_normal
    let q := QuotientGroup.mk' (Z V g)
    letI := h.quotient_direct_sum.1
    Module.finrank (ZMod 2) (Additive ((P V M g).map q)) =
      2 * Nat.log 2 ((Z V g).relIndex (A V M g)) := by
  let := h.Z_normal
  let := h.A_elementary
  let q := QuotientGroup.mk' (Z V g)
  let Aq := (A V M g).map q
  let Bq := (B V M).map q
  let U := (P V M g).map q
  let := h.quotient_direct_sum.1
  have hZA : (Z V g).map (MulAut.conj g).toMonoidHom = Z V g :=
    mem_normalizer_iff_map_conj_eq.mp (le_normalizer_of_normal (mem_top g))
  have hBA : Nat.card Bq = Nat.card Aq := by
    have hh := relIndex_map_map_of_injective (f := (MulAut.conj g).toMonoidHom)
      (Z V g) (B V M) (MulAut.conj g).injective
    rw [hZA] at hh
    rw [← relIndex_ker, ← relIndex_ker, QuotientGroup.ker_mk']
    exact hh.symm
  have hcomm : Bq ≤ centralizer (Aq : Set (X ⧸ Z V g)) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    rw [← map_commutator, commutator_comm]
    exact (Subgroup.map_eq_bot_iff _).mpr (by
      rw [QuotientGroup.ker_mk']; exact h.commutator_A_B_le_Z)
  have hcount := card_mul_eq_card_inf_mul_card_sup_of_normalizes Bq Aq
    ((le_centralizer_iff.mp hcomm).trans (Subgroup.centralizer_le_normalizer _))
  rw [h.quotient_direct_sum.2.2, Subgroup.card_bot,
    one_mul, h.quotient_direct_sum.2.1, hBA] at hcount
  have hA : Nat.card Aq = 2 ^ Nat.log 2 ((Z V g).relIndex (A V M g)) := by
    rw [← relIndex_ker, QuotientGroup.ker_mk',
      log_relIndex_eq_quotient_finrank, relIndex_eq_two_pow_quotient_finrank]
  have hU : Nat.card U = 2 ^ Module.finrank (ZMod 2) (Additive U) := by
    change Nat.card (Additive U) = _
    simpa only [Nat.card_zmod] using (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive U))
  rw [hA, ← pow_add, hU] at hcount
  have he := (Nat.pow_right_injective (by decide : 2 ≤ 2)) hcount
  dsimp only [U, q] at he ⊢
  omega

/-- The SL₂ clause of E.2.13(4), on the original actor A/C_A(V)=A/Z. -/
theorem actor_rank_ge_linear_two
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (h : Hypotheses T V M g) (hproper : V ≠ ⊤)
    (hfit : generalizedFitting X = pCore 2 X)
    (m : ℕ) (hm : m ≠ 0) (hcard : Nat.card F = 2 ^ m) :
    letI := h.Z_normal
    ∀ _e : ((X ⧸ Z V g) ⧸ pCore 2 (X ⧸ Z V g)) ≃* SL(2,F),
      m ≤ Nat.log 2 ((Z V g).relIndex (A V M g)) := by
  let := h.Z_normal
  intro e
  have hd := h.quotient_core_finrank_ge_linear_two hproper hfit m hm hcard e
  rw [h.quotient_core_finrank_eq_twice_actor] at hd
  omega

end CFSG.Quasithin.ChapterE.TwoConjugate.Hypotheses
