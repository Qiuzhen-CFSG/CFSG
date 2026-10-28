module

public import CFSG.Quasithin.ChapterE.Section03.Offenders.Basic
public import Theory.GroupTheory.PrimeRankWitness

/-!
# Quotient ranks and offender inequalities

Additivity of quotient rank identifies the rank of `Vᵍ/C_A(V)` with the
corank of `A` plus the rank of its actual induced automizer. This isolates
the numerical step of E.3.28 from its Sylow-theoretic nonnormalization step.
The conditional results below retain that step as an explicit premise; the
source theorem must discharge it from E.3.24.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.3.28–29
and E.3.33, printed pp. 237–238.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterE
open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative
variable {G : Type*} [Group G]

/-- Elementary abelianness inherited along a subgroup inclusion. -/
theorem offender_elementary_of_le {V A : Subgroup G} [IsElementaryAbelian 2 V]
    (hAV : A ≤ V) : IsElementaryAbelian 2 A := {
  toIsMulCommutative := isMulCommutative_iff.mpr (fun a b =>
    (Subgroup.inclusion_injective hAV) (by
      simpa only [map_mul] using mul_comm (Subgroup.inclusion hAV a)
        (Subgroup.inclusion hAV b)))
  exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun a =>
    Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (a : G) (hAV a.property))) }

variable [Finite G]

/-- Additivity of binary quotient rank in an elementary abelian group. -/
theorem offender_corank_add {W A B : Subgroup G} [IsElementaryAbelian 2 W]
    (hBA : B ≤ A) (hAW : A ≤ W) :
    subgroupCorank W B = subgroupCorank W A + subgroupCorank A B := by
  let _ : IsElementaryAbelian 2 A := offender_elementary_of_le hAW
  have h := Subgroup.relIndex_mul_relIndex B A W hBA hAW
  have hp (T U : Subgroup G) [IsElementaryAbelian 2 T] :
      U.relIndex T = 2 ^ subgroupCorank T U := by
    rw [subgroupCorank_eq_quotient_finrank]
    exact Subgroup.relIndex_eq_two_pow_quotient_finrank T U
  rw [hp A B, hp W A, hp W B, ← pow_add] at h
  have he := ((Nat.pow_right_injective (by decide : 2 ≤ 2)) h).symm
  omega

/-- The rank of an actual elementary abelian subgroup is bounded by prime rank. -/
theorem offender_rank_le_primeRank (A : Subgroup G) [IsElementaryAbelian 2 A] :
    rank A ≤ primeRank 2 G := by
  apply primeRank_ge_of_elementary_embedding (p := 2)
    (fun a : A => Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 A) a) _ A.subtype A.subtype_injective
  obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_card_eq
  rw [rank, hn, Nat.log_pow (by decide)]

/-- For the actual offender normalizer, quotient-rank additivity uses its action kernel. -/
theorem offender_centralizer_corank (V : Subgroup G) [IsElementaryAbelian 2 V] (g : G) :
    subgroupCorank (V.map (MulAut.conj g).toMonoidHom)
        (offenderNormalizer V g ⊓ centralizer (V : Set G)) =
      subgroupCorank (V.map (MulAut.conj g).toMonoidHom) (offenderNormalizer V g) +
        rank (inducedAutomizer V (offenderNormalizer V g)) := by
  let _ : IsElementaryAbelian 2 (V.map (MulAut.conj g).toMonoidHom) :=
    IsElementaryAbelian.map _
  rw [offender_corank_add inf_le_left (show offenderNormalizer V g ≤
    V.map (MulAut.conj g).toMonoidHom from inf_le_left),
    rank_inducedAutomizer V (offenderNormalizer V g)
      (show offenderNormalizer V g ≤ normalizer (V : Set G) from inf_le_right)]

omit [Finite G] in
/-- Every offender image is a genuine elementary abelian subgroup of `Aut_G(V)`. -/
theorem offender_inducedAutomizer_elementary (V : Subgroup G)
    [IsElementaryAbelian 2 V] (g : G) :
    IsElementaryAbelian 2 (inducedAutomizer V (offenderNormalizer V g)) := by
  let _ : IsElementaryAbelian 2 (V.map (MulAut.conj g).toMonoidHom) :=
    IsElementaryAbelian.map _
  let _ : IsElementaryAbelian 2 (offenderNormalizer V g) :=
    offender_elementary_of_le (show offenderNormalizer V g ≤
      V.map (MulAut.conj g).toMonoidHom from inf_le_left)
  exact inducedAutomizer_elementary V _ inf_le_right

/-- The upper rank bound in E.3.28 uses the actual automizer, not a model group. -/
theorem offender_automizer_rank_le (V : Subgroup G) [IsElementaryAbelian 2 V] (g : G) :
    rank (inducedAutomizer V (offenderNormalizer V g)) ≤ primeRank 2 (Automizer V) := by
  let _ := offender_inducedAutomizer_elementary V g
  exact offender_rank_le_primeRank _

/-- The numerical part of E.3.28, conditional on the nonnormalization conclusion.
The E.3.28 assembly owner must prove that premise from E.3.24. -/
theorem offender_inequalities_of_not_normalizes {V T : Subgroup G}
    [IsElementaryAbelian 2 V] {g : G} (h : IsWOffenderAt V T g)
    (hn : ¬ V ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G)) :
    globalR V ≤ (subgroupCorank (V.map (MulAut.conj g).toMonoidHom)
      (offenderNormalizer V g ⊓ centralizer (V : Set G)) : ℕ∞) ∧
    globalR V ≤ globalW V T + (rank (inducedAutomizer V (offenderNormalizer V g)) : ℕ∞) ∧
    globalW V T + (rank (inducedAutomizer V (offenderNormalizer V g)) : ℕ∞) ≤
      globalW V T + (primeRank 2 (Automizer V) : ℕ∞) ∧
    globalR V - globalW V T ≤ (rank (inducedAutomizer V (offenderNormalizer V g)) : ℕ∞) := by
  have hr : globalR V ≤ (subgroupCorank (V.map (MulAut.conj g).toMonoidHom)
      (offenderNormalizer V g ⊓ centralizer (V : Set G)) : ℕ∞) := by
    rw [offenderNormalizer_inf_centralizer]
    exact globalR_le_conjugate_centralizer_corank g hn
  have hs : globalR V ≤ globalW V T +
      (rank (inducedAutomizer V (offenderNormalizer V g)) : ℕ∞) := by
    rw [h.2, ← ENat.natCast_add, ← offender_centralizer_corank]
    exact hr
  refine ⟨hr, hs, ?_, ?_⟩
  · exact add_le_add le_rfl (ENat.natCast_le_natCast.mpr (offender_automizer_rank_le V g))
  · exact tsub_le_iff_left.mpr hs

/-- The equality of centralizers and the fixed-space-family conclusion in E.3.33
follow directly from the proved E.3.10 for the same automizer action. -/
theorem offender_fixedSpaceFamily_of_lt_globalS {V T : Subgroup G}
    [IsElementaryAbelian 2 V] {g : G} (h : IsWOffenderAt V T g)
    (hs : globalW V T < globalS V) :
    V ⊓ centralizer (offenderNormalizer V g : Set G) =
        V ⊓ centralizer (V.map (MulAut.conj g).toMonoidHom : Set G) ∧
      inducedAutomizer V (offenderNormalizer V g) ∈
        fixedSpaceFamily (automizerRepresentation V)
          ((globalS V).toNat - (globalW V T).toNat) := by
  have hb : (subgroupCorank (V.map (MulAut.conj g).toMonoidHom)
      (offenderNormalizer V g) : ℕ∞) < globalS V := h.2 ▸ hs
  obtain ⟨hc, hf⟩ := inducedAutomizer_mem_fixedSpaceFamily_of_corank_lt_globalS g
    (show offenderNormalizer V g ≤ _ from le_rfl) hb h.1
  rw [h.2, ENat.toNat_natCast]
  exact ⟨hc, hf⟩

/-- The explicit positive lower bound on automizer rank in E.3.33(4). -/
theorem offender_rank_lower_of_lt_globalS {V T : Subgroup G}
    [IsElementaryAbelian 2 V] {g : G} (h : IsWOffenderAt V T g)
    (hs : globalW V T < globalS V) :
    (globalS V).toNat - (globalW V T).toNat ≤
      rank (inducedAutomizer V (offenderNormalizer V g)) ∧
    1 ≤ (globalS V).toNat - (globalW V T).toNat := by
  have hf := (offender_fixedSpaceFamily_of_lt_globalS h hs).2
  exact ⟨parameter_le_rank_of_mem_fixedSpaceFamily (automizerRepresentation V)
    (automizerRepresentation_injective V) hf, hf.1⟩

/-- The finite weak-closure minimum forces positive two-rank of the actual automizer.
A noncentralizing generator in `T` has a nontrivial elementary abelian image. -/
theorem automizer_primeRank_pos_of_globalW_ne_top {V : Subgroup G}
    [IsElementaryAbelian 2 V] {T : Sylow 2 G} (hT : HypothesisE322 V T)
    (hw : globalW V T ≠ ⊤) : 0 < primeRank 2 (Automizer V) := by
  obtain ⟨A, hA, hAC⟩ := globalW_generator (ENat.natCast_toNat hw).symm
  obtain ⟨⟨g, hAg, _⟩, hAT⟩ := hA
  let _ : IsElementaryAbelian 2 (V.map (MulAut.conj g).toMonoidHom) :=
    IsElementaryAbelian.map _
  let _ : IsElementaryAbelian 2 A := offender_elementary_of_le hAg
  have hAN := hAT.trans hT.normalizes
  let _ : IsElementaryAbelian 2 (inducedAutomizer V A) :=
    inducedAutomizer_elementary V A hAN
  have hI : IsElementaryTwo (inducedAutomizer V A) :=
    ⟨fun hz => hAC ((inducedAutomizer_eq_bot_iff hAN).mp hz), inferInstance⟩
  exact hI.rank_pos.trans_le (offender_rank_le_primeRank _)

/-- The equality case in the numerical chain of E.3.28. This lemma keeps the
nonnormalization premise explicit pending the source assembly. -/
theorem offender_ranks_of_fundamental_equality {V T : Subgroup G}
    [IsElementaryAbelian 2 V] {g : G} (h : IsWOffenderAt V T g)
    (hn : ¬ V ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G))
    (heq : globalR V = globalW V T + (primeRank 2 (Automizer V) : ℕ∞)) :
    rank (inducedAutomizer V (offenderNormalizer V g)) = primeRank 2 (Automizer V) ∧
    globalR V = (subgroupCorank (V.map (MulAut.conj g).toMonoidHom)
      (offenderNormalizer V g ⊓ centralizer (V : Set G)) : ℕ∞) := by
  have hs := (offender_inequalities_of_not_normalizes h hn).2.1
  have hrank := offender_automizer_rank_le V g
  rw [heq, h.2, ← ENat.natCast_add, ← ENat.natCast_add] at hs
  have hnat := ENat.natCast_le_natCast.mp hs
  have hr : rank (inducedAutomizer V (offenderNormalizer V g)) =
      primeRank 2 (Automizer V) := by omega
  refine ⟨hr, ?_⟩
  rw [offender_centralizer_corank, ENat.natCast_add, hr, ← h.2, heq]

/-- The subgroup and centralizer conclusions of E.3.33, conditional on the
forward nonnormalization supplied by E.3.25 in the source proof. -/
theorem offender_configuration_of_not_normalizes {V T : Subgroup G}
    [IsElementaryAbelian 2 V] {g : G} (h : IsWOffenderAt V T g)
    (hs : globalW V T < globalS V)
    (hn : ¬ V.map (MulAut.conj g).toMonoidHom ≤ normalizer (V : Set G)) :
    let U := V ⊓ centralizer (offenderNormalizer V g : Set G)
    U = V ⊓ centralizer (V.map (MulAut.conj g).toMonoidHom : Set G) ∧
    U < V ∧
    V < V ⊔ V.map (MulAut.conj g).toMonoidHom ∧
    V ⊔ V.map (MulAut.conj g).toMonoidHom ≤ centralizer (U : Set G) ∧
    ¬ centralizer (U : Set G) ≤ normalizer (V : Set G) ∧
    globalR V ≤ (subgroupCorank V U : ℕ∞) := by
  dsimp only
  let U := V ⊓ centralizer (offenderNormalizer V g : Set G)
  have hU : U = V ⊓ centralizer (V.map (MulAut.conj g).toMonoidHom : Set G) :=
    (offender_fixedSpaceFamily_of_lt_globalS h hs).1
  have hUV : U ≤ V := inf_le_left
  have hUC : U ≤ centralizer (V.map (MulAut.conj g).toMonoidHom : Set G) := by
    rw [hU]
    exact inf_le_right
  have hlt : U < V := lt_of_le_of_ne hUV (by
    intro he
    have hc : V ≤ centralizer (V.map (MulAut.conj g).toMonoidHom : Set G) := he ▸ hUC
    exact h.1 (commutator_eq_bot_iff_le_centralizer.mpr hc))
  have hVsup : V < V ⊔ V.map (MulAut.conj g).toMonoidHom :=
    left_lt_sup.mpr (fun hg => hn (hg.trans V.le_normalizer))
  have hsup : V ⊔ V.map (MulAut.conj g).toMonoidHom ≤ centralizer (U : Set G) := by
    apply sup_le
    · exact (le_centralizer_iff_isMulCommutative.mpr inferInstance).trans
        (Subgroup.centralizer_le hUV)
    · exact le_centralizer_iff.mpr hUC
  have hCN : ¬ centralizer (U : Set G) ≤ normalizer (V : Set G) :=
    fun hc => hn (le_sup_right.trans (hsup.trans hc))
  exact ⟨hU, hlt, hVsup, hsup, hCN, globalR_le_corank hUV hCN⟩

omit [Finite G] in
/-- A noncentralizing conjugate makes the minimizing family for `r` nonempty.
This justifies natural subtraction in E.3.31–32 without truncating infinity. -/
theorem globalR_ne_top_of_noncentralizing_conjugate {V : Subgroup G}
    [IsElementaryAbelian 2 V] (g : G)
    (hcomm : ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥) : globalR V ≠ ⊤ := by
  intro hr
  have hn := (globalR_eq_top_iff V).mp hr ⊥ bot_le
  have hg : g ∈ normalizer (V : Set G) := hn (by
    intro x hx
    have hx1 : x = 1 := Subgroup.mem_bot.mp hx
    simp [hx1])
  have he : V.map (MulAut.conj g).toMonoidHom = V :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
  rw [he] at hcomm
  exact hcomm (commutator_eq_bot_iff_le_centralizer.mpr
    (le_centralizer_iff_isMulCommutative.mpr inferInstance))

end CFSG.Quasithin.ChapterE
