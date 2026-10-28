module

public import CFSG.Quasithin.ChapterB.Section02.Baumann.Basic

/-!
# The enlarged module in Baumann's argument

Write Q = C_R(V), J = J(R), H = LR, I = ⟨Xi⟩, and W = α(R)V.
Every maximum elementary subgroup A of R has a centralizing maximum
replacement VC_A(V), including when A acts trivially on V. The intersection
characterization of α(Q) puts it in each replacement, so [α(Q), J] ≤ V.
Relative normality of Q in H transports this bound to the H-conjugates of J.
When these generate I, it follows that [W, I] ≤ V. Since R normalizes W,
the additional inclusion L ≤ I gives H-invariance of W.

The initial supplement W = C_W(J)V transports along any supplied conjugator
in I taking Xi into J. Subgroup-order counting then identifies the fixed-space
codimensions for V and W. Normality of Q is used only inside H; no ambient
normality of Q or W is assumed.

The theorem `enlarged_module` is a conditional prerequisite. Its three
conjugacy-reduction premises must be discharged by the B.2.18 assembly owner;
it does not claim the final Baumann theorem.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, proof of B.2.18, printed p.81, from “Set W” through
the identities m(V/C_V(Xi)) = m(W/C_W(Xi)).
-/

namespace CFSG.Quasithin.ChapterB.BaumannArgument
open Stellmacher Subgroup
open scoped commutatorElement
variable {G : Type*} [Group G]

private theorem commutator_le_normal_iff (N A B : Subgroup G) [N.Normal] :
    ⁅A, B⁆ ≤ N ↔
      A.map (QuotientGroup.mk' N) ≤
        centralizer (B.map (QuotientGroup.mk' N) : Set (G ⧸ N)) := by
  rw [← commutator_eq_bot_iff_le_centralizer, ← map_commutator, Subgroup.map_eq_bot_iff,
    QuotientGroup.ker_mk']

private theorem commutator_sSup_right_le (N A : Subgroup G) [N.Normal]
    (S : Set (Subgroup G)) (h : ∀ B ∈ S, ⁅A, B⁆ ≤ N) : ⁅A, sSup S⁆ ≤ N := by
  rw [commutator_comm, commutator_le_normal_iff, map_le_iff_le_comap]
  apply sSup_le
  intro B hB
  rw [← map_le_iff_le_comap, ← commutator_le_normal_iff, commutator_comm]
  exact h B hB

private theorem normalizer_le_normalizer_alpha (K : Subgroup G) :
    normalizer (K : Set G) ≤ normalizer (thompsonAlpha K : Set G) := by
  intro g hg
  apply mem_normalizer_iff_map_conj_eq.mpr
  change (omegaOneCenterAmbient (elementaryAbelianMaxJ K)).map
    (MulAut.conj g).toMonoidHom = _
  have hK : K.map (MulAut.conj g).toMonoidHom = K :=
    mem_normalizer_iff_map_conj_eq.mp hg
  rw [← omegaOneCenterAmbient_map_injective _ (MulAut.conj g).injective,
    ← elementaryAbelianMaxJ_map_equiv, hK]
  rfl

variable [Finite G]

private theorem alpha_centralizer_le_replacement (V R A : Subgroup G) [V.Normal]
    [IsElementaryAbelian 2 V] (hVR : V ≤ R) (hno : NoStrongOffenders V R)
    (hA : A ∈ elementaryAbelianMaxSubgroups R) :
    thompsonAlpha (R ⊓ centralizer (V : Set G)) ≤
      V ⊔ (A ⊓ centralizer (V : Set G)) := by
  have hB := maximal_replacement V R A hVR hno hA
  have hBQ : V ⊔ (A ⊓ centralizer (V : Set G)) ≤ R ⊓ centralizer (V : Set G) :=
    le_inf hB.1 (sup_le V.le_centralizer inf_le_right)
  have hmax : V ⊔ (A ⊓ centralizer (V : Set G)) ∈
      elementaryAbelianMaxSubgroups (R ⊓ centralizer (V : Set G)) :=
    ⟨hBQ, hB.2.1, fun B hBQ hBe => hB.2.2 B (hBQ.trans inf_le_left) hBe⟩
  rw [(lemma_B_2_3_7 (R ⊓ centralizer (V : Set G))).2, thompsonFamily_zero]
  exact sInf_le hmax

/-- The maximum replacements imply [α(C_R(V)), J(R)] ≤ V. -/
public theorem alpha_centralizer_commutator_maxJ_le (V R : Subgroup G) [V.Normal]
    [IsElementaryAbelian 2 V] (hVR : V ≤ R) (hno : NoStrongOffenders V R) :
    ⁅thompsonAlpha (R ⊓ centralizer (V : Set G)), elementaryAbelianMaxJ R⁆ ≤ V := by
  apply commutator_sSup_right_le
  intro A hA
  let _ : IsElementaryAbelian 2 A := hA.2.1
  let q := QuotientGroup.mk' V
  let _ : IsElementaryAbelian 2 (A.map q) := IsElementaryAbelian.map q
  rw [commutator_le_normal_iff]
  apply le_trans (map_mono (alpha_centralizer_le_replacement V R A hVR hno hA))
  change (V ⊔ (A ⊓ centralizer (V : Set G))).map q ≤ centralizer (A.map q : Set _)
  rw [Subgroup.map_sup, show V.map q = ⊥ from
    (Subgroup.map_eq_bot_iff V).mpr (by simp [q]), bot_sup_eq]
  exact (map_mono inf_le_left).trans (A.map q).le_centralizer

/-- Relative normality of Q transports the commutator bound over the
supplied H-conjugates of J(R). -/
public theorem alpha_centralizer_commutator_generated_le (V R L I : Subgroup G) [V.Normal]
    [IsElementaryAbelian 2 V] (hVR : V ≤ R) (hno : NoStrongOffenders V R)
    (hLQ : L ≤ normalizer ((R ⊓ centralizer (V : Set G) : Subgroup G) : Set G))
    (hI : I = sSup (conjugatesBy (L ⊔ R) (elementaryAbelianMaxJ R))) :
    ⁅thompsonAlpha (R ⊓ centralizer (V : Set G)), I⁆ ≤ V := by
  have hHQ : L ⊔ R ≤ normalizer ((R ⊓ centralizer (V : Set G) : Subgroup G) : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (inf_le_left.trans le_sup_right)).mp
      (centralizer_normal_in_join V R L hLQ)
  have hHa := hHQ.trans (normalizer_le_normalizer_alpha _)
  rw [hI]
  apply commutator_sSup_right_le
  rintro D ⟨g, hg, rfl⟩
  have ha : (thompsonAlpha (R ⊓ centralizer (V : Set G))).map
      (MulAut.conj g).toMonoidHom = thompsonAlpha (R ⊓ centralizer (V : Set G)) :=
    mem_normalizer_iff_map_conj_eq.mp (hHa hg)
  have hv : V.map (MulAut.conj g).toMonoidHom = V :=
    mem_normalizer_iff_map_conj_eq.mp (show g ∈ normalizer (V : Set G) from
      Subgroup.le_normalizer_of_normal (mem_top g))
  have hc := map_mono (f := (MulAut.conj g).toMonoidHom)
    (alpha_centralizer_commutator_maxJ_le V R hVR hno)
  rwa [map_commutator, ha, hv] at hc

/-- The commutator of W = α(R)V with the generated subgroup lies in V. -/
public theorem alpha_sup_commutator_generated_le (V R L I : Subgroup G) [V.Normal]
    [IsElementaryAbelian 2 V] (hVR : V ≤ R) (hno : NoStrongOffenders V R)
    (hLQ : L ≤ normalizer ((R ⊓ centralizer (V : Set G) : Subgroup G) : Set G))
    (hI : I = sSup (conjugatesBy (L ⊔ R) (elementaryAbelianMaxJ R))) :
    ⁅thompsonAlpha R ⊔ V, I⁆ ≤ V := by
  have hc := alpha_centralizer_commutator_generated_le V R L I hVR hno hLQ hI
  rw [commutator_le_normal_iff] at hc ⊢
  rw [Subgroup.map_sup, show V.map (QuotientGroup.mk' V) = ⊥ from
    (Subgroup.map_eq_bot_iff V).mpr (by simp), sup_bot_eq]
  exact (map_mono (centralizer_rank_and_alpha V R hVR hno).2.2.2).trans hc

/-- H = LR normalizes the enlarged module, with the conjugacy-generation
and residual-containment conclusions supplied explicitly. -/
public theorem alpha_sup_normalized (V R L I : Subgroup G) [V.Normal]
    [IsElementaryAbelian 2 V] (hVR : V ≤ R) (hno : NoStrongOffenders V R)
    (hLQ : L ≤ normalizer ((R ⊓ centralizer (V : Set G) : Subgroup G) : Set G))
    (hI : I = sSup (conjugatesBy (L ⊔ R) (elementaryAbelianMaxJ R))) (hLI : L ≤ I) :
    L ⊔ R ≤ normalizer ((thompsonAlpha R ⊔ V : Subgroup G) : Set G) := by
  have hIn : I ≤ normalizer ((thompsonAlpha R ⊔ V : Subgroup G) : Set G) :=
    le_normalizer_iff_commutator_le_left.mpr
      ((alpha_sup_commutator_generated_le V R L I hVR hno hLQ hI).trans le_sup_right)
  apply sup_le (hLI.trans hIn)
  intro r hr
  apply mem_normalizer_iff_map_conj_eq.mpr
  have ha : (thompsonAlpha R).map (MulAut.conj r).toMonoidHom = thompsonAlpha R :=
    mem_normalizer_iff_map_conj_eq.mp (normalizer_le_normalizer_alpha R (R.le_normalizer hr))
  have hv : V.map (MulAut.conj r).toMonoidHom = V :=
    mem_normalizer_iff_map_conj_eq.mp (show r ∈ normalizer (V : Set G) from
      Subgroup.le_normalizer_of_normal (mem_top r))
  change (thompsonAlpha R ⊔ V).map (MulAut.conj r).toMonoidHom = _
  rw [Subgroup.map_sup, ha, hv]

omit [Finite G] in
private theorem map_fixed_eq (e : G ≃* G) (W A : Subgroup G) :
    (W ⊓ centralizer (A : Set G)).map e.toMonoidHom =
      W.map e.toMonoidHom ⊓ centralizer (A.map e.toMonoidHom : Set G) := by
  apply le_antisymm
  · apply le_inf (map_mono inf_le_left)
    rw [← commutator_eq_bot_iff_le_centralizer, ← map_commutator]
    rw [commutator_eq_bot_iff_le_centralizer.mpr (show
      W ⊓ centralizer (A : Set G) ≤ centralizer (A : Set G) from inf_le_right),
      Subgroup.map_bot]
  · rintro _ ⟨⟨w, hw, rfl⟩, hc⟩
    refine ⟨w, ⟨hw, mem_centralizer_iff.mpr ?_⟩, rfl⟩
    intro a ha
    apply e.injective
    simpa using mem_centralizer_iff.mp hc (e a) (mem_map_of_mem e.toMonoidHom ha)

omit [Finite G] in
private theorem fixed_sup_of_conjugate_le (V W J X : Subgroup G) [V.Normal]
    (g : G) (hg : g ∈ normalizer (W : Set G))
    (hXJ : X.map (MulAut.conj g).toMonoidHom ≤ J)
    (hsplit : W = (W ⊓ centralizer (J : Set G)) ⊔ V) (hVW : V ≤ W) :
    W = (W ⊓ centralizer (X : Set G)) ⊔ V := by
  apply le_antisymm _ (sup_le inf_le_left hVW)
  apply (map_le_map_iff_of_injective (f := (MulAut.conj g).toMonoidHom)
    (MulAut.conj g).injective).mp
  have hW : W.map (MulAut.conj g).toMonoidHom = W :=
    mem_normalizer_iff_map_conj_eq.mp hg
  have hV : V.map (MulAut.conj g).toMonoidHom = V :=
    mem_normalizer_iff_map_conj_eq.mp (show g ∈ normalizer (V : Set G) from
      Subgroup.le_normalizer_of_normal (mem_top g))
  rw [Subgroup.map_sup, map_fixed_eq, hW, hV]
  exact hsplit.le.trans (sup_le_sup (inf_le_inf_left _ (centralizer_le hXJ)) le_rfl)

/-- Transport the initial supplement to each Xi using the supplied
conjugators inside I. Neither invariance nor a supplement is assumed. -/
public theorem alpha_sup_eq_fixed_sup_generators {ι : Type*} [Fintype ι]
    (V R : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    (X : ι → Subgroup G) (h : HypothesesAD V R X)
    (hI : (⨆ i, X i) = sSup (conjugatesBy (pResidual 2 G ⊔ R) (elementaryAbelianMaxJ R)))
    (hconj : ∀ i, ∃ g ∈ (⨆ i, X i),
      (X i).map (MulAut.conj g).toMonoidHom ≤ elementaryAbelianMaxJ R) (i : ι) :
    thompsonAlpha R ⊔ V =
      ((thompsonAlpha R ⊔ V) ⊓ centralizer (X i : Set G)) ⊔ V := by
  have hIn : (⨆ i, X i) ≤ normalizer ((thompsonAlpha R ⊔ V : Subgroup G) : Set G) :=
    le_normalizer_iff_commutator_le_left.mpr
      ((alpha_sup_commutator_generated_le V R (pResidual 2 G) (⨆ i, X i)
        h.V_le_R h.no_strong h.normalizes hI).trans le_sup_right)
  obtain ⟨g, hg, hXJ⟩ := hconj i
  exact fixed_sup_of_conjugate_le V (thompsonAlpha R ⊔ V) (elementaryAbelianMaxJ R)
    (X i) g (hIn hg) hXJ (alpha_sup_eq_fixed_sup V R) le_sup_right

private theorem elementary_card_pow_log (E : Subgroup G) [IsElementaryAbelian 2 E] :
    Nat.card E = 2 ^ Nat.log 2 (Nat.card E) := by
  obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 E).exists_card_eq
  rw [hn, Nat.log_pow Nat.one_lt_two]

omit [Finite G] in
private theorem card_inf_mul_relIndex (A B : Subgroup G) :
    Nat.card ↥(A ⊓ B) * A.relIndex B = Nat.card B := by
  simpa only [Subgroup.relIndex_bot_left, Subgroup.inf_relIndex_right] using
    Subgroup.relIndex_mul_relIndex (⊥ : Subgroup G) (A ⊓ B) B bot_le inf_le_right

/-- A fixed-space supplement identifies the two fixed-space quotient ranks.
Normality is required only for V, not for the ambient fixed space. -/
public theorem fixedCodim_eq_of_fixed_sup (V W A : Subgroup G) [V.Normal]
    [IsElementaryAbelian 2 W] (hVW : V ≤ W)
    (hsplit : W = (W ⊓ centralizer (A : Set G)) ⊔ V) :
    fixedCodim W A = fixedCodim V A := by
  let C := W ⊓ centralizer (A : Set G)
  let D := V ⊓ centralizer (A : Set G)
  let _ : IsElementaryAbelian 2 V := IsElementaryAbelian.of_le hVW
  let _ : IsElementaryAbelian 2 C := IsElementaryAbelian.of_le (show C ≤ W from inf_le_left)
  let _ : IsElementaryAbelian 2 D := IsElementaryAbelian.of_le (show D ≤ V from inf_le_left)
  have hsup : V ⊔ C = W := (sup_comm V C).trans hsplit.symm
  have hinf : V ⊓ C = D := by
    dsimp [C, D]
    rw [← inf_assoc, inf_eq_left.mpr hVW]
  have hW : Nat.card V * V.relIndex C = Nat.card W := by
    have ht := card_inf_mul_relIndex V (V ⊔ C)
    rw [inf_sup_self, Subgroup.relIndex_sup_left, hsup] at ht
    exact ht
  have hC : Nat.card D * V.relIndex C = Nat.card C := by
    simpa only [hinf] using card_inf_mul_relIndex V C
  have hprod : Nat.card W * Nat.card D = Nat.card V * Nat.card C := by
    rw [← hW, ← hC]
    ac_rfl
  rw [elementary_card_pow_log W, elementary_card_pow_log D,
    elementary_card_pow_log V, elementary_card_pow_log C, ← pow_add, ← pow_add] at hprod
  have hrank := congrArg (Nat.log 2) hprod
  simp only [Nat.log_pow Nat.one_lt_two] at hrank
  change Nat.log 2 (Nat.card W) - Nat.log 2 (Nat.card C) =
    Nat.log 2 (Nat.card V) - Nat.log 2 (Nat.card D)
  omega

/-- The source equality m(V/C_V(J(R))) = m(W/C_W(J(R))). -/
public theorem alpha_sup_fixedCodim_maxJ (V R : Subgroup G) [V.Normal]
    [IsElementaryAbelian 2 V] (hVR : V ≤ R) (hno : NoStrongOffenders V R) :
    fixedCodim (thompsonAlpha R ⊔ V) (elementaryAbelianMaxJ R) =
      fixedCodim V (elementaryAbelianMaxJ R) := by
  let _ := alpha_sup_elementary V R hVR hno
  exact fixedCodim_eq_of_fixed_sup V (thompsonAlpha R ⊔ V) (elementaryAbelianMaxJ R)
    le_sup_right (alpha_sup_eq_fixed_sup V R)

/-- The source identities mi = m(W/C_W(Xi)) for all generators. -/
public theorem alpha_sup_fixedCodim_generators {ι : Type*} [Fintype ι]
    (V R : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    (X : ι → Subgroup G) (h : HypothesesAD V R X)
    (hI : (⨆ i, X i) = sSup (conjugatesBy (pResidual 2 G ⊔ R) (elementaryAbelianMaxJ R)))
    (hconj : ∀ i, ∃ g ∈ (⨆ i, X i),
      (X i).map (MulAut.conj g).toMonoidHom ≤ elementaryAbelianMaxJ R) (i : ι) :
    fixedCodim (thompsonAlpha R ⊔ V) (X i) = fixedCodim V (X i) := by
  let _ := alpha_sup_elementary V R h.V_le_R h.no_strong
  exact fixedCodim_eq_of_fixed_sup V (thompsonAlpha R ⊔ V) (X i) le_sup_right
    (alpha_sup_eq_fixed_sup_generators V R X h hI hconj i)

/-- The enlarged-module part of B.2.18, conditional only on the three
outputs of the independent conjugacy reduction. This is not the final
Baumann theorem. -/
public theorem enlarged_module {ι : Type*} [Fintype ι]
    (V R : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    (X : ι → Subgroup G) (h : HypothesesAD V R X)
    (hI : (⨆ i, X i) = sSup (conjugatesBy (pResidual 2 G ⊔ R) (elementaryAbelianMaxJ R)))
    (hLI : pResidual 2 G ≤ ⨆ i, X i)
    (hconj : ∀ i, ∃ g ∈ (⨆ i, X i),
      (X i).map (MulAut.conj g).toMonoidHom ≤ elementaryAbelianMaxJ R) :
    pResidual 2 G ⊔ R ≤ normalizer ((thompsonAlpha R ⊔ V : Subgroup G) : Set G) ∧
      ∀ i, thompsonAlpha R ⊔ V =
        ((thompsonAlpha R ⊔ V) ⊓ centralizer (X i : Set G)) ⊔ V := by
  exact ⟨alpha_sup_normalized V R (pResidual 2 G) (⨆ i, X i)
    h.V_le_R h.no_strong h.normalizes hI hLI,
    alpha_sup_eq_fixed_sup_generators V R X h hI hconj⟩

end CFSG.Quasithin.ChapterB.BaumannArgument
