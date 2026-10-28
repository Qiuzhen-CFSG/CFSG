module
public import CFSG.Quasithin.Chapter3.Section01.CommonNormalKnownSimple

public import CFSG.Quasithin.Chapter3.Defs
public import CFSG.Quasithin.Chapter3.Section01.LocalGeometry
public import CFSG.Quasithin.Chapter3.Section01.Configuration

/-!
# Common normal subgroups and the QTKE qrc configuration

Source: Aschbacher–Smith, combined manuscript (1 March 2004), §3.1,
pp. 571–578. `LocalGeometry` proves the interval, minimal-overgroup and
TI calculations of 3.1.2–3.1.4. `Configuration` states the actual local
hypotheses 3.1.5 and derives D.1.1 when the common-normal branch fails.

The older declarations below are retained for compatibility. They are
conditional subgroup-transfer and propositional lemmas, **not** proofs of
the numbered source theorems: `CommonNormalData` assumes ambient normality,
and `QrcCertificate` assumes its alternatives. Moreover the source's qrc
parameters are not natural numbers, and dual FF is an intermediate case
which must be eliminated, not a final alternative of 3.1.6. Final assembly
must use `QrcHypotheses` and discharge the C.5, D.1, B.5 and E.2 inputs.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter3

variable {G : Type*} [Group G]

/-- A common-normal conclusion for the older ambient-normality data. -/
def CommonNormalConclusion (d : CommonNormalData (G := G)) : Prop :=
  ∃ R₀ : Subgroup G, R₀ ≤ d.R ∧ R₀ ≠ ⊥ ∧
    NormalIn R₀ (generated d.M₀ d.H)

/-- Transfer of an already ambient-normal subgroup to the generated subgroup.

The witness is `R` itself.  The explicit ambient normality hypothesis in
`CommonNormalData` is stronger than the hypotheses of source Theorem 3.1.1;
this lemma does not establish that source theorem.
-/
public theorem common_normal_subgroup (d : CommonNormalData (G := G)) :
    CommonNormalConclusion d := by
  refine ⟨d.R, le_rfl, d.R_ne_bot, ?_⟩
  apply normalIn_of_normal
  · exact d.R_le_T.trans (d.T_le_M₀.trans le_generated_left)
  · exact d.Rnormal

@[inherit_doc common_normal_subgroup]
public theorem theorem_3_1_1 (d : CommonNormalData (G := G)) :
    CommonNormalConclusion d := common_normal_subgroup d

/-- Legacy natural-number parameters. These do not represent the source's
rank ratios and must not be used to state the final qrc theorem. -/
structure QrcParameters where
  q : ℕ
  qhat : ℕ
  V_le_O2 : Prop
  dualFF : Prop

/-- A legacy certificate assuming a disjunction; constructing it is a separate
obligation. Its dual-FF alternative is not a conclusion of source 3.1.6. -/
structure QrcCertificate (d : CommonNormalData (G := G)) (P : QrcParameters) : Prop where
  common : CommonNormalConclusion d ∨
    (¬ P.V_le_O2 ∧ P.qhat ≤ 2) ∨ P.q ≤ 2 ∨ P.dualFF

/-- The disjunction carried by the legacy certificate. -/
def QrcConclusion (d : CommonNormalData (G := G)) (P : QrcParameters) : Prop :=
  CommonNormalConclusion d ∨
    (¬ P.V_le_O2 ∧ P.qhat ≤ 2) ∨ P.q ≤ 2 ∨ P.dualFF

public theorem qrc_lemma (d : CommonNormalData (G := G)) (P : QrcParameters)
    (h : QrcCertificate d P) : QrcConclusion d P := h.common

@[inherit_doc qrc_lemma]
public theorem theorem_3_1_6 (d : CommonNormalData (G := G)) (P : QrcParameters)
    (h : QrcCertificate d P) : QrcConclusion d P := qrc_lemma d P h

/-- The strict q̂ bound used when `V` is a TI-set under `M`. -/
public theorem qrc_lemma_of_ti (d : CommonNormalData (G := G)) (P : QrcParameters)
    (hcommon : ¬ CommonNormalConclusion d)
    (hstrict : ¬ P.V_le_O2 → P.qhat < 2)
    (h : QrcCertificate d P) :
    (¬ P.V_le_O2 ∧ P.qhat < 2) ∨ P.q ≤ 2 ∨ P.dualFF := by
  rcases h.common with h | h
  · exact False.elim (hcommon h)
  rcases h with h | h
  · left
    exact ⟨h.1, hstrict h.1⟩
  rcases h with h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

end CFSG.Quasithin.Chapter3
