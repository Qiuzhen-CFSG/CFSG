module

public import Theory.SpecificGroups.Thompson.Model.Simplicity.ClassCoverage.Twos.SylowWords

/-!
# Candidate involution representatives and fusion witnesses

Fifteen words in the fixed Sylow candidate and fifteen ambient conjugators
come from the exploratory computations recorded in `Twos/source/`. All are
evaluated in the concrete matrix group. Their membership is proved here;
class coverage and conjugacy identities remain separate matrix certificates.
No class census or matrix equality is accepted from the external calculation.
-/

@[expose] public section
namespace Thompson.Simplicity.TwoLocal.SylowCandidate

/-- Evaluate a signed word in the ten fixed generators; `true` means positive. -/
def evalGenerators (w : List (Fin 10 × Bool)) : Model :=
  (w.map fun x => if x.2 then generators x.1 else (generators x.1)⁻¹).prod

theorem evalGenerators_mem (w : List (Fin 10 × Bool)) :
    evalGenerators w ∈ subgroup := by
  induction w with
  | nil => exact subgroup.one_mem
  | cons x w ih =>
    apply subgroup.mul_mem _ ih
    dsimp only
    split
    · exact generators_mem x.1
    · exact subgroup.inv_mem (generators_mem x.1)

/-- The signed source words of the fifteen proposed local involution classes. -/
def representativeWords : Fin 15 → List (Fin 10 × Bool) :=
  ![[(0, false), (0, false)],
    [(7, false), (7, false)],
    [(6, false), (6, false)],
    [(7, false), (7, false), (5, false), (2, false), (5, false), (0, false)],
    [(1, false), (5, false), (1, false), (5, false)],
    [(7, false), (1, false), (4, false), (0, true), (7, false), (4, false), (0, false)],
    [(7, false), (7, false), (2, false), (0, false)],
    [(7, false), (7, false), (7, false), (1, false), (5, false), (1, false), (5, false)],
    [(1, false)],
    [(5, false), (2, false), (5, false), (0, false), (1, false), (5, true), (1, false)],
    [(5, false), (2, false), (5, false), (0, false), (1, false), (0, false), (8, false), (1, false), (0, false)],
    [(4, false)],
    [(7, false), (7, false), (0, false)],
    [(7, false), (7, false), (5, false), (2, false), (5, false), (0, false), (6, false)],
    [(9, false)] ]

def representative (i : Fin 15) : Model := evalGenerators (representativeWords i)

theorem representative_mem (i : Fin 15) : representative i ∈ subgroup :=
  evalGenerators_mem (representativeWords i)

/-- Short positive words in the original ambient generators. -/
def bridgeStrings : Fin 15 → String :=
  !["baababaabbbaababaaaa",
    "aaabbbaaabaababaaaaa",
    "aabaabaaabaabaabbabb",
    "abaaabaabaaaaabbaaab",
    "bbbabbabbaaaaaabbaaa",
    "baabaaabaaabbbbabbaa",
    "aaabbbbaaababbabbaab",
    "abaabaaabbbbabbaaabb",
    "abaaabababbbbabbbabb",
    "babbbbbbaaaabaaaaaba",
    "baaaaabaabbaabbbaabb",
    "aaabbabbbabbbbbaaabb",
    "ababbabbaaaaabbabbba",
    "aabbaabaaaaaabbbbbab",
    "bbbbbaaababaaaaaabab" ]

def bridgeWord (i : Fin 15) : Model := word (bridgeStrings i)

/-- Candidate odd orders; only their use as exponents is defined here. -/
def bridgeExponent : Fin 15 → ℕ :=
  ![13, 21, 19, 13, 21, 19, 9, 27, 21, 13, 19, 19, 27, 27, 13]

/-- Product of a local word with an ambient conjugate of `a`. -/
def bridgeProduct (i : Fin 15) : Model :=
  representative i * (bridgeWord i)⁻¹ * generatorA * bridgeWord i

/-- Explicit proposed conjugator, using the odd-product construction. -/
def bridgeConjugator (i : Fin 15) : Model :=
  bridgeWord i * bridgeProduct i ^ ((bridgeExponent i - 1) / 2)

/-- The internal census obligation for the actual fixed subgroup. -/
def LocalCoverage : Prop :=
  ∀ y : Model, y ∈ subgroup → orderOf y = 2 →
    ∃ (i : Fin 15) (g : Model), representative i = g * y * g⁻¹

/-- Local coverage and the fifteen explicit identities imply local fusion. -/
theorem involutionFusion_of_certificates
    (hlocal : LocalCoverage)
    (hbridge : ∀ i : Fin 15,
      generatorA = bridgeConjugator i * representative i * (bridgeConjugator i)⁻¹) :
    InvolutionFusion := by
  intro y hy ho
  obtain ⟨i, g, hg⟩ := hlocal y hy ho
  refine ⟨bridgeConjugator i * g, ?_⟩
  rw [hbridge i, hg]
  simp only [mul_inv_rev, mul_assoc]

end Thompson.Simplicity.TwoLocal.SylowCandidate
