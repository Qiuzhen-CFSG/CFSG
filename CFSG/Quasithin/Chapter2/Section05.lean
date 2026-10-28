module

public import CFSG.Quasithin.Chapter2.Defs
public import CFSG.Quasithin.Chapter2.Section05.SourceCompletionInputs
public import CFSG.Quasithin.Chapter2.Section05.ShadowPair
public import CFSG.Quasithin.Chapter2.Section05.PSL2PairSource
public import CFSG.Quasithin.Chapter2.Section05.A6Shadow.SourceCentralizer
public import CFSG.Quasithin.Chapter2.Section05.A6Shadow.SourceQuotient
public import CFSG.Quasithin.Chapter2.Section05.A6Shadow.SourceComponent
public import CFSG.Quasithin.Chapter2.Section05.A6Shadow.OriginalFrattini.Source
public import CFSG.Quasithin.Chapter2.Section05.A6Shadow.Source
public import CFSG.Quasithin.Chapter2.Section05.Source
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.M10CoreSource
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.PGLNineCoreSource
public import CFSG.Quasithin.Chapter2.Section05.OvercomponentsSource

/-!
# Eliminating the shadows when `Γe0` is empty

This file records the set-theoretic and maximality consequences used at the
start and end of Aschbacher--Smith, §2.5 (combined manuscript, 1 March 2004,
pp. 550--570).  The structural analysis of components is carried by the
chapter's recognition results; the interfaces here keep the characteristic-2
collection explicit, so the elementary consequences can be reused without
assuming a classification theorem.

`PSL2PairSource` now proves the complete prime-pair implication in 2.5.21
from the earlier source bundle, constructing centralizer containment, faithful
actions, the marked-class equality and fusion, then applying `ShadowPair`. The native `ZD` theorem discharges its final
Aschbacher Lemma 3.4 input. `PrimeSource.Source` now constructs the original
prime-component crossing, proves the source component normality and persistence,
and supplies the terminal contradiction with no additional premises.

For an actual A₆ component, `NonabelianCoreSource` now eliminates the M₁₀
and PGL₂(9) alternatives and constructs the full Aut(A₆) quotient. Its
`A6Shadow.SourceComponent` consumer proves the original centralizer identity
H = C_G(t), deriving the quotient and compatible action internally.

`A6Shadow.OriginalFrattini.Source` constructs the earlier A₆ data from that
same original tuple and proves 2.5.23–25: the complete four-group normalizer
pair correspondence, its literal Sylow subgroups, Φ(O₂(H)) ≠ 1, and the
crossing identities tˣ = zK and z = t zK. `A6Shadow.Source` then proves
the original terminal contradiction with no additional premises: the full
overcomponent analysis and exceptional A₈ argument retain K in every
core-involution centralizer; marked generation yields rank one; and the
three core alternatives lead to the terminal geometry.

`Source` combines these branches with the original PSL₃(3) and M₁₁ exclusions.
It proves that the original nonempty-delta hypotheses force Γₑ₀ to be nonempty.
The characteristic-two shadow classification in §2.4 remains the separate
source obligation for the complete Theorem 2.1.1.
-/

namespace CFSG.Quasithin.Chapter2

variable {G : Type*} [Group G]
variable {E : Set (Subgroup G)} {M : Subgroup G}

/-- Membership in `Γe0` is exactly simultaneous membership in `Γ₀` and in the
characteristic-2 collection. -/
public theorem mem_gammaEvenZero_iff {H : Subgroup G} :
    H ∈ gammaEvenZero E M ↔ H ∈ gammaZero E M ∧ H ∈ E := Iff.rfl

/-- A member of `Γ` contains a local subgroup outside `M`, hence cannot itself
be contained in `M`.  This is the elementary part of Notation 2.3.5 used
throughout §2.5. -/
public theorem gamma_not_le_of_mem {H : Subgroup G} (hH : H ∈ gamma E M) :
    ¬ H ≤ M := by
  obtain ⟨P, hP, hPH⟩ := hH.2
  intro hHM
  exact hP.2.2.2.2 (hPH.trans hHM)

/-- Every local pair appearing under a subgroup in `Γ` has its second
coordinate outside `M`. -/
public theorem localPair_snd_not_le_of_mem
    {P : Subgroup G × Subgroup G} (hP : P ∈ localPairs E M) :
    ¬ P.2 ≤ M := hP.2.2.2.2

/-- Two normal subgroups with trivial intersection commute.  This is the
elementary group-theoretic step behind Lemma 2.5.5(2), where the two copies of
`S_C` are normal in `S` and have trivial intersection. -/
public theorem commutator_eq_bot_of_normal_of_inf_eq_bot
    (A B : Subgroup G) [A.Normal] [B.Normal] (hAB : A ⊓ B = ⊥) :
    ⁅A, B⁆ = ⊥ := by
  apply le_antisymm _ bot_le
  rw [← hAB]
  exact Subgroup.commutator_le_inf A B

/-- The hypothesis `Γe0 = ∅` excludes every characteristic-2 member of `Γ₀`.
This is the formal content of the standing assumption at the beginning of
§2.5. -/
public theorem not_mem_gammaEvenZero_of_empty
    (hΓ : gammaEvenZero E M = ∅) {H : Subgroup G}
    (hH : H ∈ gammaZero E M) : H ∉ E := by
  intro hHE
  have hmem : H ∈ gammaEvenZero E M := ⟨hH, hHE⟩
  rw [hΓ] at hmem
  exact hmem

/-- The same exclusion in implication form, convenient for local arguments. -/
public theorem gammaZero_disjoint_characteristicTwo
    (hΓ : gammaEvenZero E M = ∅) :
    Disjoint (gammaZero E M) E := by
  rw [Set.disjoint_left]
  intro H hH hHE
  exact not_mem_gammaEvenZero_of_empty hΓ hH hHE

/-- Any construction of a characteristic-2 subgroup inside `Γ₀` contradicts
`Γe0 = ∅`.  This is the final bookkeeping step used whenever the §2.5
component analysis produces `N_G(A) ∈ E`. -/
public theorem false_of_gammaZero_mem_of_mem_characteristicTwo
    (hΓ : gammaEvenZero E M = ∅) {H : Subgroup G}
    (hH : H ∈ gammaZero E M) (hHE : H ∈ E) : False := by
  exact not_mem_gammaEvenZero_of_empty hΓ hH hHE

/-- If `Γ₀` is nonempty under the §2.5 standing assumption, its members all
lie outside the characteristic-2 collection. -/
public theorem gammaZero_subset_compl_of_empty
    (hΓ : gammaEvenZero E M = ∅) :
    gammaZero E M ⊆ Eᶜ := by
  intro H hH hHE
  exact not_mem_gammaEvenZero_of_empty hΓ hH hHE

end CFSG.Quasithin.Chapter2
