module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalGeometry
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanPreparation
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2
public import Theory.Mathieu.M23.Basic

/-!
# The two source obligations in the generic Cartan-escape argument

The local assertion 5.1.13 concerns A ∩ Y for Y in H(H), whereas the
global assertion 5.2.2 concerns A itself. A local-control implication
reduces failure of global normalization to a subgroup E of A for which
E H has nontrivial two-core and E fails to normalize O²(H). Taking
Y = E H then supplies exactly the local assertion's intersection A ∩ Y.

`CartanExceptionalConclusion` states the requested mathematical output,
including the full commutator module, the literal residual quotient and
actual quotient isomorphisms for a relative C-component. It is a target,
not an assumed classification theorem. The theorem below assembles the
two still-explicit source implications; it does not prove either of them.

Source: Aschbacher--Smith, 5.1.13 and 5.2.2, printed pp.635--638,646--649.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The exact exceptional output needed before choosing an A₅ marking. -/
def CartanExceptionalConclusion (T : Sylow 2 G) (L W H : Subgroup G) : Prop :=
  IsOneOrTwoA5Modules L (layer L W) ∧
    ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 4 ∧
    ∃ X : Subgroup G, residual H ≤ X ∧ X ≤ omegaCentralizer T ∧
      (X.subgroupOf (omegaCentralizer T)).IsCComponent ∧
      (Nonempty ((X ⧸ pCore 2 X) ≃* alternatingGroup (Fin 7)) ∨
        Nonempty ((X ⧸ pCore 2 X) ≃* Sporadic.LeechRelated.J2.Carrier) ∨
        Nonempty ((X ⧸ pCore 2 X) ≃* Sporadic.Mathieu.M23))

/-- The local normalization condition used at the start of the proof of
5.2.2. The nontrivial core is that of the actual generated subgroup. -/
def CartanLocalControl (A H : Subgroup G) : Prop :=
  ∀ E : Subgroup G, E ≤ A → (E ⊔ H).pCoreIn 2 ≠ ⊥ →
    E ≤ normalizer (residual H : Set G)

/-- The local source implication 5.1.13, with all original hypotheses.
Quantifying over the Sylow and module choices permits its reuse at the
changed Sylow subgroup in the proof of 5.2.2. This definition asserts no
inhabitant; its proof is an independent prerequisite of the global step. -/
def SourceLocalCartanEscape (κ : GroupClass.{u}) (G : Type u) [Group G] [Finite G] : Prop :=
  ∀ (T : Sylow 2 G) (L W : Subgroup G) (n : ℕ), Input κ T L W n →
    ∀ H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
      1 < ChapterE.generationParameter H →
      ∀ A B : Subgroup G, CartanPair T L H A B →
        ∀ Y ∈ Chapter1.HOver G (H : Set G),
          ¬ A ⊓ Y ≤ normalizer (residual H : Set G) →
          CartanExceptionalConclusion T L W H

omit [Finite G] in
/-- Failure of local control produces a literal member of H(H), and the
intersected Cartan in 5.1.13 still fails to normalize the same residual. -/
theorem exists_local_cartan_escape {A H : Subgroup G}
    (h : ¬ CartanLocalControl A H) :
    ∃ Y ∈ Chapter1.HOver G (H : Set G),
      ¬ A ⊓ Y ≤ normalizer (residual H : Set G) := by
  classical
  by_contra hn
  apply h
  intro E hEA hcore
  have hY : E ⊔ H ∈ Chapter1.HOver G (H : Set G) :=
    ⟨hcore, show H ≤ E ⊔ H from le_sup_right⟩
  have hAY : A ⊓ (E ⊔ H) ≤ normalizer (residual H : Set G) := by
    by_contra hnot
    exact hn ⟨E ⊔ H, hY, hnot⟩
  exact (le_inf hEA le_sup_left).trans hAY

/-- Assemble local escape classification and the local-to-global
normalization implication on any compatible pair. Both source proofs
remain explicit; no A₅ model or chosen-module invariance is assumed. -/
theorem cartan_exceptional_of_local_and_global
    {T : Sylow 2 G} {L W H A B : Subgroup G}
    (c : CartanPair T L H A B)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hTH : (T : Subgroup G) ≤ H)
    (hescape : ¬ (normalizer (((T : Subgroup G).subgroupOf L) : Set L)).map L.subtype ≤
      normalizer (residual H : Set G))
    (hlocal : ∀ Y ∈ Chapter1.HOver G (H : Set G),
      ¬ A ⊓ Y ≤ normalizer (residual H : Set G) →
      CartanExceptionalConclusion T L W H)
    (hglobal : CartanLocalControl A H → A ≤ normalizer (residual H : Set G)) :
    CartanExceptionalConclusion T L W H := by
  have hA : ¬ A ≤ normalizer (residual H : Set G) := by
    intro hAN
    apply hescape
    rw [← localBorel_eq_map]
    exact (c.normalizes_residual_iff hTL hTH).mp hAN
  obtain ⟨Y, hY, hAY⟩ := exists_local_cartan_escape (fun hh => hA (hglobal hh))
  exact hlocal Y hY hAY

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
