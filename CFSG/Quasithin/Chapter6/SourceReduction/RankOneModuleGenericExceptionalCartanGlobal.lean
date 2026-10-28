module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalReduction

/-!
# Source obligations for the Cartan local-to-global argument

The first part of the proof of original 5.2.2 uses 5.1.6 to reduce the
Cartan to its order-three and order-five subgroups, together with a factor
whose join with H has nontrivial two-core. The remaining argument excludes
each such prime actor, using genuine F.1.1 and the changed-Sylow argument.

The two predicates below specify these independent source obligations.
They do not assert that either obligation has been proved. Their assembly
uses the actual generated subgroups, and retains the local 5.1.13 theorem
explicitly so it can be applied at the changed Sylow subgroup.

Source: Aschbacher--Smith, 5.1.6 and 5.2.2, printed pp.631--633,646--649.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The precise small-Cartan consequence of 5.1.6 consumed by 5.2.2.
In the degree-eight row the first factor is the order-seventeen torus;
its nontrivial two-core is justified by the central omega subgroup.
The predicate is a proof obligation, not an inhabited source interface. -/
def SourceCartanSmallGeneration (κ : GroupClass.{u})
    (G : Type u) [Group G] [Finite G] : Prop :=
  ∀ (T : Sylow 2 G) (L W : Subgroup G) (n : ℕ), Input κ T L W n →
    ∀ H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
      1 < ChapterE.generationParameter H →
      ∀ A B : Subgroup G, CartanPair T L H A B →
        CartanLocalControl A H → (A ⊔ H).pCoreIn 2 = ⊥ →
          CartanSmallGeneration A H n

/-- The order-three/order-five part of 5.2.2, with the full source input.
The degree is only restricted to the three values supplied by 5.1.6.
Constructing the source rank-one parabolic, checking genuine F.1.1,
excluding its zero-core models, and making the changed-Sylow argument
are all required to establish this predicate. -/
def SourceCartanPrimeExclusion (κ : GroupClass.{u})
    (G : Type u) [Group G] [Finite G] : Prop :=
  SourceLocalCartanEscape κ G →
    ∀ (T : Sylow 2 G) (L W : Subgroup G) (n : ℕ), Input κ T L W n →
      ∀ H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
        1 < ChapterE.generationParameter H →
        ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4 →
        ∀ A B : Subgroup G, CartanPair T L H A B →
          CartanLocalControl A H → (n = 2 ∨ n = 4 ∨ n = 8) →
          ∀ (p : ℕ) (D : Subgroup G), CartanPrimeActor A H p D → False

/-- Assemble the two independent source branches into the exact global
normalization premise. Neither source obligation is discharged here. -/
theorem cartan_normalizes_of_prime_sources {κ : GroupClass.{u}}
    (hsmall : SourceCartanSmallGeneration κ G)
    (hprime : SourceCartanPrimeExclusion κ G)
    (h513 : SourceLocalCartanEscape κ G)
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (h : Input κ T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (c : CartanPair T L H A B) (hcontrol : CartanLocalControl A H) :
    A ≤ normalizer (residual H : Set G) := by
  by_contra hnot
  have hzero := hcontrol.core_eq_bot_of_not_normalizes le_rfl hnot
  have hs := hsmall T L W n h H hH hgen A B c hcontrol hzero
  obtain ⟨p, D, hd⟩ := hs.exists_prime_actor hcontrol hnot
  exact hprime h513 T L W n h H hH hgen hthree A B c hcontrol hs.1 p D hd

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
