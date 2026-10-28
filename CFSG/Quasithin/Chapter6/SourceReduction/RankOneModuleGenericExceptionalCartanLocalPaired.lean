module

public import CFSG.Quasithin.Chapter6.SourceReduction.LocalSieve.PairedHall
public import CFSG.Quasithin.Chapter6.SourceReduction.LocalSieve.PairedContainers

/-!
# Removing paired residuals once the original Cartan supplies a cubic

Apply the Hall-plane obstruction to the genuine E.2.2 seed. An escaping
cubic forces that seed to be the whole literal two-residual. Source 1.2.4
then supplies a normal C-component relative to the original local overgroup,
and escape makes the inclusion proper. At degree two the left Cartan has
order three, so this reduction requires no additional cubic witness.

The original input also supplies a containing component whose nonnormal
branch has a moved A₅ seed, the prescribed Hall plane E₉, and quotient J₁
or exceptional odd-prime PSL₂. The latter retains its actual A₅ seed image.

The local sieve must still construct its inverted cubic and exclude the
remaining containing models. The A₇ and whole-module arguments remain
with the original local Cartan classification assembly.

Source: Aschbacher–Smith 5.1.13, printed pp.636–638.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]

/-- A literal escaping cubic makes the whole residual a local component and gives its proper normal container. -/
theorem localCartan_cubic_escape_residual_component
    {T : Sylow 2 G} {L W H A B Y D : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hpar : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (hDA : D ≤ A) (hDc : Nat.card D = 3)
    (hD : ¬ D ≤ normalizer (residual H : Set G)) :
    ((residual H).subgroupOf H).IsCComponent ∧
      IsQuasisimple (residual H ⧸ pCore 2 (residual H)) ∧
      residual H ∈ Chapter1.L G (T : Subgroup G) ∧
      ∃ X : Subgroup G, X ≤ Y ∧ (X.subgroupOf Y).IsCComponent ∧
        (X.subgroupOf Y).Normal ∧ residual H < X := by
  obtain ⟨K, hKH, hK, hqs, hgen, hKL, horbit⟩ :=
    LocalSieve.exists_seed h.qtke h.sylow_normalizes hH hpar
  have he := LocalSieve.escape_seed_eq_residual_of_cubic h hH hpar c hKH hK hqs
    hgen hKL horbit hY hescape hDA hDc hD
  subst K
  exact ⟨hK, hqs, hKL,
    LocalSieve.exists_proper_normal_component h.qtke hH.1.1.2 hKL hY hescape⟩

/-- At field degree two the original Cartan itself is cubic, so the paired branch is impossible. -/
theorem localCartan_degree_two_escape_residual_component
    {T : Sylow 2 G} {L W H A B Y : Subgroup G}
    (h : Input KnownSimple.IsKnownSimple T L W 2)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hpar : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G)) :
    ((residual H).subgroupOf H).IsCComponent ∧
      IsQuasisimple (residual H ⧸ pCore 2 (residual H)) ∧
      residual H ∈ Chapter1.L G (T : Subgroup G) ∧
      ∃ X : Subgroup G, X ≤ Y ∧ (X.subgroupOf Y).IsCComponent ∧
        (X.subgroupOf Y).Normal ∧ residual H < X := by
  have hAc : Nat.card A = 3 := (c.left_cyclic_and_card h.sylow_normalizes h.linear).2
  exact localCartan_cubic_escape_residual_component h hH hpar c hY hescape
    le_rfl hAc (fun hn => hescape (inf_le_left.trans hn))

/-- The original local sieve has a normal container or the two precise paired containing rows, with B = E₉. -/
theorem localCartan_containing_component_cases
    {T : Sylow 2 G} {L W H A B Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hpar : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G)) :
    ∃ K : Subgroup G, K ≤ H ∧ (K.subgroupOf H).IsCComponent ∧
      IsQuasisimple (K ⧸ pCore 2 K) ∧ K ⊔ (T : Subgroup G) = H ∧
      K ∈ Chapter1.L G (T : Subgroup G) ∧
      componentOrbit K (T : Subgroup G) = residual H ∧
      ∃ C : Subgroup Y, C.IsCComponent ∧ K ≤ C.map Y.subtype ∧
        residual H < componentOrbit (C.map Y.subtype) (T : Subgroup G) ∧
        ((componentOrbit (C.map Y.subtype) (T : Subgroup G)).subgroupOf Y).Normal ∧
        (C.Normal ∨ ((normalizer (C : Set Y)).index = 2 ∧
          K < residual H ∧ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 4 ∧
          IsElementaryAbelian 3 B ∧ Nat.card B = 9 ∧
          (Nonempty ((C ⧸ pCore 2 C) ≃* Janko1.Model) ∨
            ∃ p : ℕ, Chapter1.Section02.A312ExceptionalPrime p ∧
              ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 2 p ∧
              Chapter1.Section02.LocalModels.IsAlternating
                ((K.subgroupOf Y).map (QuotientGroup.mk' (pCore 2 Y))) 5))) := by
  obtain ⟨K, hKH, hK, hqs, hgen, hKL, horbit, C, ⟨hC, hKC, hRC⟩, _⟩ :=
    LocalSieve.exists_seed_embedding h.qtke h.sylow_normalizes hH hpar hY
  obtain ⟨hnormal, hstrict⟩ := LocalSieve.containing_orbit_normal_and_strict
    h.qtke hH.1.1.2 hY C hC hRC hescape
  refine ⟨K, hKH, hK, hqs, hgen, hKL, horbit, C, hC, hKC, hstrict, hnormal, ?_⟩
  by_cases hn : C.Normal
  · exact Or.inl hn
  · have hmoved := LocalSieve.nonnormal_container_seed_moved h.qtke hKH hH.1.1.2
      hKL hY C hC hKC hn
    have hlinear := LocalSieve.moved_seed_linear_four_of_escape h.qtke hKL hgen
      horbit hmoved hY hescape
    obtain ⟨hB, hBc⟩ := LocalSieve.moved_seed_right_hall_plane h hH hpar c hKH hK hqs
      hgen horbit hmoved hlinear
    obtain ⟨hi, hm⟩ := LocalSieve.nonnormal_container_models h.qtke hKH hH.1.1.2
      hKL horbit hY hescape C hC hKC hn
    exact Or.inr ⟨hi, lt_of_le_of_ne ((le_componentOrbit K _).trans_eq horbit) hmoved,
      hlinear, hB, hBc, hm⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
