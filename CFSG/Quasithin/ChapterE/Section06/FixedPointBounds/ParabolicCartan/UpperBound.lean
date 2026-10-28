module
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds
/-!
# The sufficient numerical Cartan route for E.6.27

Keep the Cartan witness at its actual exponent c. The original condition
n(H)>1 applies 4.4.13 to the fixed subgroup regardless of c. In the faithful
branch, n(H)≤c and c≤n′ give exactly the contradiction required by the
large-parabolic argument. The original maximal subgroup, residual embedding,
Hall subgroup and Sylow remain unchanged.

The source model and numerical upper-bound producers must construct the
witness and n(H)≤c. These consumer theorems do not assume or prove n(H)=c,
and preserve all earlier interfaces. Source: Aschbacher–Smith E.6.27,
printed p.257, and 4.4.13(1), printed pp.623–624.
-/

public section
namespace CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan
open Subgroup ChapterB
open scoped Pointwise
universe u
variable {G X : Type u} [Group G] [Finite G] [Group X] [Finite X]
theorem alternative_of_hall_data_at
    {Kc : GroupClass.{u}} {T : Sylow 2 G} {M V U : Subgroup G}
    (h : HypothesisE61 Kc T M V) (hU : U ≠ ⊥) (hUV : U ≤ V)
    (earlier : Source4413One Kc G)
    (f : X →* G) (hf : Function.Injective f)
    (S : Sylow 2 X) (hP : IsMinimalParabolicOver S ⊤)
    (hcore : pCore 2 X ≠ ⊥) (hn : 1 < generationParameter X)
    (hmax : minimalParabolicMax S hP = M.comap f)
    (hescape : ¬ f.range ≤ M)
    {c : ℕ} (d : HallCartanData f M U S c) :
    ParabolicCartanAlternative V M U f.range c := by
  classical
  have hYrange : d.hallGroup.map f ≤ f.range := by
    rintro _ ⟨x, _, rfl⟩
    exact ⟨x, rfl⟩
  by_cases hfaith : d.witness.cyclicGroup.map
      (M ⊓ centralizer (U : Set G)).subtype ⊓ centralizer (V : Set G) = ⊥
  · exact Or.inl ⟨d.witness,
      (map_mono d.witness.cyclic_le).trans (d.hall_image ▸ hYrange), hfaith⟩
  · have hfixed := (nonfaithful_cartan_overgroup_fixed d.witness hfaith).1
    let C : Subgroup X := (centralizer (V : Set G)).comap f
    have hne : d.hallGroup ⊓ C ≠ ⊥ := by
      intro he
      apply hfixed
      apply eq_bot_iff.mpr
      rintro y ⟨hy, hyC⟩
      rw [← d.hall_image] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      have hx1 : x = 1 := by
        have hx0 : x ∈ d.hallGroup ⊓ C := ⟨hx, hyC⟩
        simpa only [he, mem_bot] using hx0
      simp only [hx1, map_one, mem_bot]
    have hSN : (S : Subgroup X).map f ≤ normalizer (V : Set G) := by
      rw [d.sylow_image]
      exact (map_subtype_le _).trans (h.localCentralizer_le_normalizer hU hUV)
    have hSC : (S : Subgroup X) ≤ normalizer (C : Set X) :=
      (map_le_iff_le_comap.mp
        (hSN.trans (normalizer_le_normalizer_centralizer V))).trans
          ((centralizer (V : Set G)).le_normalizer_comap f)
    obtain ⟨p, A, hp, _, hA, hAe, hAC, hAo, hAS⟩ :=
      exists_elementary_odd_invariant_permuting (d.abelian hf) (d.odd hf)
        hne hSC d.frattini d.normalizes
    have hgen : M.comap f ⊔ normalizer (A : Set X) = ⊤ := by
      rw [← hmax]
      exact earlier h.simpleQTKE X inferInstance inferInstance f hf hcore hn S hP
        d.hallGroup (hmax ▸ d.hall_le) (hmax ▸ d.hall) p hp A hAe
        (hAC.trans inf_le_left) hAS
    refine Or.inr ⟨A.map f, ?_, ?_, hAo.of_dvd_nat (card_map_dvd A f), ?_⟩
    · intro he
      apply hA
      apply eq_bot_iff.mpr
      intro x hx
      have hf1 : f x = 1 := by
        simpa only [he, mem_bot] using mem_map_of_mem f hx
      exact hf (hf1.trans (map_one f).symm)
    · rintro y ⟨x, hx, rfl⟩
      exact ⟨⟨⟨x, rfl⟩, d.hall_le (hAC hx).1⟩, (hAC hx).2⟩
    · intro hN
      have hNM : normalizer (A : Set X) ≤ M.comap f := by
        intro x hx
        exact hN ⟨⟨x, rfl⟩, A.le_normalizer_map f (mem_map_of_mem f hx)⟩
      have htop : (⊤ : Subgroup X) ≤ M.comap f := by
        rw [← hgen]
        exact sup_le le_rfl hNM
      apply hescape
      rintro y ⟨x, rfl⟩
      exact htop (mem_top x)

theorem residual_alternative_of_hall_data_at
    {Kc : GroupClass.{u}} {T : Sylow 2 G} {M V U : Subgroup G}
    (h : HypothesisE61 Kc T M V) (hU : U ≠ ⊥) (hUV : U ≤ V)
    (earlier : Source4413One Kc G)
    (H : Subgroup (primeToResidual 2 (centralizer (U : Set G))))
    (R : Sylow 2 H) (hP : IsMinimalParabolicOver R ⊤)
    (hcore : pCore 2 H ≠ ⊥) (hn : 1 < generationParameter H)
    (hmax : minimalParabolicMax R hP = M.comap (residualEmbedding U H))
    (hescape : ¬ (H.map (primeToResidual 2 (centralizer (U : Set G))).subtype).map
      (centralizer (U : Set G)).subtype ≤ M)
    {c : ℕ} (d : HallCartanData (residualEmbedding U H) M U R c) :
    ParabolicCartanAlternative V M U
      ((H.map (primeToResidual 2 (centralizer (U : Set G))).subtype).map
        (centralizer (U : Set G)).subtype) c := by
  rw [← residualEmbedding_range] at hescape ⊢
  exact alternative_of_hall_data_at h hU hUV earlier (residualEmbedding U H)
    (residualEmbedding_injective U H) R hP hcore hn hmax hescape d

/-- The exact original Sylow and residual-parabolic consumer. The nontrivial
two-core and intrinsic minimal-parabolic premises have both been discharged.
Only the model construction and maximal-overgroup placement remain. -/
theorem residual_alternative_of_constructed_hall_at
    {Kc : GroupClass.{u}} {T : Sylow 2 G} {M V U : Subgroup G}
    (h : HypothesisE61 Kc T M V) (hU : U ≠ ⊥) (hUV : U ≤ V)
    (earlier : Source4413One Kc G)
    (S : Sylow 2 (centralizer (U : Set G)))
    (hSM : (S : Subgroup (centralizer (U : Set G))).map
      (centralizer (U : Set G)).subtype ≤ M)
    (H : Subgroup (primeToResidual 2 (centralizer (U : Set G))))
    (hH : IsMinimalParabolicOver (residualSylow S) H)
    (hn : 1 < generationParameter H)
    (hescape : ¬ (H.map (primeToResidual 2 (centralizer (U : Set G))).subtype).map
      (centralizer (U : Set G)).subtype ≤ M)
    (hmax : (minimalParabolicMax (parabolicSylow S H hH)
      (minimalParabolic_subtype (residualSylow S) H hH)).map
        (residualEmbedding U H) ≤ M)
    {c : ℕ} (d : HallCartanData (residualEmbedding U H) M U
      (parabolicSylow S H hH) c) :
    ParabolicCartanAlternative V M U
      ((H.map (primeToResidual 2 (centralizer (U : Set G))).subtype).map
        (centralizer (U : Set G)).subtype) c := by
  apply residual_alternative_of_hall_data_at h hU hUV earlier H
    (parabolicSylow S H hH) (minimalParabolic_subtype (residualSylow S) H hH)
    (residual_twoCore_ne_bot h hU hUV S H hH) hn _ hescape d
  apply maximal_eq_overlap_of_image_le _ _ _ _ _ hmax
  · rwa [parabolicSylow_image]
  · rwa [residualEmbedding_range]

end CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan

namespace CFSG.Quasithin.ChapterE.Section06.FixedPointBounds
open Subgroup
universe u
variable {G : Type u} [Group G] [Finite G]
theorem centralizer_le_of_parabolic_upper_bounds
    {Kc : GroupClass.{u}} {T : Sylow 2 G} {M V U : Subgroup G}
    (h : HypothesisE61 Kc T M V) (hU : U ≠ ⊥) (hUV : U ≤ V)
    (j : ℕ)
    (hn : nPrime (inducedAutomizer V (M ⊓ centralizer (U : Set G))) ≤ j)
    (hodd : ∀ X : Subgroup G, X ≠ ⊥ → X ≤ M ⊓ centralizer (V : Set G) →
      Odd (Nat.card X) → normalizer (X : Set G) ≤ M)
    (P : Sylow 2 ↥(M ⊓ centralizer (U : Set G)))
    (hN : normalizer ((P : Subgroup ↥(M ⊓ centralizer (U : Set G))).map
      (M ⊓ centralizer (U : Set G)).subtype : Set G) ≤ M)
    (hsmall : ∀ S : Sylow 2 (centralizer (U : Set G)),
      (S : Subgroup (centralizer (U : Set G))).map (centralizer (U : Set G)).subtype =
        (P : Subgroup ↥(M ⊓ centralizer (U : Set G))).map
          (M ⊓ centralizer (U : Set G)).subtype →
      ∀ H : Subgroup (primeToResidual 2 (centralizer (U : Set G))),
        ChapterB.IsMinimalParabolicOver (residualSylow S) H →
        generationParameter H ≤ j →
        (H.map (primeToResidual 2 (centralizer (U : Set G))).subtype).map
          (centralizer (U : Set G)).subtype ≤ M)
    (hlarge : ∀ S : Sylow 2 (centralizer (U : Set G)),
      (S : Subgroup (centralizer (U : Set G))).map (centralizer (U : Set G)).subtype =
        (P : Subgroup ↥(M ⊓ centralizer (U : Set G))).map
          (M ⊓ centralizer (U : Set G)).subtype →
      ∀ H : Subgroup (primeToResidual 2 (centralizer (U : Set G))),
        ChapterB.IsMinimalParabolicOver (residualSylow S) H →
        j < generationParameter H →
        ¬ (H.map (primeToResidual 2 (centralizer (U : Set G))).subtype).map
          (centralizer (U : Set G)).subtype ≤ M →
        ∃ c : ℕ, generationParameter H ≤ c ∧ ParabolicCartanAlternative V M U
          ((H.map (primeToResidual 2 (centralizer (U : Set G))).subtype).map
            (centralizer (U : Set G)).subtype) c) :
    centralizer (U : Set G) ≤ M := by
  obtain ⟨S, hS⟩ := exists_sylow_of_local_normalizer P hN
  apply le_of_residual_minimalParabolics S (hS ▸ hN)
  intro H hH
  by_cases hsmallH : generationParameter H ≤ j
  · exact hsmall S hS H hH hsmallH
  · by_contra hescape
    have hlargeH := Nat.lt_of_not_ge hsmallH
    obtain ⟨c,hc,ha⟩ := hlarge S hS H hH hlargeH hescape
    exact not_large_parabolic_alternative h hU hUV (hlargeH.trans_le hc) hn hodd ha

end CFSG.Quasithin.ChapterE.Section06.FixedPointBounds
