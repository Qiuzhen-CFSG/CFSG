module

public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.Inputs
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.FixedSubgroup
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.Localization

/-!
# The Hall fixed-subgroup deduction in E.6.27

A complete n' witness gives the faithful alternative immediately. Otherwise
its abelian Hall overgroup has a nontrivial fixed subgroup. We choose an
odd-prime omega subgroup, prove the required permutation property, and apply
exactly the generation clause of 4.4.13(1). Mapping this subgroup through the
original embedding gives the requested escaping relative normalizer.

This is a conditional assembly. Construction of `HallCartanData` from marked
E.2.2 models and identification of the unique maximal overgroup with H ∩ M
remain obligations. They are not included in the earlier-source contract.
The specialization to the twice-mapped residual parabolic retains the literal
maps and its original generation parameter.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), E.6.27,
printed p.257, and 4.4.13(1), printed pp.623--624.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan

open Subgroup ChapterB
open scoped Pointwise

universe u
variable {G X : Type u} [Group G] [Finite G] [Group X] [Finite X]

omit [Finite G] [Finite X] in
/-- Oddness belongs to the Hall subgroup in the original parabolic. -/
theorem HallCartanData.odd {f : X →* G} (hf : Function.Injective f)
    {M U : Subgroup G} {S : Sylow 2 X} {n : ℕ} (d : HallCartanData f M U S n) :
    Odd (Nat.card d.hallGroup) := by
  have ho := d.witness.odd.of_dvd_nat
    (card_map_dvd d.witness.abelianGroup (M ⊓ centralizer (U : Set G)).subtype)
  rwa [← d.hall_image, card_map_of_injective hf] at ho

omit [Finite G] [Finite X] in
/-- Injectivity, rather than a change of group structure, transfers commutativity. -/
theorem HallCartanData.abelian {f : X →* G} (hf : Function.Injective f)
    {M U : Subgroup G} {S : Sylow 2 X} {n : ℕ} (d : HallCartanData f M U S n) :
    IsMulCommutative d.hallGroup := by
  let := d.witness.abelian
  have hc : IsMulCommutative (d.hallGroup.map f) := by
    rw [d.hall_image]
    infer_instance
  let := hc
  apply IsMulCommutative.of_comm
  intro a b
  apply Subtype.ext
  apply hf
  simpa only [Subgroup.coe_mul, map_mul] using setLike_mul_comm (s := d.hallGroup.map f)
    (mem_map_of_mem f a.property) (mem_map_of_mem f b.property)

/-- Complete the two alternatives once the marked-model construction and the
local maximal-overgroup identification have been proved. The only earlier-source
input is the precisely typed elementary-subgroup clause of 4.4.13. -/
theorem alternative_of_hall_data
    {Kc : GroupClass.{u}} {T : Sylow 2 G} {M V U : Subgroup G}
    (h : HypothesisE61 Kc T M V) (hU : U ≠ ⊥) (hUV : U ≤ V)
    (earlier : Source4413One Kc G)
    (f : X →* G) (hf : Function.Injective f)
    (S : Sylow 2 X) (hP : IsMinimalParabolicOver S ⊤)
    (hcore : pCore 2 X ≠ ⊥) (hn : 1 < generationParameter X)
    (hmax : minimalParabolicMax S hP = M.comap f)
    (hescape : ¬ f.range ≤ M)
    (d : HallCartanData f M U S (generationParameter X)) :
    ParabolicCartanAlternative V M U f.range (generationParameter X) := by
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

/-- Application to the exact twice-mapped subgroup in the published hlarge
consumer. Construction of the Hall data and the three local placement premises
remains with this task; this theorem does not assert that they exist. -/
theorem residual_alternative_of_hall_data
    {Kc : GroupClass.{u}} {T : Sylow 2 G} {M V U : Subgroup G}
    (h : HypothesisE61 Kc T M V) (hU : U ≠ ⊥) (hUV : U ≤ V)
    (earlier : Source4413One Kc G)
    (H : Subgroup (primeToResidual 2 (centralizer (U : Set G))))
    (R : Sylow 2 H) (hP : IsMinimalParabolicOver R ⊤)
    (hcore : pCore 2 H ≠ ⊥) (hn : 1 < generationParameter H)
    (hmax : minimalParabolicMax R hP = M.comap (residualEmbedding U H))
    (hescape : ¬ (H.map (primeToResidual 2 (centralizer (U : Set G))).subtype).map
      (centralizer (U : Set G)).subtype ≤ M)
    (d : HallCartanData (residualEmbedding U H) M U R (generationParameter H)) :
    ParabolicCartanAlternative V M U
      ((H.map (primeToResidual 2 (centralizer (U : Set G))).subtype).map
        (centralizer (U : Set G)).subtype) (generationParameter H) := by
  rw [← residualEmbedding_range] at hescape ⊢
  exact alternative_of_hall_data h hU hUV earlier (residualEmbedding U H)
    (residualEmbedding_injective U H) R hP hcore hn hmax hescape d

/-- The exact original Sylow and residual-parabolic consumer. The nontrivial
two-core and intrinsic minimal-parabolic premises have both been discharged.
Only the model construction and maximal-overgroup placement remain. -/
theorem residual_alternative_of_constructed_hall
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
    (d : HallCartanData (residualEmbedding U H) M U
      (parabolicSylow S H hH) (generationParameter H)) :
    ParabolicCartanAlternative V M U
      ((H.map (primeToResidual 2 (centralizer (U : Set G))).subtype).map
        (centralizer (U : Set G)).subtype) (generationParameter H) := by
  apply residual_alternative_of_hall_data h hU hUV earlier H
    (parabolicSylow S H hH) (minimalParabolic_subtype (residualSylow S) H hH)
    (residual_twoCore_ne_bot h hU hUV S H hH) hn _ hescape d
  apply maximal_eq_overlap_of_image_le _ _ _ _ _ hmax
  · rwa [parabolicSylow_image]
  · rwa [residualEmbedding_range]

end CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan

end
