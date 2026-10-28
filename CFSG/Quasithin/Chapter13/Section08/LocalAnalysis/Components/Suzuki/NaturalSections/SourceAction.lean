module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Suzuki.Reduction
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.SourceSeed
public import Theory.GroupAction.SubgroupQuotientFullAction

/-!
# The actual source action and its generating seed

Conjugation on U_H/V₁ descends through H/O₂(H) using [U_H,O₂(H)] ≤ V₁.
The exact centralizer equality gives faithfulness. The H*-orbit of the image
of V₃ spans the quotient because U_H is the H-conjugate span of V₃.
Relative normalization preserves the seed, and irreducibility plus a
noncentral commutator makes its L₁*-commutator equal to the whole seed.

The quotient, seed subspace and representative action formula reuse the
independent constructions in ChiefFactors.SourceSeed. No later L₄ result
is used. The inputs here are the actual normalization, centralizer and seed
facts from the earlier source setup, not a natural Suzuki module assumption.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), notation on
printed p.946, 13.7.3(6) on p.936, and the seed argument in 13.8.16 on p.953.
This does not yet establish the natural central-section classification.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section08.Components.Suzuki.NaturalSections
open ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors
variable {G : Type*} [Group G] (H V₃ V₁ : Subgroup G)
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]

/-- Conjugation on the literal quotient, factored through the actual two-core. -/
theorem exists_sourceAction
    (hn : H ≤ normalizer (V₁ : Set G))
    (hQ : ⁅Source.UH H V₃, Source.QH H⁆ ≤ V₁) :
    ∃ ρ : Representation (ZMod 2) (Source.Hstar H) (SourceSpace H V₃ V₁),
      IsSourceAction H V₃ V₁ ρ := by
  have hU : H ≤ normalizer (Source.UH H V₃ : Set G) :=
    le_normalizer_conjugateSpanBy V₃ H
  obtain ⟨a, ha⟩ := exists_quotient_conjugation_action H (Source.UH H V₃) V₁
    hU hn inferInstance
  have hk := quotient_conjugation_action_kills_commutator_layer H
    (Source.UH H V₃) V₁ (Source.QH H) inferInstance hU hQ a ha
  have hka : pCore 2 H ≤ a.ker := by
    intro x hx
    apply hk
    exact mem_map_of_mem H.subtype hx
  let b := QuotientGroup.lift (pCore 2 H) a hka
  let ρ : Representation (ZMod 2) (Source.Hstar H) (SourceSpace H V₃ V₁) :=
    { toFun g := (b g).toMonoidHom.toAdditive.toZModLinearMap 2
      map_one' := by
        ext v
        change Additive.ofMul (b 1 v.toMul) = v
        rw [map_one]
        rfl
      map_mul' := by
        intro x y
        ext v
        change Additive.ofMul (b (x * y) v.toMul) = _
        rw [map_mul]
        rfl }
  refine ⟨ρ, ?_⟩
  intro h u
  exact congrArg Additive.ofMul (ha h u)

/-- The orbit of the actual seed spans all of Ũ_H. -/
theorem sourceSeed_orbit_span
    (ρ : Representation (ZMod 2) (Source.Hstar H) (SourceSpace H V₃ V₁))
    (hρ : IsSourceAction H V₃ V₁ ρ) :
    Submodule.span (ZMod 2) {v | ∃ h : Source.Hstar H,
      ∃ a ∈ sourceSeedSpace H V₃ V₁, ρ h a = v} = ⊤ := by
  let S := Submodule.span (ZMod 2) {v | ∃ h : Source.Hstar H,
    ∃ a ∈ sourceSeedSpace H V₃ V₁, ρ h a = v}
  have hs : ∀ h : Source.Hstar H, ∀ v ∈ S, ρ h v ∈ S := by
    intro h v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨g, a, ha, rfl⟩ := hv
      apply Submodule.subset_span
      exact ⟨h * g, a, ha, by rw [map_mul]; rfl⟩
    | zero => simp
    | add v w hv hw ihv ihw => simpa using S.add_mem ihv ihw
    | smul c v hv ih => simpa using S.smul_mem c ih
  have he := sourceSeedSpace_generates H V₃ V₁ ρ hρ
    (⟨S, hs⟩ : Subrepresentation ρ) (by
      intro v hv
      exact Submodule.subset_span ⟨1, v, hv, by simp⟩)
  exact congrArg Subrepresentation.toSubmodule he

/-- Subgroups normalizing V₃ stabilize its actual image in Ũ_H. -/
theorem sourceSeed_stable
    (ρ : Representation (ZMod 2) (Source.Hstar H) (SourceSpace H V₃ V₁))
    (hρ : IsSourceAction H V₃ V₁ ρ) (P : Subgroup G)
    (hP : P ≤ normalizer (V₃ : Set G)) :
    Source.starImage H P ≤ subspaceStabilizer ρ (sourceSeedSpace H V₃ V₁) := by
  apply le_subspaceStabilizer
  rintro _ ⟨h, hh, rfl⟩ _ ⟨u, hu, rfl⟩
  change ρ (QuotientGroup.mk' (pCore 2 H) h)
    (Additive.ofMul (sourceProjection H V₃ V₁ u)) ∈ sourceSeedSpace H V₃ V₁
  rw [hρ]
  exact ⟨sourceConjugate H V₃ h u,
    (mem_normalizer_iff.mp (hP hh) u).mp hu, rfl⟩

/-- A noncentral ambient commutator moves the literal quotient seed. -/
theorem sourceSeed_commutator_ne_bot
    (ρ : Representation (ZMod 2) (Source.Hstar H) (SourceSpace H V₃ V₁))
    (hρ : IsSourceAction H V₃ V₁ ρ) (L : Subgroup G) (hLH : L ≤ H)
    (hn : ¬ ⁅V₃, L⁆ ≤ V₁) :
    subspaceCommutator ρ (sourceSeedSpace H V₃ V₁) (Source.starImage H L) ≠ ⊥ := by
  intro he
  apply hn
  rw [commutator_comm]
  apply commutator_le.mpr
  intro l hl v hv
  let u : Source.UH H V₃ := ⟨v, le_conjugateSpanBy V₃ H hv⟩
  let h : H := ⟨l, hLH hl⟩
  have hx : Additive.ofMul (sourceProjection H V₃ V₁ u) ∈ sourceSeedSpace H V₃ V₁ :=
    ⟨u, hv, rfl⟩
  have hh : QuotientGroup.mk' (pCore 2 H) h ∈ Source.starImage H L :=
    mem_map_of_mem _ hl
  have hd := Submodule.subset_span (R := ZMod 2)
    (s := {w | ∃ k ∈ Source.starImage H L, ∃ a ∈ sourceSeedSpace H V₃ V₁,
      w = ρ k a - a}) ⟨_, hh, _, hx, rfl⟩
  change ρ (QuotientGroup.mk' (pCore 2 H) h)
    (Additive.ofMul (sourceProjection H V₃ V₁ u)) -
      Additive.ofMul (sourceProjection H V₃ V₁ u) ∈
      subspaceCommutator ρ (sourceSeedSpace H V₃ V₁) (Source.starImage H L) at hd
  rw [he, Submodule.mem_bot, sub_eq_zero, hρ] at hd
  have hquot := congrArg Additive.toMul hd
  have hm := QuotientGroup.eq_iff_div_mem.mp hquot
  change l * v * l⁻¹ / v ∈ V₁ at hm
  simpa only [commutatorElement_def, div_eq_mul_inv] using hm

/-- The irreducible parabolic seed is generated by the normal L₁-action.
The hypotheses are invariance, irreducibility and an ambient noncentral
commutator, rather than an assumed seed commutator identity. -/
theorem sourceSeed_commutator
    (ρ : Representation (ZMod 2) (Source.Hstar H) (SourceSpace H V₃ V₁))
    (hρ : IsSourceAction H V₃ V₁ ρ) (P L : Subgroup G) (hLH : L ≤ H)
    (hLP : L ≤ P) (hP : P ≤ normalizer (V₃ : Set G))
    (hn : Source.starImage H P ≤ normalizer (Source.starImage H L : Set (Source.Hstar H)))
    (hi : IsAtom (invariantSubspace ρ (Source.starImage H P)
      (sourceSeedSpace H V₃ V₁) (sourceSeed_stable H V₃ V₁ ρ hρ P hP)))
    (hmove : ¬ ⁅V₃, L⁆ ≤ V₁) :
    subspaceCommutator ρ (sourceSeedSpace H V₃ V₁) (Source.starImage H L) =
      sourceSeedSpace H V₃ V₁ := by
  let A := sourceSeedSpace H V₃ V₁
  let C := subspaceCommutator ρ A (Source.starImage H L)
  have hAP := sourceSeed_stable H V₃ V₁ ρ hρ P hP
  have hCP : Source.starImage H P ≤ subspaceStabilizer ρ C :=
    subspaceCommutator_invariant_normalizer ρ hAP hn
  let D := invariantSubspace ρ (Source.starImage H P) C hCP
  have hCA : C ≤ A := by
    apply Submodule.span_le.mpr
    rintro _ ⟨l, hl, v, hv, rfl⟩
    have hlP : l ∈ Source.starImage H P := map_mono (subgroupOf_mono H hLP) hl
    exact A.sub_mem ((hAP hlP v).2 hv) hv
  have hD : D ≠ ⊥ := by
    intro he
    exact sourceSeed_commutator_ne_bot H V₃ V₁ ρ hρ L hLH hmove
      (congrArg Subrepresentation.toSubmodule he)
  exact congrArg Subrepresentation.toSubmodule ((hi.le_iff_eq hD).mp hCA)

/-- The full source centralizer equality supplies faithfulness on Ũ_H. -/
theorem sourceAction_injective
    (ρ : Representation (ZMod 2) (Source.Hstar H) (SourceSpace H V₃ V₁))
    (hρ : IsSourceAction H V₃ V₁ ρ)
    (hker : ∀ h : H, (∀ u : Source.UH H V₃, ⁅(h : G), (u : G)⁆ ∈ V₁) →
      h ∈ pCore 2 H) : Function.Injective ρ := by
  apply ρ.ker_eq_bot_iff.mp
  apply bot_unique
  intro x hx
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 H) x
  apply (QuotientGroup.eq_one_iff h).mpr
  apply hker h
  intro u
  have he := congrArg (fun f : Module.End (ZMod 2) (SourceSpace H V₃ V₁) =>
    f (Additive.ofMul (sourceProjection H V₃ V₁ u))) hx
  change ρ (QuotientGroup.mk' (pCore 2 H) h)
      (Additive.ofMul (sourceProjection H V₃ V₁ u)) =
    Additive.ofMul (sourceProjection H V₃ V₁ u) at he
  rw [hρ] at he
  have hm := QuotientGroup.eq_iff_div_mem.mp (congrArg Additive.toMul he)
  change (h : G) * (u : G) * (h : G)⁻¹ / (u : G) ∈ V₁ at hm
  simpa only [commutatorElement_def, div_eq_mul_inv] using hm

/-- Ambient relative normalizers induce the correct star normalizers. -/
theorem starImage_normalizes (P L : Subgroup G)
    (hn : P ≤ normalizer (L : Set G)) :
    Source.starImage H P ≤ normalizer (Source.starImage H L : Set (Source.Hstar H)) := by
  apply (map_mono (show P.subgroupOf H ≤ normalizer (L.subgroupOf H : Set H) from ?_)).trans
    (le_normalizer_map _)
  apply le_normalizer_iff.mpr
  intro p hp l hl
  exact le_normalizer_iff.mp hn p hp l hl

/-- Orbit generation and the seed identity yield the full commutator once
normality of L₁* in H* has been supplied by the Borel argument. -/
theorem source_commutator_top
    (ρ : Representation (ZMod 2) (Source.Hstar H) (SourceSpace H V₃ V₁))
    (hρ : IsSourceAction H V₃ V₁ ρ) (P L : Subgroup G) (hLH : L ≤ H)
    (hLP : L ≤ P) (hP : P ≤ normalizer (V₃ : Set G))
    (hn : P ≤ normalizer (L : Set G))
    (hi : IsAtom (invariantSubspace ρ (Source.starImage H P)
      (sourceSeedSpace H V₃ V₁) (sourceSeed_stable H V₃ V₁ ρ hρ P hP)))
    (hmove : ¬ ⁅V₃, L⁆ ≤ V₁)
    (hLn : (Source.starImage H L).Normal) :
    subspaceCommutator ρ ⊤ (Source.starImage H L) = ⊤ := by
  let := hLn
  apply commutator_top_of_orbit_seed ρ ⊤ (Source.starImage H L)
    (sourceSeedSpace H V₃ V₁) le_normalizer_of_normal
  · exact sourceSeed_commutator H V₃ V₁ ρ hρ P L hLH hLP hP
      (starImage_normalizes H P L hn) hi hmove
  · simpa using sourceSeed_orbit_span H V₃ V₁ ρ hρ

end CFSG.Quasithin.Chapter13.Section08.Components.Suzuki.NaturalSections


end
