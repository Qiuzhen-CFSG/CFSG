module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.SourceOrbit

/-!
# The source supplement interface for the external branch

The source setup gives `H = K L₁ T` in both local cases.  In the ordinary
case `X = L₁`, so this immediately gives the actor generation used by the
two-conjugate orbit argument.  In the covered case the source statement uses
`X = L₁,+` and `L₁ = X L₀`; the local natural setup does not identify the
remaining `L₀` direction with a subgroup of `K`.  Consequently the stronger
identity `[L₁,T] = L₁` is not inserted here.

The orbit calculation only needs the actual quotient generation
`K* ⊔ (X* ⊔ P) = H*`.  The adapter below exposes that contract directly and
keeps the older `ExternalInputs`/`SourceCubicInputs` records unchanged.  This
is the source-level replacement for the hidden full-commutator premise; the
ordinary branch discharges it from the literal source generation, while the
covered branch must supply the corresponding quotient calculation from its
actual supplement geometry.

Source: Aschbacher--Smith, proof of 13.8.20(a), printed pp.954--955, with
Notation 13.2.1--2 and the orbit calculation in F.9.18(4).
-/

@[expose] public noncomputable section

open Subgroup Representation Representation.BinaryOffender InvertedCubicTensor Theory.GroupTheory
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules

open FFSections
open FFSections.SourceOrbit
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases

universe u
variable {G : Type u} [Group G] [Finite G]

variable (H K X L₁ T V₃ V₁ : Subgroup G)
    [(V₁.subgroupOf (Source.UH H V₃)).Normal]
    [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]
    [(Source.starImage H K).Normal]
    (ρ : Representation (ZMod 2) (Source.Hstar H)
      (SeedAction.Space H V₃ V₁))
    (P : Sylow 2 (Source.Hstar H)) (s : S₃ →* Source.Hstar H)

omit [Finite G] in
/-- A source generation equality descends to the required actor generation as
soon as the local supplement is absorbed modulo the component.  This is the
weaker calculation used by the covered case: it does not identify the whole
commutator `[L₁,T]` with `L₁`. -/
theorem star_generation_of_component_supplement
    (H K X L₁ T : Subgroup G)
    (hgen : H = K ⊔ (L₁ ⊔ T)) (hXH : X ≤ H)
    (hL : L₁ ≤ K ⊔ X)
    (P : Subgroup (Source.Hstar H))
    (hP : P = Source.starImage H T) :
    Source.starImage H K ⊔ (Source.starImage H X ⊔ P) = ⊤ := by
  have hKH : K ≤ H := by
    rw [hgen]
    exact le_sup_left
  have hLH : L₁ ≤ H := by
    rw [hgen]
    exact le_sup_left.trans le_sup_right
  have hTH : T ≤ H := by
    rw [hgen]
    exact le_sup_right.trans le_sup_right
  have hXT : K ⊔ (X ⊔ T) = H := by
    apply le_antisymm
    · exact sup_le hKH (sup_le hXH hTH)
    · rw [hgen]
      have hKt : K ≤ K ⊔ (X ⊔ T) := le_sup_left
      have hXt : X ≤ K ⊔ (X ⊔ T) :=
        (show X ≤ X ⊔ T from le_sup_left).trans
          (show X ⊔ T ≤ K ⊔ (X ⊔ T) from le_sup_right)
      have hTt : T ≤ K ⊔ (X ⊔ T) :=
        (show T ≤ X ⊔ T from le_sup_right).trans
          (show X ⊔ T ≤ K ⊔ (X ⊔ T) from le_sup_right)
      have hKX : K ⊔ X ≤ K ⊔ (X ⊔ T) := sup_le hKt hXt
      have hLT : L₁ ⊔ T ≤ K ⊔ (X ⊔ T) :=
        sup_le (hL.trans hKX) hTt
      exact sup_le hKt hLT
  unfold Source.starImage
  have hsub :
      K.subgroupOf H ⊔ (X.subgroupOf H ⊔ T.subgroupOf H) = ⊤ := by
    rw [← subgroupOf_sup hXH hTH,
      ← subgroupOf_sup hKH (sup_le hXH hTH), hXT.symm, subgroupOf_self]
  have hm := congrArg (Subgroup.map (QuotientGroup.mk' (pCore 2 H))) hsub
  simpa only [Subgroup.map_sup, sup_assoc, Source.starImage,
    map_top_of_surjective _ (QuotientGroup.mk'_surjective _), hP] using hm

omit [Finite G] in
/-- The ordinary local case gives the exact actor generation needed by the
source orbit, without using the full commutator identity. -/
theorem ordinary_star_generation
    (H K X L₁ T : Subgroup G)
    (hgen : H = K ⊔ (L₁ ⊔ T)) (hX : X = L₁)
    (P : Subgroup (Source.Hstar H))
    (hP : P = Source.starImage H T) :
    Source.starImage H K ⊔ (Source.starImage H X ⊔ P) = ⊤ := by
  have hLH : L₁ ≤ H := by
    rw [hgen]
    exact le_sup_left.trans le_sup_right
  apply star_generation_of_component_supplement H K X L₁ T hgen
    (hX ▸ hLH)
  rw [hX]
  exact le_sup_right
  exact hP

omit [Finite G] in
/-- The covered factorization `L₁ = X Z` reduces the supplement calculation to
the placement of the central residual `Z` in the component.  The placement is
kept explicit because the source's local Borel argument supplies it only in
the branches where it has actually been proved. -/
theorem covered_star_generation_of_factorization
    (H K X Z L₁ T : Subgroup G)
    (hgen : H = K ⊔ (L₁ ⊔ T)) (hXH : X ≤ H)
    (hfactor : L₁ = X ⊔ Z) (hZK : Z ≤ K)
    (P : Subgroup (Source.Hstar H))
    (hP : P = Source.starImage H T) :
    Source.starImage H K ⊔ (Source.starImage H X ⊔ P) = ⊤ := by
  apply star_generation_of_component_supplement H K X L₁ T hgen hXH
  · rw [hfactor]
    exact sup_le le_sup_right (hZK.trans le_sup_left)
  · exact hP

omit [Finite G] in
/-- The generic orbit adapter.  It is deliberately phrased with the actual
quotient generation conclusion rather than with `[L₁,T] = L₁`; all subgroup,
Sylow and quotient data remain literal. -/
theorem selected_cubic_orbit_of_supplement_generation
    {V : Type u} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (K : Subgroup G) [K.Normal]
    (s : S₃ →* G)
    (hs : ∀ (k : K) g, Commute (k : G) (s g))
    (P : Subgroup G) (I : Submodule (ZMod 2) V)
    (hI : IsIrrPlus ρ K I)
    (hIP : P ≤ subspaceStabilizer ρ I)
    (hX : ((alternatingGroup (Fin 3)).map s).Normal)
    (hactor : K ⊔ ((alternatingGroup (Fin 3)).map s ⊔ P) = ⊤)
    (hinj : Function.Injective s)
    (hgen : subspaceCommutator ρ ⊤ ((alternatingGroup (Fin 3)).map s) = ⊤) :
    (s cubic)⁻¹ ∈ (alternatingGroup (Fin 3)).map s ∧
      (s cubic)⁻¹ ≠ 1 ∧
      rightConjugate ρ I (s cubic)⁻¹ ≠ I ∧
      I ≤ orbitSpan ρ ⊤ I ∧
      rightConjugate ρ I (s cubic)⁻¹ ≤ orbitSpan ρ ⊤ I ∧
      orbitSpan ρ ⊤ I = I ⊔ rightConjugate ρ I (s cubic)⁻¹ ∧
      Disjoint (I.map (fixedSpace ρ K).mkQ)
        ((rightConjugate ρ I (s cubic)⁻¹).map (fixedSpace ρ K).mkQ) := by
  exact selected_cubic_orbit_of_generation ρ K s hs P I hI hIP hX hactor hinj hgen

/-! The next record is the source orbit contract with the full commutator field
removed.  The quotient-generation field is the only supplement conclusion
consumed by the orbit proof. -/

structure AdequateExternalInputs : Prop where
  component_normal : (K.subgroupOf H).Normal
  centerless : center (Source.starImage H K) = ⊥
  component_rank : primeRank 3 K ≤ 1
  model : Structure.ExternalCarrier (Source.starImage H K)
  solvable : Group.IsSolvable (L₁ ⊔ T : Subgroup G)
  one_twoPerfect : IsPPerfect 2 L₁
  fitting : Components.Fitting.twoFittingResidual H = ⊥ ∨
    Components.Fitting.twoFittingResidual H = X
  cubic_card : Nat.card (Source.starImage H X) = 3
  cubic_normal : (Source.starImage H X).Normal
  embedding : Function.Injective s
  commuting : ∀ (k : Source.starImage H K) g,
    Commute (k : Source.Hstar H) (s g)
  mark : (alternatingGroup (Fin 3)).map s = Source.starImage H X
  cubic_generation : subspaceCommutator ρ ⊤ (Source.starImage H X) = ⊤

variable {𝒦 : GroupClass.{u}}

/-- Construct the complete source orbit conclusion from the adequate quotient
generation.  No proof of `[L₁,T]=L₁` is used. -/
theorem exists_source_orbit_of_full_f918_of_supplement_generation
    (L V : Subgroup G)
    (f : SourceOrbit.F918Hypotheses H K L L₁ T V V₃ V₁ ρ P 𝒦)
    (d : AdequateExternalInputs H K X L₁ T V₃ V₁ ρ s)
    (hactor : Source.starImage H K ⊔
      (Source.starImage H X ⊔ (P : Subgroup (Source.Hstar H))) = ⊤)
    (earlier : SourceOrbit.FullF918Four 𝒦) :
    ∃ I : Submodule (ZMod 2) (SeedAction.Space H V₃ V₁),
      ∃ hI : IsIrrPlusWith ρ (Source.starImage H K) P I,
        ∃ hIP : (P : Subgroup (Source.Hstar H)) ≤ subspaceStabilizer ρ I,
          SourceOrbit.SelectedOrbitConclusion H K X V₃ V₁ ρ P s I hI hIP
            d.commuting 𝒦 := by
  let : (K.subgroupOf H).Normal := d.component_normal
  let : IsQuasisimple (Source.starImage H K) :=
    SourceOrbit.source_quasisimple H K L₁ T V₃ V₁ ρ P L V f
  let : IsMulCommutative (MulAut.Outer (Source.starImage H K)) :=
    externalCarrier_outer_abelian d.model d.centerless
  have hfull := earlier G H K L L₁ T V V₃ V₁ ρ P f
  obtain ⟨I, hI⟩ := exists_homogeneous_of_quasisimple ρ f.faithful
    (Source.starImage H K) P
  obtain ⟨hIP, hIT, hff⟩ := ff_of_fourConclusion ρ
    (Source.starImage H K) P s d.commuting
    (by rw [d.mark]; exact d.cubic_generation) hfull I hI
  have hgen : subspaceCommutator ρ ⊤
      ((alternatingGroup (Fin 3)).map s) = ⊤ := by
    rw [d.mark]
    exact d.cubic_generation
  have hx : ((alternatingGroup (Fin 3)).map s).Normal := by
    rw [d.mark]
    exact d.cubic_normal
  obtain ⟨ht, htne, hmoved, hIW, htW, horbit, hdis⟩ :=
    selected_cubic_orbit_of_supplement_generation ρ
      (Source.starImage H K) s d.commuting P I hI.isIrrPlus hIP hx
      (by rw [d.mark]; exact hactor) d.embedding hgen
  have a : SourceOrbit.ActionImage.SourceHypotheses H K L₁ T V₃ V₁ ρ P I 𝒦 :=
    { conjugation := f.conjugation
      generation := by
        rw [f.generation, f.single_component, f.overlap]
        simp only [sup_assoc]
      sylow_image := f.sylow_image
      sqtk := f.sqtk
      quasisimple := SourceOrbit.source_quasisimple H K L₁ T V₃ V₁ ρ P L V f
      centerless := d.centerless
      selected := hI
      invariant := hIP
      ff := hff }
  let : Finite (centralQuotient ρ (Source.starImage H K) I) :=
    Finite.of_surjective _ (SourceOrbit.ActionImage.projection_surjective ρ
      (Source.starImage H K) I)
  have he := SourceOrbit.selectedMultiplicityEquiv ρ
    (Source.starImage H K) s d.commuting I hI.isIrrPlus (s cubic)⁻¹ horbit hgen
  have htX : (s cubic)⁻¹ ∈ Source.starImage H X := by
    rw [← d.mark]
    exact ht
  have concl : SourceOrbit.SelectedOrbitConclusion H K X V₃ V₁ ρ P s I hI hIP
      d.commuting 𝒦 :=
    ⟨hIT, hff,
      SourceOrbit.ActionImage.quotient_ff ρ
        (Source.starImage H K) P I hI.invariant hIP hI hff,
      htX, htne, hmoved, hIW, htW, horbit, hdis, ⟨he⟩,
      SourceOrbit.ActionImage.source_b4 H K L₁ T V₃ V₁ ρ P I a,
      SourceOrbit.ActionImage.source_b42 H K L₁ T V₃ V₁ ρ P I a⟩
  exact ⟨I, hI, hIP, concl⟩

/-- Orbit assembly with the weaker source supplement calculation exposed at
the natural interface.  The only extra source fact is `L₁ ≤ K ⊔ X`; in the
ordinary case this is immediate, while the covered case can use the explicit
factorization theorem above once its central residual placement is available. -/
theorem exists_source_orbit_of_full_f918_of_component_supplement
    (L V : Subgroup G)
    (f : SourceOrbit.F918Hypotheses H K L L₁ T V V₃ V₁ ρ P 𝒦)
    (d : AdequateExternalInputs H K X L₁ T V₃ V₁ ρ s)
    (hXH : X ≤ H) (hL : L₁ ≤ K ⊔ X)
    (earlier : SourceOrbit.FullF918Four 𝒦) :
    ∃ I : Submodule (ZMod 2) (SeedAction.Space H V₃ V₁),
      ∃ hI : IsIrrPlusWith ρ (Source.starImage H K) P I,
        ∃ hIP : (P : Subgroup (Source.Hstar H)) ≤ subspaceStabilizer ρ I,
          SourceOrbit.SelectedOrbitConclusion H K X V₃ V₁ ρ P s I hI hIP
            d.commuting 𝒦 := by
  have hgen : H = K ⊔ (L₁ ⊔ T) := by
    rw [f.generation, f.single_component, f.overlap]
  apply exists_source_orbit_of_full_f918_of_supplement_generation
    H K X L₁ T V₃ V₁ ρ P s L V f d
    (star_generation_of_component_supplement H K X L₁ T hgen hXH hL
      (P : Subgroup (Source.Hstar H)) f.sylow_image) earlier

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules
