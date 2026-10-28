module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.Realization
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.LinearTwo
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.RankTwo

/-!
# The external FF alternatives on the literal source module

The complete earlier F.9.18(4) implication selects a homogeneous constituent,
its genuine two-conjugate orbit and its faithful central action image.
`Realization` supplies the original actor and quotient maps in the precise
form required by the family deductions. The complete B.4.2 list then excludes
the even-degree unitary family and yields natural L₂ or odd-degree L₃ sections,
or the exceptional marked S₅ × S₃ action on W = [U,K*].

Both natural alternatives contain actual tensor coordinates on the source
sections, central bottom and quotient, and the original Borel marking. L₃
allows either natural orientation independently on each of its two layers.
The exceptional alternative retains the full ambient action on the moved
space; no equality W = U is asserted. The subsequent source endpoint restricts
displacement and quadraticity to W and eliminates this alternative.

These are conditional section-assembly theorems. The parent ExternalModules
assembly must supply the genuine structural and F.9 standing setup, the two
complete earlier classification implications, the source quadratic offender,
the original Borel, the full earlier Fitting alternative, and (for the endpoint)
13.8.18(4), actual conjugation and placement. No selected constituent, specialized
module alternative, faithfulness on W, B-centralization, fixed-space equality
or final external-X contradiction is assumed. The complete 13.8.20 remains
with that parent; existing whole-U conditional APIs remain unchanged.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
13.8.20(a), printed pp.954–955; B.4.2, pp.86–87; F.9.18, pp.325–326.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender InvertedCubicTensor Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
open CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.NoStrong
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections

variable {D U : Type*} [Group D] [AddCommGroup U] [Module (ZMod 2) U]
  (ρ : Representation (ZMod 2) D U) (K : Subgroup D) (s : S₃ →* D)
  (hs : ∀ (k : K) g, Commute (k : D) (s g)) (B₀ : Subgroup D)

/-- A natural L₂ tensor section on the original module, in the original Borel marking.
Both field parities are retained. -/
def LinearTwoSections : Prop :=
  ∃ F : BinaryField, 1 < F.degree ∧ ∃ e : K ≃* SL(2,F.Carrier),
    (B₀.subgroupOf K).map e.toMonoidHom = Matrix.SpecialLinearGroup.rankOneBorel F.Carrier ∧
    ∃ C W : Subrepresentation ρ,
      C.toSubmodule ≤ Representation.invariants (ρ.comp K.subtype) ∧
      (∀ (g : K) (v : U), ρ g v - v ∈ W.toSubmodule) ∧
      Nonempty (NaturalLayers.TensorLayer (ρ.comp K.subtype) (linearNatural F 2) e
        C.toSubmodule W.toSubmodule)

/-- One or two independently oriented natural L₃ tensor sections under the same
original Borel marking, with central bottom and top quotient. -/
def LinearThreeSections : Prop :=
  ∃ F : BinaryField, 1 < F.degree ∧ ∃ ho : Odd F.degree,
    ∃ e : K ≃* PSL(3,F.Carrier),
      (B₀.subgroupOf K).map e.toMonoidHom = Matrix.PSL3.LinearThree.borel F.Carrier ∧
      ∃ C W : Subrepresentation ρ,
        C.toSubmodule ≤ Representation.invariants (ρ.comp K.subtype) ∧
        IsProjectiveNaturalOrDual ho F.card_eq
          (RankTwo.projectiveMultiplicity ρ K.subtype s hs e C W) ∧
        Nonempty (NaturalLayers.TensorLayer (ρ.comp K.subtype)
          (RankTwo.projectiveMultiplicity ρ K.subtype s hs e C W) e C.toSubmodule W.toSubmodule) ∧
        ((∀ (k : K) v, ρ k v - v ∈ W.toSubmodule) ∨
          ∃ D : Subrepresentation ρ,
            IsProjectiveNaturalOrDual ho F.card_eq
              (RankTwo.projectiveMultiplicity ρ K.subtype s hs e W D) ∧
            Nonempty (NaturalLayers.TensorLayer (ρ.comp K.subtype)
              (RankTwo.projectiveMultiplicity ρ K.subtype s hs e W D) e W.toSubmodule D.toSubmodule) ∧
            ∀ (k : K) v, ρ k v - v ∈ D.toSubmodule)

/-- The adequate exceptional alternative retains the actual moved module, with
full marked ambient action on it. It makes no assertion that W equals U. -/
def MovedFiveSection : Prop :=
  ∃ W : Subrepresentation ρ, W.toSubmodule = subspaceCommutator ρ ⊤ K ∧
    Nonempty (LinearTwo.FiveReconstruction.FullCoordinates W.toRepresentation K s)

universe u
variable {G : Type u} [Group G] [Finite G]
    {𝒦 : GroupClass.{u}}
    (H K X L L₁ L₁plus V V₃ V₁ : Subgroup G) (T : Sylow 2 G)
    [(X.subgroupOf H).Normal] [(Source.starImage H K).Normal]
    [(V₁.subgroupOf (Source.UH H V₃)).Normal]
    [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]
    (ρ : Representation (ZMod 2) (Source.Hstar H) (SeedAction.Space H V₃ V₁))
    (P : Sylow 2 (Source.Hstar H)) (s : S₃ →* Source.Hstar H)
    (f : SourceOrbit.F918Hypotheses H K L L₁ (T : Subgroup G) V V₃ V₁ ρ P 𝒦)
    (d : SourceOrbit.ExternalInputs H K X L₁ (T : Subgroup G) V₃ V₁ ρ s)
    (hlocal : (Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∧ X = L₁) ∨
      (SolvableExclusion.IsTripleCoverSix (L ⧸ pCore 2 L) ∧ X = L₁plus))
    (hfit : SolvableExclusion.ResidualAlternative L L₁ L₁plus
      (Components.Fitting.twoFittingResidual H))
    (hF918 : SourceOrbit.FullF918Four 𝒦) (hB42 : FullB42.{u,u} 𝒦)
    (A : Subgroup (Source.Hstar H)) (hA : IsElementaryTwo A)
    (hAquad : IsQuadratic ρ A) (hbound : fixedCodim ρ A ≤ 2 * rank A)
    (hAfaith : A ⊓ centralizer (Source.starImage H K : Set (Source.Hstar H)) = ⊥)
    (S : Sylow 2 (Source.starImage H K)) (B₀ : Subgroup (Source.Hstar H))
    (hB : B₀.subgroupOf (Source.starImage H K) = normalizer (S : Set (Source.starImage H K)))

include f d hlocal hfit hB42 hA hAquad hbound hAfaith hB in
private theorem alternatives_of_realized
    {E N : Type u} [Group E] [Finite E] [AddCommGroup N] [Module (ZMod 2) N] [Finite N]
    (σ : Representation (ZMod 2) E N) (hσ : B4Hypotheses 𝒦 σ) (hff : IsFFModule σ)
    (r : LinearTwo.FiveReconstruction.ConstituentRealization ρ (Source.starImage H K) σ
      (generalizedFitting E))
    (W : Subrepresentation ρ)
    (hactor : r.actor = Source.starImage H K ⊔ Source.starImage H (T : Subgroup G))
    (hne : r.space ≠ r.space.map (ρ (s cubic)))
    (horbit : W.toSubmodule = r.space ⊔ r.space.map (ρ (s cubic)))
    (a : N ≃ₗ[ZMod 2]
      SectionMultiplicity ρ s (LinearTwo.centralBottom ρ (Source.starImage H K) W) W)
    (ha : ∀ (k : Source.starImage H K) v,
      a (σ (r.component k) v) = sectionMultiplicityAction ρ (Source.starImage H K).subtype
        s d.commuting (LinearTwo.centralBottom ρ (Source.starImage H K) W) W k (a v)) :
    (LinearTwoSections ρ (Source.starImage H K) B₀ ∨
      LinearThreeSections ρ (Source.starImage H K) s d.commuting B₀) ∨
      MovedFiveSection ρ (Source.starImage H K) s := by
  let Ks := Source.starImage H K
  let : (K.subgroupOf H).Normal := d.component_normal
  let : Group.IsSolvable (L₁ ⊔ (T : Subgroup G) : Subgroup G) := d.solvable
  let : IsQuasisimple Ks := SourceOrbit.source_quasisimple H K L₁ (T : Subgroup G)
    V₃ V₁ ρ P L V f
  have hK : IsComponent (Source.Hstar H) Ks := ⟨(inferInstance : Ks.Normal).isSubnormal, inferInstance⟩
  have hgen : H = K ⊔ L₁ ⊔ (T : Subgroup G) := by
    rw [f.generation, f.single_component, f.overlap, sup_assoc]
  cases d.model with
  | linearTwo n hn iso =>
    obtain ⟨F, _, _, hcard, ⟨eK⟩⟩ := iso
    let := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using hcard)
    have ha' : ∀ k v,
        a.symm (sectionMultiplicityAction ρ Ks.subtype s d.commuting
          (LinearTwo.centralBottom ρ Ks W) W k v) = σ (r.component k) (a.symm v) := by
      intro k v
      apply a.injective
      rw [a.apply_symm_apply, ha, a.apply_symm_apply]
    obtain ⟨_, _, _, hmoved, hcase⟩ := LinearTwo.source_layer_or_moved_coordinates hB42
      H K X L L₁ L₁plus V₃ V₁ T f.sqtk hgen hlocal hfit hK n hn hcard eK
      ρ f.conjugation f.faithful s d.embedding d.commuting d.mark d.cubic_generation
      σ hσ hff r hactor W hne horbit a.symm ha'
      A hA hAquad hbound hAfaith S B₀ hB
    rcases hcase with ⟨F', hdeg, e, hBe, hc, hq, layer⟩ | ⟨_, c⟩
    · exact Or.inl (Or.inl ⟨F', by simpa only [hdeg] using hn, e, hBe,
        LinearTwo.centralBottom ρ Ks W, W, hc, hq, layer⟩)
    · exact Or.inr ⟨W, hmoved, c⟩
  | linearThree n hn ho iso =>
    obtain ⟨F, _, _, hcard, ⟨eK⟩⟩ := iso
    let := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using hcard)
    let : Algebra (ZMod 2) F := ZMod.algebra _ _
    let B : BinaryField := { Carrier := F, degree := n, degree_pos := by omega, card_eq := hcard }
    have ha' : ∀ (k : generalizedFitting E) v,
        a (σ k v) = sectionMultiplicityAction ρ Ks.subtype s d.commuting
          (LinearTwo.centralBottom ρ Ks W) W (r.component.symm k) (a v) := by
      intro k v
      simpa only [r.component.apply_symm_apply] using ha (r.component.symm k) v
    obtain ⟨_, e, hBe, layers⟩ := RankTwo.source_natural_sections hB42
      H K X L L₁ L₁plus V₃ V₁ T f.sqtk hgen hlocal hfit hK
      n hn ho hcard eK ρ f.conjugation s d.embedding d.commuting d.mark d.cubic_generation
      σ hσ hff r hactor W hne horbit a ha'
      A hA hAquad hbound hAfaith S B₀ hB
    exact Or.inl (Or.inr ⟨B, hn, ho, e, hBe,
      RankTwo.oneOrTwo_tensor_layers ρ Ks.subtype s d.commuting e ho hcard layers
        (by rw [d.mark]; exact d.cubic_generation)⟩)
  | unitaryThree n hn he iso =>
    obtain ⟨F, _, _, J, hcard, hconj, ⟨eK⟩⟩ := iso
    have hcard' : Nat.card F = 2 ^ (2 * n) := by
      rw [hcard, ← pow_mul, Nat.mul_comm n 2]
    exact (RankTwo.unitary_not_ff σ hB42 hσ J (by omega) he hcard' hconj
      (r.component.symm.trans eK) hff).elim

include f d hlocal hfit hF918 hB42 hA hAquad hbound hAfaith hB in
/-- The external FF module alternatives from the complete earlier F.9.18(4)
and B.4.2 implications. The constituent, faithful action image, actual orbit,
central quotient and multiplicity maps are all constructed. The unitary branch
is excluded, while the exceptional alternative uses only the moved module.
The parent's genuine structural, offender and Borel inputs remain explicit. -/
theorem source_alternatives :
    (LinearTwoSections ρ (Source.starImage H K) B₀ ∨
      LinearThreeSections ρ (Source.starImage H K) s d.commuting B₀) ∨
      MovedFiveSection ρ (Source.starImage H K) s := by
  let Ks := Source.starImage H K
  let : IsQuasisimple Ks := SourceOrbit.source_quasisimple H K L₁ (T : Subgroup G)
    V₃ V₁ ρ P L V f
  obtain ⟨I, hI, hIP, o⟩ := SourceOrbit.exists_source_orbit_of_full_f918
    H K X L₁ (T : Subgroup G) V₃ V₁ ρ P s L V f d hF918
  let τ := SourceOrbit.ActionImage.centralAction ρ Ks P I hI.invariant hIP
  let σ := imageRepresentation τ
  let r := Realization.constituent ρ Ks P I hI hIP d.centerless
  let W := SourceOrbit.selectedOrbitUpper ρ I
  let : Finite (centralQuotient ρ Ks I) :=
    Finite.of_surjective _ (SourceOrbit.ActionImage.projection_surjective ρ Ks I)
  obtain ⟨a₀⟩ := o.multiplicity
  let a := Realization.multiplicityCoordinates ρ Ks P I hI s d.commuting a₀
  have ha : ∀ (k : Ks) v,
      a (σ (r.component k) v) = sectionMultiplicityAction ρ Ks.subtype s d.commuting
        (LinearTwo.centralBottom ρ Ks W) W k (a v) :=
    Realization.multiplicityCoordinates_equivariant
      ρ Ks P I hI hIP d.centerless s d.commuting a₀
  have hactor : r.actor = Ks ⊔ Source.starImage H (T : Subgroup G) := by
    change Ks ⊔ (P : Subgroup (Source.Hstar H)) = _
    rw [f.sylow_image]
  have hne : r.space ≠ r.space.map (ρ (s cubic)) := by
    intro he
    apply o.conjugate_ne
    change I = I.map (ρ (s cubic)) at he
    simpa only [rightConjugate, inv_inv] using he.symm
  have horbit : W.toSubmodule = r.space ⊔ r.space.map (ρ (s cubic)) := by
    change orbitSpan ρ ⊤ I = I ⊔ I.map (ρ (s cubic))
    simpa only [rightConjugate, inv_inv] using o.orbit
  exact alternatives_of_realized H K X L L₁ L₁plus V V₃ V₁ T ρ P s f d
    hlocal hfit hB42 A hA hAquad hbound hAfaith S B₀ hB
    σ o.b4 o.central_ff r W hactor hne horbit a ha

include f d hlocal hfit hF918 hB42 hA hAquad hbound hAfaith hB in
/-- The adequate exceptional exclusion leaves precisely the natural L₂/L₃
sections for `ExternalModules.Natural`. The earlier rank implication, actual
H-conjugation, placement and quadraticity are supplied by final source assembly;
faithfulness on the moved space and absence of transvections on U are proved. -/
theorem source_natural_alternatives
    (Vγ Vα T₀ : Subgroup G)
    (earlier_13_8_18_4 : SeedAction.IsConjugation H V₃ V₁ ρ →
      H = K ⊔ L₁ ⊔ (T : Subgroup G) →
      (∀ g, Module.finrank (ZMod 2) (LinearMap.range (ρ g - LinearMap.id)) ≠ 1) →
      1 < rank (Source.starImage H Vγ))
    (hVγH : Vγ ≤ H) (h : H)
    (hconj : Vγ.map (MulAut.conj (h : G)).toMonoidHom = Vα)
    (hplace : Source.starImage H Vα ≤ Source.starImage H T₀)
    (hcore : Source.starImage H T₀ =
      (Source.starImage H L₁ ⊔ Source.starImage H (T : Subgroup G)).pCoreIn 2)
    (hT₀K : Source.starImage H T₀ ≤ Source.starImage H K)
    (hquad : IsQuadratic ρ (Source.starImage H Vγ)) :
    LinearTwoSections ρ (Source.starImage H K) B₀ ∨
      LinearThreeSections ρ (Source.starImage H K) s d.commuting B₀ := by
  rcases source_alternatives H K X L L₁ L₁plus V V₃ V₁ T ρ P s f d hlocal hfit
    hF918 hB42 A hA hAquad hbound hAfaith S B₀ hB with hnat | ⟨W, _, ⟨c⟩⟩
  · exact hnat
  · have hgen : H = K ⊔ L₁ ⊔ (T : Subgroup G) := by
      rw [f.generation, f.single_component, f.overlap, sup_assoc]
    exact (LinearTwo.FiveReconstruction.tensor_branch_impossible_on_moved
      H K L₁ V₃ V₁ Vγ Vα T₀ T ρ s W f.conjugation hgen c earlier_13_8_18_4
      hVγH h hconj hplace hcore hT₀K hquad).elim

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections
