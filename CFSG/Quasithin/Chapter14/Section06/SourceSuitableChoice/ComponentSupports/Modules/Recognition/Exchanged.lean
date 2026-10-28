module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Classification.Sieve.ExchangedNormalizer
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Modules.Recognition.Actors
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Modules.Recognition.Placement
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Modules.ComponentDecomposition

/-!
# Full terminal actor and suitable-support consumers in the exchanged branch

The proved generation Mc=⟨Kᵀ⟩T puts F.9.18's quadratic actor, homogeneous
seed and exhaustion-or-FF alternatives on the original full U/Z. The
component models also supply the full component sum. The actual index-two
component stabilizer and its local normalizer discharge the corresponding
premises in the whole-support U0--U3 application, with W=[U,K].

Natural-module recognition, FF elimination, directness and separation are
still required. The final application retains the explicit ordinary-module
fixed-free input; it is used only in the exchanged L₃(2) branch and imposes
no such condition on the five-dimensional A6 cover. All remaining module
and suitable-vector assembly belongs to qt-e-suitable-component-supports;
original 14.6.18 belongs to qt-e-14625-source and the final suitable source
clauses belong to qt-e-suitable-existence.

Source: Aschbacher--Smith F.9.18, pp.325--326, and 14.6.21--24,
printed pp.1037--1039.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
open Representation.BinaryOffender.Homogeneous Representation.OneCohomology
namespace CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Modules.Recognition
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open Classification Classification.Sieve
open Chapter13.Section08.SourceCompletion.F918
open Chapter13.Section08.CriticalGeometry.Reorientation
variable {G : Type*} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (hsolv : ∀ J ∈ Chapter1.HOver G (T : Set G), Group.IsSolvable J → J ≤ M)
include hG hempty hM hunique hmany hcard e hab hsolv

/-- The original U/Z supplies the faithful quadratic actor and all intermediate-span inputs. -/
theorem terminal_nonnormal_component_span_inputs
    (K : Subgroup G) (hKH : K ≤ Mc) (hK : (K.subgroupOf Mc).IsCComponent)
    (hn : ¬ (K.subgroupOf Mc).Normal) :
    ∃ hU : IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) Mc),
      let _ := hU
      ∃ (a : LocalQuotientAction Mc (conjugateSpanBy (localModule T M) Mc) (centralInvolutions T))
        (B : Subgroup Mc) (I : Submodule (ZMod 2) (Additive
          ((conjugateSpanBy (localModule T M) Mc) ⧸
            (centralInvolutions T).subgroupOf (conjugateSpanBy (localModule T M) Mc)))),
        B ≤ (((sourceResidual M Mc ⊔ (T : Subgroup G)) ⊓ Mc).pCoreIn 2).subgroupOf Mc ∧
        IsIrrPlusWith a.representation
          (componentOrbit (actorImage Mc K) (quotientSylow Mc T (terminal_outside hG T hempty hM hunique hmany hcard e).1.2))
          (quotientSylow Mc T (terminal_outside hG T hempty hM hunique hmany hcard e).1.2) I ∧
        ChapterD.Section03.InternalModuleHypotheses KnownSimple.IsKnownSimple a.representation
          (quotientSylow Mc T (terminal_outside hG T hempty hM hunique hmany hcard e).1.2)
          (componentOrbit (actorImage Mc K) (quotientSylow Mc T (terminal_outside hG T hempty hM hunique hmany hcard e).1.2)) I ∧
        QuadraticMember a.representation (B.map (QuotientGroup.mk' (pCore 2 Mc))) ∧
        B.map (QuotientGroup.mk' (pCore 2 Mc)) ⊓
          centralizer (actorImage Mc (conjugateSpanBy K (T : Subgroup G)) : Set (Mc ⧸ pCore 2 Mc)) = ⊥ ∧
        ∀ X : Subgroup (Mc ⧸ pCore 2 Mc), actorImage Mc K ≤ X → actorImage Mc T ≤ X →
          SpanActorResult a.representation (B.map (QuotientGroup.mk' (pCore 2 Mc))) X I := by
  exact source_component_span_inputs hG T hempty hM hunique hmany hcard e hab hsolv Mc
    (terminal_outside hG T hempty hM hunique hmany hcard e) K hKH hK
    (terminal_nonnormal_generated hG T hempty hM hunique hmany hcard e hab hsolv K hKH hK hn)

/-- F.9.18 now applies to the entire original U/Z in the exchanged branch.
The FF alternatives remain explicit until the diagram-module exclusion. -/
theorem terminal_nonnormal_seed_orbit_exhaustion_or_ff
    (K : Subgroup G) (hKH : K ≤ Mc) (hK : (K.subgroupOf Mc).IsCComponent)
    (hn : ¬ (K.subgroupOf Mc).Normal)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) Mc)]
    (a : LocalQuotientAction Mc (conjugateSpanBy (localModule T M) Mc) (centralInvolutions T))
    (B : Subgroup Mc)
    (hB : B ≤ (((sourceResidual M Mc ⊔ (T : Subgroup G)) ⊓ Mc).pCoreIn 2).subgroupOf Mc)
    (hA : QuadraticMember a.representation (B.map (QuotientGroup.mk' (pCore 2 Mc))))
    {I : Submodule (ZMod 2) (Additive ((conjugateSpanBy (localModule T M) Mc) ⧸
      (centralInvolutions T).subgroupOf (conjugateSpanBy (localModule T M) Mc)))}
    (hI : IsIrrPlusWith a.representation
      (componentOrbit (actorImage Mc K) (quotientSylow Mc T (terminal_outside hG T hempty hM hunique hmany hcard e).1.2))
      (quotientSylow Mc T (terminal_outside hG T hempty hM hunique hmany hcard e).1.2) I) :
    orbitSpan a.representation ⊤ I = subspaceCommutator a.representation ⊤
      (actorImage Mc (conjugateSpanBy K (T : Subgroup G))) ∨
    (IsFFModule (imageRepresentation (seedOrbit a.representation I).toRepresentation) ∧
      IsFFModule (imageRepresentation (seedOrbit a.representation I).quotientRepresentation)) ∨
      IsStrongFFModule (imageRepresentation (seedOrbit a.representation I).toRepresentation) ∨
        IsStrongFFModule (imageRepresentation (seedOrbit a.representation I).quotientRepresentation) := by
  exact source_seed_orbit_exhaustion_or_ff hG T hempty hM hunique hmany hcard e hab hsolv Mc
    (terminal_outside hG T hempty hM hunique hmany hcard e) K hKH hK
    (terminal_nonnormal_generated hG T hempty hM hunique hmany hcard e hab hsolv K hKH hK hn)
    a B hB hA hI

/-- The exchanged branch discharges index two and the local normalizer
in the literal whole-support U0--U3 consumer. Separation and natural-module
fixed-freeness remain with the component-support assembly owner. -/
theorem source_exists_on_exchanged_component_support_of_fixed_free
    (K : Subgroup G) (hKM : K ≤ Mc) (hK : (K.subgroupOf Mc).IsCComponent)
    (hn : ¬ (K.subgroupOf Mc).Normal)
    (hseparate : let W := ⁅conjugateSpanBy (localModule T M) Mc,K⁆
      ∀ t ∈ (T : Subgroup G), t ∉ (T : Subgroup G) ⊓ normalizer (K : Set G) →
        W ⊓ W.map (MulAut.conj t⁻¹).toMonoidHom ≤ centralizer (K : Set G) ∧
        K ≤ normalizer (W.map (MulAut.conj t⁻¹).toMonoidHom : Set G))
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Nontrivial V]
    (τ : Representation (ZMod 2) (Mc ⊓ normalizer (K : Set G) : Subgroup G) V)
    (c : BinaryConjugationSection (Mc ⊓ normalizer (K : Set G))
      ⁅conjugateSpanBy (localModule T M) Mc,K⁆ (centralInvolutions T) τ)
    (hfree : fixed (τ.comp (K.subgroupOf (Mc ⊓ normalizer (K : Set G))).subtype) = ⊥) :
    let h := terminal_hypothesis hG T hempty hM hunique hmany hcard e hab
    ∃ u ∈ ⁅conjugateSpanBy (localModule T M) Mc,K⁆,
      u ^ 2 = 1 ∧ u ≠ 1 ∧
      suitableQuotientCentralizer h u = (T : Subgroup G) ⊓ normalizer (K : Set G) ∧
      Suitable h Mc u := by
  obtain ⟨t,ht,hnt,hprod,hall,hindex⟩ := terminal_nonnormal_component_pair
    hG T hempty hM hunique hmany hcard e hab hsolv K hKM hK hn
  exact source_exists_on_component_support_of_fixed_free
    hG T hempty hM hunique hmany hcard e hab hsolv K hKM hK hindex
    (terminal_nonnormal_sylow_component_normalizer
      hG T hempty hM hunique hmany hcard e hab hsolv K hKM hK hn)
    hseparate τ c hfree

/-- The full component sum of 14.6.23(3) in the exchanged branch,
without a normal-component catalogue premise. Directness still requires the
natural-support recognition. -/
theorem terminal_nonnormal_canonical_component_sum
    (K : Subgroup G) (hKM : K ≤ Mc) (hK : (K.subgroupOf Mc).IsCComponent)
    (hn : ¬ (K.subgroupOf Mc).Normal) :
    let h := terminal_hypothesis hG T hempty hM hunique hmany hcard e hab
    let _ : IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) Mc) :=
      h.UH_elementary_of_V_le_QH ((le_conjugateSpanBy _ _).trans h.UH_le_QH)
    let U := conjugateSpanBy (localModule T M) Mc
    let Z := centralInvolutions T
    ∃ ρ : Representation (ZMod 2) Mc (Additive (U ⧸ Z.subgroupOf U)),
      ∃ c : BinaryConjugationSection Mc U Z ρ,
        (⨆ K : {K : Subgroup Mc // K.IsCComponent},
          c.imageSpace ⁅U, K.val.map Mc.subtype⁆) ⊔ fixed ρ = ⊤ :=
  source_canonical_component_sum_of_models
    hG T hempty hM hunique hmany hcard e hab hsolv
    (source_nonnormal_all_component_models hG T hempty hM hunique hmany hcard e hab hsolv
      Mc (terminal_outside hG T hempty hM hunique hmany hcard e) K hKM hK hn)

end CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Modules.Recognition
