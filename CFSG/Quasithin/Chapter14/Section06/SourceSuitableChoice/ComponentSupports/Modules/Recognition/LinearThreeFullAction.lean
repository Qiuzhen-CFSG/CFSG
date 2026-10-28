module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Modules.Recognition.LinearThreeQuadraticCovers
public import Theory.Representation.BinaryOffender.HomogeneousOrbitAction
public import Theory.Representation.SLThreeCentralExtension.PairedQuadratic

/-!
# Full component actions on the original central-cover orbit

The detecting quadratic actor constructed on the original U/Z induces
inner automorphisms of the chosen component. The full homogeneous-orbit
kernel theorem turns this into equality of actions on the entire orbit,
including any central covering lines. Thus the actual component action is
faithful and has quadratic ratio at most two, without a splitting premise.

These are the full-module inputs to the paired-cover obstruction in14.6.22.
The cover exclusion, full support exhaustion and final suitable-vector
assembly remain with qt-e-suitable-component-supports. Original14.6.18 is
the explicit hsolv premise, discharged by qt-e-14625-source.
Source: Aschbacher--Smith A.1.41, F.9.18(2),14.6.22, pp.31,325,1038.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
open Representation.BinaryOffender.Homogeneous
namespace CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Modules.Recognition
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open Classification Classification.Sieve
open Chapter13.Section08.SourceCompletion.F918
open Chapter13.Section08.CriticalGeometry.Reorientation
open Chapter13.Section08.Components.SourceModels
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


/-- The actual component has a faithful action of quadratic ratio at most
two on a natural central-cover orbit in the original terminal U/Z. -/
theorem terminal_nonnormal_full_component_action
    (K : Subgroup G) (hKM : K ≤ Mc) (hK : (K.subgroupOf Mc).IsCComponent)
    (hn : ¬ (K.subgroupOf Mc).Normal) :
    ∃ hU : IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) Mc),
      let _ := hU
      ∃ a : LocalQuotientAction Mc (conjugateSpanBy (localModule T M) Mc) (centralInvolutions T),
      ∃ (I : Submodule (ZMod 2) (Additive ((conjugateSpanBy (localModule T M) Mc) ⧸
        (centralInvolutions T).subgroupOf (conjugateSpanBy (localModule T M) Mc))))
        (hI : IsIrrPlusWith a.representation (actorImage Mc K)
          (actorImage Mc T ⊓ normalizer (actorImage Mc K : Set (Mc ⧸ pCore 2 Mc))) I),
      Nonempty (ChapterB.QuasisimpleSource.ActionEquiv
        (centralQuotientRepresentation a.representation (actorImage Mc K) I hI.isIrrPlus.choose)
        (ChapterB.QuasisimpleSource.linearNatural ChapterB.QuasisimpleSource.BinaryField.two 3)) ∧
      let O := orbitSpan a.representation
        (actorImage Mc T ⊓ normalizer (actorImage Mc K : Set (Mc ⧸ pCore 2 Mc))) I
      let σ := (invariantSubspace a.representation (actorImage Mc K) O
        (orbitSpan_component_invariant a.representation hI.normalizes hI.isIrrPlus)).toRepresentation
      Function.Injective σ ∧ quadraticRatio σ ≤ 2 ∧
      ∃ (C : Subgroup (Mc ⧸ pCore 2 Mc)),
        C ≤ actorImage Mc T ⊓ normalizer (actorImage Mc K : Set (Mc ⧸ pCore 2 Mc)) ∧
        ¬ C ≤ centralizer (actorImage Mc K : Set (Mc ⧸ pCore 2 Mc)) ∧
        C ∈ ChapterD.RPlusBound a.representation 2 ∧ IsQuadratic a.representation C ∧
        (C.comap (QuotientGroup.mk' (pCore 2 Mc))).map Mc.subtype ≤
          normalizer ((originalSection a).subspacePreimage I : Set G) ∧
        ∃ f : (actorImage Mc K ⊔ C : Subgroup (Mc ⧸ pCore 2 Mc)) →* actorImage Mc K,
          (∀ k : actorImage Mc K, f (inclusion le_sup_left k) = k) ∧
          ∀ g v, v ∈ O → a.representation g.val v = a.representation (f g).val v := by
  obtain ⟨hU,a,I,hI,⟨b⟩,C,hCP,hnC,hC,hqC,_,hO,hqO,hN,hi⟩ :=
    terminal_nonnormal_stable_central_cover hG T hempty hM hunique hmany hcard e hab hsolv
      K hKM hK hn
  let := hU
  let : Module.Finite (ZMod 2) (Additive ((conjugateSpanBy (localModule T M) Mc) ⧸
    (centralInvolutions T).subgroupOf (conjugateSpanBy (localModule T M) Mc))) := Module.Finite.of_finite
  have hout := terminal_outside hG T hempty hM hunique hmany hcard e
  have hD := source_quotient_component hG T hempty hM hunique hmany hcard e hab hsolv
    Mc hout K hKM hK
  let : IsQuasisimple (actorImage Mc K) := hD.2
  let j : actorImage Mc K ≃* BinaryLinearThree.Group := b.groupEquiv
  have hz : center (actorImage Mc K) = ⊥ := by
    apply bot_unique
    intro k hk
    have hh := (centerCongr j ⟨k,hk⟩).property
    change j k ∈ center BinaryLinearThree.Group at hh
    rw [show center BinaryLinearThree.Group = ⊥ from Matrix.PSL3Two.center_eq_bot,mem_bot] at hh
    exact j.injective (hh.trans j.map_one.symm)
  let P := actorImage Mc T ⊓ normalizer (actorImage Mc K : Set (Mc ⧸ pCore 2 Mc))
  have hP : IsPGroup 2 P := (quotientSylow Mc T hout.1.2).isPGroup'.of_injective
    (inclusion (show P ≤ (quotientSylow Mc T hout.1.2 : Subgroup (Mc ⧸ pCore 2 Mc)) from inf_le_left))
    (inclusion_injective _)
  refine ⟨hU,a,I,hI,⟨b⟩,orbit_component_faithful a.representation hz hP hI,
    (orbit_component_quadraticRatio_le a.representation hz hP hI hCP hi hO).trans hqO,
    C,hCP,hnC,hC,hqC,hN,?_⟩
  exact orbit_inner_actor_map a.representation hz hP hI hCP hi


/-- On the actual selected terminal orbit, two nonsplit natural/dual
four-dimensional covers with at most a central-line intersection are
impossible. Constructing the literal pair marking remains the next step
in the source support assembly. -/
theorem terminal_nonnormal_paired_cover_obstruction
    (K : Subgroup G) (hKM : K ≤ Mc) (hK : (K.subgroupOf Mc).IsCComponent)
    (hn : ¬ (K.subgroupOf Mc).Normal) :
    ∃ hU : IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) Mc),
      let _ := hU
      ∃ a : LocalQuotientAction Mc (conjugateSpanBy (localModule T M) Mc) (centralInvolutions T),
      ∃ (I : Submodule (ZMod 2) (Additive ((conjugateSpanBy (localModule T M) Mc) ⧸
        (centralInvolutions T).subgroupOf (conjugateSpanBy (localModule T M) Mc))))
        (hI : IsIrrPlusWith a.representation (actorImage Mc K)
          (actorImage Mc T ⊓ normalizer (actorImage Mc K : Set (Mc ⧸ pCore 2 Mc))) I)
        (b : ChapterB.QuasisimpleSource.ActionEquiv
          (centralQuotientRepresentation a.representation (actorImage Mc K) I hI.isIrrPlus.choose)
          (ChapterB.QuasisimpleSource.linearNatural ChapterB.QuasisimpleSource.BinaryField.two 3)),
      let O := orbitSpan a.representation
        (actorImage Mc T ⊓ normalizer (actorImage Mc K : Set (Mc ⧸ pCore 2 Mc))) I
      let σ := (invariantSubspace a.representation (actorImage Mc K) O
        (orbitSpan_component_invariant a.representation hI.normalizes hI.isIrrPlus)).toRepresentation
      let τ := σ.comp b.groupEquiv.symm.toMonoidHom
      quadraticRatio τ ≤ 2 ∧
      ∀ (U V : Subrepresentation τ)
        (p : U.toRepresentation.IntertwiningMap BinaryLinearThree.W)
        (q : V.toRepresentation.IntertwiningMap BinaryLinearThree.W.dual),
        Representation.OneCohomology.IsCover p → Representation.OneCohomology.IsCover q →
        Module.finrank (ZMod 2) U.toSubmodule = 4 →
        Module.finrank (ZMod 2) V.toSubmodule = 4 →
        Module.finrank (ZMod 2) ↥(U.toSubmodule ⊓ V.toSubmodule) ≤ 1 → False := by
  have hh := terminal_nonnormal_full_component_action
    hG T hempty hM hunique hmany hcard e hab hsolv K hKM hK hn
  rcases hh with ⟨hU,hh⟩
  let := hU
  rcases hh with ⟨a,I,hI,hb,hh⟩
  rcases hb with ⟨b⟩
  obtain ⟨_,hsmall,_⟩ := hh
  let : Module.Finite (ZMod 2) (Additive ((conjugateSpanBy (localModule T M) Mc) ⧸
    (centralInvolutions T).subgroupOf (conjugateSpanBy (localModule T M) Mc))) := Module.Finite.of_finite
  let O := orbitSpan a.representation
    (actorImage Mc T ⊓ normalizer (actorImage Mc K : Set (Mc ⧸ pCore 2 Mc))) I
  let σ := (invariantSubspace a.representation (actorImage Mc K) O
    (orbitSpan_component_invariant a.representation hI.normalizes hI.isIrrPlus)).toRepresentation
  let τ := σ.comp b.groupEquiv.symm.toMonoidHom
  have hq : quadraticRatio τ ≤ 2 :=
    (quadraticRatio_le_of_injective_equivariant σ τ b.groupEquiv.toMonoidHom
      b.groupEquiv.injective (LinearEquiv.refl _ _) (by
        intro k v
        change σ k v = σ (b.groupEquiv.symm (b.groupEquiv k)) v
        rw [b.groupEquiv.symm_apply_apply])).trans hsmall
  refine ⟨hU,a,I,hI,b,hq,?_⟩
  intro U V p q hp hq' hdimU hdimV hint
  exact Representation.OneCohomology.SLThreeCentralExtension.not_small_quadraticRatio_of_paired_covers
    τ U V p hp q hq' hdimU hdimV hint hq

end CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Modules.Recognition
