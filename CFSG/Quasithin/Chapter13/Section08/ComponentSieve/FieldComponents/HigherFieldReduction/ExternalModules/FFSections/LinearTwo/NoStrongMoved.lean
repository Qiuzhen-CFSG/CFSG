module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.LinearTwo.NoStrongMoved.NoFF
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.SeedAction
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Fitting
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Sections
/-!
# The external L₂ no-strong and moved-space argument

For the literal source action on U_H/V₁, the normal cubic subgroup and the
small Fitting residual give faithful noncentral section actions. The PSL₂
irreducible reduction excludes strong FF-offenders on the actual KT action
and on its relevant faithful section images. The cubic full-moved-space
argument also excludes the two-FF branch of F.9.18(6), leaving exactly
W = [U_H/V₁,K*]. In particular neither non-FF nor this equality is an input.

The final theorem retains the actual conjugation action, PSL₂ isomorphism,
commuting S₃ marking and the genuine H-orbit of an Irr⁺ constituent. It works
for every such orbit; the SourceOrbit input's additional T-invariance, FF
identification and compatible two-conjugate coordinates are not needed for
this stronger intermediate conclusion. Section faithfulness is on H* itself,
then restricted to KT; no step infers O₂(KT) = 1 from O₂(H*) = 1.

The two remaining universal inputs are the complete B.4.2 action list
`FullB42` and the complete B.1.5(3) implication `FullIrrInvariance`. The latter
is the boundary to be discharged by the B.1 irreducible-invariance owner.
The source setup and earlier F.9.18(2) ratio-two witness remain explicit for
the final external-L₂ assembly owner.

Source: Aschbacher–Smith, 13.8.20(a), printed p.954; B.1.5(3), pp.69–70;
B.4.2, p.86; F.9.18(6), pp.325–326, combined manuscript of 1 March 2004.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory InvertedCubicTensor
open scoped MatrixGroups IsMulCommutative
open CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.NoStrong
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.LinearTwo.NoStrongMoved
universe u v w
private def imageEquivOfFaithful
    {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (hf : Function.Injective ρ) :
    D ≃* actionImage ρ :=
  MulEquiv.ofBijective (actionHom ρ)
    ⟨fun _ _ h => hf (congrArg (imageRepresentation ρ) h),
      ρ.asGroupHom.rangeRestrict_surjective⟩

private theorem imageEquivOfFaithful_symm_action
    {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (hf : Function.Injective ρ)
    (g : actionImage ρ) (v : V) :
    imageRepresentation ρ g v = ρ ((imageEquivOfFaithful ρ hf).symm g) v := by
  obtain ⟨x,rfl⟩ := ρ.asGroupHom.rangeRestrict_surjective g
  change ρ x v = ρ ((imageEquivOfFaithful ρ hf).symm (imageEquivOfFaithful ρ hf x)) v
  rw [MulEquiv.symm_apply_apply]

private theorem ff_of_image
    {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (hf : Function.Injective ρ)
    (h : IsFFModule (imageRepresentation ρ)) : IsFFModule ρ :=
  h.map_equivariant (imageRepresentation ρ) ρ
    (imageEquivOfFaithful ρ hf).symm.toMonoidHom
    (imageEquivOfFaithful ρ hf).symm.injective (LinearEquiv.refl _ _)
    (imageEquivOfFaithful_symm_action ρ hf)

private theorem strong_of_image
    {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (hf : Function.Injective ρ)
    (h : IsStrongFFModule (imageRepresentation ρ)) : IsStrongFFModule ρ :=
  CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.FFExclusions.strongFF_map_equivariant
    (imageRepresentation ρ) ρ (imageEquivOfFaithful ρ hf).symm.toMonoidHom
    (imageEquivOfFaithful ρ hf).symm.injective (LinearEquiv.refl _ _)
    (imageEquivOfFaithful_symm_action ρ hf) h

variable {D : Type u} [Group D] [Finite D] (K X : Subgroup D)
    [K.Normal] [X.Normal] [IsQuasisimple K]
    {𝒦 : GroupClass.{u}} (hB42 : FullB42.{u,v} 𝒦)
    (hInv : FullIrrInvariance.{u,v})
    {F : Type w} [Field F] [Finite F] [CharP F 2]
    (e : K ≃* PSL(2,F)) (hS : IsSQTK 𝒦 D)
    (hx : Nat.card X = 3)
    (hc : centralizer (K : Set D) ⊓ centralizer (X : Set D) ≤ X)
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (ρ : Representation (ZMod 2) D V)
    (s : S₃ →* D) (hs : ∀ (k : K) g, Commute (k : D) (s g))
    (hmark : (alternatingGroup (Fin 3)).map s = X)
    (hg : subspaceCommutator ρ ⊤ X = ⊤)

omit [Finite D] [X.Normal] in
include hmark in
private theorem cubic_mem : s cubic ∈ X := by
  rw [← hmark]
  exact mem_map_of_mem s (show cubic ∈ alternatingGroup (Fin 3) from by change Equiv.Perm.sign cubic = 1; decide +kernel)

omit [Finite D] [K.Normal] [X.Normal] [IsQuasisimple K] in
include hmark hs in
private theorem component_centralizes_cubic : K ≤ centralizer (X : Set D) := by
  intro k hk x hx
  rw [← hmark] at hx
  obtain ⟨g,_,rfl⟩ := hx
  exact (hs ⟨k,hk⟩ g).symm.eq

include hB42 hInv e hS hx hc hg in
/-- The actual restricted KT action has no strong FF-offender. This proof
permits a nontrivial O₂(KT); its cubic action is inherited from H. -/
theorem no_strong_restriction (hf : Function.Injective ρ) (E : Subgroup D) :
    ¬ IsStrongFFModule (ρ.comp E.subtype) := by
  intro h
  apply no_strong_cubic K X hB42 hInv e hS hx hc ρ hf hg
  exact CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.FFExclusions.strongFF_map_equivariant
    (ρ.comp E.subtype) ρ E.subtype E.subtype_injective
    (LinearEquiv.refl _ _) (fun _ _ => rfl) h

include hB42 hInv e hS hx hc hg hmark in
/-- Every literal noncentral invariant section is faithful, and its faithful
image after restriction to KT has no strong FF-offender. -/
theorem section_faithful_no_strong (C W : Subrepresentation ρ) (E : Subgroup D)
    (hn : ¬ ∀ k ∈ K, ∀ v, sectionRepresentation ρ C W k v = v) :
    Function.Injective (sectionRepresentation ρ C W) ∧
      ¬ IsStrongFFModule (imageRepresentation ((sectionRepresentation ρ C W).comp E.subtype)) := by
  let σ := sectionRepresentation ρ C W
  let : Finite (W.toSubmodule ⧸ (sectionLower ρ C W).toSubmodule) :=
    Finite.of_surjective _ (Submodule.mkQ_surjective _)
  have hfree := section_fixedFree ρ s C W (by rw [hmark]; exact hg)
  have hf := faithful_of_cubic K X hx hc σ hn (s cubic) (cubic_mem X s hmark) hfree
  refine ⟨hf, ?_⟩
  have hfull := full_of_fixedFree X σ (s cubic) (cubic_mem X s hmark) hfree
  exact fun h => no_strong_restriction K X hB42 hInv e hS hx hc σ hfull hf E
    (strong_of_image _ (hf.comp E.subtype_injective) h)

include hB42 hInv e hS hx hc hg hmark hs in
/-- All alternatives of F.9.18(6) are discharged. In particular, the two-FF
branch is contradicted by the proved cubic full-moved-space exclusion. -/
theorem moved_space (W : Subrepresentation ρ)
    (hW : W.toSubmodule ≠ ⊥)
    (hfull : subspaceCommutator ρ W.toSubmodule K = W.toSubmodule)
    (A : Subgroup D) (hA : IsElementaryTwo A)
    (hbound : fixedCodim ρ A ≤ 2 * rank A)
    (hfaith : A ⊓ centralizer (K : Set D) = ⊥) :
    W.toSubmodule = subspaceCommutator ρ ⊤ K := by
  have hxmem := cubic_mem X s hmark
  have hfree := ambient_fixedFree_of_commutator ρ s (by rw [hmark]; exact hg)
  have hwfree := fixedFree_of_injective (ρ.comp s) (W.toRepresentation.comp s)
    W.toSubmodule.subtype W.toSubmodule.subtype_injective (fun _ => rfl) hfree
  have hwfull := full_of_fixedFree X W.toRepresentation (s cubic) hxmem hwfree
  have hnW := subrepresentation_action_nontrivial ρ W K hW hfull
  have hfW := faithful_of_cubic K X hx hc W.toRepresentation hnW (s cubic) hxmem hwfree
  have hqfree := fixedFree_of_surjective (ρ.comp s) (W.quotientRepresentation.comp s)
    W.toSubmodule.mkQ W.toSubmodule.mkQ_surjective (fun _ => rfl) hfree
  let : Finite (V ⧸ W.toSubmodule) := Finite.of_surjective _ W.toSubmodule.mkQ_surjective
  have hqfull := full_of_fixedFree X W.quotientRepresentation (s cubic) hxmem hqfree
  by_contra hne
  have hnQ := quotient_action_nontrivial ρ W K hfull hne
  have hfQ := faithful_of_cubic K X hx hc W.quotientRepresentation hnQ (s cubic) hxmem hqfree
  rcases faithful_image_ff_alternative_of_quasisimple ρ W K A hA hbound hfaith hW hfull
    with he | ⟨hwff,_⟩ | hwstrong | hqstrong
  · exact hne he
  · have hKW : subspaceCommutator W.toRepresentation ⊤ K = ⊤ := by
      apply Submodule.map_injective_of_injective W.toSubmodule.subtype_injective
      have he := subspaceCommutator_map_embedding ρ W.toRepresentation (MonoidHom.id D)
        W.toSubmodule.subtype (fun _ _ => rfl) K ⊤
      simpa only [Submodule.map_top, Submodule.range_subtype, Subgroup.map_id, hfull] using he.symm
    exact not_ff_cubic_full K X hB42 hInv e hS hx hc
      (component_centralizes_cubic K X s hs hmark) W.toRepresentation hfW s hs hmark hwfull hnW hKW
      (ff_of_image _ hfW hwff)
  · exact no_strong_cubic K X hB42 hInv e hS hx hc W.toRepresentation hfW hwfull
      (strong_of_image _ hfW hwstrong)
  · exact no_strong_cubic K X hB42 hInv e hS hx hc W.quotientRepresentation hfQ hqfull
      (strong_of_image _ hfQ hqstrong)
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.LinearTwo.NoStrongMoved

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.LinearTwo.NoStrongMoved

private theorem solvable_centralizer_of_supplement {D : Type*} [Group D]
    (K P : Subgroup D) [K.Normal] [Group.IsSolvable P]
    (hg : K ⊔ P = ⊤) (hz : center K = ⊥) :
    Group.IsSolvable (centralizer (K : Set D)) := by
  let q := QuotientGroup.mk' K
  have hmap : P.map q = ⊤ := by
    have he := congrArg (map q) hg
    simpa only [q, Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq,
      map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] using he
  have hf : Function.Surjective (q.comp P.subtype) := by
    intro y
    have hy : y ∈ P.map q := by rw [hmap]; trivial
    obtain ⟨p,hp,he⟩ := hy
    exact ⟨⟨p,hp⟩,he⟩
  let : Group.IsSolvable (D ⧸ K) := Group.isSolvable_of_surjective hf
  exact centralizer_solvable_of_centerless_quotient K hz

universe u w
variable {G : Type u} [Group G] [Finite G]

/-- The literal source action on U_H/V₁ satisfies the no-strong restriction
and the F.9.18(6) moved-space equality. The earlier source inputs are the
SQTK hypothesis, H = KL₁T, solvability of L₁T, the exact 13.8.14 Fitting
alternative, the actual conjugation action, the marked commuting S₃, full
cubic generation, and the F.9.18(2) faithful ratio-two actor. The orbit is
an actual H-orbit of an Irr⁺ constituent. The stronger intermediate result
needs no FF or two-conjugate hypothesis on that orbit. -/
theorem source_no_strong_and_moved
    {𝒦 : GroupClass.{u}} (hB42 : FullB42.{u,u} 𝒦) (hInv : FullIrrInvariance.{u,u})
    (H K X L₁ T V₃ V₁ : Subgroup G)
    [(K.subgroupOf H).Normal] [(X.subgroupOf H).Normal]
    [(V₁.subgroupOf (Source.UH H V₃)).Normal]
    [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]
    [Group.IsSolvable (L₁ ⊔ T : Subgroup G)]
    (hH : IsSQTK 𝒦 H) (hgen : H = K ⊔ (L₁ ⊔ T))
    (hfit : Components.Fitting.twoFittingResidual H = ⊥ ∨
      Components.Fitting.twoFittingResidual H = X)
    (hK : IsComponent (Source.Hstar H) (Source.starImage H K))
    {F : Type w} [Field F] [Finite F] [CharP F 2]
    (n : ℕ) (_hn : 1 < n) (_hcard : Nat.card F = 2^n)
    (e : Source.starImage H K ≃* PSL(2,F))
    (ρ : Representation (ZMod 2) (Source.Hstar H) (SeedAction.Space H V₃ V₁))
    (_hρ : SeedAction.IsConjugation H V₃ V₁ ρ) (hfaithful : Function.Injective ρ)
    (s : S₃ →* Source.Hstar H) (hinj : Function.Injective s)
    (hs : ∀ (k : Source.starImage H K) g, Commute (k : Source.Hstar H) (s g))
    (hmark : (alternatingGroup (Fin 3)).map s = Source.starImage H X)
    (hcubic : subspaceCommutator ρ ⊤ (Source.starImage H X) = ⊤)
    (I : Submodule (ZMod 2) (SeedAction.Space H V₃ V₁))
    (hI : IsIrrPlus ρ (Source.starImage H K) I)
    (W : Subrepresentation ρ) (hW : W.toSubmodule = orbitSpan ρ ⊤ I)
    (A : Subgroup (Source.Hstar H)) (hA : IsElementaryTwo A)
    (_hquad : IsQuadratic ρ A) (hbound : fixedCodim ρ A ≤ 2 * rank A)
    (hAfaith : A ⊓ centralizer (Source.starImage H K : Set (Source.Hstar H)) = ⊥) :
    ¬ IsStrongFFModule (ρ.comp (Source.starImage H K ⊔ Source.starImage H T).subtype) ∧
      (∀ C D : Subrepresentation ρ,
        (¬ ∀ k ∈ Source.starImage H K, ∀ v, sectionRepresentation ρ C D k v = v) →
        Function.Injective (sectionRepresentation ρ C D) ∧
          ¬ IsStrongFFModule (imageRepresentation ((sectionRepresentation ρ C D).comp
            (Source.starImage H K ⊔ Source.starImage H T).subtype))) ∧
      W.toSubmodule = subspaceCommutator ρ ⊤ (Source.starImage H K) := by
  let Ks := Source.starImage H K
  let Xs := Source.starImage H X
  let : Ks.Normal := (inferInstance : (K.subgroupOf H).Normal).map _
    (QuotientGroup.mk'_surjective _)
  let : Xs.Normal := (inferInstance : (X.subgroupOf H).Normal).map _
    (QuotientGroup.mk'_surjective _)
  let : IsQuasisimple Ks := hK.2
  have hSQ : IsSQTK 𝒦 (Source.Hstar H) :=
    IrreducibleReduction.sqtk_two_quotient hH (pCore 2 H) pCore_isPGroup
  have hx : Nat.card Xs = 3 := by
    change Nat.card (Source.starImage H X) = 3
    rw [← hmark, Subgroup.card_map_of_injective hinj, nat_card_alternatingGroup]
    norm_num
  have hKH : K ≤ H := by rw [hgen]; exact le_sup_left
  have hPH : L₁ ⊔ T ≤ H := by rw [hgen]; exact le_sup_right
  let P := Source.starImage H (L₁ ⊔ T)
  let : Group.IsSolvable P := by
    let : Group.IsSolvable ((L₁ ⊔ T).subgroupOf H) :=
      Group.isSolvable_of_isSolvable_injective
        (f := (subgroupOfEquivOfLe hPH).toMonoidHom) (subgroupOfEquivOfLe hPH).injective
    exact Group.isSolvable_of_surjective
      ((QuotientGroup.mk' (pCore 2 H)).subgroupMap_surjective ((L₁ ⊔ T).subgroupOf H))
  have hGP : Ks ⊔ P = ⊤ := by
    change Source.starImage H K ⊔ Source.starImage H (L₁ ⊔ T) = ⊤
    unfold Source.starImage
    rw [← Subgroup.map_sup, ← subgroupOf_sup hKH hPH, ← hgen]
    simp [map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  have hF : fittingSubgroup (Source.Hstar H) ≤ Xs := by
    rw [← Components.Fitting.twoFittingResidual_star H]
    rcases hfit with hfit | hfit
    · simp [hfit, Source.starImage]
    · rw [hfit]
  have hc := common_centralizer_le Ks Xs
    (solvable_centralizer_of_supplement Ks P hGP (psl_center_bot Ks e)) hF
  refine ⟨no_strong_restriction Ks Xs hB42 hInv e hSQ hx hc ρ hcubic hfaithful _, ?_, ?_⟩
  · intro C D hn
    exact section_faithful_no_strong Ks Xs hB42 hInv e hSQ hx hc ρ s hmark hcubic C D _ hn
  apply moved_space Ks Xs hB42 hInv e hSQ hx hc ρ s hs hmark hcubic W
  · rw [hW]
    exact orbitSpan_ne_bot ρ hI
  · rw [hW]
    exact orbitSpan_full_commutator ρ (by rw [normalizer_eq_top]) hI
  · exact hA
  · exact hbound
  · exact hAfaith

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.LinearTwo.NoStrongMoved
