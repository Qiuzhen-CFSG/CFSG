module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Characteristic.Quotient

/-!
# The odd-component action input

This file records the action which is used in the odd part of the remaining
case of 14.7.68(2).  The action is assembled from the actual normalizer of the
chosen component and the literal two-core quotient.  It is then transported
through `fixedComponentQuotientEquiv`; the displayed formula on representatives
is retained so that no abstract identification of the two quotients is hidden.

The two conclusions of A.3.6 which can occur in the non-quasisimple branch are
kept as separate fields of `EarlierOddAction`: the natural `SL₂(p)` and
nilpotent `SL₂(5)` alternatives therefore have independent source inputs.  The
small simple and three-cover alternatives are also explicit.  These fields are
the precise earlier-source odd-action obstruction; no star-core containment or
quasisimplicity is built into the interface.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
14.7.68(2), pp.1071--1072; A.3.6, pp.43--45; 1.2.1(4), p.504.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08
open Chapter1.Section02.LocalModels

universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]

namespace OddAction

/-- The literal action of the normalizer of `B` on `B / O₂(B)`. -/
def componentNormalizerAction (B : Subgroup G) :
    normalizer (B : Set G) →* MulAut (B ⧸ pCore 2 B) :=
  (quotientAut (pCore 2 B)).comp B.normalizerMonoidHom

/-- Restriction of the preceding action to an elementary actor `A`. -/
def componentActorAction (A B : Subgroup G) (hA : A ≤ normalizer (B : Set G)) :
    A →* MulAut (B ⧸ pCore 2 B) :=
  (componentNormalizerAction B).comp (inclusion hA)

/-- Transport of an automorphism action across an actual group isomorphism. -/
def componentTransportAction {A C B : Type u} [Group A] [Group C] [Group B]
    (e : C ≃* B) (ρ : A →* MulAut C) : A →* MulAut B :=
  (MulAut.congr e).toMonoidHom.comp ρ

omit [Finite G] in
theorem componentNormalizerAction_apply (B : Subgroup G)
    (g : normalizer (B : Set G)) (x : B) :
    componentNormalizerAction B g (QuotientGroup.mk' (pCore 2 B) x) =
      QuotientGroup.mk' (pCore 2 B) (B.normalizerMonoidHom g x) := by
  change quotientAut (pCore 2 B) (B.normalizerMonoidHom g)
      (QuotientGroup.mk' (pCore 2 B) x) = _
  rw [quotientAut_apply_mk]

omit [Finite G] in
theorem componentNormalizerAction_apply_val (B : Subgroup G)
    (g : normalizer (B : Set G)) (x : B) :
    componentNormalizerAction B g (QuotientGroup.mk' (pCore 2 B) x) =
      QuotientGroup.mk' (pCore 2 B)
        ⟨(g : G) * (x : G) * (g : G)⁻¹,
          (mem_normalizer_iff.mp g.property (x : G)).mp x.property⟩ := by
  change quotientAut (pCore 2 B) (B.normalizerMonoidHom g)
      (QuotientGroup.mk' (pCore 2 B) x) = _
  rw [quotientAut_apply_mk]
  rfl

omit [Finite G] in
theorem componentTransportAction_apply {A C B : Type u} [Group A] [Group C] [Group B]
    (e : C ≃* B) (ρ : A →* MulAut C) (a : A) (x : C) :
    componentTransportAction e ρ a (e x) = e (ρ a x) := by
  simp [componentTransportAction]

variable (d : Data T L V F W) (c : CriticalPath (L := L) F)

/-- The canonical action of `Uα` on the image of `Lᵤ/O₂(Lᵤ)` in
`Gᵤ/O₂(Gᵤ)`.  The hypotheses are deliberately the actual ambient
normalization and component containment, rather than a family label. -/
noncomputable def fixedComponentOddAction (u : F.U) {Lu : Subgroup G}
    (hLu : Lu ≤ d.fixedCentralizer u)
    (hc : (Lu.subgroupOf (d.fixedCentralizer u)).IsCComponent)
    (hnormalizer : c.Uα ≤ normalizer (Lu : Set G)) :
    c.Uα →* MulAut (d.fixedComponentImage u Lu) :=
  componentTransportAction (d.fixedComponentQuotientEquiv u hLu hc)
    (componentActorAction c.Uα Lu hnormalizer)

theorem fixedComponentOddAction_apply (u : F.U) {Lu : Subgroup G}
    (hLu : Lu ≤ d.fixedCentralizer u)
    (hc : (Lu.subgroupOf (d.fixedCentralizer u)).IsCComponent)
    (hnormalizer : c.Uα ≤ normalizer (Lu : Set G))
    (a : c.Uα) (x : Lu ⧸ pCore 2 Lu) :
    fixedComponentOddAction d c u hLu hc hnormalizer a
        (d.fixedComponentQuotientEquiv u hLu hc x) =
      d.fixedComponentQuotientEquiv u hLu hc
        (componentActorAction c.Uα Lu hnormalizer a x) := by
  simpa [fixedComponentOddAction] using
    (componentTransportAction_apply (d.fixedComponentQuotientEquiv u hLu hc)
      (componentActorAction c.Uα Lu hnormalizer) a x)

theorem fixedComponentOddAction_apply_mk (u : F.U) {Lu : Subgroup G}
    (hLu : Lu ≤ d.fixedCentralizer u)
    (hc : (Lu.subgroupOf (d.fixedCentralizer u)).IsCComponent)
    (hnormalizer : c.Uα ≤ normalizer (Lu : Set G))
    (a : c.Uα) (x : Lu) :
    fixedComponentOddAction d c u hLu hc hnormalizer a
        (d.fixedComponentQuotientEquiv u hLu hc
          (QuotientGroup.mk' (pCore 2 Lu) x)) =
      d.fixedComponentQuotientEquiv u hLu hc
        (QuotientGroup.mk' (pCore 2 Lu)
          (Lu.normalizerMonoidHom ⟨(a : G), hnormalizer a.property⟩ x)) := by
  rw [fixedComponentOddAction_apply]
  change d.fixedComponentQuotientEquiv u hLu hc
      (componentNormalizerAction Lu ⟨(a : G), hnormalizer a.property⟩
        (QuotientGroup.mk' (pCore 2 Lu) x)) = _
  rw [componentNormalizerAction_apply]

/- The preceding identity is also visible in the original ambient quotient;
this is the representative equation used by the fixed-component source. -/
theorem fixedComponentOddAction_apply_mk_ambient (u : F.U) {Lu : Subgroup G}
    (hLu : Lu ≤ d.fixedCentralizer u)
    (hc : (Lu.subgroupOf (d.fixedCentralizer u)).IsCComponent)
    (hnormalizer : c.Uα ≤ normalizer (Lu : Set G))
    (a : c.Uα) (x : Lu) :
    ((fixedComponentOddAction d c u hLu hc hnormalizer a
        (d.fixedComponentQuotientEquiv u hLu hc
          (QuotientGroup.mk' (pCore 2 Lu) x))) :
      (d.fixedCentralizer u) ⧸ pCore 2 (d.fixedCentralizer u)) =
      QuotientGroup.mk' (pCore 2 (d.fixedCentralizer u))
        ⟨(a : G) * (x : G) * (a : G)⁻¹,
          hLu ((mem_normalizer_iff.mp (hnormalizer a.property) (x : G)).mp
            x.property)⟩ := by
  rw [fixedComponentOddAction_apply_mk]
  exact d.fixedComponentQuotientEquiv_apply u hLu hc
    (Lu.normalizerMonoidHom ⟨(a : G), hnormalizer a.property⟩ x)

/-- The local odd-action witness.  Its action is the canonical action above;
the two nontriviality fields are the only data supplied by the source
argument. -/
structure Witness {X Q : Type u} [Group X] [Finite X] [Group Q] [Finite Q]
    (A : Subgroup X) (B : Subgroup Q) (ρ : A →* MulAut B) : Prop where
  actor_nontrivial : A ≠ ⊥
  actor_elementary : IsElementaryAbelian 2 A
  action_nontrivial : ρ ≠ 1

/-- Earlier-source obstruction for the odd section.  The natural and
nilpotent alternatives are separate because A.3.6 gives different action
lemmas for them.  `simple` and `cover` retain the other two constructors of
the displayed A.3.6 alternative instead of silently discarding them. -/
structure EarlierOddAction {Q : Type u} [Group Q] [Finite Q]
    (B : Subgroup Q) {X : Type u} [Group X] [Finite X]
    (A : Subgroup X)
    (ρ : A →* MulAut B) : Prop where
  natural :
    Chapter1.Section02.A36Natural B →
      Chapter1.Section02.CenterFrattiniSource.OmegaActionData B →
      Witness A B ρ → False
  nilpotent :
    Chapter1.Section02.A36Nilpotent B →
      Chapter1.Section02.CenterFrattiniSource.OmegaActionData B →
      Witness A B ρ → False
  simple :
    IsComponent Q B → IsSimpleGroup B → TheoremCModel B →
      Chapter1.Section02.CenterFrattiniSource.OmegaActionData B →
      Witness A B ρ → False
  cover :
    IsComponent Q B →
      Nonempty (Subgroup.center B ≃* Multiplicative (ZMod 3)) →
      ThreeCoverModel B →
      Chapter1.Section02.CenterFrattiniSource.OmegaActionData B →
      Witness A B ρ → False

/-- The actual local configuration used by the odd-action obstruction.  The
quotient hypothesis is the contradiction branch of 14.7.68(2), and is not
replaced by quasisimplicity of the component itself. -/
structure Case (d : Data T L V F W) (c : CriticalPath (L := L) F)
    (u : F.U) (Lu : Subgroup G) : Prop where
  member : (u : G) ∈ d.U₀
  nonidentity : (u : G) ≠ 1
  fixed : d.FixedModuloPoint u
  normalizer : normalizer (K F : Set G) = F.H
  maximal : IsMaximalTwoLocal F.H
  sylow : Chapter1.IsSylowIn 2 (d.fixedSylow u) (d.fixedCentralizer u)
  le_centralizer : Lu ≤ d.fixedCentralizer u
  component : (Lu.subgroupOf (d.fixedCentralizer u)).IsCComponent
  larger : K F < Lu
  normal : (Lu.subgroupOf (d.fixedCentralizer u)).Normal
  outside : ¬ Lu ≤ F.H
  nonquasisimple : ¬ IsQuasisimple (Lu ⧸ pCore 2 Lu)


variable {d c}

theorem Uα_le_fixedSylow (u : F.U) (earlier : c.EarlierImages)
    (hfixed : c.Uα ≤ d.fixedCentralizer u) :
    c.Uα ≤ d.fixedSylow u := by
  change c.Uα ≤ (T : Subgroup G) ⊓ d.fixedCentralizer u
  exact le_inf (c.Uα_le_sylow earlier) hfixed

theorem Uα_le_component_normalizer (u : F.U) {Lu : Subgroup G}
    (h : Case d c u Lu)
    (hfixed : c.Uα ≤ d.fixedCentralizer u) :
    c.Uα ≤ normalizer (Lu : Set G) := by
  exact hfixed.trans
    ((normal_subgroupOf_iff_le_normalizer h.le_centralizer).mp h.normal)

variable (d c)

theorem star_Uα_le_core_of_odd_action
    (earlier : c.EarlierImages) (u : F.U) {Lu : Subgroup G}
    (h : Case d c u Lu)
    (hfixed : c.Uα ≤ d.fixedCentralizer u)
    (hA36 : ∀ (X : Type u) [Group X] [Finite X],
      IsSQTK KnownSimple.IsKnownSimple X → pCore 2 X = ⊥ → ∀ B : Subgroup X,
        B.IsCComponent → Chapter1.Section02.A36Conclusion B)
    (source : EarlierOddAction
      (Q := d.fixedCentralizer u ⧸ pCore 2 (d.fixedCentralizer u))
      (B := d.fixedComponentImage u Lu) (X := G) (A := c.Uα)
      (ρ := fixedComponentOddAction d c u h.le_centralizer h.component
        (Uα_le_component_normalizer (d := d) (c := c) u h hfixed)))
    (odd : star F c.Uα ≠ ⊥ →
      fixedComponentOddAction d c u h.le_centralizer h.component
        (Uα_le_component_normalizer (d := d) (c := c) u h hfixed) ≠ 1) :
    c.Uα ≤ F.H.pCoreIn 2 := by
  have hnormalizer := Uα_le_component_normalizer (d := d) (c := c) u h hfixed
  have hω := d.fixedComponent_omega_of_not_quasisimple hA36 u h.nonidentity
    h.le_centralizer h.component h.nonquasisimple
  have hstructure := d.fixedComponent_earlier_structure hA36 u h.nonidentity h.component
  by_contra hnot
  have hstar : star F c.Uα ≠ ⊥ := by
    intro hz
    apply hnot
    have hcore : c.Uα ≤ F.H.pCoreIn 2 := by
      have hk : (c.Uα.subgroupOf F.H) ≤ pCore 2 F.H := by
        simpa only [star, Subgroup.map_eq_bot_iff, starMap,
          QuotientGroup.ker_mk'] using hz
      intro x hx
      exact mem_map.mpr ⟨⟨x, c.Uα_le_H earlier hx⟩, hk hx, rfl⟩
    exact hcore
  have hactor : c.Uα ≠ ⊥ := by
    intro hzero
    apply hstar
    rw [hzero]
    simp [star]
  have hw : Witness (X := G) (Q := d.fixedCentralizer u ⧸ pCore 2 (d.fixedCentralizer u))
      c.Uα (d.fixedComponentImage u Lu)
      (fixedComponentOddAction d c u h.le_centralizer h.component hnormalizer) :=
    ⟨hactor, c.Uα_elementary d, odd hstar⟩
  rcases hstructure.1 with ⟨halt, hcommon⟩
  cases halt with
  | simple hcomponent hsimple hmodel =>
      exact source.simple hcomponent hsimple hmodel hω hw
  | cover hcomponent hcenter hmodel =>
      exact source.cover hcomponent hcenter hmodel hω hw
  | natural hnatural =>
      exact source.natural hnatural hω hw
  | nilpotent hnilpotent =>
      exact source.nilpotent hnilpotent hω hw

end OddAction
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
