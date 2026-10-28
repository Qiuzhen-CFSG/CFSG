module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.ActorRecognition.Equality
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.ActorRecognition.Transfer
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.RootPullback.Source

/-!
# The actual q³ image of a noncentral conjugate module

The original automizer acts on the central quotient through the same component
marking. Exact fixed-vector lifting transports its A_(2n) condition through
the full central cover. The model calculation therefore recognizes the actual
conjugation image as a conjugate of the full elementary group of order q³.
The homomorphism acts on the entire original module and its kernel is exactly
C_(Vᵍ)(V). No numerical label is used in place of a group or representation.

The final theorem discharges the parameter input using the proved source
parameter family. Its remaining hypotheses are the allowed earlier-source
maximal-local uniqueness, third-space centralizer bound and fixed-line clause,
whose final assembly belongs to qt-d-1222-natural-local-geometry.
ActorRecognition.Frame uses the literal recognized image in RootPullback.
Reciprocal plane reconstruction and full 11.2.2(5) remain with
qt-d-1222-natural-weak-closure-source.
Source: Aschbacher--Smith B.4.6(7,9) and 11.2.2(3--5), pp.88--89,767--768.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open scoped IsMulCommutative
open Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterE
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.ActorRecognition
open Atlas.G2 Parameters.FullAutomizer Parameters.RootActors
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier)))

/-- Exact fixed-space lifting preserves the source parameter on the original
inner automizer, with the entire central kernel still present. -/
theorem original_inner_family
    (B : Subgroup (Automizer V)) (hinner : B ≤ inducedAutomizer V L)
    {k : ℕ} :
    letI := D.elementary
    B ∈ fixedSpaceFamily (automizerRepresentation V) k →
    ((layerEquiv D S (Coordinates.g2 m)).toMonoidHom.comp (inclusion hinner)).range ∈
      fixedSpaceFamily (NaturalOffenders.binaryAction (F:=S.field.Carrier)) k := by
  let := D.elementary
  intro hB
  let c := Coordinates.g2 m
  obtain ⟨ρ,hρ,he,hres⟩ := exists_faithful_quotient_action D S c
  let e₀ : c.Space ≃ₗ[ZMod 2] Natural.Space S.field.Carrier :=
    LinearEquiv.ofBijective
      (({toFun := id,map_zero' := rfl,map_add' := fun _ _ => rfl} :
        c.Space →+ Natural.Space S.field.Carrier).toZModLinearMap 2) Function.bijective_id
  let E := e₀.trans ((Restricted.NaturalCoordinates.equiv S.field.Carrier).restrictScalars (ZMod 2))
  let j := (layerEquiv D S c).toMonoidHom.comp (inclusion hinner)
  have hact (a : B) (v : c.Space) :
      E (ρ a v) = NaturalOffenders.binaryAction (j a) (E v) := by
    have hh := hres (inclusion hinner a) v
    change ρ a v = c.modelAction (j a) v at hh
    rw [hh]
    exact LinearMap.congr_fun ((Restricted.NaturalCoordinates.repEquiv S.field.Carrier).isIntertwining' (j a)) v
  apply family_range_of_fixed_lifting (automizerRepresentation V)
    (NaturalOffenders.binaryAction (F:=S.field.Carrier)) j
    ((layerEquiv D S c).injective.comp (inclusion_injective hinner))
    (E.toLinearMap.comp (projectionLinear D S c))
    (E.surjective.comp (projectionLinear_surjective D S c)) _ _ hB
  · intro a x
    exact (congrArg E (he a x)).trans (hact a _)
  · intro a x hx
    apply original_layer_fixed_lifts D S c ρ hres a (hinner a.property) x
    apply E.injective
    exact (hact a _).trans hx

/-- The actual original conjugation homomorphism has the same range as
the marked automizer inclusion, including the whole centralizer kernel. -/
theorem innerActor_range {A : Subgroup G}
    (hAN : A ≤ normalizer (V : Set G))
    (hinner : inducedAutomizer V A ≤ inducedAutomizer V L) :
    (RootPullback.innerActor D S m hAN hinner).range =
      ((layerEquiv D S (Coordinates.g2 m)).toMonoidHom.comp (inclusion hinner)).range := by
  ext z
  constructor
  · rintro ⟨a,rfl⟩
    exact ⟨⟨V.normalizerMonoidHom.rangeRestrict (inclusion hAN a),
      ⟨inclusion hAN a,a.property,rfl⟩⟩,rfl⟩
  · rintro ⟨b,rfl⟩
    obtain ⟨x,hx,he⟩ := b.property
    refine ⟨⟨x.val,hx⟩,?_⟩
    change layerEquiv D S (Coordinates.g2 m) _ = layerEquiv D S (Coordinates.g2 m) _
    congr 1
    apply Subtype.ext
    exact he

/-- Every noncentral zeroth conjugate has the full q³ actor image in an
actual model frame. The action and kernel are the original ambient ones. -/
theorem exists_conjugate_actor_full_image
    (hs : @globalS G _ V D.elementary = (2 * S.field.degree : ℕ))
    (g : G) (hg : V.map (MulAut.conj g).toMonoidHom ≤ T)
    (hnon : ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥) :
    ∃ (a : (V.map (MulAut.conj g).toMonoidHom) →* Model S.field.Carrier)
      (u : Model S.field.Carrier),
      (∀ (x : V.map (MulAut.conj g).toMonoidHom) (v : D.space),
        (D.spaceEquiv (Multiplicative.ofAdd (Preliminary.markedAction D m (a x) v)) : G) =
          (x : G) * (D.spaceEquiv (Multiplicative.ofAdd v) : G) * (x : G)⁻¹) ∧
      a.ker = (centralizer (V : Set G)).subgroupOf (V.map (MulAut.conj g).toMonoidHom) ∧
      a.range = (EvenTwoRank.elementary S.field.Carrier).map (MulAut.conj u).toMonoidHom := by
  let := D.elementary
  let A := V.map (MulAut.conj g).toMonoidHom
  have hAN : A ≤ normalizer (V : Set G) := hg.trans S.sylow_normalizes
  have hinner := RootPullback.conjugate_image_inner D S m hs g hg hnon
  have hb : (subgroupCorank A A : ℕ∞) < globalS V := by
    rw [show subgroupCorank A A = 0 by simp [subgroupCorank],hs]
    exact_mod_cast (by have := S.nonbinary; omega : 0<2*S.field.degree)
  have hfamily := (inducedAutomizer_mem_fixedSpaceFamily_of_corank_lt_globalS g
    (le_inf le_rfl hAN) hb hnon).2
  rw [hs,ENat.toNat_natCast,show subgroupCorank A A = 0 by simp [subgroupCorank],Nat.sub_zero] at hfamily
  obtain ⟨u,hu⟩ := family_eq_conjugate_elementary S.field.card_eq
    (by have := S.nonbinary; omega) _ (original_inner_family D S m _ hinner hfamily)
  refine ⟨RootPullback.innerActor D S m hAN hinner,u,
    RootPullback.innerActor_action D S m hAN hinner,
    RootPullback.innerActor_ker D S m hAN hinner,?_⟩
  exact (innerActor_range D S m hAN hinner).trans hu

/-- The completed source parameters now supply full actor recognition
without a numerical parameter or model-image premise. -/
theorem exists_conjugate_actor_of_preceding
    (f : InvariantFlag (Coordinates.g2 m))
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N → L ≤ N → N = normalizer (L : Set G))
    (hthree : centralizer (f.Vi 2 : Set G) ≤ normalizer (L : Set G))
    (hline : f.Vi 0 ≤ V ⊓ centralizer (sourceTL T L : Set G))
    (g : G) (hg : V.map (MulAut.conj g).toMonoidHom ≤ T)
    (hnon : ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥) :
    ∃ (a : (V.map (MulAut.conj g).toMonoidHom) →* Model S.field.Carrier)
      (u : Model S.field.Carrier),
      (∀ (x : V.map (MulAut.conj g).toMonoidHom) (v : D.space),
        (D.spaceEquiv (Multiplicative.ofAdd (Preliminary.markedAction D m (a x) v)) : G) =
          (x : G) * (D.spaceEquiv (Multiplicative.ofAdd v) : G) * (x : G)⁻¹) ∧
      a.ker = (centralizer (V : Set G)).subgroupOf (V.map (MulAut.conj g).toMonoidHom) ∧
      a.range = (EvenTwoRank.elementary S.field.Carrier).map (MulAut.conj u).toMonoidHom := by
  exact exists_conjugate_actor_full_image D S m
    (Parameters.source_parameters D S f hunique hthree hline).2.2.1.2 g hg hnon
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.ActorRecognition
