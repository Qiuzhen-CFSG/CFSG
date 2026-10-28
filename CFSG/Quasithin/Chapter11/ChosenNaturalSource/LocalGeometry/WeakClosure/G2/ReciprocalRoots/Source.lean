module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.ReciprocalRoots.Transfer
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.ActorRecognition.Frame

/-!
# The original 11.2.2 reciprocal root family

The checked actor recognition recenters the original quotient marking and
identifies the full q³ image of each noncentral Vᵍ in T. The proved source
parameters supply the strict r-bound. For every full long-root preimage D,
we construct its double centralizer, exact reciprocal corank and actual
long-root action on Vᵍ, retaining the original action and both kernels.

Only the permitted earlier-source maximal-local uniqueness, third-space
centralizer bound and fixed-line clause remain explicit. Their final discharge
belongs to qt-d-1222-natural-local-geometry. This is the reciprocal-root step
of 11.2.2(5), not its completed weak-closure conclusion: the central containment
and common full-plane family remain with qt-d-1222-natural-weak-closure-source.
No RootSpan.moved or vanishing of C_V(L) is assumed.
Source: Aschbacher--Smith 11.2.2(3--5), printed pp.767--768.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open scoped IsMulCommutative
open Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterE

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.ReciprocalRoots
open Atlas.G2 Atlas.G2.Natural
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier)))

/-- The exact reciprocal long-root calculation on the original conjugate module.
The entire root preimage and both original centralizer kernels are retained. -/
structure RootData (g : G)
    (a : (V.map (MulAut.conj g).toMonoidHom) →* Model S.field.Carrier)
    (Z : Subgroup (Model S.field.Carrier)) where
  normalizes : V ⊓ centralizer (RootPullback.rootPreimage _ a Z : Set G) ≤
    normalizer (V.map (MulAut.conj g).toMonoidHom : Set G)
  double_centralizer : (V.map (MulAut.conj g).toMonoidHom) ⊓ centralizer
    (V ⊓ centralizer (RootPullback.rootPreimage _ a Z : Set G) : Set G) =
      RootPullback.rootPreimage _ a Z
  corank : subgroupCorank (V.map (MulAut.conj g).toMonoidHom)
    ((V.map (MulAut.conj g).toMonoidHom) ⊓ centralizer
      (V ⊓ centralizer (RootPullback.rootPreimage _ a Z : Set G) : Set G)) =
        2*S.field.degree
  actor : (V ⊓ centralizer (RootPullback.rootPreimage _ a Z : Set G) : Subgroup G) →*
    Model S.field.Carrier
  conjugator : Model S.field.Carrier
  action : ∀ (x : (V ⊓ centralizer (RootPullback.rootPreimage _ a Z : Set G) : Subgroup G)) (v : D.space),
    MulAut.conj g (D.spaceEquiv (Multiplicative.ofAdd (Preliminary.markedAction D m (actor x) v)) : G) =
      (x : G) * MulAut.conj g (D.spaceEquiv (Multiplicative.ofAdd v) : G) * (x : G)⁻¹
  kernel : actor.ker = (centralizer (V.map (MulAut.conj g).toMonoidHom : Set G)).subgroupOf
    (V ⊓ centralizer (RootPullback.rootPreimage _ a Z : Set G))
  root_image : actor.range ≤ LieParabolicSetup.highestRoot.map (MulAut.conj conjugator).toMonoidHom

/-- Construct all reciprocal data from the recognized original actor and strict r-bound. -/
def rootData (g : G)
    (a : (V.map (MulAut.conj g).toMonoidHom) →* Model S.field.Carrier)
    (hact : ∀ (x : V.map (MulAut.conj g).toMonoidHom) (v : D.space),
      (D.spaceEquiv (Multiplicative.ofAdd (Preliminary.markedAction D m (a x) v)) : G) =
        (x : G) * (D.spaceEquiv (Multiplicative.ofAdd v) : G) * (x : G)⁻¹)
    (ha : a.range = EvenTwoRank.elementary S.field.Carrier)
    (hr : (2*S.field.degree : ℕ∞) < globalR V)
    (Z : Subgroup (Model S.field.Carrier))
    (hZ : Z ∈ RootCentralizers.longRoots S.field.Carrier) : RootData D S m g a Z := by
  apply Classical.choice
  obtain ⟨b,u,hb,hbk,hbr⟩ := reciprocal_root_actor D S m g a hact ha hr Z hZ
  exact ⟨{
    normalizes := rootCentralizer_normalizes D S g a ha hr Z hZ
    double_centralizer := doubleCentralizer D S m _ a hact Z hZ ha
    corank := reciprocal_corank D S m _ a hact ha Z hZ
    actor := b
    conjugator := u
    action := hb
    kernel := hbk
    root_image := hbr }⟩

/-- Actual 11.2.2(5) reciprocal root application. Actor recognition and both
numerical parameters are discharged, leaving only the permitted preceding
source clauses. Central containment and plane reconstruction are subsequent steps. -/
theorem source_root_family (f : InvariantFlag (Coordinates.g2 m))
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N → L ≤ N → N = normalizer (L : Set G))
    (hthree : centralizer (f.Vi 2 : Set G) ≤ normalizer (L : Set G))
    (hline : f.Vi 0 ≤ V ⊓ centralizer (sourceTL T L : Set G))
    (g : G) (hg : V.map (MulAut.conj g).toMonoidHom ≤ T)
    (hnon : ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥) :
    ∃ (u : Model S.field.Carrier)
      (a : (V.map (MulAut.conj g).toMonoidHom) →* Model S.field.Carrier),
      (∀ (x : V.map (MulAut.conj g).toMonoidHom) (v : D.space),
        (D.spaceEquiv (Multiplicative.ofAdd
          (Preliminary.markedAction D (ActorRecognition.recentered D S m u) (a x) v)) : G) =
            (x : G) * (D.spaceEquiv (Multiplicative.ofAdd v) : G) * (x : G)⁻¹) ∧
      a.ker = (centralizer (V : Set G)).subgroupOf (V.map (MulAut.conj g).toMonoidHom) ∧
      a.range = EvenTwoRank.elementary S.field.Carrier ∧
      ∀ Z ∈ RootCentralizers.longRoots S.field.Carrier,
        Nonempty (RootData D S (ActorRecognition.recentered D S m u) g a Z) := by
  obtain ⟨a,u,hact,hker,ha⟩ :=
    ActorRecognition.exists_conjugate_actor_of_preceding D S m f hunique hthree hline g hg hnon
  let a' := (MulAut.conj u⁻¹).toMonoidHom.comp a
  have ha' : a'.range = EvenTwoRank.elementary S.field.Carrier := by
    rw [MonoidHom.range_comp,ha,map_map]
    have he : (MulAut.conj u⁻¹).toMonoidHom.comp (MulAut.conj u).toMonoidHom =
        MonoidHom.id (Model S.field.Carrier) := by
      ext x
      simp [MulAut.conj_apply,mul_assoc]
    rw [he,map_id]
  have hact' (x : V.map (MulAut.conj g).toMonoidHom) (v : D.space) :
      (D.spaceEquiv (Multiplicative.ofAdd
        (Preliminary.markedAction D (ActorRecognition.recentered D S m u) (a' x) v)) : G) =
          (x : G) * (D.spaceEquiv (Multiplicative.ofAdd v) : G) * (x : G)⁻¹ := by
    change (D.spaceEquiv (Multiplicative.ofAdd
      (Preliminary.markedAction D (ActorRecognition.recentered D S m u) (MulAut.conj u⁻¹ (a x)) v)) : G) = _
    rw [ActorRecognition.recentered_action]
    exact hact x v
  have hker' : a'.ker = a.ker := by
    ext x
    change MulAut.conj u⁻¹ (a x) = 1 ↔ a x = 1
    exact map_eq_one_iff _ (MulAut.conj u⁻¹).injective
  refine ⟨u,a',hact',hker'.trans hker,ha',?_⟩
  intro Z hZ
  exact ⟨rootData D S _ g a' hact' ha'
    (RootPullback.strict_globalR_of_preceding D S m f hunique hthree hline) Z hZ⟩
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.ReciprocalRoots
