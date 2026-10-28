module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.CentralContainment.Model
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.ReciprocalRoots.Centralizers
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.FixedCodimensions.Dimensions
public import CFSG.Quasithin.ChapterE.Section06.Obstructions

/-!
# The original root-centralizer hyperplane and full commutator

Lift the chosen module through the existing surjective Weyl-cover map, over
its literal natural projection. The two root fixed spaces span a hyperplane;
its full original preimage lies in the span of the original root centralizers,
so that span has binary corank at most n. The full-cover commutator calculation
also puts every element of C_V(L) in [V,A] for the recognized q³ actor A.

Normalization applies the first result to the reciprocal covering center and
the second after establishing mutual normalization. Both statements retain
all original central kernels. Source: Aschbacher--Smith B.4.6(3,7) and the
central-cover repair of 11.2.2(5), printed pp.88,768.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open scoped IsMulCommutative
open Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterE
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.CentralContainment
open Atlas.G2 Atlas.G2.Natural
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier)))
    (A : Subgroup G) (a : A →* Model S.field.Carrier)
    (hact : ∀ (x : A) (v : D.space),
      (D.spaceEquiv (Multiplicative.ofAdd (Preliminary.markedAction D m (a x) v)) : G) =
        (x : G) * (D.spaceEquiv (Multiplicative.ofAdd v) : G) * (x : G)⁻¹)

private theorem exists_cover :
    ∃ p : (RootCentralizers.coverAction S.field.Carrier).IntertwiningMap
        (Preliminary.markedAction D m), Function.Surjective p ∧
      ∀ x, Preliminary.markedProjection D m (p x) = mk S.field.Carrier x := by
  have hq : 2 < Nat.card S.field.Carrier := by
    rw [S.field.card_eq]
    exact (by simpa using Nat.pow_lt_pow_right (by decide : 1 < 2) S.nonbinary)
  exact OrthogonalCover.ParabolicFixed.exists_full_quotient S.field.Carrier
    (Preliminary.markedProjection D m) hq (Preliminary.markedProjection_isCover D m)

private def subgroupSpace (B : Subgroup G) : Submodule (ZMod 2) D.space :=
  AddSubgroup.toZModSubmodule 2 (AddSubgroup.toSubgroup.symm
    (B.comap (V.subtype.comp D.spaceEquiv.toMonoidHom)))

include hact in
private theorem cover_span_le
    (p : (RootCentralizers.coverAction S.field.Carrier).IntertwiningMap
      (Preliminary.markedAction D m)) :
    (RootCentralizers.fixedSpan S.field.Carrier).map p.toLinearMap ≤
      subgroupSpace D (rootCentralizerSpan V (RootPullback.roots A a)) := by
  rw [RootCentralizers.fixedSpan,Submodule.map_iSup]
  apply iSup_le
  intro Z
  rw [Submodule.map_iSup]
  apply iSup_le
  intro hZ
  rintro _ ⟨v,hv,rfl⟩
  have hp : (D.spaceEquiv (Multiplicative.ofAdd (p v)) : G) ∈
      V ⊓ centralizer (RootPullback.rootPreimage A a Z : Set G) := by
    refine ⟨(D.spaceEquiv (Multiplicative.ofAdd (p v))).property,?_⟩
    rintro _ ⟨x,hx,rfl⟩
    apply (ReciprocalRoots.fixed_iff_commute D S m A a hact x (p v)).mp
    have he := LinearMap.congr_fun (p.isIntertwining' (a x)) v
    change p (RootCentralizers.coverAction S.field.Carrier (a x) v) =
      Preliminary.markedAction D m (a x) (p v) at he
    rw [show RootCentralizers.coverAction S.field.Carrier (a x) v = v from hv ⟨a x,hx⟩] at he
    exact he.symm
  exact (show V ⊓ centralizer (RootPullback.rootPreimage A a Z : Set G) ≤
    rootCentralizerSpan V (RootPullback.roots A a) from
      le_iSup_of_le _ (le_iSup_of_le ⟨Z,hZ,rfl⟩ le_rfl)) hp

include hact in
theorem hyperplane_le_rootCentralizerSpan :
    (Coordinates.g2 m).preimage (naturalHyperplane S.field.Carrier) ≤
      rootCentralizerSpan V (RootPullback.roots A a) := by
  obtain ⟨p,hp,hover⟩ := exists_cover D S m
  intro x hx
  let v : V := ⟨x,D.centralQuotientPreimage_le _ hx⟩
  let w : D.space := (D.spaceEquiv.symm v).toAdd
  obtain ⟨z,hz⟩ := hp w
  have hw : (Preliminary.markedProjection D m w) ∈ naturalHyperplane S.field.Carrier := by
    exact ((Coordinates.g2 m).mem_preimage _ v).mp hx
  have h7 : z.val 7 = 0 := by
    have hh := hover z
    rw [hz] at hh
    rw [hh] at hw
    exact hw
  have hs : z ∈ RootCentralizers.fixedSpan S.field.Carrier := by
    rw [RootCentralizers.fixedSpan_eq_hyperplane]
    exact h7
  have hh := cover_span_le D S m A a hact p (Submodule.mem_map.mpr ⟨z,hs,hz⟩)
  change (D.spaceEquiv (Multiplicative.ofAdd w) : G) ∈ rootCentralizerSpan V (RootPullback.roots A a) at hh
  simpa only [w,v,ofAdd_toAdd,MulEquiv.apply_symm_apply] using hh

include hact in
theorem rootCentralizerSpan_corank_le :
    subgroupCorank V (rootCentralizerSpan V (RootPullback.roots A a)) ≤ S.field.degree := by
  have hc := ChapterE.Section06.subgroupCorank_antitone
    (V:=V) (hyperplane_le_rootCentralizerSpan D S m A a hact)
  rw [Parameters.NaturalDimensions.pullback_corank D S (Coordinates.g2 m)] at hc
  change subgroupCorank V (rootCentralizerSpan V (RootPullback.roots A a)) ≤
    S.field.degree * Module.finrank S.field.Carrier
      (Natural.Space S.field.Carrier ⧸ naturalHyperplane S.field.Carrier) at hc
  rw [naturalHyperplane_codim,mul_one] at hc
  exact hc

include hact in
private theorem cover_commutator_le
    (ha : a.range = EvenTwoRank.elementary S.field.Carrier)
    (p : (RootCentralizers.coverAction S.field.Carrier).IntertwiningMap
      (Preliminary.markedAction D m)) :
    (subspaceCommutator (RootCentralizers.coverAction S.field.Carrier) ⊤
      (EvenTwoRank.elementary S.field.Carrier)).map p.toLinearMap ≤
        subgroupSpace D ⁅V,A⁆ := by
  rw [subspaceCommutator,Submodule.map_span]
  apply Submodule.span_le.mpr
  rintro _ ⟨_,⟨b,hb,v,-,rfl⟩,rfl⟩
  rw [←ha] at hb
  obtain ⟨x,rfl⟩ := hb
  have he := LinearMap.congr_fun (p.isIntertwining' (a x)) v
  change p (RootCentralizers.coverAction S.field.Carrier (a x) v) =
    Preliminary.markedAction D m (a x) (p v) at he
  rw [map_sub]
  change p (RootCentralizers.coverAction S.field.Carrier (a x) v) - p v ∈
    subgroupSpace D ⁅V,A⁆
  rw [he]
  let j : Multiplicative D.space →* G := V.subtype.comp D.spaceEquiv.toMonoidHom
  change j (Multiplicative.ofAdd (Preliminary.markedAction D m (a x) (p v)-p v)) ∈ ⁅V,A⁆
  rw [ofAdd_sub,map_div,div_eq_mul_inv]
  change (D.spaceEquiv (Multiplicative.ofAdd (Preliminary.markedAction D m (a x) (p v))) : G) *
    (D.spaceEquiv (Multiplicative.ofAdd (p v)) : G)⁻¹ ∈ ⁅V,A⁆
  rw [hact,commutator_comm]
  exact commutator_mem_commutator x.property (D.spaceEquiv (Multiplicative.ofAdd (p v))).property

include hact in
theorem central_le_full_commutator (ha : a.range = EvenTwoRank.elementary S.field.Carrier) :
    V ⊓ centralizer (L : Set G) ≤ ⁅V,A⁆ := by
  obtain ⟨p,hp,hover⟩ := exists_cover D S m
  rintro x ⟨hxV,hxL⟩
  let v : V := ⟨x,hxV⟩
  let w : D.space := (D.spaceEquiv.symm v).toAdd
  have hw : w ∈ Preliminary.centralSpace D :=
    (Preliminary.mem_centralSpace_iff D w).mpr (by
      dsimp only [w]
      rw [ofAdd_toAdd,MulEquiv.apply_symm_apply]
      exact hxL)
  obtain ⟨z,hz⟩ := hp w
  have hzker : z ∈ (scalarLine S.field.Carrier).restrictScalars (ZMod 2) := by
    apply (Submodule.Quotient.mk_eq_zero _).mp
    change mk S.field.Carrier z = 0
    rw [←hover,hz]
    exact show w ∈ (Preliminary.markedProjection D m).toLinearMap.ker from
      (Preliminary.markedProjection_ker D m).symm ▸ hw
  have hs := scalar_le_full_commutator S.field.Carrier hzker
  have hh := cover_commutator_le D S m A a hact ha p (Submodule.mem_map.mpr ⟨z,hs,hz⟩)
  change (D.spaceEquiv (Multiplicative.ofAdd w) : G) ∈ ⁅V,A⁆ at hh
  simpa only [w,v,ofAdd_toAdd,MulEquiv.apply_symm_apply] using hh

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.CentralContainment
