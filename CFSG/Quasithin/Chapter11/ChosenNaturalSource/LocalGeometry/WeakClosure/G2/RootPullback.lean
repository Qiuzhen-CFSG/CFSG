module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.RootCover
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.RootTransfer

/-!
# Original long-root preimages and the retained central term

The selected long roots are pulled back through the actual actor homomorphism
on the conjugate module. Their original indices are q², including the entire
kernel of that homomorphism. The strict global r-bound therefore makes their
relative centralizers in V normalize the conjugate module.

The checked Weyl-cover identity is transported through the original chosen
space equivalence. It puts the full marked three-space in the conjugate module
joined with C_V(L). Containment in the conjugate itself is equivalent to
containment of C_V(L); no vanishing or splitting of the center is assumed.
The actor marking and its q³ image are explicit local inputs. The Source
consumer constructs the actual inner actor; recognition of that image and
reciprocal plane reconstruction remain with qt-d-1222-natural-weak-closure-source.
This is not yet an unconditional proof of source 11.2.2(5).

Source: Aschbacher--Smith, B.4.6(3) and 11.2.2(5), printed pp.88,768.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open scoped IsMulCommutative
open Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.RootPullback
open Atlas.G2 Atlas.G2.Natural
variable {G : Type*} [Group G]
variable {F : Type*} [Field F] [CharP F 2] [Algebra (ZMod 2) F]

/-- A full original preimage, retaining the actor kernel. -/
def rootPreimage (A : Subgroup G) (a : A →* Model F) (Z : Subgroup (Model F)) :
    Subgroup G := (Z.comap a).map A.subtype

/-- The actual ambient family of long-root preimages. -/
def roots (A : Subgroup G) (a : A →* Model F) : Set (Subgroup G) :=
  rootPreimage A a '' RootCentralizers.longRoots F

omit [CharP F 2] [Algebra (ZMod 2) F] in
theorem rootPreimage_le (A : Subgroup G) (a : A →* Model F) (Z : Subgroup (Model F)) :
    rootPreimage A a Z ≤ A := map_subtype_le _

omit [CharP F 2] [Algebra (ZMod 2) F] in
/-- Pullback preserves the exact corank 2n in the original actor. -/
theorem rootPreimage_corank [Finite F] (A : Subgroup G) (a : A →* Model F)
    (ha : a.range = EvenTwoRank.elementary F) {n : ℕ} (hc : Nat.card F = 2 ^ n)
    {Z : Subgroup (Model F)} (hZ : Z ∈ RootCentralizers.longRoots F) :
    ChapterE.subgroupCorank A (rootPreimage A a Z) = 2 * n := by
  unfold ChapterE.subgroupCorank rootPreimage
  have hi := relIndex_map_map_of_injective (Z.comap a) (⊤ : Subgroup A) A.subtype_injective
  simp only [← MonoidHom.range_eq_map, range_subtype, relIndex_top_right] at hi
  rw [hi, index_comap, ha]
  exact RootCentralizers.root_corank F hc hZ

omit [CharP F 2] [Algebra (ZMod 2) F] in
/-- The source r-bound applies to the original conjugate and each full root preimage. -/
theorem span_normalizes {V : Subgroup G} [IsElementaryAbelian 2 V]
    (g : G) (a : (V.map (MulAut.conj g).toMonoidHom) →* Model F)
    [Finite F] (ha : a.range = EvenTwoRank.elementary F)
    {n : ℕ} (hc : Nat.card F = 2 ^ n)
    (hr : (2 * n : ℕ∞) < ChapterE.globalR V) :
    rootCentralizerSpan V (roots _ a) ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G) := by
  apply iSup_le
  intro B
  apply iSup_le
  rintro ⟨Z,hZ,rfl⟩
  apply inf_le_right.trans
  apply ChapterE.centralizer_le_normalizer_of_corank_lt_globalR (rootPreimage_le _ _ _)
  rw [rootPreimage_corank _ _ ha hc hZ, ChapterE.globalR_map_equiv]
  exact_mod_cast hr
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.RootPullback

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.RootPullback
open Atlas.G2 Atlas.G2.Natural
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier)))

private def subgroupSpace (B : Subgroup G) : Submodule (ZMod 2) D.space :=
  AddSubgroup.toZModSubmodule 2 (AddSubgroup.toSubgroup.symm
    (B.comap (V.subtype.comp D.spaceEquiv.toMonoidHom)))

variable (A : Subgroup G) (a : A →* Model S.field.Carrier)
    (hact : ∀ (x : A) (v : D.space),
      (D.spaceEquiv (Multiplicative.ofAdd (Preliminary.markedAction D m (a x) v)) : G) =
        (x : G) * (D.spaceEquiv (Multiplicative.ofAdd v) : G) * (x : G)⁻¹)

include hact

private theorem fixedSpan_le : markedRootSpan D S m ≤
    subgroupSpace D (rootCentralizerSpan V (roots A a)) := by
  apply iSup_le
  intro Z
  apply iSup_le
  intro hZ v hv
  have hc : (D.spaceEquiv (Multiplicative.ofAdd v) : G) ∈
      V ⊓ centralizer (rootPreimage A a Z : Set G) := by
    refine ⟨(D.spaceEquiv (Multiplicative.ofAdd v)).property, ?_⟩
    rintro _ ⟨x,hx,rfl⟩
    have hh := hact x v
    have hf : Preliminary.markedAction D m (a x) v = v := hv ⟨a x,hx⟩
    rw [hf] at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh.symm)
  exact (show V ⊓ centralizer (rootPreimage A a Z : Set G) ≤
      rootCentralizerSpan V (roots A a) from le_iSup_of_le (rootPreimage A a Z)
        (le_iSup_of_le (show rootPreimage A a Z ∈ roots A a from ⟨Z,hZ,rfl⟩) le_rfl)) hc

private theorem moved_le (ha : a.range = EvenTwoRank.elementary S.field.Carrier) :
    subspaceCommutator (Preliminary.markedAction D m) (markedRootSpan D S m)
      (EvenTwoRank.elementary S.field.Carrier) ≤
        subgroupSpace D ⁅rootCentralizerSpan V (roots A a), A⁆ := by
  apply Submodule.span_le.mpr
  rintro _ ⟨b,hb,v,hv,rfl⟩
  rw [←ha] at hb
  obtain ⟨x,rfl⟩ := hb
  let j : Multiplicative D.space →* G := V.subtype.comp D.spaceEquiv.toMonoidHom
  change j (Multiplicative.ofAdd (Preliminary.markedAction D m (a x) v - v)) ∈ ⁅rootCentralizerSpan V (roots A a), A⁆
  rw [ofAdd_sub,map_div,div_eq_mul_inv]
  change (D.spaceEquiv (Multiplicative.ofAdd (Preliminary.markedAction D m (a x) v)) : G) *
    (D.spaceEquiv (Multiplicative.ofAdd v) : G)⁻¹ ∈ ⁅rootCentralizerSpan V (roots A a), A⁆
  rw [hact,commutator_comm]
  exact commutator_mem_commutator x.property (fixedSpan_le D S m A a hact hv)

/-- The original full third preimage is contained in the actual root
commutator together with the original central kernel. -/
theorem threePreimage_le_commutator_sup
    (ha : a.range = EvenTwoRank.elementary S.field.Carrier) :
    (Coordinates.g2 m).preimage
      ((NaturalOffenders.upper (F := S.field.Carrier)).comap
        (Restricted.NaturalCoordinates.coordinates S.field.Carrier)) ≤
      ⁅rootCentralizerSpan V (roots A a), A⁆ ⊔ (V ⊓ centralizer (L : Set G)) := by
  let U := ⁅rootCentralizerSpan V (roots A a), A⁆ ⊔ (V ⊓ centralizer (L : Set G))
  have hs : markedThreePreimage D S m ≤ subgroupSpace D U := by
    rw [← (original_root_span_commutator D S m).1]
    apply sup_le
    · exact (moved_le D S m A a hact ha).trans (fun _ hv => (show ⁅rootCentralizerSpan V (roots A a), A⁆ ≤ U from le_sup_left) hv)
    · intro v hv
      exact (show V ⊓ centralizer (L : Set G) ≤ U from le_sup_right) ⟨(D.spaceEquiv (Multiplicative.ofAdd v)).property,
        (Preliminary.mem_centralSpace_iff D v).mp hv⟩
  intro v hv
  let v' : V := ⟨v,D.centralQuotientPreimage_le _ hv⟩
  let w : D.space := (D.spaceEquiv.symm v').toAdd
  have hw : w ∈ markedThreePreimage D S m := by
    rw [markedThreePreimage_mem]
    simpa only [w, ofAdd_toAdd, MulEquiv.apply_symm_apply] using hv
  have hh := hs hw
  change (D.spaceEquiv (Multiplicative.ofAdd w) : G) ∈ U at hh
  simpa only [w, ofAdd_toAdd, MulEquiv.apply_symm_apply] using hh
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.RootPullback

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.RootPullback
open Atlas.G2 Atlas.G2.Natural
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier)))
    (g : G) (a : (V.map (MulAut.conj g).toMonoidHom) →* Model S.field.Carrier)
    (hact : ∀ (x : V.map (MulAut.conj g).toMonoidHom) (v : D.space),
      (D.spaceEquiv (Multiplicative.ofAdd (Preliminary.markedAction D m (a x) v)) : G) =
        (x : G) * (D.spaceEquiv (Multiplicative.ofAdd v) : G) * (x : G)⁻¹)
    (ha : a.range = EvenTwoRank.elementary S.field.Carrier)
    (hr : (2 * S.field.degree : ℕ∞) < ChapterE.globalR V)

include hact ha hr in
/-- The strict r-bound puts the full three-space in the conjugate module
augmented by the original central kernel, with no discarded central term. -/
theorem threePreimage_le_conjugate_sup :
    (Coordinates.g2 m).preimage
      ((NaturalOffenders.upper (F := S.field.Carrier)).comap
        (Restricted.NaturalCoordinates.coordinates S.field.Carrier)) ≤
      V.map (MulAut.conj g).toMonoidHom ⊔ (V ⊓ centralizer (L : Set G)) := by
  let := D.elementary
  exact (threePreimage_le_commutator_sup D S m _ a hact ha).trans
    (sup_le_sup_right
      (le_normalizer_iff_commutator_le_right.mp
        (span_normalizes g a ha S.field.card_eq hr)) _)

include hact ha hr in
/-- The exact remaining ambient condition is containment of the central
kernel in the conjugate, not vanishing of that kernel. -/
theorem threePreimage_le_conjugate_iff :
    (Coordinates.g2 m).preimage
      ((NaturalOffenders.upper (F := S.field.Carrier)).comap
        (Restricted.NaturalCoordinates.coordinates S.field.Carrier)) ≤
      V.map (MulAut.conj g).toMonoidHom ↔
        V ⊓ centralizer (L : Set G) ≤ V.map (MulAut.conj g).toMonoidHom := by
  constructor
  · intro h
    apply le_trans _ h
    rw [← (Coordinates.g2 m).preimage_bot]
    exact ((Coordinates.g2 m).preimage_le_iff _ _).mpr bot_le
  · intro h
    exact (threePreimage_le_conjugate_sup D S m g a hact ha hr).trans (sup_le le_rfl h)
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.RootPullback
