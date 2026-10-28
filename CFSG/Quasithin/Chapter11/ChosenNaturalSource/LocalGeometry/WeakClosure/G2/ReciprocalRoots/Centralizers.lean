module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.RootPullback
public import Theory.Representation.G2NaturalLongRootFixer

/-!
# The original G₂ root double centralizer

The pointwise fixer of a long-root fixed space is that same full field root.
Every vector of the natural quotient lifts to the original central cover,
with fixed vectors remaining fixed. Transport along the actual conjugation
homomorphism therefore gives C_A(C_V(D)) = D for every full root preimage D.
Its index is q². The strict r-bound makes C_V(D) normalize A = Vᵍ, so this is
the exact reciprocal action index used to recognize the next long root.

Neither the actor kernel nor C_V(L) is discarded. Transfer applies these
calculations to the original reciprocal actor; Source supplies the actual
11.2.2 inputs. Source: Aschbacher--Smith B.4.6(4,7) and 11.2.2(5), printed
pp.88,768. The subsequent central containment and plane reconstruction stay
with qt-d-1222-natural-weak-closure-source.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open scoped IsMulCommutative
open Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterE
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.ReciprocalRoots
open Atlas.G2 Atlas.G2.Natural
variable {F : Type*} [Field F] [CharP F 2] [Algebra (ZMod 2) F]

theorem root_fixedSpace (u : Model F) :
    fixedSpace (NaturalOffenders.binaryNatural (F:=F))
      (LieParabolicSetup.highestRoot.map (MulAut.conj u).toMonoidHom) =
    fixedSpace (NaturalOffenders.binaryNatural (F:=F))
      (zpowers (MulAut.conj u (rootA 1))) := by
  let Z := (LieParabolicSetup.highestRoot (F:=F)).map (MulAut.conj u).toMonoidHom
  have hk := NaturalLongRootFixer.subspaceKernel_fixedSpace_longRoot u 1 (one_ne_zero (α:=F))
  apply le_antisymm
  · apply ChapterE.fixedSpace_antitone
    exact zpowers_le.mpr (mem_map_of_mem _ ⟨Multiplicative.ofAdd 1,rfl⟩)
  · intro v hv z
    have hz : z.val ∈ subspaceKernel (NaturalOffenders.binaryNatural (F:=F))
        (fixedSpace (NaturalOffenders.binaryNatural (F:=F))
          (zpowers (MulAut.conj u (rootA 1)))) ⊤ := hk.symm ▸ z.property
    exact hz.2 v hv

theorem root_fixer (u : Model F) :
    subspaceKernel (NaturalOffenders.binaryNatural (F:=F))
      (fixedSpace (NaturalOffenders.binaryNatural (F:=F))
        (LieParabolicSetup.highestRoot.map (MulAut.conj u).toMonoidHom)) ⊤ =
    LieParabolicSetup.highestRoot.map (MulAut.conj u).toMonoidHom := by
  rw [root_fixedSpace]
  exact NaturalLongRootFixer.subspaceKernel_fixedSpace_longRoot u 1 (one_ne_zero (α:=F))

theorem root_fixer_of_mem {Z : Subgroup (Model F)} (hZ : Z ∈ RootCentralizers.longRoots F) :
    subspaceKernel (NaturalOffenders.binaryNatural (F:=F))
      (fixedSpace (NaturalOffenders.binaryNatural (F:=F)) Z) ⊤ = Z := by
  obtain ⟨-,u,rfl⟩ := hZ
  exact root_fixer u

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier)))
    (A : Subgroup G) (a : A →* Model S.field.Carrier)
    (hact : ∀ (x : A) (v : D.space),
      (D.spaceEquiv (Multiplicative.ofAdd (Preliminary.markedAction D m (a x) v)) : G) =
        (x : G) * (D.spaceEquiv (Multiplicative.ofAdd v) : G) * (x : G)⁻¹)

include hact in
theorem fixed_iff_commute (x : A) (v : D.space) :
    Preliminary.markedAction D m (a x) v = v ↔
      (x : G) * (D.spaceEquiv (Multiplicative.ofAdd v) : G) =
        (D.spaceEquiv (Multiplicative.ofAdd v) : G) * (x : G) := by
  constructor
  · intro hv
    exact mul_inv_eq_iff_eq_mul.mp ((hact x v).symm.trans (congrArg
      (fun w : D.space => (D.spaceEquiv (Multiplicative.ofAdd w) : G)) hv))
  · intro hv
    apply Multiplicative.ofAdd.injective
    apply D.spaceEquiv.injective
    apply Subtype.ext
    exact (hact x v).trans (mul_inv_eq_iff_eq_mul.mpr hv)

include hact in
theorem rootCentralizer_mem (Z : Subgroup (Model S.field.Carrier))
    (hZ : Z ≤ a.range) (v : D.space) :
    (D.spaceEquiv (Multiplicative.ofAdd v) : G) ∈
      V ⊓ centralizer (RootPullback.rootPreimage A a Z : Set G) ↔
    Preliminary.markedProjection D m v ∈
      fixedSpace (NaturalOffenders.binaryNatural (F:=S.field.Carrier)) Z := by
  have hf := marked_fixedSpace D S m Z
  change fixedSpace (Preliminary.markedAction D m) Z =
    (fixedSpace (NaturalOffenders.binaryNatural (F:=S.field.Carrier)) Z).comap
      (Preliminary.markedProjection D m).toLinearMap at hf
  constructor
  · intro hv
    change v ∈ (fixedSpace (NaturalOffenders.binaryNatural (F:=S.field.Carrier)) Z).comap
      (Preliminary.markedProjection D m).toLinearMap
    rw [←hf]
    intro z
    obtain ⟨x,hx⟩ := hZ z.property
    have hxZ : (x : G) ∈ RootPullback.rootPreimage A a Z :=
      ⟨x,show a x ∈ Z from hx.symm ▸ z.property,rfl⟩
    change Preliminary.markedAction D m z.val v = v
    rw [←hx]
    exact (fixed_iff_commute D S m A a hact x v).mpr (hv.2 x hxZ)
  · intro hv
    have hv' : v ∈ fixedSpace (Preliminary.markedAction D m) Z := by
      rw [hf]
      exact hv
    refine ⟨(D.spaceEquiv (Multiplicative.ofAdd v)).property,?_⟩
    rintro _ ⟨x,hx,rfl⟩
    exact (fixed_iff_commute D S m A a hact x v).mp (hv' ⟨a x,hx⟩)

include hact in
theorem doubleCentralizer (Z : Subgroup (Model S.field.Carrier))
    (hZ : Z ∈ RootCentralizers.longRoots S.field.Carrier)
    (ha : a.range = EvenTwoRank.elementary S.field.Carrier) :
    A ⊓ centralizer (V ⊓ centralizer (RootPullback.rootPreimage A a Z : Set G) : Set G) =
      RootPullback.rootPreimage A a Z := by
  have hZa : Z ≤ a.range := ha.symm ▸ RootCentralizers.root_le_elementary S.field.Carrier hZ
  apply le_antisymm
  · rintro x ⟨hxA,hx⟩
    let b : A := ⟨x,hxA⟩
    have hb : a b ∈ subspaceKernel (NaturalOffenders.binaryNatural (F:=S.field.Carrier))
        (fixedSpace (NaturalOffenders.binaryNatural (F:=S.field.Carrier)) Z) ⊤ := by
      refine ⟨mem_top _,?_⟩
      intro v hv
      obtain ⟨w,rfl⟩ := (Preliminary.markedProjection_isCover D m).1 v
      have hw := (rootCentralizer_mem D S m A a hact Z hZa w).mpr hv
      have hbfix := (fixed_iff_commute D S m A a hact b w).mpr (hx _ hw).symm
      have he := LinearMap.congr_fun ((Preliminary.markedProjection D m).isIntertwining' (a b)) w
      change Preliminary.markedProjection D m (Preliminary.markedAction D m (a b) w) =
        NaturalOffenders.binaryNatural (a b) (Preliminary.markedProjection D m w) at he
      rw [hbfix] at he
      exact he.symm
    rw [root_fixer_of_mem hZ] at hb
    exact ⟨b,hb,rfl⟩
  · intro x hx
    refine ⟨RootPullback.rootPreimage_le A a Z hx,?_⟩
    intro v hv
    exact (hv.2 x hx).symm

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.ReciprocalRoots


namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.ReciprocalRoots
open Atlas.G2 Atlas.G2.Natural
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier)))
    (A : Subgroup G) (a : A →* Model S.field.Carrier)
    (hact : ∀ (x : A) (v : D.space),
      (D.spaceEquiv (Multiplicative.ofAdd (Preliminary.markedAction D m (a x) v)) : G) =
        (x : G) * (D.spaceEquiv (Multiplicative.ofAdd v) : G) * (x : G)⁻¹)
    (ha : a.range = EvenTwoRank.elementary S.field.Carrier)

include hact ha in
theorem reciprocal_corank (Z : Subgroup (Model S.field.Carrier))
    (hZ : Z ∈ RootCentralizers.longRoots S.field.Carrier) :
    subgroupCorank A (A ⊓ centralizer
      (V ⊓ centralizer (RootPullback.rootPreimage A a Z : Set G) : Set G)) =
        2*S.field.degree := by
  rw [doubleCentralizer D S m A a hact Z hZ ha]
  exact RootPullback.rootPreimage_corank A a ha S.field.card_eq hZ

omit A in
theorem rootCentralizer_normalizes (g : G)
    (a : (V.map (MulAut.conj g).toMonoidHom) →* Model S.field.Carrier)
    (ha : a.range = EvenTwoRank.elementary S.field.Carrier)
    (hr : (2*S.field.degree : ℕ∞) < globalR V)
    (Z : Subgroup (Model S.field.Carrier))
    (hZ : Z ∈ RootCentralizers.longRoots S.field.Carrier) :
    V ⊓ centralizer (RootPullback.rootPreimage _ a Z : Set G) ≤
      normalizer (V.map (MulAut.conj g).toMonoidHom : Set G) := by
  let := D.elementary
  apply inf_le_right.trans
  apply centralizer_le_normalizer_of_corank_lt_globalR (RootPullback.rootPreimage_le _ a Z)
  rw [RootPullback.rootPreimage_corank _ a ha S.field.card_eq hZ,globalR_map_equiv]
  exact_mod_cast hr

include hact ha in
theorem rootCentralizer_noncentral (Z : Subgroup (Model S.field.Carrier))
    (hZ : Z ∈ RootCentralizers.longRoots S.field.Carrier) :
    ⁅A,V ⊓ centralizer (RootPullback.rootPreimage A a Z : Set G)⁆ ≠ ⊥ := by
  intro he
  have hc := reciprocal_corank D S m A a hact ha Z hZ
  have hca : A ⊓ centralizer (V ⊓ centralizer (RootPullback.rootPreimage A a Z : Set G) : Set G) = A :=
    inf_eq_left.mpr (commutator_eq_bot_iff_le_centralizer.mp he)
  have hc0 : subgroupCorank A A = 2*S.field.degree :=
    (congrArg (subgroupCorank A) hca).symm.trans hc
  norm_num [subgroupCorank] at hc0
  have := S.nonbinary
  omega
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.ReciprocalRoots
