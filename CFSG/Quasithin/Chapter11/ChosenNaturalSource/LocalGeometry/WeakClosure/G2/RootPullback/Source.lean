module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.RootPullback
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.Localization.Consumers

/-!
# The original G₂ actor and flag in the corrected root transfer

The actual conjugation map is reindexed by the same L/O₂(L) marking. Its
kernel is the original relative centralizer, and it intertwines the action
on the entire chosen module. The proved parameter family makes every
noncentral zeroth conjugate an inner actor and gives the strict r-bound;
the linear-three exception is excluded on the same central quotient.

The common-frame theorem identifies the model third preimage with an actual
L-conjugate of the supplied flag. The final application therefore retains
both the literal flag and its central kernel in the root containment.
Recognition of the q³ actor image, recovery of the central term, and reciprocal
plane reconstruction are still local obligations of
qt-d-1222-natural-weak-closure-source. The final application states its
recognized actor input explicitly; it does not prove unconditional 11.2.2(5).
The earlier maximal-local, third-space and fixed-line premises remain with
their existing source owners and qt-d-1222-natural-local-geometry.

Source: Aschbacher--Smith, 11.2.2(3--5), printed pp.767--768.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open scoped IsMulCommutative
open Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterE
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.RootPullback
open Atlas.G2 Atlas.G2.Natural Parameters.FullAutomizer Parameters.RootActors
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier)))
    {A : Subgroup G} (hAN : A ≤ normalizer (V : Set G))
    (hinner : inducedAutomizer V A ≤ inducedAutomizer V L)

/-- The actual conjugation map, reindexed by the original component marking. -/
def innerActor : A →* Model S.field.Carrier :=
  (layerEquiv D S (Coordinates.g2 m)).toMonoidHom.comp
    (((V.normalizerMonoidHom.rangeRestrict).comp (inclusion hAN)).codRestrict
      (inducedAutomizer V L) (fun x => hinner ⟨inclusion hAN x,x.property,rfl⟩))

/-- The actor realizes conjugation on the full chosen module, not just its quotient. -/
theorem innerActor_action (x : A) (v : D.space) :
    (D.spaceEquiv (Multiplicative.ofAdd
      (Preliminary.markedAction D m (innerActor D S m hAN hinner x) v)) : G) =
      (x : G) * (D.spaceEquiv (Multiplicative.ofAdd v) : G) * (x : G)⁻¹ := by
  let b : inducedAutomizer V L :=
    ⟨V.normalizerMonoidHom.rangeRestrict (inclusion hAN x),
      hinner ⟨inclusion hAN x,x.property,rfl⟩⟩
  obtain ⟨l,hl⟩ := layerAction_surjective D b
  have ha : innerActor D S m hAN hinner x = (Coordinates.g2 m).quotientMap l := by
    change layerEquiv D S (Coordinates.g2 m) b = _
    rw [←hl,layerEquiv_apply]
  rw [ha]
  change (D.spaceEquiv (Multiplicative.ofAdd
    (Preliminary.markedAction D m (m.groupEquiv (QuotientGroup.mk' (pCore 2 L) l)) v)) : G) = _
  rw [Preliminary.markedAction_mk]
  have he := congrArg (fun z : inducedAutomizer V L =>
    ((z.val.val) (D.spaceEquiv (Multiplicative.ofAdd v)) : G)) hl
  have hc : (D.spaceEquiv (Multiplicative.ofAdd (D.chosenAction l v)) : G) =
      (l : G) * (D.spaceEquiv (Multiplicative.ofAdd v) : G) * (l : G)⁻¹ := by
    rw [D.spaceEquiv_apply,D.spaceEquiv_apply]
    rfl
  exact hc.trans he

/-- The exact original centralizer is the kernel of this actor homomorphism. -/
theorem innerActor_ker :
    (innerActor D S m hAN hinner).ker = (centralizer (V : Set G)).subgroupOf A := by
  ext x
  change innerActor D S m hAN hinner x = 1 ↔ (x : G) ∈ centralizer (V : Set G)
  constructor
  · intro hx v hv
    let w : D.space := (D.spaceEquiv.symm ⟨v,hv⟩).toAdd
    have he := innerActor_action D S m hAN hinner x w
    rw [hx,map_one,Module.End.one_apply] at he
    simp only [w,ofAdd_toAdd,MulEquiv.apply_symm_apply] at he
    exact (mul_inv_eq_iff_eq_mul.mp he.symm).symm
  · intro hx
    change layerEquiv D S (Coordinates.g2 m)
      ⟨V.normalizerMonoidHom.rangeRestrict (inclusion hAN x), _⟩ = 1
    apply (map_eq_one_iff _ (layerEquiv D S (Coordinates.g2 m)).injective).mpr
    apply Subtype.ext
    apply Subtype.ext
    apply MulEquiv.ext
    intro v
    apply Subtype.ext
    exact mul_inv_eq_iff_eq_mul.mpr (hx v.val v.property).symm
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.RootPullback

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.RootPullback
open Atlas.G2 Atlas.G2.Natural Parameters.FullAutomizer Parameters.RootActors
open CFSG.Quasithin.ChapterE.Section06
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier)))
    (f : InvariantFlag (Coordinates.g2 m))

/-- The standard full third preimage is an actual L-conjugate of the supplied flag. -/
theorem exists_flag_conjugate : ∃ l : L,
    (Coordinates.g2 m).preimage
      ((NaturalOffenders.upper (F := S.field.Carrier)).comap
        (Restricted.NaturalCoordinates.coordinates S.field.Carrier)) =
      (f.Vi 2).map (MulAut.conj (l : G)).toMonoidHom := by
  obtain ⟨b,-,hthree,-⟩ := Localization.exists_common_frame D S m f
  obtain ⟨l,hl⟩ := (Coordinates.g2 m).quotientMap_surjective b⁻¹
  refine ⟨l,?_⟩
  rw [InvariantFlag.Vi, (Coordinates.g2 m).preimage_conjugate, hl]
  change _ = (Coordinates.g2 m).preimage ((f.space 2).map (Natural.action S.field.Carrier b⁻¹))
  rw [hthree,←Submodule.map_comp]
  have he : (Natural.action S.field.Carrier b⁻¹).comp (Natural.action S.field.Carrier b) =
      LinearMap.id := by
    apply LinearMap.ext
    intro v
    exact (Natural.action S.field.Carrier).inv_self_apply b v
  rw [he,Submodule.map_id]
  rfl

include m in
/-- The G₂ marking excludes the linear-three exception using the same central quotient. -/
theorem not_linearThree :
    ¬ Nonempty (ActionEquiv D.centralQuotientAction (linearNatural S.field 3)) := by
  rintro ⟨m3⟩
  have hd (c : Coordinates D S.field) :
      subgroupCorank V (V ⊓ centralizer (L : Set G)) =
        S.field.degree * Module.finrank S.field.Carrier c.Space := by
    rw [←c.preimage_bot, Parameters.NaturalDimensions.pullback_corank D S c]
    rw [(Submodule.quotEquivOfEqBot (⊥ : Submodule S.field.Carrier c.Space) rfl).finrank_eq]
  have h6 := hd (Coordinates.g2 m)
  have h3 := hd (Coordinates.sl3 m3)
  rw [Parameters.NaturalDimensions.field_dimension] at h6 h3
  have hn := S.nonbinary
  dsimp only at h6 h3
  omega

/-- The strict r-bound in this marking follows from the completed parameter family. -/
theorem strict_globalR_of_preceding
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N → L ≤ N → N = normalizer (L : Set G))
    (hthree : centralizer (f.Vi 2 : Set G) ≤ normalizer (L : Set G))
    (hline : f.Vi 0 ≤ V ⊓ centralizer (sourceTL T L : Set G)) :
    (2 * S.field.degree : ℕ∞) < globalR V := by
  rcases (Parameters.source_parameters D S f hunique hthree hline).2.2.1.1 with hr | hr
  · exact hr
  · exact (not_linearThree D S m hr.1).elim

include m in
/-- Every noncentral original zeroth conjugate has inner action on V. -/
theorem conjugate_image_inner
    (hs : @globalS G _ V D.elementary = (2 * S.field.degree : ℕ))
    (g : G) (hg : V.map (MulAut.conj g).toMonoidHom ≤ T)
    (hnon : ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥) :
    inducedAutomizer V (V.map (MulAut.conj g).toMonoidHom) ≤ inducedAutomizer V L := by
  let := D.elementary
  let A := V.map (MulAut.conj g).toMonoidHom
  have hAN : A ≤ normalizer (V : Set G) := hg.trans S.sylow_normalizes
  have hcor : subgroupCorank A A = 0 := by simp [subgroupCorank]
  have hb : (subgroupCorank A A : ℕ∞) < globalS V := by
    rw [hcor,hs]
    exact_mod_cast (by have := S.nonbinary; omega : 0 < 2 * S.field.degree)
  have hfamily := (inducedAutomizer_mem_fixedSpaceFamily_of_corank_lt_globalS g
    (le_inf le_rfl hAN) hb hnon).2
  rw [hs,ENat.toNat_natCast,hcor,Nat.sub_zero] at hfamily
  exact g2_original_two_family_inner D S m _
    (fixedSpaceFamily_mono (automizerRepresentation V) (by decide)
      (by have := S.nonbinary; omega : 2 ≤ 2 * S.field.degree) hfamily)

/-- Actual inner conjugation coordinates, with exactly the original centralizer kernel. -/
theorem exists_conjugate_actor
    (hs : @globalS G _ V D.elementary = (2 * S.field.degree : ℕ))
    (g : G) (hg : V.map (MulAut.conj g).toMonoidHom ≤ T)
    (hnon : ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥) :
    ∃ a : (V.map (MulAut.conj g).toMonoidHom) →* Model S.field.Carrier,
      (∀ (x : V.map (MulAut.conj g).toMonoidHom) (v : D.space),
        (D.spaceEquiv (Multiplicative.ofAdd (Preliminary.markedAction D m (a x) v)) : G) =
          (x : G) * (D.spaceEquiv (Multiplicative.ofAdd v) : G) * (x : G)⁻¹) ∧
      a.ker = (centralizer (V : Set G)).subgroupOf (V.map (MulAut.conj g).toMonoidHom) := by
  have hinner := conjugate_image_inner D S m hs g hg hnon
  exact ⟨innerActor D S m (hg.trans S.sylow_normalizes) hinner,
    innerActor_action D S m (hg.trans S.sylow_normalizes) hinner,
    innerActor_ker D S m (hg.trans S.sylow_normalizes) hinner⟩

/-- Literal flag application of the corrected root transfer. Only earlier
source clauses and the explicit recognized root action remain as inputs. -/
theorem flag_containment_of_preceding
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N → L ≤ N → N = normalizer (L : Set G))
    (hthree : centralizer (f.Vi 2 : Set G) ≤ normalizer (L : Set G))
    (hline : f.Vi 0 ≤ V ⊓ centralizer (sourceTL T L : Set G))
    (g : G) (a : (V.map (MulAut.conj g).toMonoidHom) →* Model S.field.Carrier)
    (hact : ∀ (x : V.map (MulAut.conj g).toMonoidHom) (v : D.space),
      (D.spaceEquiv (Multiplicative.ofAdd (Preliminary.markedAction D m (a x) v)) : G) =
        (x : G) * (D.spaceEquiv (Multiplicative.ofAdd v) : G) * (x : G)⁻¹)
    (ha : a.range = EvenTwoRank.elementary S.field.Carrier) :
    ∃ l : L,
      (f.Vi 2).map (MulAut.conj (l : G)).toMonoidHom ≤
        V.map (MulAut.conj g).toMonoidHom ⊔ (V ⊓ centralizer (L : Set G)) ∧
      ((f.Vi 2).map (MulAut.conj (l : G)).toMonoidHom ≤
          V.map (MulAut.conj g).toMonoidHom ↔
        V ⊓ centralizer (L : Set G) ≤ V.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨l,hl⟩ := exists_flag_conjugate D S m f
  have hr := strict_globalR_of_preceding D S m f hunique hthree hline
  refine ⟨l,?_,?_⟩
  · rw [←hl]
    exact threePreimage_le_conjugate_sup D S m g a hact ha hr
  · rw [←hl]
    exact threePreimage_le_conjugate_iff D S m g a hact ha hr
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.RootPullback
