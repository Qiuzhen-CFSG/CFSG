module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Models.Torus
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.LinearThreeLocal
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.Symplectic
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.G2

/-!
# Torus exclusions without supplied parabolic markings

The actual smaller image is a proper local C-component at a full Sylow
subgroup. In SL₃, Sp₄ and G₂ the source placement theorems conjugate it to
one of the literal parabolic residuals. Conjugating the group marking and
linear coordinates together applies the proved moving-scalar obstruction.
The literal B.5.1 central quotient is retained; the repeated-three row uses
its original fully moved space and allows every multiplicity.

These results discharge the local-subgroup markings formerly required by
the torus exclusions. Recognition of the containing action and original
rank-one section, and the other source rows, remain with the final owner
qt-d-10-nona5-point-constrained.
Source: Aschbacher--Smith 10.2.9, printed pp.751--752.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource
private def conjugateActionEquiv {A B V W : Type*} [Group A] [Group B]
    [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) A V} {σ : Representation (ZMod 2) B W}
    (E : ActionEquiv ρ σ) (g : B) : ActionEquiv ρ σ where
  groupEquiv := E.groupEquiv.trans (MulAut.conj g)
  linearEquiv := E.linearEquiv.trans (LinearEquiv.ofBijective (σ g) (σ.apply_bijective g))
  intertwines x v := by
    change σ g (E.linearEquiv (ρ x v)) = σ (g * E.groupEquiv x * g⁻¹) (σ g (E.linearEquiv v))
    rw [E.intertwines]
    simp only [map_mul,Module.End.mul_apply,Representation.inv_self_apply]

open Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.PointControl.Constrained
open ChapterA.Section03 Chapter3.Section02 ChapterB.InternalThompsonAction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {t v : G} {I : Subgroup G}
  (c : Context D t v I)
variable [(internalModule D v I).Normal] [IsElementaryAbelian 2 (internalModule D v I)]

omit [IsElementaryAbelian 2 (internalModule D v I)] in
/-- Recognition preserves the actual proper local component and its full Sylow. -/
theorem Context.marked_small_image_local (af : ActionFacts c)
    {M : Type*} [Group M] [Finite M]
    (E : ((I.subgroupOf (pointJoin T v I)).map (actionMk (internalModule D v I))) ≃* M) :
    let B := ((L.subgroupOf (pointJoin T v I)).map (actionMk (internalModule D v I))).subgroupOf
      ((I.subgroupOf (pointJoin T v I)).map (actionMk (internalModule D v I)))
    B.map E.toMonoidHom ≠ ⊤ ∧ ∃ S : Sylow 2 M,
      B.map E.toMonoidHom ∈ localCComponents S := by
  dsimp only
  obtain ⟨hp,R,hR,hl⟩ := af.small_local
  let : Group.IsSolvable E.toMonoidHom.ker := by
    rw [E.toMonoidHom.ker_eq_bot_iff.mpr E.injective]
    infer_instance
  refine ⟨?_, ⟨(R.mapSurjective ((actionMk (internalModule D v I)).subgroupMap_surjective
    (I.subgroupOf (pointJoin T v I)))).mapSurjective E.surjective,
    Chapter1.Section02.localCComponents_map_of_solvable_ker hl E.toMonoidHom⟩⟩
  intro he
  apply hp.ne
  apply map_injective (f := E.toMonoidHom) E.injective
  rw [map_top_of_surjective E.toMonoidHom E.surjective]
  exact he
/-- The SL₃ natural central section is excluded with its local placement proved. -/
theorem Context.no_linearThree_source_section_of_local
    (af : ActionFacts c) {F : Type*} [Field F] [Finite F] [CharP F 2]
    [Algebra (ZMod 2) F] {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (hspan : ⁅D.fullModule,L⁆ ≤ orbitModule D v I)
    (s : MovedSection (action (internalModule D v I)) (Subgroup.map (actionMk (internalModule D v I))
        (Subgroup.subgroupOf I (pointJoin T v I))))
    (E : ActionEquiv (s.central.quotientRepresentation.comp ((Subgroup.map (actionMk (internalModule D v I))
        (Subgroup.subgroupOf I (pointJoin T v I)))).subtype)
      (Representation.restrictScalars (k := ZMod 2) (specialLinearNatural (k := F) 3))) : False := by
  obtain ⟨hp,S,hlocal⟩ := c.marked_small_image_local af E.groupEquiv
  obtain ⟨g,hg⟩ := ChapterA.Section03.SourceEmbeddings.FiveLocalFF.special_linear_three_local_placement
    hF hn S _ hlocal hp
  apply c.no_linearThree_source_section af hF hn e hspan s (conjugateActionEquiv E g)
  simpa only [conjugateActionEquiv, show (E.groupEquiv.trans (MulAut.conj g)).toMonoidHom =
      (MulAut.conj g).toMonoidHom.comp E.groupEquiv.toMonoidHom from rfl, map_map] using hg

/-- The Sp₄ natural central section is excluded with its local placement proved. -/
theorem Context.no_symplecticFour_source_section_of_local
    (af : ActionFacts c) {F : Type*} [Field F] [Finite F] [CharP F 2]
    [Algebra (ZMod 2) F] {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (hspan : ⁅D.fullModule,L⁆ ≤ orbitModule D v I)
    (s : MovedSection (action (internalModule D v I)) (Subgroup.map (actionMk (internalModule D v I))
        (Subgroup.subgroupOf I (pointJoin T v I))))
    (E : ActionEquiv (s.central.quotientRepresentation.comp ((Subgroup.map (actionMk (internalModule D v I))
        (Subgroup.subgroupOf I (pointJoin T v I)))).subtype)
      (Representation.restrictScalars (k := ZMod 2) (symplecticNatural (k := F) 2))) : False := by
  obtain ⟨hp,S,hlocal⟩ := c.marked_small_image_local af E.groupEquiv
  obtain ⟨g,hg⟩ := ChapterA.Section03.SourceEmbeddings.FiveLocalFF.symplectic_local_placement
    hF hn S _ hlocal hp
  apply c.no_symplecticFour_source_section af hF hn e hspan s (conjugateActionEquiv E g)
  simpa only [conjugateActionEquiv, show (E.groupEquiv.trans (MulAut.conj g)).toMonoidHom =
      (MulAut.conj g).toMonoidHom.comp E.groupEquiv.toMonoidHom from rfl, map_map] using hg

/-- The G₂ natural central section is excluded with its local placement proved. -/
theorem Context.no_g2_source_section_of_local
    (af : ActionFacts c) {F : Type*} [Field F] [Finite F] [CharP F 2]
    [Algebra (ZMod 2) F] {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (hspan : ⁅D.fullModule,L⁆ ≤ orbitModule D v I)
    (s : MovedSection (action (internalModule D v I)) (Subgroup.map (actionMk (internalModule D v I))
        (Subgroup.subgroupOf I (pointJoin T v I))))
    (E : ActionEquiv (s.central.quotientRepresentation.comp ((Subgroup.map (actionMk (internalModule D v I))
        (Subgroup.subgroupOf I (pointJoin T v I)))).subtype)
      (Representation.restrictScalars (k := ZMod 2) (Atlas.G2.Natural.action F))) : False := by
  obtain ⟨hp,S,hlocal⟩ := c.marked_small_image_local af E.groupEquiv
  have hlarge : 2 < Nat.card F := by
    rw [hF]
    have := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 2 ≤ n)
    omega
  obtain ⟨g,hg⟩ := ChapterA.Section03.SourceEmbeddings.FiveLocalFF.G2.local_placement
    hlarge S _ hlocal hp
  apply c.no_g2_source_section af hF hn e hspan s (conjugateActionEquiv E g)
  simpa only [conjugateActionEquiv, show (E.groupEquiv.trans (MulAut.conj g)).toMonoidHom =
      (MulAut.conj g).toMonoidHom.comp E.groupEquiv.toMonoidHom from rfl, map_map] using hg


/-- The repeated natural row has the same placement obstruction, for any multiplicity. -/
theorem Context.no_repeatedThree_source_section_of_local
    (af : ActionFacts c) {F : Type*} [Field F] [Finite F] [CharP F 2]
    [Algebra (ZMod 2) F] {n r : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (hspan : ⁅D.fullModule,L⁆ ≤ orbitModule D v I)
    (s : MovedSection (action (internalModule D v I))
      ((I.subgroupOf (pointJoin T v I)).map (actionMk (internalModule D v I))))
    (E : ActionEquiv (s.space.toRepresentation.comp
      ((I.subgroupOf (pointJoin T v I)).map (actionMk (internalModule D v I))).subtype)
      (repeated (Representation.restrictScalars (k := ZMod 2)
        (specialLinearNatural (k := F) 3)) r)) : False := by
  obtain ⟨hp,S,hlocal⟩ := c.marked_small_image_local af E.groupEquiv
  obtain ⟨g,hg⟩ := ChapterA.Section03.SourceEmbeddings.FiveLocalFF.special_linear_three_local_placement
    hF hn S _ hlocal hp
  let E' := conjugateActionEquiv E g
  have hm := c.fully_moved_of_moved_le hspan
  let j : Additive (internalModule D v I) →ₗ[ZMod 2] s.space.toSubmodule :=
    (LinearMap.id : Additive (internalModule D v I) →ₗ[ZMod 2]
      Additive (internalModule D v I)).codRestrict s.space.toSubmodule
      (fun _ => by rw [s.space_eq,hm]; trivial)
  apply c.no_linearThree_natural_sum af hF hn e hspan E'.groupEquiv
    (by simpa only [E',conjugateActionEquiv,show (E.groupEquiv.trans (MulAut.conj g)).toMonoidHom =
      (MulAut.conj g).toMonoidHom.comp E.groupEquiv.toMonoidHom from rfl,map_map] using hg)
    ((E'.linearEquiv.toLinearMap.comp j).prod
      (0 : Additive (internalModule D v I) →ₗ[ZMod 2] (Empty → Fin 3 → F)))
  · intro z hz
    have he : E'.linearEquiv (j z) = 0 := congrArg Prod.fst hz
    have hz' : z = 0 := congrArg Subtype.val
      (E'.linearEquiv.injective (he.trans E'.linearEquiv.map_zero.symm))
    exact hz' ▸ (fixedSpace _ _).zero_mem
  · intro x z
    apply Prod.ext
    · exact E'.intertwines x (j z)
    · funext i
      exact Empty.elim i
end CFSG.Quasithin.Chapter10.PointControl.Constrained
