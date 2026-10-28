module

public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource.FixedBlockSpecializationComparison
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.MovedSectionModel
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.ModuleIrreducibility
public import Theory.Representation.SpecialLinearThreeTransitivity
public import Theory.ElementaryAbelian.Injective

/-!
# Retaining the block from the fixed-line MS alternative

The commutator equality identifies the intrinsic U(L) with the original V.
The fifth alternative then gives the literal natural quotient of U(L), with
its original quotient marking. Perfectness, characteristic two and natural
irreducibility supply every short-group clause. This is an intrinsic block
statement; L is only known to be normal in LR, not subnormal in G.

Source: Aschbacher--Smith C.1.7, C.1.30 and C.1.34(5), pp.123,135--137;
the shared block calculation before the split in 12.4.6, p.814.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource
open Section02 ChapterC
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

/-- Multiplicative notation for the literal natural binary three-space. -/
def naturalBinaryThreeAction : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) →*
    MulAut (Multiplicative (Fin 3 → ZMod 2)) where
  toFun g := (Matrix.SpecialLinearGroup.toLin' g).toAddEquiv.toMultiplicative
  map_one' := by
    ext v : 1
    change Matrix.SpecialLinearGroup.toLin' 1 v.toAdd = v.toAdd
    rw [map_one]
    rfl
  map_mul' g h := by
    ext v : 1
    change Matrix.SpecialLinearGroup.toLin' (g*h) v.toAdd =
      Matrix.SpecialLinearGroup.toLin' g (Matrix.SpecialLinearGroup.toLin' h v.toAdd)
    rw [map_mul]
    rfl

private theorem naturalBinaryThree_irreducible
    (W : Subgroup (Multiplicative (Fin 3 → ZMod 2)))
    (hi : ∀ a v, v ∈ W → naturalBinaryThreeAction a v ∈ W) : W = ⊥ ∨ W = ⊤ := by
  by_cases hb : W = ⊥
  · exact Or.inl hb
  right
  obtain ⟨v,hv,hv1⟩ := W.bot_or_exists_ne_one.resolve_left hb
  apply top_unique
  intro w _
  by_cases hw : w = 1
  · exact hw ▸ W.one_mem
  obtain ⟨g,hg⟩ := Matrix.SpecialLinearGroup.exists_mulVec_eq_three v.toAdd w.toAdd
    (fun h => hv1 (Multiplicative.toAdd.injective h))
    (fun h => hw (Multiplicative.toAdd.injective h))
  exact (Multiplicative.toAdd.injective hg : naturalBinaryThreeAction g v = w) ▸ hi g v hv

namespace LocalGeometry
variable (d : LocalGeometry D)

/-- Identification of the original subgroup with the intrinsic block commutator. -/
theorem ms_blockU_eq (hQ : msQ L d.R = V) : (blockU L).map L.subtype = V := by
  have hm : (blockU L).map L.subtype = ⁅L.pCoreIn 2, L⁆ := by
    rw [blockU, map_commutator, ← MonoidHom.range_eq_map, range_subtype]
    rfl
  rw [hm]
  apply le_antisymm
  · rw [←hQ]
    exact commutator_mono (pCoreAmbient_mono_of_isSubnormalIn L (L ⊔ d.R) 2
      le_sup_left d.ms_relative_normal.isSubnormal) le_rfl
  · exact D.eq_commutator.le.trans (commutator_mono D.le_componentCore le_rfl)

/-- Convert the retained C.1.34 section to literal conjugation coordinates. -/
def ms_naturalSection
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hcase : FixedMSAlternative L d.R T e) (hQ : msQ L d.R = V) :
    BinaryConjugationSection L ⁅V,L⁆ (⁅V,L⁆ ⊓ centralizer (L : Set G))
      ((specialLinearNatural (k := ZMod 2) 3).comp (linearThreeActor e)) := by
  apply Classical.choice
  have hs := hcase.2.2.1
  rw [hQ, D.eq_commutator] at hs
  obtain ⟨hle,hn,hc,hnorm,f,hf⟩ := hs
  let := hnorm
  exact ⟨{
    section_le := D.eq_commutator ▸ D.le_component
    kernel_le := hle
    normalized := hn
    coordinates := f.toMonoidHom.comp (QuotientGroup.mk' _)
    onto := f.surjective.comp (QuotientGroup.mk'_surjective _)
    kernel_eq := by
      ext a
      change f (QuotientGroup.mk' _ a) = 1 ↔ _
      rw [f.map_eq_one_iff]
      exact QuotientGroup.eq_one_iff a
    equivariant := fun l a => hf l a _ rfl }⟩

/-- The original quotient marking is retained in the intrinsic block model. -/
def ms_blockModel
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hcase : FixedMSAlternative L d.R T e) (hQ : msQ L d.R = V) :
    BlockModuleModel L naturalBinaryThreeAction := by
  let c := d.ms_naturalSection e hcase hQ
  let B := ⁅V,L⁆
  have hu : (blockU L).map L.subtype = B := (d.ms_blockU_eq hQ).trans D.eq_commutator
  let eU : blockU L ≃* B :=
    ((blockU L).equivMapOfInjective L.subtype L.subtype_injective).trans
      (MulEquiv.subgroupCongr hu)
  let Z := (B ⊓ centralizer (L : Set G)).subgroupOf B
  letI : Z.Normal := c.kernel_normal
  have hk : (blockFixed L).map eU.toMonoidHom = Z := by
    ext b
    constructor
    · rintro ⟨a,ha,rfl⟩
      exact ⟨(eU a).property,fun l hl =>
        congrArg L.subtype (mem_center_iff.mp ha ⟨l,hl⟩)⟩
    · intro hb
      refine ⟨eU.symm b,?_,eU.apply_symm_apply b⟩
      apply mem_center_iff.mpr
      intro l
      apply Subtype.ext
      have he : (((eU.symm b : blockU L) : L) : G) = b :=
        congrArg (fun x : B => (x : G)) (eU.apply_symm_apply b)
      change (l : G) * (((eU.symm b : blockU L) : L) : G) =
        (((eU.symm b : blockU L) : L) : G) * (l : G)
      rw [he]
      exact hb.2 l l.property
  exact {
    quotientIso := e
    moduleIso := (QuotientGroup.congr (blockFixed L) Z eU hk).trans c.quotientEquiv
    intertwining := by
      intro l a
      apply Multiplicative.toAdd.injective
      change (c.coordinates (eU (blockConjugate L l a))).toAdd =
        specialLinearNatural 3 (linearThreeActor e l) (c.coordinates (eU a)).toAdd
      exact c.equivariant l (eU a) }

/-- The marking constructed from C.1.34 uses precisely its chosen quotient isomorphism. -/
theorem ms_blockModel_quotientIso
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hcase : FixedMSAlternative L d.R T e) (hQ : msQ L d.R = V) :
    (d.ms_blockModel e hcase hQ).quotientIso = e := rfl

/-- All short-group properties hold on L itself, without ambient subnormality. -/
theorem ms_isShort
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (ext : SLThreeExtension D)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hcase : FixedMSAlternative L d.R T e) (hQ : msQ L d.R = V) : IsShort L := by
  let := (d.ms_component h).perfect
  let : Group.IsPerfect L := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe (show L ≤ L ⊔ d.R from le_sup_left)).toMonoidHom)
    (subgroupOfEquivOfLe (show L ≤ L ⊔ d.R from le_sup_left)).surjective
  have hf : generalizedFitting L = pCore 2 L := by
    apply generalizedFitting_eq_pCore_of_selfCentralizing 2
    intro l hl
    have hc : (l : G) ∈ centralizer (V : Set G) := by
      intro v hv
      obtain ⟨a,ha,he⟩ := D.le_componentCore hv
      change (a : G) = v at he
      have hh := congrArg Subtype.val (hl a ha)
      change (a : G) * (l : G) = (l : G) * (a : G) at hh
      exact he ▸ hh
    obtain ⟨a,ha,he⟩ := (component_centralizer_eq_core D ext).le ⟨l.property,hc⟩
    exact (Subtype.ext he : a = l) ▸ ha
  refine {
    finite := inferInstance
    twoPerfect := ?_
    fitting := hf
    elementary := ?_
    central := ?_
    quotient := Or.inl h.quasisimple
    irreducible := (d.ms_blockModel e hcase hQ).irreducible
      naturalBinaryThreeAction naturalBinaryThree_irreducible }
  · intro N hn hp
    let := hn
    by_contra hne
    let : Nontrivial (L ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
    let : Group.IsPerfect (L ⧸ N) :=
      Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
    let : Group.IsNilpotent (L ⧸ N) := hp.isNilpotent
    exact Group.IsPerfect.not_isSolvable (L ⧸ N) inferInstance
  · let := D.elementary
    let i : blockU L →* V := {
      toFun := fun a => ⟨a,(d.ms_blockU_eq hQ).le (mem_map_of_mem L.subtype a.property)⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
    exact IsElementaryAbelian.of_injective i (fun a b hab =>
      Subtype.ext (Subtype.ext (congrArg (fun v : V => (v : G)) hab)))
  · intro a ha c hc
    apply Subtype.ext
    have hv := (d.ms_blockU_eq hQ).le (mem_map_of_mem L.subtype ha)
    exact ((component_centralizer_eq_core D ext).ge
      (mem_map_of_mem L.subtype hc)).2 a hv |>.symm

/-- The actual natural L₃(2) block, usable by both fixed and moving branches. -/
theorem ms_isLinearTwoBlock
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (ext : SLThreeExtension D)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hcase : FixedMSAlternative L d.R T e) (hQ : msQ L d.R = V) :
    IsLinearTwoBlock L 3 :=
  ⟨by decide, d.ms_isShort h ext e hcase hQ, hmodel,
    naturalBinaryThreeAction, ⟨d.ms_blockModel e hcase hQ⟩, fun _ _ => rfl⟩

end LocalGeometry
end CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource
