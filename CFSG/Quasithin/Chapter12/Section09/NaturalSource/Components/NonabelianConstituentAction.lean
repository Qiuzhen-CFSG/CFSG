module
public import Theory.Representation.BinaryOffender.ConstituentKernel
public import CFSG.Quasithin.ChapterG.Section10.Components.ActionImage
public import CFSG.Quasithin.ChapterG.Section10.Components.CentralizerDisplacement
public import CFSG.Quasithin.ChapterG.Section09.TwoComponents.SharpDegree
public import CFSG.Quasithin.ChapterG.Section09.CoverComponents
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.AlternatingSixCover
public import Theory.Representation.BinaryOffender.Homogeneous.DoubleCoordinates
public import Theory.Representation.BinaryOffender.Homogeneous.SchurDisplacementRank
public import Theory.Representation.BinaryAlternatingSixModels.CatalogueSource
public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.Six.FourSpace

/-!
# The marked constituent and its literal action quotient

For a proper marked constituent faithful for the elementary actor, the sharp
G.9 degree bound makes the normal component orbit a single component. The
faithful restriction lifts that equality back through the actual action
quotient. The quotient isomorphism preserves the original projection, fixed
line and self-duality for the same normal group.

The actor kernel is its centralizer of the normal orbit. Centralizing actor
displacements and the Schur rank bound are retained for the nonfaithful
branch. For an A₆ orbit, faithful conjugation bounds the actor rank by three;
module recognition and homogeneity then construct doubled natural coordinates.
These results are applied to the original flag in `NonabelianConstituents`.

Source: Aschbacher--Smith G.11.6--9, printed pp.365--369.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components

namespace FixedLineConstituent
variable {D A : Type*} [Group D] [Finite D] [AddCommGroup A]
  [Module (ZMod 2) A] [FiniteDimensional (ZMod 2) A]
  {ρ : Representation (ZMod 2) D A} {B : LinearMap.BilinForm (ZMod 2) A}
  {v : A} {W : Submodule (ZMod 2) A} {X : Subgroup D}
  [IsElementaryAbelian 2 X] {X₀ : Subgroup X}

/-- In the proper faithful marked branch the original normal orbit is a
single component, not merely a single image after quotienting. -/
theorem orbit_eq_of_proper_faithful
    (h : ChapterG.Section10.Hypothesis ρ B v W X X₀)
    (cover : Nonempty (ChapterG.Section09.SQTKCover KnownSimple.IsKnownSimple D))
    (hn : ¬ Group.IsSolvable D) {J : Subgroup D} (hJ : IsComponent D J)
    (hm : ⁅J,X⁆ ≠ ⊥) (S : Sylow 2 D)
    (hnX : (S : Subgroup D) ≤ normalizer (X : Set D))
    {I : Submodule (ZMod 2) A} (hI : IsIrrPlus ρ (componentOrbit J ⊤) I)
    (hv : v ∈ I) (hp : I ≠ ⊤)
    (hfX : Function.Injective (fun x : X => (ρ (x : D)).comp I.subtype)) :
    componentOrbit J ⊤ = J := by
  let H := componentOrbit J ⊤
  let : H.Normal := componentOrbit_top_normal J
  have hi := h.irreducible_of_not_solvable hn
  have hXI := h.stabilizes_constituent_of_point_mem hi H hI hv
  have hind := cover.some.component_normalizer_index_le_two hJ
  obtain ⟨hh,hf,hs,hiso | ⟨he,_⟩⟩ :=
    h.constituent_homogeneous_faithful_selfDual_of_point_mem hn hJ hm S hnX hind hI hv
  swap
  · exact (hp he).elim
  let σ := ChapterG.Section09.constituentAction ρ H X I hI.choose hXI
  let P := H ⊔ X
  let q := QuotientGroup.mk' σ.ker
  have h9 := h.componentHypothesis_of_marked_constituent cover hn hJ hm S hnX hind hI hv hfX
  have he : (H.subgroupOf P).map q = (J.subgroupOf P).map q :=
    ChapterG.Section09.TwoComponents.single_component_of_sharp_degree h9
      ((h.isotropic_degree_le_actor_rank_add_one hiso).trans (by omega))
  apply le_antisymm ?_ (le_componentOrbit J ⊤)
  intro a ha
  have hqa : q ⟨a,(show H ≤ P from le_sup_left) ha⟩ ∈ (H.subgroupOf P).map q :=
    mem_map.mpr ⟨_,ha,rfl⟩
  rw [he] at hqa
  obtain ⟨b,hb,hba⟩ := mem_map.mp hqa
  have hab : (⟨(b : D),(le_componentOrbit J ⊤) hb⟩ : H) = ⟨a,ha⟩ := by
    apply hf
    exact congrArg (kerRepresentation σ) hba
  have hba : (b : D) = a := congrArg (fun z : H => (z : D)) hab
  change (b : D) ∈ J at hb
  simpa only [hba] using hb
end FixedLineConstituent

namespace FixedLineConstituent
variable {D A : Type*} [Group D] [AddCommGroup A] [Module (ZMod 2) A]

/-- The actual component embeds in the constituent quotient with its projection
preserved. The same intertwiner and marked point descend through that quotient. -/
theorem quotient_markings
    (ρ : Representation (ZMod 2) D A) (H X : Subgroup D)
    (I : Submodule (ZMod 2) A) (hH : H ≤ subspaceStabilizer ρ I)
    (hX : X ≤ subspaceStabilizer ρ I)
    (hfH : Function.Injective (invariantSubspace ρ H I hH).toRepresentation)
    (hs : Nonempty (Representation.Equiv (invariantSubspace ρ H I hH).toRepresentation
      (invariantSubspace ρ H I hH).toRepresentation.dual))
    (v : I) (hfix : fixedSpace ρ X = Submodule.span (ZMod 2) {(v : A)}) :
    let σ := ChapterG.Section09.constituentAction ρ H X I hH hX
    let q := QuotientGroup.mk' σ.ker
    let Hbar := (H.subgroupOf (H ⊔ X)).map q
    let Xbar := (X.subgroupOf (H ⊔ X)).map q
    (∃ e : H ≃* Hbar, ∀ a : H,
      (e a : (H ⊔ X : Subgroup D) ⧸ σ.ker) =
        q ⟨a,(show H ≤ H ⊔ X from le_sup_left) a.property⟩) ∧
    Nonempty (Representation.Equiv ((kerRepresentation σ).comp Hbar.subtype)
      (Representation.dual ((kerRepresentation σ).comp Hbar.subtype))) ∧
    fixedSpace (kerRepresentation σ) Xbar = Submodule.span (ZMod 2) {v} := by
  intro σ q Hbar Xbar
  let p : H →* Hbar := (q.subgroupMap (H.subgroupOf (H ⊔ X))).comp
    (subgroupOfEquivOfLe (show H ≤ H ⊔ X from le_sup_left)).symm.toMonoidHom
  have hp : Function.Bijective p := by
    constructor
    · intro a b he
      apply hfH
      exact congrArg (kerRepresentation σ) (congrArg Subtype.val he)
    · exact (q.subgroupMap_surjective _).comp
        (subgroupOfEquivOfLe (show H ≤ H ⊔ X from le_sup_left)).symm.surjective
  refine ⟨⟨MulEquiv.ofBijective p hp,fun _ => rfl⟩,?_,?_⟩
  · obtain ⟨e⟩ := hs
    refine ⟨Representation.Equiv.mk e.toLinearEquiv ?_⟩
    intro a
    obtain ⟨b,rfl⟩ := q.subgroupMap_surjective (H.subgroupOf (H ⊔ X)) a
    exact e.isIntertwining' ⟨b,b.property⟩
  · ext w
    constructor
    · intro hw
      have hwX : (w : A) ∈ fixedSpace ρ X := by
        intro x
        let a : (H ⊔ X : Subgroup D) := ⟨x,(show X ≤ H ⊔ X from le_sup_right) x.property⟩
        exact congrArg Subtype.val (hw ⟨q a,mem_map_of_mem q x.property⟩)
      rw [hfix,Submodule.mem_span_singleton] at hwX
      obtain ⟨c,hc⟩ := hwX
      exact Submodule.mem_span_singleton.mpr ⟨c,Subtype.ext hc⟩
    · intro hw a
      obtain ⟨c,rfl⟩ := Submodule.mem_span_singleton.mp hw
      obtain ⟨x,rfl⟩ := q.subgroupMap_surjective (X.subgroupOf (H ⊔ X)) a
      have hv : (v : A) ∈ fixedSpace ρ X := hfix ▸ Submodule.mem_span_singleton_self _
      apply Subtype.ext
      change ρ (x : (H ⊔ X : Subgroup D)) (c • (v : A)) = c • (v : A)
      rw [map_smul,show ρ (x : (H ⊔ X : Subgroup D)) (v : A) = v from hv ⟨x,x.property⟩]
end FixedLineConstituent

/-- Faithfulness of the original elementary actor on a proper A₆ constituent
forces actual doubled natural coordinates on the whole homogeneous module. -/
theorem FixedLineConstituent.double_six_of_proper_faithful
    {D A : Type*} [Group D] [Finite D] [AddCommGroup A]
    [Module (ZMod 2) A] [FiniteDimensional (ZMod 2) A]
    {ρ : Representation (ZMod 2) D A} {B : LinearMap.BilinForm (ZMod 2) A}
    {v : A} {W : Submodule (ZMod 2) A} {X : Subgroup D}
    [IsElementaryAbelian 2 X] {X₀ : Subgroup X}
    (hg10 : ChapterG.Section10.Hypothesis ρ B v W X X₀)
    (hns : ¬ Group.IsSolvable D) (cover : ChapterG.Section09.SQTKCover KnownSimple.IsKnownSimple D)
    (S : Sylow 2 D) (hnX : (S : Subgroup D) ≤ normalizer (X : Set D))
    {J : Subgroup D} (hJ : IsComponent D J) (hm : ⁅J,X⁆ ≠ ⊥)
    {I : Submodule (ZMod 2) A} (hI : IsIrrPlus ρ (componentOrbit J ⊤) I)
    (hv : v ∈ I) (hp : I ≠ ⊤)
    (hfX : Function.Injective (fun x : X => (ρ (x : D)).comp I.subtype))
    (e : componentOrbit J ⊤ ≃* alternatingGroup (Fin 6)) :
    ChapterG.Section09.Quasiequivalent (ρ.comp (componentOrbit J ⊤).subtype)
      ((BinaryPermutation.alternatingNaturalRepresentation (Fin 6)).prod
        (BinaryPermutation.alternatingNaturalRepresentation (Fin 6))) := by
  let H := componentOrbit J ⊤
  let : H.Normal := componentOrbit_top_normal J
  let R := invariantSubspace ρ H I hI.choose
  have hi := hg10.irreducible_of_not_solvable hns
  have hind := cover.component_normalizer_index_le_two hJ
  obtain ⟨hh,hfH,_,_⟩ := hg10.constituent_homogeneous_faithful_selfDual_of_point_mem
    hns hJ hm S hnX hind hI hv
  have hXI := hg10.stabilizes_constituent_of_point_mem hi H hI hv
  have hC := constituent_kernel_eq_centralizer ρ H X I hI hXI hfH
  let f : X →* MulAut H := (MulAut.conjNormal : D →* MulAut H).comp X.subtype
  have hf : Function.Injective f := by
    apply (injective_iff_map_eq_one f).mpr
    intro x hx
    have hc : (x : D) ∈ centralizer (H : Set D) := by
      rw [← MulAut.conjNormal_ker_eq_centralizer]
      exact hx
    have hxI : (invariantSubspace ρ X I hXI).toRepresentation x = 1 := by
      change x ∈ (invariantSubspace ρ X I hXI).toRepresentation.ker
      rw [hC]
      exact hc
    apply hfX
    apply LinearMap.ext
    intro w
    have he := congrArg (fun a : Module.End (ZMod 2) I => (a w : A)) hxI
    change ρ (x : D) (w : A) = (w : A) at he
    change ρ (x : D) (w : A) = ρ (1 : D) (w : A)
    simpa only [map_one, Module.End.one_apply] using he
  let r := finrank (ZMod 2) (Additive X)
  have hr : r ≤ primeRank 2 (MulAut H) := by
    let : CommGroup X := IsMulCommutative.instCommGroup
    exact primeRank_ge_of_elementary_embedding
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 X))
      (by rw [Nat.card_congr Additive.ofMul,
        Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]) f hf
  rw [primeRank_equiv 2 (MulAut.congr e)] at hr
  have hrank := ChapterG.Section09.DefiningCharacteristic.AlternatingSixCover.alternating_six_automorphism_two_rank
  have hdegree : finrank (ZMod 2) A ≤ 8 := by
    have hd := hg10.dimension_bound.1
    have hq := (Group.rank_le_of_surjective
      (QuotientGroup.mk' X₀)
      (QuotientGroup.mk'_surjective _)).trans (IsElementaryAbelian.rank_le_finrank (p := 2) X)
    dsimp only [r] at hr
    omega
  let τ := R.toRepresentation.comp e.symm.toMonoidHom
  let : IsIrreducible τ := (irreducible_comp_surjective_iff
    e.symm.toMonoidHom e.symm.surjective _).mpr
      (hI.irreducible_of_normal_restriction ρ hi H)
  have hτ : Function.Injective τ := hfH.comp e.symm.injective
  have hspectrum := BinaryAlternatingSix.alternating_degrees τ
  change finrank (ZMod 2) I = 1 ∨ finrank (ZMod 2) I = 4 ∨
    finrank (ZMod 2) I = 16 at hspectrum
  let : Group.IsPerfect H := hJ.orbit_isPerfect ⊤
  have hlow : 3 ≤ finrank (ZMod 2) I := hI.finrank_gt_two ρ H
  have hup : finrank (ZMod 2) I ≤ 8 := I.finrank_le.trans hdegree
  have hI4 : finrank (ZMod 2) I = 4 := by
    rcases hspectrum with ht | ht | ht <;> omega
  obtain ⟨a⟩ := ChapterK.Alternating.RecognitionInputs.Six.actionEquiv_of_faithful_fourSpace τ hτ hI4
  let c := a.linearEquiv
  have hc (k : H) (w : I) : c (R.toRepresentation k w) =
      BinaryPermutation.alternatingNaturalRepresentation (Fin 6) ((e.trans a.groupEquiv) k) (c w) := by
    have he := a.intertwines (e k) w
    simpa only [τ,ChapterB.QuasisimpleSource.alternatingNatural,
      MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,MulEquiv.symm_apply_apply,
      MulEquiv.trans_apply] using he
  have hbound : finrank (ZMod 2) A ≤ 2 * finrank (ZMod 2) I := by omega
  obtain ⟨d⟩ := Homogeneous.double_coordinates_of_degree_le R
    (hI.irreducible_of_normal_restriction ρ hi H) hh hp hbound
  refine ⟨e.trans a.groupEquiv,d.toLinearEquiv.trans (c.prodCongr c),?_⟩
  intro a w
  have hd := LinearMap.congr_fun (d.isIntertwining' a) w
  change d (ρ a w) = (R.toRepresentation a (d w).1,R.toRepresentation a (d w).2) at hd
  change (c (d (ρ a w)).1,c (d (ρ a w)).2) = _
  rw [hd]
  exact Prod.ext (hc a (d w).1) (hc a (d w).2)

/-- Literal marked constituent data: the original orbit, actor kernel,
displacements, and quotient markings are all retained. -/
@[expose] def FixedLineConstituent.MarkedData
    {D A : Type*} [Group D] [Finite D] [AddCommGroup A]
    [Module (ZMod 2) A] [FiniteDimensional (ZMod 2) A]
    (ρ : Representation (ZMod 2) D A) (B : LinearMap.BilinForm (ZMod 2) A)
    (v : A) (X J : Subgroup D) [IsElementaryAbelian 2 X]
    (I : Submodule (ZMod 2) A)
    (hI : Homogeneous.IsIrrPlusWith ρ (componentOrbit J ⊤) X I) : Prop :=
  ∃ hv : v ∈ I, I ≠ ⊤ ∧
    let R := invariantSubspace ρ (componentOrbit J ⊤) I hI.invariant
    Homogeneous.homogeneousPart R ⊤ = ⊤ ∧
    Function.Injective R.toRepresentation ∧
    Nonempty (Representation.Equiv R.toRepresentation R.toRepresentation.dual) ∧
    (∀ a ∈ I, ∀ b ∈ I, B a b = 0) ∧
    finrank (ZMod 2) I ≤ finrank (ZMod 2) (Additive X) + 1 ∧
    finrank (ZMod 2) (Additive X) ≤
      finrank (ZMod 2) (IntertwiningMap R.toRepresentation R.toRepresentation) +
        primeRank 2 (MulAut (componentOrbit J ⊤)) ∧
    ∃ hXI : X ≤ subspaceStabilizer ρ I,
      (invariantSubspace ρ X I hXI).toRepresentation.ker =
        (centralizer (componentOrbit J ⊤ : Set D)).subgroupOf X ∧
      (∀ c : X,
        (c : D) ∈ centralizer (componentOrbit J ⊤ : Set D) → c ≠ 1 →
        LinearMap.range (ρ c - LinearMap.id) = I ∧
        LinearMap.ker (ρ c - LinearMap.id) = B.orthogonal I) ∧
      let H := componentOrbit J ⊤
      let σ := ChapterG.Section09.constituentAction ρ H X I hI.invariant hXI
      let q := QuotientGroup.mk' σ.ker
      let Hbar := (H.subgroupOf (H ⊔ X)).map q
      let Xbar := (X.subgroupOf (H ⊔ X)).map q
      (∃ e : H ≃* Hbar, ∀ a : H,
        (e a : (H ⊔ X : Subgroup D) ⧸ σ.ker) =
          q ⟨a,(show H ≤ H ⊔ X from le_sup_left) a.property⟩) ∧
      Nonempty (Representation.Equiv ((kerRepresentation σ).comp Hbar.subtype)
        (Representation.dual ((kerRepresentation σ).comp Hbar.subtype))) ∧
      fixedSpace (kerRepresentation σ) Xbar = Submodule.span (ZMod 2) {(⟨v,hv⟩ : I)} ∧
      (Function.Injective (fun x : X =>
        (ρ (x : D)).comp I.subtype) →
        componentOrbit J ⊤ = J ∧
        ChapterG.Section09.ComponentHypothesis KnownSimple.IsKnownSimple (kerRepresentation σ)
          Xbar ((J.subgroupOf (H ⊔ X)).map q) Hbar (finrank (ZMod 2) (Additive X)))

/-- Construct marked data from the actual fixed line, retaining the whole
irreducible alternative until the original point-component argument excludes it. -/
theorem FixedLineConstituent.marked_or_whole_of_point_mem
    {D A : Type*} [Group D] [Finite D] [AddCommGroup A]
    [Module (ZMod 2) A] [FiniteDimensional (ZMod 2) A]
    {ρ : Representation (ZMod 2) D A} {B : LinearMap.BilinForm (ZMod 2) A}
    {v : A} {W : Submodule (ZMod 2) A} {X : Subgroup D}
    [IsElementaryAbelian 2 X] {X₀ : Subgroup X}
    (hg10 : ChapterG.Section10.Hypothesis ρ B v W X X₀)
    (hns : ¬ Group.IsSolvable D) (cover : ChapterG.Section09.SQTKCover KnownSimple.IsKnownSimple D)
    (S : Sylow 2 D) (hnX : (S : Subgroup D) ≤ normalizer (X : Set D))
    {J : Subgroup D} (hJ : IsComponent D J) (hm : ⁅J,X⁆ ≠ ⊥)
    {I : Submodule (ZMod 2) A}
    (hI : Homogeneous.IsIrrPlusWith ρ (componentOrbit J ⊤) X I) (hv : v ∈ I)
    (hfix : fixedSpace ρ X = Submodule.span (ZMod 2) {v}) :
    FixedLineConstituent.MarkedData ρ B v X J I hI ∨
      IsIrreducible (ρ.comp (componentOrbit J ⊤).subtype) := by
  have hind := cover.component_normalizer_index_le_two hJ
  obtain ⟨hh,hf,hs,hiso | ⟨ht,hi⟩⟩ :=
    hg10.constituent_homogeneous_faithful_selfDual_of_point_mem hns hJ hm S hnX hind hI.isIrrPlus hv
  swap
  · exact Or.inr hi
  have hp : I ≠ ⊤ := by
    intro he
    have hz : ∀ a b : A, B a b = 0 := fun a b => hiso a (he ▸ Submodule.mem_top)
      b (he ▸ Submodule.mem_top)
    exact hg10.point_ne_zero (hg10.nondegenerate.1 v (hz v))
  let := componentOrbit_top_normal J
  have hi := hg10.irreducible_of_not_solvable hns
  have hXI := hg10.stabilizes_constituent_of_point_mem hi (componentOrbit J ⊤) hI.isIrrPlus hv
  let : Group.IsPerfect (componentOrbit J ⊤) := hJ.orbit_isPerfect ⊤
  let R := invariantSubspace ρ (componentOrbit J ⊤) I hI.invariant
  have hir : IsIrreducible R.toRepresentation :=
    hI.isIrrPlus.irreducible_of_normal_restriction ρ hi (componentOrbit J ⊤)
  have hdis := hg10.centralizer_displacement_range_and_ker hi (componentOrbit J ⊤)
    hJ.componentOrbit_top_ne_bot R hir hh hv (hI.isIrrPlus.finrank_gt_two ρ (componentOrbit J ⊤))
  have hr := finrank_le_schur_add_automorphism_rank ρ hg10.faithful
    (componentOrbit J ⊤) X R (B.orthogonal I) hdis
  obtain ⟨he,hsq,hfq⟩ := FixedLineConstituent.quotient_markings ρ
    (componentOrbit J ⊤) X I hI.invariant hXI hf hs ⟨v,hv⟩ hfix
  exact Or.inl ⟨hv,hp,hh,hf,hs,hiso,hg10.isotropic_degree_le_actor_rank_add_one hiso,hr,hXI,
    constituent_kernel_eq_centralizer ρ (componentOrbit J ⊤) X I hI.isIrrPlus hXI hf,
    hdis,he,hsq,hfq,fun hfaith =>
    ⟨FixedLineConstituent.orbit_eq_of_proper_faithful hg10 ⟨cover⟩ hns hJ hm S hnX
      hI.isIrrPlus hv hp hfaith,
     hg10.componentHypothesis_of_marked_constituent ⟨cover⟩ hns hJ hm S hnX hind
      hI.isIrrPlus hv hfaith⟩⟩

end CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
