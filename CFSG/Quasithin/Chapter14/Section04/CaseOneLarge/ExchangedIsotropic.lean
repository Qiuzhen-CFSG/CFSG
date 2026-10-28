module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.ExchangedGeometry
public import CFSG.Quasithin.ChapterG.Section09.ConstituentConjugateDual
public import CFSG.Quasithin.ChapterG.Section09.QuasiequivalenceSymmetry
public import CFSG.Quasithin.ChapterG.Section09.SingleComponentModels
public import Theory.SpecificGroups.PSL3Four.OuterSylowCommutator
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueExchangedFaithfulAction

/-!
# The genuine G.9 input in the original isotropic exchanged branch

The completed exchanged pair makes every ambient conjugate of the selected
constituent equal or complementary to it. The original form identifies a
complementary translate with the dual, giving the precise component comparison
required by G.9.3. The literal stabilizer has order 2^(dim I - 2) and acts
faithfully on the component orbit. It therefore moves one of its components;
if necessary the comparison is reversed to select the partner.

The sharp G.9 degree theorem excludes two components. Faithfulness lifts this
back to the originally selected component, which is consequently normal. Its
literal action quotient retains non-self-duality, properness, the sharp
nontrivial actor and the exhaustive simple-or-central-three-cover carrier
catalogue. Independently of the form alternative, the exchanging element
is outer on H. Normality of the original elementary actor in its Sylow group
makes its cyclic Sylow commutator elementary. The proved binary PSL₃ outer
calculation excludes every positive binary field exponent on the same central
quotient; this does not use the invalid general outer-involution shortcut.
The final application keeps the nondegenerate alternative and all
original flag markings. Carrier classification is not action recognition;
the model sieve and guarded large-case assembly remain open.

Source: Aschbacher--Smith G.10.15 and G.11.6, printed pp.361--366, and
14.4.2, pp.1006--1007; refs/quasithin.pdf. The quotient construction adapts the
checked Section03 exchanged geometry to the original rank-three flag, using
its actual cover and rank equality rather than rank-two source assumptions.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.ExchangedIsotropic
open Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
section Orbit
variable {G : Type*} [Group G] [Finite G]
private theorem orbit_pair (L : Subgroup G) (hi : (normalizer (L : Set G)).index ≤ 2) :
    componentOrbit L ⊤ = L ∨ ∃ g : G,
      componentOrbit L ⊤ = L ⊔ L.map (MulAut.conj g).toMonoidHom := by
  classical
  by_cases hn : L.Normal
  · let := hn
    left
    apply le_antisymm ?_ (le_componentOrbit L ⊤)
    exact iSup_conjugates_le_of_le_normalizer L ⊤ L le_rfl (by rw [normalizer_eq_top_iff.mpr hn])
  have hidx : (normalizer (L : Set G)).index = 2 := by
    have hp := (normalizer (L : Set G)).index_ne_zero_of_finite
    have h1 : (normalizer (L : Set G)).index ≠ 1 := by
      intro he
      exact hn (normalizer_eq_top_iff.mp (index_eq_one.mp he))
    omega
  have hN : normalizer (L : Set G) ≠ ⊤ := fun he => hn (normalizer_eq_top_iff.mp he)
  have hex : ∃ g : G, g ∉ normalizer (L : Set G) := by
    by_contra! hall
    exact hN (eq_top_iff.mpr (fun g _ => hall g))
  obtain ⟨g,hg⟩ := hex
  right
  refine ⟨g,le_antisymm ?_ (sup_le (le_componentOrbit L ⊤) ?_)⟩
  · refine iSup_le fun a => ?_
    by_cases ha : (a : G) ∈ normalizer (L : Set G)
    · have he : L.map (MulAut.conj (a : G)).toMonoidHom = L :=
        mem_normalizer_iff_map_conj_eq.mp ha
      rw [he]
      exact le_sup_left
    have hga : g⁻¹ * (a : G) ∈ normalizer (L : Set G) :=
      (mul_mem_iff_of_index_two hidx).mpr (iff_of_false (by simpa using hg) ha)
    have he : L.map (MulAut.conj (a : G)).toMonoidHom = L.map (MulAut.conj g).toMonoidHom := by
      calc
        _ = (L.map (MulAut.conj (g⁻¹ * (a : G))).toMonoidHom).map
            (MulAut.conj g).toMonoidHom := by
          rw [map_map]
          congr 1
          ext x
          simp [MulAut.conj_apply,mul_assoc]
        _ = _ := congrArg (map (MulAut.conj g).toMonoidHom)
          (mem_normalizer_iff_map_conj_eq.mp hga)
    rw [he]
    exact le_sup_right
  · exact le_iSup (fun a : (⊤ : Subgroup G) => L.map (MulAut.conj (a : G)).toMonoidHom)
      ⟨g,mem_top g⟩

end Orbit
variable {D U : Type*} [Group D] [Finite D] [AddCommGroup U]
  [Module (ZMod 2) U] [FiniteDimensional (ZMod 2) U]
  {ρ : Representation (ZMod 2) D U} {B : LinearMap.BilinForm (ZMod 2) U}
  {v : U} {W : Submodule (ZMod 2) U} {X : Subgroup D}
  [IsElementaryAbelian 2 X] {X₀ : Subgroup X}
  (h : ChapterG.Section10.Hypothesis ρ B v W X X₀)
  (hn : ¬ Group.IsSolvable D) {C : Subgroup D} (hC : IsComponent D C)
  (hind : (normalizer (C : Set D)).index ≤ 2)
  {I : Submodule (ZMod 2) U}
  (hI : Homogeneous.IsIrrPlusWith ρ (componentOrbit C ⊤) X I)
  (hc : ExchangedGeometry.CompletedData ρ B C X I hI)
  (hiso : ∀ u ∈ I, ∀ w ∈ I, B u w = 0)
  (hf : Function.Injective
    (invariantSubspace ρ (componentOrbit C ⊤) I hI.invariant).toRepresentation)

include h hn hI hc in
private theorem conjugate_eq_or_spans (a : D) :
    I.map (ρ a⁻¹) = I ∨ I ⊔ I.map (ρ a⁻¹) = ⊤ := by
  let H := componentOrbit C ⊤
  let : H.Normal := componentOrbit_top_normal C
  rcases hI.isIrrPlus.eq_or_disjoint_conjugate_of_normal_restriction
    ρ (h.irreducible_of_not_solvable hn) H a⁻¹ with he | hd
  · exact Or.inl he
  right
  obtain ⟨x,_,hcompl,hdegree⟩ := hc.2.2.1
  apply Submodule.eq_top_of_disjoint _ _ ?_ hd.symm
  rw [finrank_map_action]
  omega

include h hn hC hind hI hc hiso in
private theorem constituent_components :
    componentOrbit C ⊤ = C ∨ ∃ C₂ : Subgroup D,
      ∃ h₂H : C₂ ≤ componentOrbit C ⊤,
      IsComponent D C₂ ∧ componentOrbit C ⊤ = C ⊔ C₂ ∧
      (ChapterG.Section09.Quasiequivalent
        (invariantSubspace ρ C I ((le_componentOrbit C ⊤).trans hI.invariant)).toRepresentation
        (invariantSubspace ρ C₂ I (h₂H.trans hI.invariant)).toRepresentation ∨
       ChapterG.Section09.Quasiequivalent
        (invariantSubspace ρ C I ((le_componentOrbit C ⊤).trans hI.invariant)).toRepresentation
        (invariantSubspace ρ C₂ I (h₂H.trans hI.invariant)).toRepresentation.dual) := by
  let H := componentOrbit C ⊤
  let : H.Normal := componentOrbit_top_normal C
  rcases orbit_pair C hind with he | ⟨a,he⟩
  · exact Or.inl he
  have h₂H : C.map (MulAut.conj a).toMonoidHom ≤ componentOrbit C ⊤ := by
    rw [he]
    exact le_sup_right
  refine Or.inr ⟨_,h₂H,hC.map_equiv (MulAut.conj a),he,?_⟩
  exact ChapterG.Section09.constituent_quasiequivalent_or_dual_conjugate
    ρ H I hI.invariant B h.nondegenerate h.preserves
    (hI.isIrrPlus.irreducible_of_normal_restriction ρ (h.irreducible_of_not_solvable hn) H)
    hiso C (le_componentOrbit C ⊤) a
    (conjugate_eq_or_spans h hn hI hc a) _ _

omit [FiniteDimensional (ZMod 2) U] in
include hc in
private theorem actor_card : Nat.card (ExchangedAction.actor ρ X I) =
    2 ^ (finrank (ZMod 2) I - 2) := by
  let Y := (subspaceStabilizer ρ I).subgroupOf X
  let : IsElementaryAbelian 2 Y :=
    IsElementaryAbelian.of_injective Y.subtype Y.subtype_injective
  have hd : finrank (ZMod 2) I = finrank (ZMod 2) (Additive Y) + 2 := hc.2.2.2.1
  have hh : Nat.card Y = 2 ^ finrank (ZMod 2) (Additive Y) := by
    change Nat.card (Additive Y) = _
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
  rw [← Nat.card_congr (ExchangedAction.stabilizerEquiv ρ X I).toEquiv,hh]
  congr 1
  omega

include hC hI hc in
private theorem orbit_actor_moved :
    ⁅componentOrbit C ⊤, ExchangedAction.actor ρ X I⁆ ≠ ⊥ := by
  intro hz
  let A := ExchangedAction.actor ρ X I
  let Y := (subspaceStabilizer ρ I).subgroupOf X
  have hAC : A ≤ centralizer (componentOrbit C ⊤ : Set D) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hz)
  have ht : ∀ a : A, a = 1 := by
    intro a
    have hh := hc.2.2.2.2.2.1 (⟨⟨a,a.property.2⟩,a.property.1⟩ : Y) (hAC a.property)
    exact Subtype.ext (congrArg (fun y : Y => ((y : X) : D)) hh)
  have hcard : Nat.card A = 1 := Nat.card_eq_one_iff_exists.mpr ⟨1,ht⟩
  let : Group.IsPerfect (componentOrbit C ⊤) := hC.orbit_isPerfect ⊤
  have hd := hI.isIrrPlus.finrank_gt_two ρ (componentOrbit C ⊤)
  have hp := one_lt_pow' (show (1 : ℕ) < 2 by decide)
    (show finrank (ZMod 2) I - 2 ≠ 0 by omega)
  rw [← actor_card hI hc] at hp
  change 1 < Nat.card A at hp
  omega

include h hn hC hind hI hc hiso hf in
/-- The isotropic branch supplies G.9 on the literal stabilizer image, after
selecting a component that this stabilizer actually moves. -/
theorem exists_image_component_hypothesis
    (cover : Nonempty (ChapterG.Section09.SQTKCover KnownSimple.IsKnownSimple D)) :
    let H := componentOrbit C ⊤
    let A := ExchangedAction.actor ρ X I
    let σ := ExchangedAction.imageAction ρ H X I hI.invariant
    let image := ExchangedAction.image ρ H X I hI.invariant
    ∃ L : Subgroup (ExchangedAction.quotient ρ H X I hI.invariant),
      L ≤ image H ∧ ChapterG.Section09.ComponentHypothesis KnownSimple.IsKnownSimple
        σ (image A) L (image H) (finrank (ZMod 2) I - 2) := by
  let H := componentOrbit C ⊤
  let : H.Normal := componentOrbit_top_normal C
  let A := ExchangedAction.actor ρ X I
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_injective
    (inclusion (show A ≤ X from inf_le_right)) (inclusion_injective _)
  let image := ExchangedAction.image ρ H X I hI.invariant
  have hi := hI.isIrrPlus.irreducible_of_normal_restriction ρ
    (h.irreducible_of_not_solvable hn) H
  have hfA := h.spanning_constituent_stabilizer_faithful hc.2.1
  let : Group.IsPerfect H := hC.orbit_isPerfect ⊤
  have hd := hI.isIrrPlus.finrank_gt_two ρ H
  have hh := constituent_components h hn hC hind hI hc hiso
  have input (L : Subgroup D) (hL : IsComponent D L) (hLH : L ≤ H)
      (hm : ⁅L,A⁆ ≠ ⊥)
      (hcomp : H = L ∨ ∃ L₂ : Subgroup D, ∃ h₂H : L₂ ≤ H,
        IsComponent D L₂ ∧ H = L ⊔ L₂ ∧
        (ChapterG.Section09.Quasiequivalent
          (invariantSubspace ρ L I (hLH.trans hI.invariant)).toRepresentation
          (invariantSubspace ρ L₂ I (h₂H.trans hI.invariant)).toRepresentation ∨
         ChapterG.Section09.Quasiequivalent
          (invariantSubspace ρ L I (hLH.trans hI.invariant)).toRepresentation
          (invariantSubspace ρ L₂ I (h₂H.trans hI.invariant)).toRepresentation.dual)) :=
    ChapterG.Section09.componentHypothesis_constituent_or_dual
      ρ cover A L H I hI.invariant inf_le_left hf hfA hi (finrank (ZMod 2) I - 2)
      (actor_card hI hc) (by omega) hL hm hLH hcomp
  have himage {L : Subgroup D} (hL : L ≤ H) : image L ≤ image H :=
    Subgroup.map_mono (fun _ hx => hL hx)
  by_cases hm : ⁅C,A⁆ ≠ ⊥
  · exact ⟨image C,himage (le_componentOrbit C ⊤),input C hC (le_componentOrbit C ⊤) hm hh⟩
  have hz : ⁅C,A⁆ = ⊥ := not_ne_iff.mp hm
  rcases hh with he | ⟨C₂,h₂H,h₂,he,hq⟩
  · exact False.elim (orbit_actor_moved hC hI hc (by rw [he]; exact hz))
  have hm₂ : ⁅C₂,A⁆ ≠ ⊥ := by
    intro hz₂
    apply orbit_actor_moved hC hI hc
    apply commutator_eq_bot_iff_le_centralizer.mpr
    rw [he]
    exact sup_le (commutator_eq_bot_iff_le_centralizer.mp hz)
      (commutator_eq_bot_iff_le_centralizer.mp hz₂)
  refine ⟨image C₂,himage h₂H,input C₂ h₂ h₂H hm₂ (Or.inr ⟨C,
    le_componentOrbit C ⊤,hC,he.trans (sup_comm _ _),?_⟩)⟩
  rcases hq with hq | hq
  · exact Or.inl (ChapterG.Section09.quasiequivalent_symm _ _ hq)
  · exact Or.inr (ChapterG.Section09.quasiequivalent_dual_symm _ _ hq)

include h hn hC hind hI hc hiso hf in
/-- The sharp degree bound excludes a second component in the isotropic
branch and lifts that equality to the original normal component orbit. -/
theorem orbit_eq_component
    (cover : Nonempty (ChapterG.Section09.SQTKCover KnownSimple.IsKnownSimple D)) :
    componentOrbit C ⊤ = C := by
  let H := componentOrbit C ⊤
  let : Group.IsPerfect H := hC.orbit_isPerfect ⊤
  let image := ExchangedAction.image ρ H X I hI.invariant
  obtain ⟨L,_,hL⟩ := exists_image_component_hypothesis h hn hC hind hI hc hiso hf cover
  have hd : finrank (ZMod 2) I ≤ (finrank (ZMod 2) I - 2) + 2 := by
    have := hI.isIrrPlus.finrank_gt_two ρ H
    omega
  have he := ChapterG.Section09.TwoComponents.single_component_of_sharp_degree hL hd
  let : IsQuasisimple (image H) := by
    rw [show image H = L from he]
    exact hL.component.2
  let e := ExchangedAction.orbitEquiv ρ H X I hI.invariant hf
  let : IsQuasisimple H := IsQuasisimple.of_mulEquiv e.symm
  let : H.Normal := componentOrbit_top_normal C
  have hh : IsComponent D H := ⟨(inferInstance : H.Normal).isSubnormal,inferInstance⟩
  exact (hC.eq_of_le hh (le_componentOrbit C ⊤)).symm

include h hn hC hind hI hc hiso hf in
/-- The G.9 input is for the original orbit image in both component positions,
with its exact stabilizer order; no component recognition is assumed. -/
theorem image_single_component_hypothesis
    (cover : Nonempty (ChapterG.Section09.SQTKCover KnownSimple.IsKnownSimple D)) :
    let H := componentOrbit C ⊤
    let A := ExchangedAction.actor ρ X I
    let σ := ExchangedAction.imageAction ρ H X I hI.invariant
    let image := ExchangedAction.image ρ H X I hI.invariant
    ChapterG.Section09.ComponentHypothesis KnownSimple.IsKnownSimple
      σ (image A) (image H) (image H) (finrank (ZMod 2) I - 2) := by
  obtain ⟨L,_,hL⟩ := exists_image_component_hypothesis h hn hC hind hI hc hiso hf cover
  have he := ChapterG.Section09.TwoComponents.single_component_of_sharp_degree hL
    (by
      let : Group.IsPerfect (componentOrbit C ⊤) := hC.orbit_isPerfect ⊤
      have := hI.isIrrPlus.finrank_gt_two ρ (componentOrbit C ⊤)
      omega)
  rw [← he] at hL
  exact hL

include h hn hC hind hI hc hiso hf in
/-- The original isotropic constituent has the exhaustive simple-or-three-cover
carrier catalogue on its literal orbit image. Action recognition remains separate. -/
theorem image_carrier_models
    (cover : Nonempty (ChapterG.Section09.SQTKCover KnownSimple.IsKnownSimple D)) :
    let H := ExchangedAction.image ρ (componentOrbit C ⊤) X I hI.invariant
      (componentOrbit C ⊤)
    (IsSimpleGroup H ∧ Chapter1.Section02.LocalModels.TheoremCModel H) ∨
    (Nonempty (center H ≃* Multiplicative (ZMod 3)) ∧
      Chapter1.Section02.LocalModels.ThreeCoverModel H) :=
  (image_single_component_hypothesis h hn hC hind hI hc hiso hf cover).single_component_models

/-- The source conclusions retained on the same isotropic constituent and
literal quotient. This includes genuine G.9 input and its carrier theorem,
not a new recognition hypothesis. -/
@[expose] def IsotropicData
    (ρ : Representation (ZMod 2) D U) (C X : Subgroup D)
    (I : Submodule (ZMod 2) U)
    (hI : Homogeneous.IsIrrPlusWith ρ (componentOrbit C ⊤) X I) : Prop :=
  componentOrbit C ⊤ = C ∧ C.Normal ∧
  let H := componentOrbit C ⊤
  let A := ExchangedAction.actor ρ X I
  let σ := ExchangedAction.imageAction ρ H X I hI.invariant
  let image := ExchangedAction.image ρ H X I hI.invariant
  ChapterG.Section09.ComponentHypothesis KnownSimple.IsKnownSimple
    σ (image A) (image H) (image H) (finrank (ZMod 2) I - 2) ∧
  ¬ Nonempty (Representation.Equiv (σ.comp (image H).subtype)
    (Representation.dual (σ.comp (image H).subtype))) ∧
  ¬ Function.Surjective (Representation.asGroupHom (σ.comp (image H).subtype)) ∧
  finrank (ZMod 2) I ≤ primeRank 2 (MulAut (image H)) + 2 ∧
  ((IsSimpleGroup (image H) ∧ Chapter1.Section02.LocalModels.TheoremCModel (image H)) ∨
    (Nonempty (center (image H) ≃* Multiplicative (ZMod 3)) ∧
      Chapter1.Section02.LocalModels.ThreeCoverModel (image H)))

include h hn hC hind hI hc hiso hf in
private theorem isotropic_data
    (cover : Nonempty (ChapterG.Section09.SQTKCover KnownSimple.IsKnownSimple D))
    (hns : ¬ Nonempty (Representation.Equiv
      (invariantSubspace ρ (componentOrbit C ⊤) I hI.invariant).toRepresentation
      (invariantSubspace ρ (componentOrbit C ⊤) I hI.invariant).toRepresentation.dual)) :
    IsotropicData ρ C X I hI := by
  let H := componentOrbit C ⊤
  let A := ExchangedAction.actor ρ X I
  let σ := ExchangedAction.imageAction ρ H X I hI.invariant
  let image := ExchangedAction.image ρ H X I hI.invariant
  have he := orbit_eq_component h hn hC hind hI hc hiso hf cover
  have hi := image_single_component_hypothesis h hn hC hind hI hc hiso hf cover
  have hnorm : C.Normal := he ▸ componentOrbit_top_normal C
  refine ⟨he,hnorm,hi,
    ExchangedAction.image_not_selfDual ρ H X I hI.invariant hns,
    ExchangedAction.image_not_surjective ρ H X I hI.invariant hc.1,?_,
    image_carrier_models h hn hC hind hI hc hiso hf cover⟩
  let : (image H).Normal := hi.normal_H
  let : IsIrreducible (σ.comp (image H).subtype) := hi.irreducible
  have hr := hi.toSetup.rank_le_automorphisms (L := image H) (by
    rw [normalizer_eq_top]
    exact le_top)
  let : Group.IsPerfect H := hC.orbit_isPerfect ⊤
  have hd := hI.isIrrPlus.finrank_gt_two ρ H
  change finrank (ZMod 2) I ≤ primeRank 2 (MulAut (image H)) + 2
  omega

include h hn hC hI hc in
/-- An exchanged constituent gives an actual outer involution of H. The
normal elementary Sylow actor rules out every binary PSL₃ central quotient. -/
theorem not_binary_linear_three_central_quotient
    (S : Sylow 2 D) (hXS : X ≤ (S : Subgroup D))
    (hSX : (S : Subgroup D) ≤ normalizer (X : Set D))
    {K : Type*} [Field K] [Finite K] [CharP K 2]
    {n : ℕ} (hnpos : 0 < n) (hK : Nat.card K = 2 ^ n)
    (e : (componentOrbit C ⊤) ⧸ center (componentOrbit C ⊤) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) K) : False := by
  let H := componentOrbit C ⊤
  let : H.Normal := componentOrbit_top_normal C
  let : Group.IsPerfect H := hC.orbit_isPerfect ⊤
  obtain ⟨x,hx,_,_⟩ := hc.2.2.1
  have hp : (x : D) ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian (x : D) x.property
  have hxi : (x : D)⁻¹ = x := inv_eq_iff_mul_eq_one.mpr (by simpa only [pow_two] using hp)
  have hfix := fixedSpace_eq_bot_of_normal_faithful_irreducible ρ h.faithful
    (h.irreducible_of_not_solvable hn) H hC.componentOrbit_top_ne_bot
  have ho := hI.conjugation_not_inner ρ hfix x (by rwa [hxi])
  let Q : Subgroup D := ⁅zpowers (x : D),(S : Subgroup D) ⊓ H⁆
  have hQ : Q ≤ X := (commutator_mono (zpowers_le.mpr x.property) le_rfl).trans
    (le_normalizer_iff_commutator_le_left.mp (inf_le_left.trans hSX))
  let : IsElementaryAbelian 2 Q :=
    IsElementaryAbelian.of_injective (inclusion hQ) (inclusion_injective hQ)
  let : Fact (IsPGroup 2 Q) := ⟨IsElementaryAbelian.isPGroup 2 Q⟩
  exact Matrix.PSL3Four.OuterSylowCommutator.cyclic_commutator_frattini_ne_bot
    K hnpos hK H e S x (hXS x.property) hp ho
    (frattini_eq_bot_of_isElementaryAbelian (p := 2))

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.ExchangedIsotropic

namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open LargerDimension LargerDimension.Tensor CoreGeometry
open LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Apply the genuine G.9 isotropic deduction to the original rank-three flag.
Both form alternatives and the literal constituent action are retained. -/
theorem source_exchanged_component_input (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1) (hlarge : 64 < Nat.card F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    (hline : Submodule.span (ZMod 2) {v} = hatSpace F (F.Vi 2))
    (hn : ¬ ChapterG.Section11.LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g)))
    {C : Subgroup F.TerminalHdot} (hC : IsComponent F.TerminalHdot C)
    (hm : ⁅C,F.terminalDot (F.X g)⁆ ≠ ⊥)
    {I : Submodule (ZMod 2) (Additive F.Uhat)}
    (hI : Homogeneous.IsIrrPlusWith F.terminalRepresentation (componentOrbit C ⊤)
      (F.terminalDot (F.X g)) I) (hv : v ∉ I) :
    ExchangedGeometry.CompletedData F.terminalRepresentation B C (F.terminalDot (F.X g)) I hI ∧
    ((B.restrict I).Nondegenerate ∨
      ((∀ a ∈ I, ∀ b ∈ I, B a b = 0) ∧
        ExchangedIsotropic.IsotropicData F.terminalRepresentation C
          (F.terminalDot (F.X g)) I hI)) := by
  have hc := source_exchanged_completion d earlier hq chosen structural alternatives
    F hne hZ hlarge g hgP hgH hyp hline hn hC hm hI hv
  refine ⟨hc,?_⟩
  rcases hc.2.2.2.2.2.2 with hnd | ⟨hiso,hf,hns,_⟩
  · exact Or.inl hnd
  have hfaith : Function.Injective
      (invariantSubspace F.terminalRepresentation (componentOrbit C ⊤) I hI.invariant).toRepresentation := by
    intro a b hab
    exact hf (Units.ext hab)
  have hnonsolv := source_large_terminal_not_solvable d earlier hq chosen structural alternatives
    F hne hZ hlarge
  let := chosen.elementary
  have hind := Chapter14.Section03.NonabelianSource.Recognition.terminal_component_normalizer_index_le_two
    d.qtke F (by decide) C hC
  exact Or.inr ⟨hiso,ExchangedIsotropic.isotropic_data hyp hnonsolv hC hind hI hc hiso
    hfaith (source_terminal_cover F d chosen) hns⟩

/-- The binary PSL₃ central-quotient row is excluded on the original flag,
using its original actor and Sylow intersection. -/
theorem source_exchanged_not_binary_linear_three (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1) (hlarge : 64 < Nat.card F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    (hline : Submodule.span (ZMod 2) {v} = hatSpace F (F.Vi 2))
    (hn : ¬ ChapterG.Section11.LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g)))
    {C : Subgroup F.TerminalHdot} (hC : IsComponent F.TerminalHdot C)
    (hm : ⁅C,F.terminalDot (F.X g)⁆ ≠ ⊥)
    {I : Submodule (ZMod 2) (Additive F.Uhat)}
    (hI : Homogeneous.IsIrrPlusWith F.terminalRepresentation (componentOrbit C ⊤)
      (F.terminalDot (F.X g)) I) (hv : v ∉ I)
    {K : Type*} [Field K] [Finite K] [CharP K 2]
    {n : ℕ} (hnpos : 0 < n) (hK : Nat.card K = 2 ^ n)
    (e : (componentOrbit C ⊤) ⧸ center (componentOrbit C ⊤) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 3) K) : False := by
  have hc := source_exchanged_completion d earlier hq chosen structural alternatives
    F hne hZ hlarge g hgP hgH hyp hline hn hC hm hI hv
  let := chosen.elementary
  let P : Sylow 2 F.TerminalHdot := (T.subtype (F.invariant 1)).mapSurjective
    (QuotientGroup.mk'_surjective F.terminalHatAction.ker)
  obtain ⟨hXP,hN⟩ := source_terminal_actor_normal_in_sylow d earlier hq chosen
    structural alternatives F hne g hgP hgH
  have hnonsolv := source_large_terminal_not_solvable d earlier hq chosen structural alternatives
    F hne hZ hlarge
  exact ExchangedIsotropic.not_binary_linear_three_central_quotient hyp hnonsolv hC hI hc
    P hXP ((normal_subgroupOf_iff_le_normalizer hXP).mp hN) hnpos hK e

namespace FixedLineReduction
/-- The original remainder now has a single normal component and genuine G.9
input in its isotropic branch. The nondegenerate branch and every original
marking, fixed-point clause and mixed-size premise are retained. -/
theorem source_large_single_exchanged_remainder_of_mixed_size (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    (size : Chapter10.MixedZeroCore.MixedSizeInput G)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hlarge : 64 < Nat.card F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    ∃ heU : IsElementaryAbelian 2 F.Uhat, letI := heU
    ∃ heX : IsElementaryAbelian 2 (F.terminalDot (F.X g)), letI := heX
    ∃ (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)) (v : Additive F.Uhat),
      ChapterG.Section10.Hypothesis F.terminalRepresentation B v
        (hatSpace F (F.E g)) (F.terminalDot (F.X g))
        ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))) ∧
      Submodule.span (ZMod 2) {v} = hatSpace F (F.Vi 2) ∧
      ChapterG.Section11.NormalSylow F.terminalRepresentation v (F.terminalDot (F.X g)) ∧
      ¬ ChapterG.Section11.LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g)) ∧
      FixedLineModuleData F.terminalRepresentation B v (F.terminalDot (F.X g)) ∧
      ∃ C : Subgroup F.TerminalHdot, IsComponent F.TerminalHdot C ∧
        ⁅C,F.terminalDot (F.X g)⁆ ≠ ⊥ ∧
        ChapterG.Section10.ComponentOrthogonalData F.terminalRepresentation B C ∧
        ∃ I : Submodule (ZMod 2) (Additive F.Uhat),
        ∃ hI : Homogeneous.IsIrrPlusWith F.terminalRepresentation
            (componentOrbit C ⊤) (F.terminalDot (F.X g)) I,
          v ∉ I ∧ ChapterG.Section10.ExchangedConstituentGeometry F.terminalRepresentation B v
            (hatSpace F (F.E g)) (F.terminalDot (F.X g)) I ∧
          ExchangedGeometry.CompletedData F.terminalRepresentation B C
            (F.terminalDot (F.X g)) I hI ∧
          ((B.restrict I).Nondegenerate ∨
            ((∀ a ∈ I, ∀ b ∈ I, B a b = 0) ∧
              ExchangedIsotropic.IsotropicData F.terminalRepresentation C
                (F.terminalDot (F.X g)) I hI)) := by
  obtain ⟨heU,heX,B,v,hyp,hline,hS,hn,hmodule,C,hC,hm,horth,I,hI,hv,hgeo⟩ :=
    source_large_exchanged_remainder_of_mixed_size d earlier hq chosen structural alternatives
      classification size F hne hZ hlarge g hgP hgH
  let := heU
  let := heX
  exact ⟨heU,heX,B,v,hyp,hline,hS,hn,hmodule,C,hC,hm,horth,I,hI,hv,hgeo,
    source_exchanged_component_input d earlier hq chosen structural alternatives F hne hZ hlarge
      g hgP hgH hyp hline hn hC hm hI hv⟩
end FixedLineReduction
end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
