module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentCriticalPair.SelectedEndpoint.PairedSections
public import Theory.Representation.BinaryConjugationSection.CoordinateEmbedding
public import Theory.Representation.BinaryConjugationSection.NormalizingActors
public import Theory.Representation.PSL3Two.NaturalDualNormalizerMarking

/-!
# The actual single-component marking on the terminal quotient

Conjugation extends the paired section to Mc. The full action of its normal
component embeds this action in Aut(SL₃(2)); the fixed-factor decomposition
identifies its kernel with O₂(Mc). Descending gives a faithful automorphism
marking on the literal Mc/O₂(Mc). The original coordinate maps embed the
pair in the whole U/Z, and full natural action identifies the support
normalizer with the inverse image of the inner subgroup.

Only the actual single-L₃(2) component, paired sections and their source
placements remain inputs. No automorphism marking, whole-module embedding
or stabilizer identification is assumed. The component exclusions remain
with qt-e-suitable-component-marking using qt-e-suitable-component-supports;
qt-e-suitable-existence retains final suitable-choice assembly.

Source: Aschbacher--Smith, 14.6.22--24, printed pp.1038--1041.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open BinaryNaturalDual BinaryNaturalDual.ModelOrbits
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem normalizes_join_of_pair
    (H A B : Subgroup G)
    (hp : ∀ x ∈ H, A.map (MulAut.conj x).toMonoidHom = A ∨
      A.map (MulAut.conj x).toMonoidHom = B)
    (s : G) (hs : s ∈ H) (hsA : A.map (MulAut.conj s).toMonoidHom = B) :
    H ≤ normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  have hle (x : G) (hx : x ∈ H) : (A ⊔ B).map (MulAut.conj x).toMonoidHom ≤ A ⊔ B := by
    rw [Subgroup.map_sup]
    apply sup_le
    · rcases hp x hx with he | he
      · rw [he]; exact le_sup_left
      · rw [he]; exact le_sup_right
    · have he : (MulAut.conj x).toMonoidHom.comp (MulAut.conj s).toMonoidHom =
          (MulAut.conj (x*s)).toMonoidHom := by ext a; simp [MulAut.conj_apply,mul_assoc]
      have hmap : B.map (MulAut.conj x).toMonoidHom =
          A.map (MulAut.conj (x*s)).toMonoidHom := by
        calc
          B.map (MulAut.conj x).toMonoidHom =
              (A.map (MulAut.conj s).toMonoidHom).map (MulAut.conj x).toMonoidHom :=
            congrArg (fun R : Subgroup G => R.map (MulAut.conj x).toMonoidHom) hsA.symm
          _ = _ := by rw [map_map,he]
      rw [hmap]
      rcases hp (x*s) (H.mul_mem hx hs) with he | he
      · rw [he]; exact le_sup_left
      · rw [he]; exact le_sup_right
  intro x hx
  apply mem_normalizer_iff.mpr
  intro a
  constructor
  · intro ha
    exact hle x hx (mem_map_of_mem _ ha)
  · intro ha
    have hh := hle x⁻¹ (H.inv_mem hx) (mem_map_of_mem (MulAut.conj x⁻¹).toMonoidHom ha)
    simpa [MulAut.conj_apply,mul_assoc] using hh

private theorem naturalDual_sl (g : BinaryLinearThree.Group) :
    naturalDualRepresentation (BinaryLinear.OuterCyclic.slEquivLinear 3 g) =
      BinaryLinearThree.NaturalDual.action g := by
  apply LinearMap.ext
  intro v
  rw [naturalDualRepresentation_apply]
  apply Prod.ext
  · rfl
  · apply LinearMap.ext
    intro w
    change v.2 ((BinaryLinear.OuterCyclic.slEquivLinear 3 g)⁻¹ w) = _
    rw [←map_inv]
    rfl

namespace SelectedEndpoint
open Chapter13.Section08
open Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer
variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    [FiniteDimensional (ZMod 2) E]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    {ρ : Representation (ZMod 2) (Source.Hstar Mc) E}
    (sectionModel : ConjugationSection Mc (conjugateSpanBy (localModule T M) Mc)
      (centralInvolutions T) ρ)
    (W W' : Subgroup G)

local notation "U" => conjugateSpanBy (localModule T M) Mc
local notation "Z" => centralInvolutions T
local notation "L" => (Mc ⊓ normalizer (W : Set G) : Subgroup G)
local notation "h" => ComponentSupports.terminal_hypothesis hG T hempty hM hunique hmany hcard e hab

omit [FiniteDimensional (ZMod 2) E] in
include hG hempty hM hunique hmany hcard e hab sectionModel in
/-- The actual paired sections construct the faithful quotient automorphism
marking and the equivariant pair embedding in the original whole module.
The support normalizer is exactly the inverse image of the inner subgroup. -/
theorem source_single_component_marking
    (f : (L) →* BinaryLinear.GL (Fin 3 → ZMod 2)) (hf : Function.Surjective f)
    (c : BinaryConjugationSection (L) W Z
      (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp f))
    (cdual : BinaryConjugationSection (L) W' Z
      (Representation.dual (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp f)))
    (hWU : W ≤ U) (hW'U : W' ≤ U) (hsep : W ⊓ W' ≤ Z)
    (hB : ⁅U,Mc⁆ ≤ W ⊔ W')
    (hpair : ∀ x ∈ Mc, W.map (MulAut.conj x).toMonoidHom = W ∨
      W.map (MulAut.conj x).toMonoidHom = W')
    (K : Subgroup G)
    (hKres : (solvableResidual Mc).map Mc.subtype = K)
    (hK : (K.subgroupOf Mc).IsCComponent)
    (eK : (K ⧸ pCore 2 K) ≃* Matrix.PSL3Two.SL)
    (hKW : K ≤ normalizer (W : Set G))
    (s : G) (hs : s ∈ Mc) (hsW : W.map (MulAut.conj s).toMonoidHom = W') :
    ∃ ι : Source.Hstar Mc →* MulAut BinaryLinearThree.Group, Function.Injective ι ∧
      ∃ embedding : BinaryLinearThree.NaturalDual.Space →ₗ[ZMod 2] E,
        Function.Injective embedding ∧
        (∀ a v, ρ a (embedding v) = embedding (BinaryLinearThree.NaturalDual.autAction (ι a) v)) ∧
        (L).subgroupOf Mc = (MulAut.innerSubgroup BinaryLinearThree.Group).comap
          (ι.comp (QuotientGroup.mk' (pCore 2 Mc))) := by
  let hh := h
  let B := W ⊔ W'
  let C := commutatorPreimage U Mc Z
  let π := QuotientGroup.mk' (pCore 2 Mc)
  let : IsElementaryAbelian 2 U :=
    hh.UH_elementary_of_V_le_QH ((le_conjugateSpanBy _ _).trans hh.UH_le_QH)
  have hBU : B ≤ U := sup_le hWU hW'U
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.of_injective (inclusion hBU) (inclusion_injective hBU)
  obtain ⟨_,_,_,hfixed,hcover⟩ := source_fixed_factor_of_pair_commutator
    hG T hempty hM hunique hmany hcard e hab W W' hWU hW'U hsep f hf c cdual hB
  have hcomm : W ≤ centralizer (W' : Set G) :=
    hWU.trans ((le_centralizer_iff_isMulCommutative.mpr hab).trans (centralizer_le hW'U))
  obtain ⟨dL,_,hW,hW'⟩ := c.exists_join_section cdual hcomm hsep
  have hHB := normalizes_join_of_pair Mc W W' hpair s hs hsW
  have hHZ := hh.H_centralizes.trans (Subgroup.centralizer_le_normalizer _)
  obtain ⟨τ,hτ⟩ := dL.exists_original_quotient_action hHB hHZ
  let dH : BinaryConjugationSection Mc B Z τ := {
    section_le := hBU.trans hh.UH_le_H
    kernel_le := dL.kernel_le
    normalized := hHB
    coordinates := dL.coordinates
    onto := dL.onto
    kernel_eq := dL.kernel_eq
    equivariant := fun a b => (hτ a b).symm }
  have hτL (a : L) : τ (inclusion inf_le_left a) = naturalDualRepresentation (f a) := by
    apply LinearMap.ext
    intro v
    obtain ⟨b,hb⟩ := dL.onto (Multiplicative.ofAdd v)
    have hb' : (dL.coordinates b).toAdd = v := congrArg Multiplicative.toAdd hb
    rw [←hb',hτ]
    change (dL.coordinates ⟨(a:G)*b*(a:G)⁻¹,
      (dL.normalized a.property b).mp b.property⟩).toAdd = _
    rw [dL.equivariant,naturalDualRepresentation_apply]
    apply Prod.ext
    · rfl
    · apply LinearMap.ext
      intro w
      change (dL.coordinates b).toAdd.2 (f a⁻¹ w) =
        (dL.coordinates b).toAdd.2 ((f a)⁻¹ w)
      rw [map_inv]
  let fSL := (BinaryLinear.OuterCyclic.slEquivLinear 3).symm.toMonoidHom.comp f
  have hfSL : Function.Surjective fSL :=
    (BinaryLinear.OuterCyclic.slEquivLinear 3).symm.surjective.comp hf
  have hτSL (a : L) : τ (inclusion inf_le_left a) = BinaryLinearThree.NaturalDual.action (fSL a) := by
    rw [hτL,←naturalDual_sl]
    rw [show BinaryLinear.OuterCyclic.slEquivLinear 3 (fSL a) = f a from
      (BinaryLinear.OuterCyclic.slEquivLinear 3).apply_symm_apply (f a)]
  obtain ⟨hKL,_,_,hfull⟩ := source_component_action_placement
    hG T hempty hM hunique hmany hcard e K W hKres hK eK hKW fSL hfSL
  have hKM : K ≤ Mc := hKL.trans inf_le_left
  let iK := subgroupOfEquivOfLe hKM
  let fK := (fSL.comp (inclusion hKL)).comp iK.toMonoidHom
  have hfK : Function.Surjective fK := hfull.comp iK.surjective
  let : (K.subgroupOf Mc).Normal := by
    rw [←hKres]
    change ((solvableResidual Mc).map Mc.subtype |>.comap Mc.subtype).Normal
    rw [comap_map_eq_self_of_injective Mc.subtype_injective]
    infer_instance
  obtain ⟨α,hα,hαker⟩ := BinaryLinearThree.NaturalDual.exists_automorphism_marking
    τ (K.subgroupOf Mc) fK hfK (fun a => hτSL (inclusion hKL (iK a)))
  have hk (x : Mc) : τ x = 1 ↔ x ∈ pCore 2 Mc := by
    have hQ : (x:G) ∈ Mc.pCoreIn 2 ↔ x ∈ pCore 2 Mc := by
      change x ∈ (Mc.pCoreIn 2).subgroupOf Mc ↔ _
      rw [show (Mc.pCoreIn 2).subgroupOf Mc = pCore 2 Mc from
        comap_map_eq_self_of_injective Mc.subtype_injective _]
    rw [←hQ]
    constructor
    · intro hx
      have he : hh.kernel U = Mc.pCoreIn 2 := hh.kernel_UH_eq_QH
      rw [←he]
      apply (hh.mem_kernel_iff hh.UH_le_H).mpr
      refine ⟨x.property,?_⟩
      intro v hv
      obtain ⟨a,ha,b,hb,t,ht,rfl⟩ := hcover v hv
      have hm : ⁅a*b,(x:G)⁆ ∈ Z := by
        apply (dH.fixed_coordinate_iff_commutator_mem x ⟨a*b,mul_mem_sup ha hb⟩).mp
        rw [hx]
        rfl
      rw [commutatorElement_mul_left_eq_conj_mul]
      exact (Z).mul_mem ((hHZ (hh.UH_le_H ((U).mul_mem (hWU ha) (hW'U hb))) _).mp
        (hfixed x x.property t ht)) hm
    · intro hx
      apply LinearMap.ext
      intro v
      obtain ⟨b,hb⟩ := dH.onto (Multiplicative.ofAdd v)
      have he := (dH.fixed_coordinate_iff_commutator_mem x b).mpr
        (hh.commutator_UH_QH_le_point (commutator_mem_commutator (hBU b.property) hx))
      rw [hb] at he
      exact he
  have hkill : π.ker ≤ α.ker := by
    intro x hx
    exact (hαker x).mpr ((hk x).mpr ((QuotientGroup.eq_one_iff x).mp hx))
  let ι := π.liftOfSurjective (QuotientGroup.mk'_surjective _) ⟨α,hkill⟩
  have hιπ (x : Mc) : ι (π x) = α x := π.liftOfRightInverse_comp_apply _ _ _ _
  have hι : Function.Injective ι := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro a ha
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 Mc) a
    apply (QuotientGroup.eq_one_iff x).mpr
    apply (hk x).mp
    apply (hαker x).mp
    exact (hιπ x).symm.trans ha
  let cH : BinaryConjugationSection Mc U Z (ρ.comp π) := {
    section_le := sectionModel.le
    kernel_le := sectionModel.line_le
    normalized := sectionModel.normalizes
    coordinates := sectionModel.quotient
    onto := sectionModel.surjective
    kernel_eq := sectionModel.kernel
    equivariant := fun a b => (sectionModel.conjugates a b).symm }
  obtain ⟨emb,hemb,hecoord,heact,_⟩ := cH.exists_coordinate_embedding dH le_rfl hBU
  refine ⟨ι,hι,emb,hemb,?_,?_⟩
  · intro a v
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 Mc) a
    rw [hιπ,←hα]
    exact heact x v
  · have hQL : Mc.pCoreIn 2 ≤ L := by
      apply le_inf (pCoreIn_le 2 Mc)
      apply le_normalizer_iff_commutator_le_left.mpr
      exact ((commutator_mono hWU le_rfl).trans hh.commutator_UH_QH_le_point).trans c.kernel_le
    have hαL (x : L) : α (inclusion inf_le_left x) = MulAut.conj (fSL x) := by
      apply BinaryLinearThree.NaturalDual.autAction_injective
      rw [←hα,hτSL,BinaryLinearThree.NaturalDual.autAction_inner]
    ext x
    change (x:G) ∈ L ↔ ι (π x) ∈ MulAut.innerSubgroup BinaryLinearThree.Group
    rw [hιπ]
    constructor
    · intro hx
      exact ⟨fSL ⟨x,hx⟩,(hαL ⟨x,hx⟩).symm⟩
    · rintro ⟨g,hg⟩
      obtain ⟨y,hy⟩ := hfSL g
      have he : α x = α (inclusion inf_le_left y) := by rw [hαL,hy,hg]
      have hxy : α (x*(inclusion inf_le_left y)⁻¹) = 1 := by rw [map_mul,map_inv,he,mul_inv_cancel]
      have hxyQ := (hk _).mp ((hαker _).mp hxy)
      have hxyL : (x:G)*(y:G)⁻¹ ∈ L := hQL (mem_map_of_mem Mc.subtype hxyQ)
      simpa only [inv_mul_cancel_right] using (L).mul_mem hxyL y.property
end SelectedEndpoint
end CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair
