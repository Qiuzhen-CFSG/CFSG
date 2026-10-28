module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ComponentMoved
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalUnitaryNoncentrality.ContainingModule
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalUnitaryNoncentrality.EarlierModules
public import Theory.GroupTheory.GeneralizedFitting.TwoCoreImageComparison
public import Theory.GroupTheory.InvolutionCentralizerControl

/-!
# The nonsplit moved component module in original 13.4.10

Suppose the actual moved orbit U = [⟨Ω₁Z(T)^K⟩,K] has a nontrivial
K-fixed subgroup. Its inclusion in [R₂(KT),K] makes that larger module
nonsplit. B.5.1(2) supplies an original chosen module there. Minimality,
nonzero movement and [U,K]=U identify the larger module with U itself.
Thus this branch requires no assumed minimality or chosen-module witness.

The earlier fixed-module clause of 13.3.2 then supplies the five-dimensional
augmentation action. The actual quasisimple quotient map identifies its
kernel with O₂,Z(K), yielding a CoreMarking on the literal U. Its fixed
line is T-invariant and has order two, hence lies in Ω₁Z(T). The already
proved component centralizer identifies it with ⟨z⟩. Applying the original
orbit splitting now gives the full-seed conclusion |Ω₁Z(T)|=4 and Ω₁Z(T)≤V.

The earlier universal fixed-module input retains its producer
qt-d-1332-source and final discharge with qt-d-1341-fixed-core-source.
Quasisimplicity of K/O₂(K) and Thompson generation K=[K,J(T)] remain
explicit source inputs here. The fixed-free branch, including exclusion
of doubled natural L₃(2), and the remaining 13.4.10–17 assembly stay with
qt-d-1341-nonsolvable-source. Nonsolvability at the two original weight
choices is unchanged; this module does not assert the final contradiction.

Source: Aschbacher–Smith, B.5.1(2), 13.3.2(3), and 13.4.10(4–5),
printed pp.99,885,907–909 (combined manuscript of 1 March 2004).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open ChapterA.Section04
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L K V : Subgroup G}

omit [Finite G] in
private theorem chosen_minimal (D : ChosenModule T K V)
    (A : Subgroup G) (hAV : A ≤ V) (hn : K ≤ normalizer (A : Set G)) :
    A = V ∨ A ≤ centralizer (K : Set G) := by
  let H := K ⊔ (T : Subgroup G)
  let I : Submodule (ZMod 2) (Additive (ReducedModule H)) :=
    ((A.subgroupOf H).subgroupOf (ReducedModule H)).toAddSubgroup.toZModSubmodule 2
  have hAR : A ≤ (ReducedModule H).map H.subtype := hAV.trans D.le_reduced
  have hAH : A ≤ H := hAR.trans (map_subtype_le _)
  have hI : I ≤ D.space := by
    intro v hv
    have hh : v.toMul.val.val ∈ subspaceImage H D.space := D.image_eq.symm ▸ hAV hv
    obtain ⟨_, ⟨w, hw, rfl⟩, he⟩ := hh
    have he' : Additive.ofMul w = v :=
      Additive.toMul.injective (Subtype.ext (Subtype.ext he))
    exact he' ▸ hw
  have hi : K.subgroupOf H ≤ subspaceStabilizer (reducedRepresentation H) I := by
    apply le_subspaceStabilizer
    intro k hk a ha
    change k.val * a.toMul.val.val * k.val⁻¹ ∈ A
    exact (mem_normalizer_iff.mp (hn hk) _).mp ha
  have image : subspaceImage H I = A := by
    apply le_antisymm
    · rintro _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩
      exact hv
    · intro a ha
      obtain ⟨v, hv, he⟩ := hAR ha
      refine ⟨v, ⟨⟨v, hv⟩, ?_, rfl⟩, he⟩
      change v.val ∈ A
      change v.val = a at he
      rw [he]
      exact ha
  rcases D.irrPlus.isIrrPlus.eq_or_le_fixedSpace (reducedRepresentation H) hi hI with he | hc
  · exact Or.inl (image.symm.trans (he ▸ D.image_eq))
  · right
    intro a ha k hk
    obtain ⟨_, ⟨v, hv, rfl⟩, rfl⟩ := image.symm ▸ ha
    have hh := congrArg (fun w : Additive (ReducedModule H) => w.toMul.val.val)
      (hc hv ⟨⟨k, (le_sup_left : K ≤ H) hk⟩, hk⟩)
    change k * v.val.val * k⁻¹ = v.val.val at hh
    exact mul_inv_eq_iff_eq_mul.mp hh

/-- Nonzero fixed vectors force minimality on the actual moved orbit and identify it
with the whole reduced moved subgroup. -/
theorem component_chosen_of_moved_fixed
    {D : ChosenModule T L V}
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (m : CoreMarking D) {z : G}
    (hzT : z ∈ omegaOneCenterAmbient (T : Subgroup G)) (hz1 : z ≠ 1)
    (hKz : K ≤ centralizer ({z} : Set G))
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hfK : K ∈ MainForward.faithfulLocalComponents T)
    (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (hgen : ⁅K,elementaryAbelianMaxJ (T : Subgroup G)⁆ = K)
    (hfixed : (⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆ :
      Subgroup G) ⊓ centralizer (K : Set G) ≠ ⊥) :
    let U := ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆
    Nonempty (ChosenModule T K U) ∧
      U = ⁅(ReducedModule (K ⊔ (T : Subgroup G))).map
        (K ⊔ (T : Subgroup G)).subtype,K⁆ := by
  let H := K ⊔ (T : Subgroup G)
  let U := ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆
  let R := (ReducedModule H).map H.subtype
  obtain ⟨_,_,_,_,hSQ⟩ := MainForward.localComponents_local_setup h₀.qtke T hfK.1
  have hred := component_moved_reduced h₀ hzT hz1 hKz hTK
  have hUH : U ≤ H :=
    (le_normalizer_iff_commutator_le_left.mp (le_normalizer_conjugateSpanBy _ _)).trans
      (conjugateSpanBy_le
        ((show omegaOneCenterAmbient (T : Subgroup G) ≤ (T : Subgroup G) from
          fun _ hx => ((mem_omegaOneCenterAmbient_iff _ _).mp hx).1).trans le_sup_right)
        (le_sup_left.trans H.le_normalizer))
  have hUR : U ≤ R := by
    have hh := map_mono (f := H.subtype) hred.le_reducedPSubgroup
    rwa [map_subgroupOf_eq_of_le hUH] at hh
  have hUU : ⁅U,K⁆ = U := component_moved_eq_commutator h₀ hzT hz1 hKz hTK
  have hUB : U ≤ ⁅R,K⁆ := hUU ▸ commutator_mono hUR le_rfl
  have hBfixed : ⁅R,K⁆ ⊓ centralizer (K : Set G) ≠ ⊥ := by
    intro he
    exact hfixed (bot_unique ((inf_le_inf_right _ hUB).trans he.le))
  have hlocal : Section03.Noncentrality.Diagonal.localGroup K ⊥ T = H := by
    change (K ⊔ ⊥) ⊔ (T : Subgroup G) = H
    rw [sup_bot_eq]
  have hmoved : Section03.Noncentrality.Diagonal.movedModule K ⊥ T = ⁅R,K⁆ := by
    unfold Section03.Noncentrality.Diagonal.movedModule
      Section03.Noncentrality.Diagonal.reducedModule
    rw [hlocal]
  obtain ⟨DK⟩ := Section03.SourceCompletion.containing_moved_module_chosen T K ⊥
    bot_le hTK (hlocal.symm ▸ hSQ)
    (hlocal.symm ▸ hfK.1.1)
    hqK hfK.2.2 hgen (hmoved.symm ▸ hBfixed)
  have DK' : ChosenModule T K ⁅R,K⁆ := hmoved ▸ DK
  have hn : K ≤ normalizer (U : Set G) := normalizer_commutator_ge_right _ _
  have he : U = ⁅R,K⁆ := (chosen_minimal DK' U hUB hn).resolve_right (by
    intro hc
    have hh := commutator_eq_bot_iff_le_centralizer.mpr hc
    rw [hUU] at hh
    exact component_moved_ne_bot h structural m hKM hh)
  refine ⟨?_,he⟩
  change Nonempty (ChosenModule T K U)
  rw [he]
  exact ⟨DK'⟩

open Section08.TransvectionRecognition.Component.ModelExtension

/-- Convert the faithful augmentation action to the literal central-core quotient,
retaining the conjugation formula on every original component element. -/
theorem coreMarking_of_faithful_core_action (DK : ChosenModule T K V)
    (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (a : letI := DK.actionCentralizer_normal
      ChapterB.QuasisimpleSource.ActionEquiv DK.faithfulAction
        (BinaryPermutation.alternatingCoreRepresentation (Fin 6))) :
    Nonempty (CoreMarking DK) := by
  let := hqK
  let := DK.actionCentralizer_normal
  let f := a.groupEquiv.toMonoidHom.comp DK.coreToFaithful
  have hf : Function.Surjective f := a.groupEquiv.surjective.comp DK.coreToFaithful_surjective
  have hk : f.ker = center (K ⧸ pCore 2 K) := by
    have hh := IsQuasisimple.comap_center_of_surjective f hf
    have hz : center (alternatingGroup (Fin 6)) = ⊥ :=
      alternatingGroup.center_eq_bot (by simp)
    rw [hz] at hh
    exact hh
  let q := f.comp (QuotientGroup.mk' (pCore 2 K))
  have hq : Function.Surjective q := hf.comp (QuotientGroup.mk'_surjective _)
  have hker : q.ker = centralCore K := by
    rw [← MonoidHom.comap_ker,hk]
  let e : (K ⧸ centralCore K) ≃* alternatingGroup (Fin 6) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective q hq)
  let c := DK.spaceEquiv.symm.trans a.linearEquiv.toAddEquiv.toMultiplicative
  refine ⟨⟨e,c,?_⟩⟩
  intro k v
  obtain ⟨w,rfl⟩ := DK.spaceEquiv.surjective v
  have hv : V.normalizerMonoidHom ⟨k.val,DK.normalizes k.property⟩ (DK.spaceEquiv w) =
      DK.spaceEquiv (Multiplicative.ofAdd (DK.chosenAction k w.toAdd)) := by
    apply Subtype.ext
    rw [normalizerMonoidHom_apply_apply_coe,DK.spaceEquiv_apply]
    have hw := DK.spaceEquiv_apply w.toAdd
    change (DK.spaceEquiv w).val = w.toAdd.val.toMul.val.val at hw
    rw [hw]
    rfl
  rw [hv]
  change a.linearEquiv (DK.spaceEquiv.symm (DK.spaceEquiv _)).toAdd =
    BinaryPermutation.coreRepresentation (Fin 6)
      (e (QuotientGroup.mk' (centralCore K) k)).val
      (a.linearEquiv (DK.spaceEquiv.symm (DK.spaceEquiv w)).toAdd)
  simp only [DK.spaceEquiv.symm_apply_apply]
  exact a.intertwines (QuotientGroup.mk' ((centralizer (V : Set G)).subgroupOf K) k) w.toAdd

omit [Finite G] in
private theorem core_fixed_le_omega (DK : ChosenModule T K V) (mK : CoreMarking DK)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G)) :
    V ⊓ centralizer (K : Set G) ≤ omegaOneCenterAmbient (T : Subgroup G) := by
  let C := V ⊓ centralizer (K : Set G)
  have hn : (T : Subgroup G) ≤ normalizer (C : Set G) := by
    apply le_normalizer_iff.mpr
    intro t ht x hx
    refine ⟨(mem_normalizer_iff.mp (hTV ht) x).mp hx.1,?_⟩
    intro k hk
    have hk' : t⁻¹ * k * t ∈ K := by
      simpa only [inv_inv] using
        (mem_normalizer_iff.mp (DK.sylow_normalizes_component ((T : Subgroup G).inv_mem ht)) k).mp hk
    have he := congrArg (fun a : G => t * a * t⁻¹) (hx.2 (t⁻¹ * k * t) hk')
    convert he using 1 <;> group
  have hc : C ≤ centralizer (T : Set G) := le_centralizer_iff.mp
    (hn.trans (normalizer_le_centralizer_of_card_two C mK.card_fixed))
  let := DK.elementary
  intro x hx
  exact (mem_omegaOneCenterAmbient_iff _ _).mpr
    ⟨DK.le_sylow hx.1,elemPow_eq_one_of_isElementaryAbelian x hx.1,hc hx⟩

/-- The nonsplit source branch constructs the whole-module marking, its precise
fixed involution line, and the full omega-center conclusion of 13.4.10(5). -/
theorem component_core_marking_of_moved_fixed
    {D : ChosenModule T L V}
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (m : CoreMarking D)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    {z : G} (hzV : z ∈ V)
    (hzT : z ∈ omegaOneCenterAmbient (T : Subgroup G)) (hz1 : z ≠ 1)
    (hKz : K ≤ centralizer ({z} : Set G))
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hfK : K ∈ MainForward.faithfulLocalComponents T)
    (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (hgen : ⁅K,elementaryAbelianMaxJ (T : Subgroup G)⁆ = K)
    (hfixed : (⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆ :
      Subgroup G) ⊓ centralizer (K : Set G) ≠ ⊥) :
    let U := ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆
    ∃ DK : ChosenModule T K U, Nonempty (CoreMarking DK) ∧
      U ⊓ centralizer (K : Set G) = zpowers z ∧
      U = ⁅(ReducedModule (K ⊔ (T : Subgroup G))).map
        (K ⊔ (T : Subgroup G)).subtype,K⁆ ∧
      Nonempty (ComponentModuleAt DK z) ∧
      omegaOneCenterAmbient (T : Subgroup G) =
        V ⊓ omegaOneCenterAmbient (T : Subgroup G) ∧
      Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 4 := by
  let U := ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆
  obtain ⟨⟨DK⟩,hUR⟩ := component_chosen_of_moved_fixed h₀ h structural m hzT hz1
    hKz hTK hKM hfK hqK hgen hfixed
  obtain ⟨a⟩ := fixed h₀ K hfK U DK hfixed
  obtain ⟨mK⟩ := coreMarking_of_faithful_core_action DK hqK a
  have hred := component_moved_reduced h₀ hzT hz1 hKz hTK
  have hTU : (T : Subgroup G) ≤ normalizer (U : Set G) := le_sup_right.trans
    (le_normalizer_of_normal_subgroupOf (DK.le_sylow.trans le_sup_right) (hK := hred.normal))
  have hCZ := core_fixed_le_omega DK mK hTU
  have hCZz : U ⊓ centralizer (K : Set G) ≤ zpowers z := by
    rw [←component_full_fixed_line h structural z hz1 hzT hindex K hKz hKM]
    exact le_inf hCZ inf_le_right
  have hzcard : Nat.card (zpowers z) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime ((mem_omegaOneCenterAmbient_iff _ _).mp hzT).2.1 hz1
  have he : U ⊓ centralizer (K : Set G) = zpowers z :=
    eq_of_le_of_card_ge hCZz (by rw [hzcard,mK.card_fixed])
  have hzU : z ∈ U := (he.symm ▸ mem_zpowers z).1
  have hs := full_seed_of_component_split h structural m ⟨z,hzV⟩
    (fun hh => hz1 (congrArg Subtype.val hh)) hzT hindex DK
    (ComponentModuleAt.coreSix mK hzU) hKz hKM
    (component_seed_split h₀ hzT hz1 hKz hTK)
  exact ⟨DK,⟨mK⟩,he,hUR,⟨ComponentModuleAt.coreSix mK hzU⟩,hs⟩

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
