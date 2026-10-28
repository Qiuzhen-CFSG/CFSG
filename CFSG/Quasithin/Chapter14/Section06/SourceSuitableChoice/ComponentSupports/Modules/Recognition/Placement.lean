module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Modules.Recognition.Seeds
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Modules.Natural
public import Theory.Representation.BinaryConjugationSection.ConjugationCoordinates
public import Theory.GroupTheory.CComponent.NormalPair
public import Theory.GroupTheory.PGroup.MutualNormalizerCommutator

/-!
# Placement and coordinates of the literal component support

The image of an original relative component in H/O₂(H) is an ordinary
component, placing K in the preimage of F*. The two-core normalizes K,
so 14.6.2 puts the original central line in [U_H,K]. Mutual normalization
also places this commutator in O₂(K), and its original normalizer acts on
it. At H=Mc this constructs the literal binary section [U,K]/Z.

The final application supplies U0--U3 on W=[U,K] and S=N_T(K), using
these proved placements in the existing fixed-moving consumer. Its
fixed-free module input, index, local normalizer and separated supports
remain explicit obligations of qt-e-suitable-component-supports. This
ordinary whole-support application does not classify the natural summands
or assert fixed-freeness of the five-dimensional A6 cover. Original
14.6.18 remains the allowed input owned by qt-e-14625-source.
Source: Aschbacher--Smith 14.6.2, 14.6.19 and 14.6.22--24,
printed pp.1021,1037--1039.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.OneCohomology
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Modules.Recognition
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open Classification Classification.Sieve
variable {G : Type*} [Group G] [Finite G]

/-- The ambient two-core normalizes the literal relative component. -/
private theorem component_core_normalizes {H K : Subgroup G}
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent) :
    H.pCoreIn 2 ≤ normalizer (K : Set G) := by
  have hm := (map_mono (hK.pCore_le_normalizer 2) (f := H.subtype)).trans
    (le_normalizer_map H.subtype)
  rwa [map_subgroupOf_eq_of_le hKH] at hm

private theorem component_twoPerfect {H K : Subgroup G}
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent) : IsPPerfect 2 K := by
  let : Group.IsPerfect (K.subgroupOf H) := hK.perfect
  let : Group.IsPerfect K := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hKH).toMonoidHom) (subgroupOfEquivOfLe hKH).surjective
  intro N hN hq
  let : N.Normal := hN
  by_contra hne
  let : Nontrivial (K ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
  let : Group.IsNilpotent (K ⧸ N) := hq.isNilpotent
  exact Group.IsPerfect.not_isSolvable (K ⧸ N) inferInstance

variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (hsolv : ∀ J ∈ Chapter1.HOver G (T : Set G), Group.IsSolvable J → J ≤ M)
include hG hempty hM hunique hmany hcard e hab hsolv

/-- The original component lies in the preimage of F*(H/O₂(H)). -/
theorem source_component_fitting_placement
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent) :
    K ≤ ChapterA.Section04.twoGeneralizedFittingPreimage H := by
  have hc := component_le_generalizedFitting (H ⧸ pCore 2 H) (actorImage H K)
    (source_quotient_component hG T hempty hM hunique hmany hcard e hab hsolv H hH K hKH hK)
  have hi : K.subgroupOf H ≤
      (generalizedFitting (H ⧸ pCore 2 H)).comap (QuotientGroup.mk' (pCore 2 H)) :=
    (map_le_iff_le_comap).mp hc
  have hm := map_mono hi (f := H.subtype)
  rwa [map_subgroupOf_eq_of_le hKH] at hm

/-- The whole literal support contains the original central line and lies in
both U_H and O₂(K). It is normalized by the actual component normalizer in H. -/
theorem source_component_support_placement
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent) :
    let U := conjugateSpanBy (localModule T M) H
    centralInvolutions T ≤ ⁅U,K⁆ ∧
      ⁅U,K⁆ ≤ U ⊓ K.pCoreIn 2 ∧
      H ⊓ normalizer (K : Set G) ≤ normalizer (⁅U,K⁆ : Subgroup G) := by
  let U := conjugateSpanBy (localModule T M) H
  have h := source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH
  have hUQ : U ≤ H.pCoreIn 2 := h.UH_le_QH
  let : IsElementaryAbelian 2 U :=
    h.UH_elementary_of_V_le_QH ((le_conjugateSpanBy _ _).trans hUQ)
  have hnU : H ≤ normalizer (U : Set G) := le_normalizer_conjugateSpanBy _ _
  have hnK := component_core_normalizes hKH hK
  have hp := component_twoPerfect hKH hK
  have hn : K ≠ ⊥ := by
    intro hz
    exact hK.ne_bot (by rw [hz,bot_subgroupOf])
  refine ⟨source_lemma_14_6_2 hG T hempty hM hunique hmany hcard e hab H hH K
    (source_component_fitting_placement hG T hempty hM hunique hmany hcard e hab hsolv
      H hH K hKH hK) hp hn hnK,?_,?_⟩
  · refine le_inf (le_normalizer_iff_commutator_le_left.mp (hKH.trans hnU)) ?_
    rw [commutator_comm]
    exact commutator_le_pCore_of_mutual_normalization K U
      (IsElementaryAbelian.isPGroup 2 U) (hKH.trans hnU) (hUQ.trans hnK)
  · intro x hx
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (hnU hx.1),
      mem_normalizer_iff_map_conj_eq.mp hx.2]

/-- The original H=Mc support supplies the fitting, central-line and
normalization inputs for the exchanged-support branch of the vector geometry. -/
theorem terminal_component_support_inputs
    (K : Subgroup G) (hKM : K ≤ Mc) (hK : (K.subgroupOf Mc).IsCComponent) :
    let U := conjugateSpanBy (localModule T M) Mc
    K ≤ ChapterA.Section04.twoGeneralizedFittingPreimage Mc ∧
      centralInvolutions T ≤ ⁅U,K⁆ ∧ ⁅U,K⁆ ≤ U ⊓ K.pCoreIn 2 ∧
      K ⊔ Mc.pCoreIn 2 ≤ normalizer (⁅U,K⁆ : Subgroup G) ∧
      (T : Subgroup G) ⊓ normalizer (K : Set G) ≤ normalizer (⁅U,K⁆ : Subgroup G) := by
  have hout := terminal_outside hG T hempty hM hunique hmany hcard e
  obtain ⟨hz,hle,hn⟩ := source_component_support_placement
    hG T hempty hM hunique hmany hcard e hab hsolv Mc hout K hKM hK
  exact ⟨source_component_fitting_placement hG T hempty hM hunique hmany hcard e hab hsolv
    Mc hout K hKM hK, hz, hle,
    (sup_le (le_inf hKM K.le_normalizer)
      (le_inf (pCoreIn_le 2 Mc) (component_core_normalizes hKM hK))).trans hn,
    (inf_le_inf hout.1.2 le_rfl).trans hn⟩

/-- The literal support has canonical coordinates on [U,K]/Z under its
original component normalizer. No abstract module or quotient marking is assumed. -/
theorem terminal_component_support_coordinates
    (K : Subgroup G) (hKM : K ≤ Mc) (hK : (K.subgroupOf Mc).IsCComponent) :
    let W := ⁅conjugateSpanBy (localModule T M) Mc,K⁆
    ∃ hW : IsElementaryAbelian 2 W,
      let _ := hW
      ∃ τ : Representation (ZMod 2) (Mc ⊓ normalizer (K : Set G) : Subgroup G)
        (Additive (W ⧸ (centralInvolutions T).subgroupOf W)),
        Nonempty (BinaryConjugationSection (Mc ⊓ normalizer (K : Set G))
          W (centralInvolutions T) τ) := by
  let h := terminal_hypothesis hG T hempty hM hunique hmany hcard e hab
  let U := conjugateSpanBy (localModule T M) Mc
  let W := ⁅U,K⁆
  let : IsElementaryAbelian 2 U :=
    h.UH_elementary_of_V_le_QH ((le_conjugateSpanBy _ _).trans h.UH_le_QH)
  obtain ⟨hz,hle,hn⟩ := source_component_support_placement
    hG T hempty hM hunique hmany hcard e hab hsolv Mc
    (terminal_outside hG T hempty hM hunique hmany hcard e) K hKM hK
  have hW : IsElementaryAbelian 2 W := IsElementaryAbelian.of_le (hle.trans inf_le_left)
  let := hW
  refine ⟨hW,?_⟩
  exact BinaryConjugationSection.exists_conjugation_coordinates
    (Mc ⊓ normalizer (K : Set G)) W (centralInvolutions T)
    ((hle.trans inf_le_right).trans ((pCoreIn_le 2 K).trans (le_inf hKM K.le_normalizer)))
    hn hz (inf_le_left.trans (h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _)))

/-- On the literal whole component support W=[U,K], the source calculations
supply fitting placement, Z≤W and normalization for the fixed-moving consumer.
The natural-section marking and the remaining normalizer/separation statements
stay with this task's exchanged-component assembly. -/
theorem source_exists_on_component_support_of_fixed_free
    (K : Subgroup G) (hKM : K ≤ Mc) (hK : (K.subgroupOf Mc).IsCComponent)
    (hindex : ((T : Subgroup G) ⊓ normalizer (K : Set G)).relIndex (T : Subgroup G) = 2)
    (hlocal : Mc ⊓ normalizer (((T : Subgroup G) ⊓ normalizer (K : Set G) : Subgroup G) : Set G) =
      (T : Subgroup G))
    (hseparate : let W := ⁅conjugateSpanBy (localModule T M) Mc,K⁆
      ∀ t ∈ (T : Subgroup G), t ∉ (T : Subgroup G) ⊓ normalizer (K : Set G) →
        W ⊓ W.map (MulAut.conj t⁻¹).toMonoidHom ≤ centralizer (K : Set G) ∧
        K ≤ normalizer (W.map (MulAut.conj t⁻¹).toMonoidHom : Set G))
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Nontrivial V]
    (τ : Representation (ZMod 2) (Mc ⊓ normalizer (K : Set G) : Subgroup G) V)
    (c : BinaryConjugationSection (Mc ⊓ normalizer (K : Set G))
      ⁅conjugateSpanBy (localModule T M) Mc,K⁆ (centralInvolutions T) τ)
    (hfree : fixed (τ.comp (K.subgroupOf (Mc ⊓ normalizer (K : Set G))).subtype) = ⊥) :
    let h := terminal_hypothesis hG T hempty hM hunique hmany hcard e hab
    ∃ u ∈ ⁅conjugateSpanBy (localModule T M) Mc,K⁆,
      u ^ 2 = 1 ∧ u ≠ 1 ∧
      suitableQuotientCentralizer h u = (T : Subgroup G) ⊓ normalizer (K : Set G) ∧
      Suitable h Mc u := by
  let : Group.IsPerfect (K.subgroupOf Mc) := hK.perfect
  let : Group.IsPerfect K := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hKM).toMonoidHom) (subgroupOfEquivOfLe hKM).surjective
  obtain ⟨hfit,hz,hle,hn,_⟩ := terminal_component_support_inputs
    hG T hempty hM hunique hmany hcard e hab hsolv K hKM hK
  exact source_exists_of_fixed_free_central_overlap
    hG T hempty hM hunique hmany hcard e hab K _ _ _
    ⟨hfit,hle.trans inf_le_left,hz,le_sup_left.trans hn,inf_le_left,hindex,hlocal,hseparate⟩
    τ c (inf_le_inf (terminal_outside hG T hempty hM hunique hmany hcard e).1.2 le_rfl) hfree

end CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Modules.Recognition
