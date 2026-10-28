module
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.NoThreeSupport
public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.NineSupport

/-!
# Irreducibility of the original normal elementary-nine component

Work in the literal quotient M/C_M(U) of the selected local subgroup. If
its normal elementary-nine core and the image of T preserve a proper
subspace, T normalizes each of the two cubic support actors. Each actor
fixes the opposite plane. The original unique maximal overgroup of C_G(Z)
therefore contains both full preimages, and hence the full odd-core preimage.

The Sylow-fixed vectors generate U under that core. Consequently U equals
the original intersection span over M intersect Mc. The actual ordering
conclusion and A.5.6 exclude this nontrivial M-normal span. This proves
irreducibility and constructs the support datum from the source order,
dimension, and movement premises when it is not already marked.

Source: Aschbacher--Smith 15.1.2, printed p.1085, elementary-nine paragraph.
The proof uses the previously proved span obstruction; no recognition of
all subgroups of O4+(2) or later Chapter 15 theorem is assumed.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

private theorem irreducible_mono {G V : Type*} [Group G] [AddCommGroup V]
    [Module (ZMod 2) V] (ρ : Representation (ZMod 2) G V) {A B : Subgroup G}
    (hAB : A ≤ B) (hi : IsIrreducible (ρ.comp A.subtype)) :
    IsIrreducible (ρ.comp B.subtype) := by
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial (ρ.comp A.subtype)
  apply IsSimpleOrder.of_forall_eq_top
  intro C hC
  let D : Subrepresentation (ρ.comp A.subtype) := ⟨C.toSubmodule, by
    intro a v hv
    exact C.apply_mem_toSubmodule ⟨a,hAB a.property⟩ hv⟩
  rcases eq_bot_or_eq_top D with hd | hd
  · exact (hC (Subrepresentation.toSubmodule_injective
      (show C.toSubmodule = ⊥ from congrArg Subrepresentation.toSubmodule hd))).elim
  · exact Subrepresentation.toSubmodule_injective
      (show C.toSubmodule = ⊤ from congrArg Subrepresentation.toSubmodule hd)

private theorem source_no_reducible_two_support_component
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (U : Subgroup M) [U.Normal] [IsElementaryAbelian 2 U]
    (P : Subgroup (M ⧸ centralizer (U : Set M))) [P.Normal] [IsElementaryAbelian 3 P]
    (d : ChapterD.FittingConfigurations.SupportFactors
      (NormalElementaryQuotient.representation U
        (QuotientGroup.mk' (centralizer (U : Set M)))
        (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)) P 2)
    (C : Submodule (ZMod 2) (Additive U)) (hC0 : C ≠ ⊥) (hC1 : C ≠ ⊤)
    (hC : P ⊔ ((T.subtype hM.1.2 : Subgroup M).map
      (QuotientGroup.mk' (centralizer (U : Set M)))) ≤ subspaceStabilizer
      (NormalElementaryQuotient.representation U
        (QuotientGroup.mk' (centralizer (U : Set M)))
        (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)) C) : False := by
  let q := QuotientGroup.mk' (centralizer (U : Set M))
  let ρ := NormalElementaryQuotient.representation U q
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
  let S := T.subtype hM.1.2
  let B := Mc.subgroupOf M
  have hf : Function.Injective ρ := NormalElementaryQuotient.representation_injective U q
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
  have hS : IsPGroup 2 ((S : Subgroup M).map q) := S.isPGroup'.map q
  let X := d.ambient 0
  let R := d.ambient 1
  have hn := d.two_normalized_of_reducible ρ hf ((S : Subgroup M).map q) C hC0 hC1 hC
  have hnX := hn 0
  have hnR := hn 1
  have hXR : X ⊔ R = P := by
    rw [← d.ambients_generate ρ]
    apply le_antisymm (sup_le (le_iSup _ 0) (le_iSup _ 1))
    apply iSup_le
    intro i
    fin_cases i
    · exact le_sup_left
    · exact le_sup_right
  have hfix (i j : Fin 2) (hne : i ≠ j) : fixedSpace ρ (d.ambient i) ≠ ⊥ := by
    intro he
    have hz := bot_unique (he ▸ d.cross_fixed ρ hf hne.symm)
    have hd := d.support_dim j
    change Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ (d.ambient j)) = 2 at hd
    rw [hz] at hd
    simp at hd
  have hXfix := hfix 0 1 (by decide)
  have hRfix := hfix 1 0 (by decide)
  have hXM := normalized_actor_preimage_le_partner_of_fixed_ne_bot T hM.1.2 hu U X hnX hXfix
  have hRM := normalized_actor_preimage_le_partner_of_fixed_ne_bot T hM.1.2 hu U R hnR hRfix
  have hXB : X.comap q ≤ B := by
    intro x hx
    exact hXM (mem_map_of_mem M.subtype hx)
  have hRB : R.comap q ≤ B := by
    intro x hx
    exact hRM (mem_map_of_mem M.subtype hx)
  have hXmap : X ≤ B.map q := by
    apply (map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) X).ge.trans
    exact map_mono hXB
  have hRmap : R ≤ B.map q := by
    apply (map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) R).ge.trans
    exact map_mono hRB
  have hker : q.ker ≤ B := by
    intro x hx
    apply hXB
    change q x ∈ X
    rw [show q x = 1 from hx]
    exact X.one_mem
  have hPB : P.comap q ≤ B := by
    have hp : P ≤ B.map q := hXR ▸ sup_le hXmap hRmap
    have hh := comap_mono (f := q) hp
    rwa [comap_map_eq_self hker] at hh
  have hPMc : (P.comap q).map M.subtype ≤ Mc := by
    rintro x ⟨y,hy,rfl⟩
    exact hPB hy
  have hgen := d.fixed_generates ρ hf _ hS
  have hspan := component_span_of_partner_actor T hM.1.2 U P hPMc hgen
  let W := (U.map M.subtype) ⊓ centralInvolutions T
  have hUne : U.map M.subtype ≠ ⊥ := by
    intro he
    have hUbot := (map_eq_bot_iff_of_injective U M.subtype_injective).mp he
    have hc : Nat.card U = 1 := by rw [hUbot]; simp
    have hv : Module.finrank (ZMod 2) (Additive U) = 0 := by
      have : Subsingleton U := (Nat.card_eq_one_iff_unique.mp hc).1
      exact Module.finrank_zero_of_subsingleton
    have hd := (d.support_dim (0 : Fin 2))
    change Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ (d.ambient (0 : Fin 2))) = 2 at hd
    have hl := Submodule.finrank_le (subspaceCommutator ρ ⊤ (d.ambient (0 : Fin 2)))
    rw [hv, hd] at hl
    omega
  have hWne : W ≠ ⊥ := by
    intro he
    apply hUne
    rw [hspan]
    change conjugateSpanBy W (Mc ⊓ M) = ⊥
    apply bot_unique
    exact conjugateSpanBy_le (by rw [he]) (by rw [normalizer_eq_top]; exact le_top)
  have hMc : Mc ∈ maximalLocals T := by
    refine ⟨(show Mc ∈ maximalTwoLocalOvergroups
      (centralizer (centralInvolutions T : Set G)) from hu ▸ Set.mem_singleton Mc).1,?_⟩
    apply le_trans _ (centralizer_le_partner T hu)
    intro t ht z hz
    exact (((mem_omegaOneCenterAmbient_iff _ z).mp hz).2.2 t ht).symm
  have hnU : M ≤ normalizer (U.map M.subtype : Set G) := by
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map,range_subtype]
      using U.le_normalizer_map M.subtype
  exact source_no_invariant_span_of_centralizing_orderingMaximal hG T hempty hM hJ
    hMc hne.symm W hWne inf_le_right (hspan ▸ hnU)

/-- The original normal two-plane component is irreducible under its core and T. -/
theorem source_nine_component_irreducible
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (U : Subgroup M) [U.Normal] [IsElementaryAbelian 2 U]
    (P : Subgroup (M ⧸ centralizer (U : Set M))) [P.Normal] [IsElementaryAbelian 3 P]
    (d : ChapterD.FittingConfigurations.SupportFactors
      (NormalElementaryQuotient.representation U
        (QuotientGroup.mk' (centralizer (U : Set M)))
        (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)) P 2) :
    IsIrreducible ((NormalElementaryQuotient.representation U
      (QuotientGroup.mk' (centralizer (U : Set M)))
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)).comp
      (P ⊔ ((T.subtype hM.1.2 : Subgroup M).map
        (QuotientGroup.mk' (centralizer (U : Set M))))).subtype) := by
  let q := QuotientGroup.mk' (centralizer (U : Set M))
  let ρ := NormalElementaryQuotient.representation U q
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
  have hd := d.finrank_eq ρ
  let : Nontrivial (Additive U) := Module.nontrivial_of_finrank_pos (by rw [hd]; decide)
  apply IsSimpleOrder.of_forall_eq_top
  intro C hC0
  by_contra hC1
  have hc0 : C.toSubmodule ≠ ⊥ := fun he => hC0 (Subrepresentation.toSubmodule_injective he)
  have hc1 : C.toSubmodule ≠ ⊤ := fun he => hC1 (Subrepresentation.toSubmodule_injective he)
  apply source_no_reducible_two_support_component hG T hempty hM hJ hu hne U P d
    C.toSubmodule hc0 hc1
  apply le_subspaceStabilizer
  intro g hg v hv
  exact C.apply_mem_toSubmodule ⟨g,hg⟩ hv

/-- The source E9 endpoint supplies its own two support planes. -/
theorem source_nine_component_irreducible_of_card
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (U : Subgroup M) [U.Normal] [IsElementaryAbelian 2 U]
    (P : Subgroup (M ⧸ centralizer (U : Set M))) [P.Normal] [IsElementaryAbelian 3 P]
    (hP : Nat.card P = 9)
    (hdim : Module.finrank (ZMod 2) (Additive U) = 4)
    (hmoved : subspaceCommutator (NormalElementaryQuotient.representation U
      (QuotientGroup.mk' (centralizer (U : Set M)))
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)) ⊤ P = ⊤) :
    IsIrreducible ((NormalElementaryQuotient.representation U
      (QuotientGroup.mk' (centralizer (U : Set M)))
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)).comp
      (P ⊔ ((T.subtype hM.1.2 : Subgroup M).map
        (QuotientGroup.mk' (centralizer (U : Set M))))).subtype) := by
  let q := QuotientGroup.mk' (centralizer (U : Set M))
  let ρ := NormalElementaryQuotient.representation U q
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
  have hf := NormalElementaryQuotient.representation_injective U q
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
  obtain ⟨d⟩ := ChapterD.FittingConfigurations.supportFactors_of_nine_four_moved
    ρ hf P hP hdim hmoved
  exact source_nine_component_irreducible hG T hempty hM hJ hu hne U P d

/-- The literal component-plus-Sylow action is irreducible whenever it contains the nine-core. -/
theorem source_nine_extension_irreducible
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (U : Subgroup M) [U.Normal] [IsElementaryAbelian 2 U]
    (P : Subgroup (M ⧸ centralizer (U : Set M))) [P.Normal] [IsElementaryAbelian 3 P]
    (hP : Nat.card P = 9) (hdim : Module.finrank (ZMod 2) (Additive U) = 4)
    (hmoved : subspaceCommutator (NormalElementaryQuotient.representation U
      (QuotientGroup.mk' (centralizer (U : Set M)))
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)) ⊤ P = ⊤)
    (R : Subgroup (M ⧸ centralizer (U : Set M))) (hPR : P ≤ R) :
    IsIrreducible ((NormalElementaryQuotient.representation U
      (QuotientGroup.mk' (centralizer (U : Set M)))
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)).comp
      (R ⊔ ((T.subtype hM.1.2 : Subgroup M).map
        (QuotientGroup.mk' (centralizer (U : Set M))))).subtype) :=
  irreducible_mono _ (sup_le_sup_right hPR _)
    (source_nine_component_irreducible_of_card hG T hempty hM hJ hu hne U P hP hdim hmoved)

end CFSG.Quasithin.Chapter15.Section01
