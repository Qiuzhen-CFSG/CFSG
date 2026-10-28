module
public import CFSG.Quasithin.Chapter15.Section01.OrderingSource.Assembly
public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.PermutedThreeSeed
public import CFSG.Quasithin.Chapter15.Section03.InitialSource.OddImage
public import Theory.Representation.NormalElementaryQuotient

/-!
# Excluding the three-plane indecomposable in the original local action

For a normal elementary binary subgroup U of the selected local M, work on
its literal faithful quotient M/C_M(U). A normal elementary ternary actor
with three canonical natural supports has a Sylow-normalized splitting into
one marked actor and the other two. Both have nonzero fixed spaces on their
opposite supports. The unique maximal overgroup of C_G(Z) therefore contains
their full preimages, and hence the full odd actor's preimage.

The Sylow-fixed vectors generate U under that actor. Translating this linear
span back to the original group gives U = <(U intersect Z)^(M intersect Mc)>.
The actual ordering theorem and A.5.6 exclude this nontrivial M-invariant span.
Thus case (6) of D.2.17 cannot occur on an M-normal component. The marked
support data is exactly the existing D.2 family; no recognition premise is
introduced here.

Source: Aschbacher--Smith, 15.1.2, printed p.1085, first full paragraph.
The proof uses cross-centralization: the first actor fixes the opposite two
supports, and the other two actors fix the first support.
-/

public section

open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

theorem normalized_actor_preimage_le_partner_of_fixed_ne_bot
    (T : Sylow 2 G) {M Mc : Subgroup G} (hTM : (T : Subgroup G) ≤ M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (U : Subgroup M) [U.Normal] [IsElementaryAbelian 2 U]
    (A : Subgroup (M ⧸ centralizer (U : Set M)))
    (hn : ((T.subtype hTM : Subgroup M).map
      (QuotientGroup.mk' (centralizer (U : Set M)))) ≤ normalizer (A : Set _))
    (hfix : fixedSpace (NormalElementaryQuotient.representation U
      (QuotientGroup.mk' (centralizer (U : Set M)))
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)) A ≠ ⊥) :
    (A.comap (QuotientGroup.mk' (centralizer (U : Set M)))).map M.subtype ≤ Mc := by
  let q := QuotientGroup.mk' (centralizer (U : Set M))
  have he : (A.comap q).map q = A := map_comap_eq_self_of_surjective
    (QuotientGroup.mk'_surjective _) A
  by_contra hescape
  have hbot := fixed_eq_bot_of_image_normalized T hTM hu U (A.comap q)
    (by rw [he]; exact hn) hescape
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hfix
  have hc : (v.toMul : M) ∈ centralizer (A.comap q : Set M) :=
    (NormalElementaryQuotient.mem_fixedSpace_image U q (QuotientGroup.mk'_surjective _)
      (QuotientGroup.ker_mk' _) (A.comap q) v).mp (he.symm ▸ hv)
  have hm : (v.toMul : M) ∈ U ⊓ centralizer (A.comap q : Set M) := ⟨v.toMul.property, hc⟩
  rw [hbot] at hm
  apply hv0
  exact Additive.toMul.injective (Subtype.ext (Subgroup.mem_bot.mp hm))

omit [Finite G] in
theorem component_span_of_partner_actor
    (T : Sylow 2 G) {M Mc : Subgroup G} (hTM : (T : Subgroup G) ≤ M)
    (U : Subgroup M) [U.Normal] [IsElementaryAbelian 2 U]
    (P : Subgroup (M ⧸ centralizer (U : Set M)))
    (hPMc : (P.comap (QuotientGroup.mk' (centralizer (U : Set M)))).map M.subtype ≤ Mc)
    (hgen : Homogeneous.orbitSpan (NormalElementaryQuotient.representation U
      (QuotientGroup.mk' (centralizer (U : Set M)))
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)) P
      (fixedSpace (NormalElementaryQuotient.representation U
        (QuotientGroup.mk' (centralizer (U : Set M)))
        (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _))
        ((T.subtype hTM : Subgroup M).map (QuotientGroup.mk' (centralizer (U : Set M))))) = ⊤) :
    U.map M.subtype = conjugateSpanBy ((U.map M.subtype) ⊓ centralInvolutions T) (Mc ⊓ M) := by
  let q := QuotientGroup.mk' (centralizer (U : Set M))
  let ρ := NormalElementaryQuotient.representation U q
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
  let S := T.subtype hTM
  let W := (U.map M.subtype) ⊓ centralInvolutions T
  let K := conjugateSpanBy W (Mc ⊓ M)
  let B : Subgroup U := (K.subgroupOf M).subgroupOf U
  let C := AddSubgroup.toZModSubmodule 2 B.toAddSubgroup
  have hfixed : fixedSpace ρ ((S : Subgroup M).map q) ≤ C := by
    intro v hv
    have hc : (v.toMul : M) ∈ centralizer (S : Set M) :=
      (NormalElementaryQuotient.mem_fixedSpace_image U q (QuotientGroup.mk'_surjective _)
        (QuotientGroup.ker_mk' _) S v).mp hv
    have hz : ((v.toMul : M) : G) ∈ centralInvolutions T := by
      apply (mem_omegaOneCenterAmbient_iff _ _).mpr
      refine ⟨(IsElementaryAbelian.isPGroup 2 U).le_sylow_of_normal S v.toMul.property, ?_, ?_⟩
      · exact congrArg M.subtype (elemPow_eq_one_of_isElementaryAbelian (p := 2) _ v.toMul.property)
      · intro t ht
        exact congrArg M.subtype (hc ⟨t,hTM ht⟩ ht)
    exact le_conjugateSpanBy W (Mc ⊓ M) ⟨mem_map_of_mem M.subtype v.toMul.property,hz⟩
  have hstable : P ≤ subspaceStabilizer ρ C := by
    apply le_subspaceStabilizer
    intro p hp v hv
    obtain ⟨m,hm⟩ := QuotientGroup.mk'_surjective (centralizer (U : Set M)) p
    have hmP : m ∈ P.comap q := by change q m ∈ P; rwa [hm]
    have hmMc : (m : G) ∈ Mc := hPMc (mem_map_of_mem M.subtype hmP)
    change ((ρ p v).toMul : M) ∈ K.subgroupOf M
    change (((ρ p v).toMul : M) : G) ∈ K
    rw [← hm, NormalElementaryQuotient.representation_apply]
    exact le_normalizer_iff.mp (le_normalizer_conjugateSpanBy W (Mc ⊓ M))
      m ⟨hmMc,m.property⟩ v.toMul hv
  have hCtop : C = ⊤ := top_unique (by
    rw [← hgen]
    exact Homogeneous.orbitSpan_le ρ hfixed hstable)
  apply le_antisymm
  · rintro x ⟨u,hu,rfl⟩
    have hv : Additive.ofMul (⟨u,hu⟩ : U) ∈ C := hCtop ▸ Submodule.mem_top
    exact hv
  · have hn : M ≤ normalizer (U.map M.subtype : Set G) := by
      simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map,range_subtype]
        using U.le_normalizer_map M.subtype
    exact conjugateSpanBy_le inf_le_left (inf_le_right.trans hn)

theorem source_no_three_support_component
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
        (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)) P 3) : False := by
  let q := QuotientGroup.mk' (centralizer (U : Set M))
  let ρ := NormalElementaryQuotient.representation U q
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
  let S := T.subtype hM.1.2
  let B := Mc.subgroupOf M
  have hf : Function.Injective ρ := NormalElementaryQuotient.representation_injective U q
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
  have hS : IsPGroup 2 ((S : Subgroup M).map q) := S.isPGroup'.map q
  obtain ⟨X,R,hnX,hnR,hXR,hXfix,hRfix⟩ := d.exists_normalized_split ρ hf _ hS
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
    have hd := (d.support_dim (0 : Fin 3))
    change Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ (d.ambient (0 : Fin 3))) = 2 at hd
    have hl := Submodule.finrank_le (subspaceCommutator ρ ⊤ (d.ambient (0 : Fin 3)))
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

end CFSG.Quasithin.Chapter15.Section01
