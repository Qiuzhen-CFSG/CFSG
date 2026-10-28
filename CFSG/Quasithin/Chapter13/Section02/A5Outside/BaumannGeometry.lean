module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.ThompsonMarking
public import Theory.GroupTheory.PrimeIndexCentralizer
public import Stellmacher.BaumannMap

/-!
# Baumann images and the two flag-point centralizers

The pointwise fixer of the marked plane identifies the original Baumann
image with the already marked Thompson image. Each of the two points of
V₂ outside V₁ supplements the T-fixed line, so C_T(v)=C_T(V₂)=Baum(T).
The actual cores O₂(LT) and O₂(H) already centralize this plane and lie
in T; therefore adjoining either core to Baum(T) leaves it unchanged.

The final applications use the literal contrary join H∨O²(N_L(T∩L)).
They remove the centralizer and core-product premises of 13.2.11(4).
Identifying these two points with the original E.2.3 factor lines, and
identifying their stabilizers with N_T(Hᵢ), remain separate source steps.
Source: Aschbacher–Smith 13.2.11(2),(4) and13.2.12, pp.881–882.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.A5Source.Context
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}
  (d : Context T L V V₁ V₂ V₃)
include d

theorem flag_plane_centralizer_eq_point (v : G) (hv : v ∈ V₂) (hv₁ : v ∉ V₁) :
    (T : Subgroup G) ⊓ centralizer (V₂ : Set G) =
      (T : Subgroup G) ⊓ centralizer ({v} : Set G) := by
  have hc : Nat.card V₁ * V₁.relIndex V₂ = Nat.card V₂ := by
    simpa only [relIndex_bot_left] using
      relIndex_mul_relIndex ⊥ V₁ V₂ bot_le d.flag.one_le_two
  rw [d.flag.one_card,d.flag.two_card] at hc
  have hi : V₁.relIndex V₂ = 2 := by omega
  exact (inf_centralizer_eq_of_prime_index_supplement (T : Subgroup G) V₁ V₂
    d.flag.one_le_two Nat.prime_two hi
    (d.flag.one_invariant.trans (normalizer_le_centralizer_of_card_two _ d.flag.one_card))
    v hv hv₁).symm
end CFSG.Quasithin.Chapter13.Section05.A5Source.Context

namespace CFSG.Quasithin.Chapter13.Section02.A5Outside
variable {G : Type*} [Group G] [Finite G]

theorem source_baumann_eq_flag_point_centralizer
    {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
    (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H) (hz : center H = ⊥)
    (v : G) (hv : v ∈ V₂) (hv₁ : v ∉ V₁) :
    ChapterB.baumann (T : Subgroup G) = (T : Subgroup G) ⊓ centralizer ({v} : Set G) :=
  (source_baumann_eq_flag_plane_centralizer d hH hB hZ hs hz).trans
    (d.flag_plane_centralizer_eq_point v hv hv₁)

theorem source_core_products_eq_baumann
    {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
    (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H) (hz : center H = ⊥) :
    (L ⊔ (T : Subgroup G)).pCoreIn 2 ⊔ ChapterB.baumann (T : Subgroup G) =
      ChapterB.baumann (T : Subgroup G) ∧
    H.pCoreIn 2 ⊔ ChapterB.baumann (T : Subgroup G) =
      ChapterB.baumann (T : Subgroup G) := by
  have hQ : (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ ChapterB.baumann (T : Subgroup G) := by
    rw [source_baumann_eq_flag_plane_centralizer d hH hB hZ hs hz]
    apply le_inf ?_ (d.chosen.core_centralizes.trans (centralizer_le d.flag.two_le_V))
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le le_sup_right] using
      pCoreIn_le_sylow (L ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
  have hO : H.pCoreIn 2 ≤ ChapterB.baumann (T : Subgroup G) := by
    have hU := omegaOrbit_reduced d.hypothesis.qtke T hH
    have hUH : omegaOrbit T H ≤ H := conjugateSpanBy_le
      (fun _ hx => hH.1.1.2 ((mem_omegaOneCenterAmbient_iff _ _).mp hx).1) H.le_normalizer
    have hEU : ChapterB.thompsonAlpha (T : Subgroup G) ≤ omegaOrbit T H :=
      (source_alpha_eq_omegaOrbit_fixed d hH hB hZ hs hz).le.trans inf_le_left
    apply le_inf ?_ ?_
    · exact (pCoreIn_le_sylow H (T.subtype hH.1.1.2)).trans_eq
        (show ((T.subtype hH.1.1.2 : Sylow 2 H) : Subgroup H).map H.subtype =
          (T : Subgroup G) from map_subgroupOf_eq_of_le hH.1.1.2)
    · rintro x ⟨x,hx,rfl⟩ e he
      exact congrArg H.subtype ((le_centralizer_iff.mp hU.le_centralizer_pCore) hx
        ⟨e,hUH (hEU he)⟩ (hEU he))
  exact ⟨sup_eq_right.mpr hQ,sup_eq_right.mpr hO⟩
open BinaryPermutation.FivePairFixedSpaces

theorem source_thompson_baumann_and_plane_marking
    {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
    (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H) (hz : center H = ⊥) :
    let K := L ⊔ (T : Subgroup G)
    let S := T.subtype (show (T : Subgroup G) ≤ K from le_sup_right)
    ∃ g : Perm, (S : Subgroup K).map d.localActor =
      (normalizer (pairClosure : Set Perm)).map (MulAut.conj g).toMonoidHom ∧
      d.flag.preimage V₂ = (fixedSubgroup (first * second)).map (actionHom g) ∧
      (elementaryAbelianMaxJ (S : Subgroup K)).map d.localActor =
        pairClosure.map (MulAut.conj g).toMonoidHom ∧
      (ChapterB.baumann (S : Subgroup K)).map d.localActor =
        pairClosure.map (MulAut.conj g).toMonoidHom := by
  let K := L ⊔ (T : Subgroup G)
  let S := T.subtype (show (T : Subgroup G) ≤ K from le_sup_right)
  obtain ⟨g,hP,hW,hJ⟩ := source_thompson_and_plane_marking d hH hB hZ hs hz
  have hBm : (ChapterB.baumann (S : Subgroup K)).map K.subtype =
      ChapterB.baumann (T : Subgroup G) := by
    change ((S : Subgroup K) ⊓ centralizer
      (omegaOneCenterAmbient (elementaryAbelianMaxJ (S : Subgroup K)) : Set K)).map K.subtype = _
    have hSm : (S : Subgroup K).map K.subtype = (T : Subgroup G) :=
      map_subgroupOf_eq_of_le le_sup_right
    rw [baumann_map_injective K.subtype K.subtype_injective,hSm]
    rfl
  refine ⟨g,hP,hW,hJ,le_antisymm ?_ ?_⟩
  · rintro a ⟨t,ht,rfl⟩
    apply (BinaryPermutation.FiveSylowPlane.fixes_marked_plane_iff g _).mp
    rw [← hW]
    intro x hx
    have htG : (t : G) ∈ ChapterB.baumann (T : Subgroup G) := by
      rw [← hBm]
      exact mem_map_of_mem K.subtype ht
    rw [source_baumann_eq_flag_plane_centralizer d hH hB hZ hs hz] at htG
    apply d.flag.module.injective
    change d.flag.module.map (Multiplicative.ofAdd
      (BinaryPermutation.coreRepresentation (Fin 5) (d.flag.normalizerAction ⟨t,_⟩) x.toAdd)) = _
    rw [← d.flag.normalizer_equivariant]
    exact mul_inv_eq_iff_eq_mul.mpr ((mem_centralizer_iff.mp htG.2 _ hx).symm)
  · rw [← hJ]
    exact map_mono (ChapterB.elementaryAbelianMaxJ_le_baumann _)

theorem source_coreFree_borel_join_baumann_marking
    {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
    (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H)
    (hL₁Z : borelResidual T L ≤
      centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hcore : (H ⊔ borelResidual T L).pCoreIn 2 = ⊥) :
    let K := L ⊔ (T : Subgroup G)
    let S := T.subtype (show (T : Subgroup G) ≤ K from le_sup_right)
    ∃ g : Perm, (S : Subgroup K).map d.localActor =
      (normalizer (pairClosure : Set Perm)).map (MulAut.conj g).toMonoidHom ∧
      d.flag.preimage V₂ = (fixedSubgroup (first * second)).map (actionHom g) ∧
      (elementaryAbelianMaxJ (S : Subgroup K)).map d.localActor =
        pairClosure.map (MulAut.conj g).toMonoidHom ∧
      (ChapterB.baumann (S : Subgroup K)).map d.localActor =
        pairClosure.map (MulAut.conj g).toMonoidHom :=
  source_thompson_baumann_and_plane_marking d hH hB hZ hs
    (source_center_eq_bot_of_borel_join_core_eq_bot d hH hL₁Z hcore)


theorem source_coreFree_borel_join_point_centralizers
    {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
    (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H)
    (hL₁Z : borelResidual T L ≤
      centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hcore : (H ⊔ borelResidual T L).pCoreIn 2 = ⊥) :
    (∀ v ∈ V₂, v ∉ V₁ → ChapterB.baumann (T : Subgroup G) =
      (T : Subgroup G) ⊓ centralizer ({v} : Set G)) ∧
      (L ⊔ (T : Subgroup G)).pCoreIn 2 ⊔ ChapterB.baumann (T : Subgroup G) =
        ChapterB.baumann (T : Subgroup G) ∧
      H.pCoreIn 2 ⊔ ChapterB.baumann (T : Subgroup G) =
        ChapterB.baumann (T : Subgroup G) := by
  have hz := source_center_eq_bot_of_borel_join_core_eq_bot d hH hL₁Z hcore
  exact ⟨fun v hv hv₁ => source_baumann_eq_flag_point_centralizer d hH hB hZ hs hz v hv hv₁,
    source_core_products_eq_baumann d hH hB hZ hs hz⟩

end CFSG.Quasithin.Chapter13.Section02.A5Outside
