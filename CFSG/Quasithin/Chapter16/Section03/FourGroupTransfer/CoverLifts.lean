module

public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.Contracts
public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.CoverLifts.Inputs
public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.CoverLifts.TableReduction
public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.CoverLifts.Adequate
public import Theory.GroupTheory.DoubleCoverCentralizer.Recognition

/-!
# The exceptional cover argument in four-group transfer

The source assembly derives the intermediate table reduction from the literal
earlier center and involution clauses. E1 first identifies Z(I) with O₂(I).
The order formula for the centralizer then gives order four or eight; I.2.2
forces its noncentral elements to have order four, and rank-one recognition
gives actual C₄ or Q₈ isomorphisms. A nonidentity inner actor and its lift supply
the equality of automorphisms needed for the later factorization e = r₀f.

The non-2-central mark and the bound on the outer image are proved by the
source-table adapter, rather than assumed by the source assembly. The earlier
source clauses and the precise I.2.2 lifting clause remain explicit inputs;
their producers and the ambient transfer are owned by the section assemblies.
The separately exported adequate J₂ route uses the preimage of the actual
actor image and proves it quaternion, without identifying the full fixer with
a two-group.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
16.3.6, last paragraph, printed p.1179 / PDF p.1196; I.2.2(5b),(7b),
printed pp.409–410 / PDF pp.420–421; 16.1.2 and 16.1.5, pp.1170–1172.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.FourGroupTransfer.CoverLifts
open Subgroup Theory.GroupTheory Theory.GroupTheory.DoubleCoverCentralizer ClassificationModels
variable {G : Type*} [Group G] [Finite G] {𝒦 : GroupClass}
variable {E L : Subgroup G} {i : G}

/-- E1 identifies the two-core with the center before the lifting clauses are used. -/
theorem enlargement_center_eq_core (hG : Hypothesis1611 𝒦 G) (hi : orderOf i = 2)
    (h : ExceptionalEnlargement E L i) :
    center (Enlargement L i) = pCore 2 (Enlargement L i) :=
  hG.evenType.component_center_eq_twoCore hi h.component

/-- Conditional cover assembly. The table reduction is an intermediate
obligation; this theorem does not assert it or prove the source theorem 16.3.6. -/
theorem exceptional_cover_lifts_of_table_reduction
    (hG : Hypothesis1611 𝒦 G) (hi : orderOf i = 2)
    (h : ExceptionalEnlargement E L i) (hcard : Nat.card E = 4)
    (hcomp : CentralizesAsComponent E L) (ht : TableReduction E L i h)
    (hlift : NonTwoCentralInvolutionLifting (Enlargement L i)) :
    CoverLiftConclusion E L i h := by
  classical
  let I := Enlargement L i
  let J := ComponentInside L i
  let C := ComponentCentralizer L i
  let α := inducedAction E I h.normalizes
  let : Group.IsPerfect J := componentInside_perfect hcard hcomp
  let : IsElementaryAbelian 2 E := h.elementary
  have himage : α.range = centralizer (J.map MulAut.conj : Set (MulAut I)) := by
    rw [← component_action_range L i]
    exact h.image_eq
  have hZeq := enlargement_center_eq_core hG hi h
  have hZne : center I ≠ ⊥ := by
    change center (Enlargement L i) ≠ ⊥
    rw [hZeq]
    exact h.core_ne
  have hZ : Nat.card (center I) = 2 := by
    have hn : Nat.card (center I) ≠ 1 := fun hh => hZne ((center I).eq_bot_iff_card.mpr hh)
    have hp : 0 < Nat.card (center I) := Nat.card_pos
    have hb := ht.center_bound
    change Nat.card (center I) ≤ 2 at hb
    omega
  have hcount : Nat.card C = 2 * Nat.card (innerActors α) := by
    rw [centralizer_card J α h.faithful himage, hZ]
  have hC : Nat.card C = 4 ∨ Nat.card C = 8 := by
    rcases innerActors_card α hcard ht.inner_index with hb | hb
    · exact Or.inl (by rw [hcount, hb])
    · exact Or.inr (by rw [hcount, hb])
  have ha2 (e : E) : (α e) ^ 2 = 1 := by
    rw [← map_pow, Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 E) e, map_one]
  have horder (f : I) (hf : f ∈ C) (hz : f ∉ center I) :
      orderOf (QuotientGroup.mk' (center I) f) = 2 := by
    have hm : MulAut.conj f ∈ α.range := by
      rw [himage]
      exact (conj_mem_centralizer_iff J f).mpr hf
    obtain ⟨e, he⟩ := hm
    have hn : MulAut.conj f ≠ 1 := by
      intro hh
      exact hz ((conj_kernel (H := I)) ▸ (show f ∈ (MulAut.conj : I →* MulAut I).ker from hh))
    have ho : orderOf (MulAut.conj f) = 2 :=
      orderOf_eq_prime (he ▸ ha2 e) hn
    exact (orderOf_injective quotientConj quotientConj_injective _).symm.trans ho
  have hfour (f : C) (hz : (f : I) ∉ center I) : orderOf f = 4 := by
    rw [← orderOf_coe]
    apply order_four_of_marked_coset hZ hlift f (horder f f.property hz)
    apply ht.non_two_central_mark f (horder f f.property hz)
    rw [himage]
    exact (conj_mem_centralizer_iff J f).mpr f.property
  have hshape := centralizer_shape C (center_le_centralizer (J : Set I)) hZ hC hfour
  constructor
  · rcases hshape with hq | ⟨hc4, hc⟩
    · exact Or.inl hq
    · refine Or.inr ⟨hc, ?_⟩
      have hb2 : Nat.card (innerActors α) = 2 := by omega
      have hout : ∃ e : E, α e ∉ (MulAut.conj : I →* MulAut I).range := by
        by_contra! hall
        have hbtop : innerActors α = ⊤ := top_unique (fun e _ => hall e)
        have hbcard : Nat.card (innerActors α) = Nat.card E := by
          rw [hbtop]
          exact Nat.card_congr Subgroup.topEquiv.toEquiv
        omega
      obtain ⟨e, he⟩ := hout
      exact ht.outer_m12 e he
  · obtain ⟨e, he, f, hf⟩ := exists_inner_actor α hcard ht.inner_index
    have hfC : f ∈ C := (conj_mem_centralizer_iff J f).mp (by
      rw [← hf, ← himage]
      exact ⟨e, rfl⟩)
    have hfZ : f ∉ center I := by
      intro hz
      have hh : α e = α 1 := by
        rw [map_one, hf]
        exact (show f ∈ (MulAut.conj : I →* MulAut I).ker from (conj_kernel (H := I)).symm ▸ hz)
      exact he (h.faithful hh)
    refine ⟨e, he, f, ?_, ?_, ?_, hf⟩
    · intro l hl
      exact congrArg Subtype.val (mem_centralizer_iff.mp hfC
        ⟨l, ComponentTransfer.le_layerClosure _ _ hl⟩ hl)
    · exact (orderOf_coe (⟨f, hfC⟩ : C)).trans (hfour ⟨f, hfC⟩ hfZ)
    · apply (QuotientGroup.eq_one_iff (f ^ 2)).mp
      change QuotientGroup.mk' (center I) (f ^ 2) = 1
      rw [map_pow, ← horder f hfC hfZ, pow_orderOf_eq_one]

/-- The exceptional-cover implication from the literal earlier source clauses.
The center bound, inner-index bound, outer M₁₂ restriction and non-2-central
mark are all derived here; only the exact earlier source inputs remain. -/
theorem exceptional_cover_lifts_of_source
    (source : TableReduction.CenterClause (G := G) 𝒦)
    (tables : TableReduction.InvolutionTables)
    (hG : Hypothesis1611 𝒦 G) (hi : orderOf i = 2)
    (h : ExceptionalEnlargement E L i) (hcard : Nat.card E = 4)
    (hcomp : CentralizesAsComponent E L)
    (hlift : NonTwoCentralInvolutionLifting (Enlargement L i)) :
    CoverLiftConclusion E L i h :=
  exceptional_cover_lifts_of_table_reduction hG hi h hcard hcomp
    (TableReduction.table_reduction_of_source source tables hG hi h hcard hcomp) hlift

end CFSG.Quasithin.Chapter16.FourGroupTransfer.CoverLifts
