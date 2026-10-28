module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SymmetricSix.SelectedGroup
public import Theory.SpecificGroups.SymmetricSeven.ThreePairsCubic
public import Stellmacher.OmegaOneCenterMap
public import Stellmacher.ElementaryAbelianMaxJMap
public import Theory.ElementaryAbelian.Basic

/-!
# The natural seven-point cubic on the original two-subgroup

An invariant cubic in the original two-core quotient has index three over
any original two-subgroup containing the core. The vector e₀+e₁ is fixed by
the three disjoint transpositions. Its cubic translate is moved by the first
transposition. Equivariant coordinates on a normal elementary subgroup place
these vectors in the literal omega-center span of the selected preimage.

Source: Aschbacher–Smith C.1.24(a), printed pp.130–131.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterC.RankOne.SevenSource.Natural
open SymmetricSix
open Theory.SpecificGroups.SymmetricSeven.ThreePairsCubic
open Representation.AlternatingSevenConjugatePair.ElementaryGeometry
variable {G : Type*} [Group G] [Finite G]

/-- The cubic preimage has index three for an arbitrary two-group image. -/
theorem selected_index_three_of_twoGroup (R : Subgroup G) (hpR : IsPGroup 2 R)
    (hQR : pCore 2 G ≤ R) (M : Subgroup (G ⧸ pCore 2 G)) (hM : Nat.card M=3)
    (hn : R.map (QuotientGroup.mk' (pCore 2 G)) ≤ normalizer (M : Set (G ⧸ pCore 2 G))) :
    (R.subgroupOf (selectedGroup R M)).index=3 := by
  let q := QuotientGroup.mk' (pCore 2 G)
  let A := R.map q
  have hAc : Nat.Coprime (Nat.card M) (Nat.card A) := by
    obtain ⟨n,hn⟩ := (hpR.map q).exists_card_eq
    rw [hM,hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  have hd : Disjoint M A := disjoint_of_coprime_natCard hAc
  have hcard : Nat.card (M ⊔ A : Subgroup (G ⧸ pCore 2 G))=3 * Nat.card A := by
    rw [card_sup_eq_mul_of_normalizes_of_disjoint M A hn hd,hM]
  have hi : A.relIndex (M ⊔ A)=3 := by
    have hh := relIndex_mul_relIndex (⊥ : Subgroup (G ⧸ pCore 2 G)) A (M ⊔ A) bot_le le_sup_right
    rw [relIndex_bot_left,relIndex_bot_left,hcard,Nat.mul_comm 3] at hh
    exact Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := A)) hh
  change R.relIndex (selectedGroup R M)=3
  have hh := relIndex_map_map q R (selectedGroup R M)
  rw [show q.ker=pCore 2 G from QuotientGroup.ker_mk' _,sup_of_le_left hQR,
    sup_of_le_left (core_le_selectedGroup R M)] at hh
  rw [←hh]
  change A.relIndex (((M ⊔ A).comap q).map q)=3
  rw [map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _]
  exact hi

/-- The original two-subgroup is a Sylow subgroup of the selected preimage. -/
theorem selected_sylow_of_twoGroup (R : Subgroup G) (hpR : IsPGroup 2 R)
    (hQR : pCore 2 G ≤ R) (M : Subgroup (G ⧸ pCore 2 G)) (hM : Nat.card M=3)
    (hn : R.map (QuotientGroup.mk' (pCore 2 G)) ≤ normalizer (M : Set (G ⧸ pCore 2 G))) :
    ∃ P : Sylow 2 (selectedGroup R M),
      (P : Subgroup (selectedGroup R M))=R.subgroupOf (selectedGroup R M) ∧
      (P : Subgroup (selectedGroup R M)).index=3 := by
  have hi := selected_index_three_of_twoGroup R hpR hQR M hM hn
  exact ⟨hpR.comap_subtype.toSylow
    (show ¬2 ∣ (R.subgroupOf (selectedGroup R M)).index by rw [hi];decide),rfl,hi⟩

omit [Finite G] in
/-- The same natural vector proves movement of the actual omega-center span. -/
theorem omega_span_moved (U R A : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (hUR : U ≤ R) (q : G →* Sym)
    (e : U ≃* Multiplicative (BinaryPermutation.natural (Fin 7)))
    (he : ∀ (g : G) (v : U), (e (MulAut.conjNormal g v)).toAdd =
      BinaryPermutation.naturalRepresentation (Fin 7) (q g) (e v).toAdd)
    (hR : R.map q ≤ pairElementary) (hrA : swap01 ∈ A.map q)
    (hcG : cubic ∈ q.range) :
    ¬A ≤ centralizer (normalClosure (omegaOneCenterAmbient R : Set G) : Set G) := by
  let u : U := e.symm (Multiplicative.ofAdd pairPoint)
  have heu : (e u).toAdd=pairPoint := congrArg Multiplicative.toAdd (e.apply_symm_apply _)
  have huR : (u:G) ∈ omegaOneCenterAmbient R := by
    apply (mem_omegaOneCenterAmbient_iff R (u:G)).mpr
    refine ⟨hUR u.property,elemPow_eq_one_of_isElementaryAbelian (u:G) u.property,?_⟩
    intro a ha
    have hfix : MulAut.conjNormal a u=u := by
      apply e.injective
      apply Multiplicative.toAdd.injective
      rw [he,heu]
      exact pairPoint_fixed ⟨q a,hR (mem_map_of_mem q ha)⟩
    have hh := congrArg (fun z : U => (z:G)) hfix
    change a*(u:G)*a⁻¹=(u:G) at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  obtain ⟨g,hg⟩ := hcG
  let w : U := MulAut.conjNormal g u
  have hw : (w:G) ∈ normalClosure (omegaOneCenterAmbient R : Set G) :=
    normalClosure_normal.conj_mem _ (subset_normalClosure huR) g
  obtain ⟨a,ha,hqa⟩ := hrA
  intro hA
  have hfix : MulAut.conjNormal a w=w := by
    apply Subtype.ext
    change a*(w:G)*a⁻¹=(w:G)
    rw [←hA ha (w:G) hw]
    group
  have hh := he a w
  rw [hfix,hqa] at hh
  have hwcoord : (e w).toAdd=BinaryPermutation.naturalRepresentation (Fin 7) cubic pairPoint := by
    rw [show w=MulAut.conjNormal g u from rfl,he,hg,heu]
  rw [hwcoord] at hh
  exact reflection_moves_cubic_pairPoint hh.symm

omit [Finite G] in
/-- Restriction keeps the selected preimage and its literal Thompson subgroup. -/
theorem selected_omega_movement (R U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (hUR : U ≤ R) (M : Subgroup (G ⧸ pCore 2 G))
    (q : G →* Sym) (hR : R.map q ≤ pairElementary)
    (hrJ : swap01 ∈ (elementaryAbelianMaxJ R).map q)
    (hcH : cubic ∈ (selectedGroup R M).map q)
    (e : U ≃* Multiplicative (BinaryPermutation.natural (Fin 7)))
    (he : ∀ (g : G) (v : U), (e (MulAut.conjNormal g v)).toAdd =
      BinaryPermutation.naturalRepresentation (Fin 7) (q g) (e v).toAdd) :
    ¬elementaryAbelianMaxJ (R.subgroupOf (selectedGroup R M)) ≤
      centralizer (normalClosure (omegaOneCenterAmbient
        (R.subgroupOf (selectedGroup R M)) : Set (selectedGroup R M)) : Set (selectedGroup R M)) := by
  let H := selectedGroup R M
  let U' := U.subgroupOf H
  let eU : U' ≃* U := subgroupOfEquivOfLe (hUR.trans (le_selectedGroup R M))
  let : IsElementaryAbelian 2 U' := IsElementaryAbelian.subgroupOf (hUR.trans (le_selectedGroup R M))
  have he' : ∀ (g : H) (v : U'), ((eU.trans e) (MulAut.conjNormal g v)).toAdd =
      BinaryPermutation.naturalRepresentation (Fin 7) ((q.comp H.subtype) g) ((eU.trans e) v).toAdd := by
    intro g v
    exact he g (eU v)
  have hR' : (R.subgroupOf H).map (q.comp H.subtype) ≤ pairElementary := by
    rw [←map_map,map_subgroupOf_eq_of_le (le_selectedGroup R M)]
    exact hR
  have hrJ' : swap01 ∈ (elementaryAbelianMaxJ (R.subgroupOf H)).map (q.comp H.subtype) := by
    rw [←map_map,←elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective,
      map_subgroupOf_eq_of_le (le_selectedGroup R M)]
    exact hrJ
  have hc' : cubic ∈ (q.comp H.subtype).range := by
    obtain ⟨x,hx,hxc⟩ := hcH
    exact ⟨⟨x,hx⟩,hxc⟩
  exact omega_span_moved U' (R.subgroupOf H) (elementaryAbelianMaxJ (R.subgroupOf H))
    (comap_mono hUR) (q.comp H.subtype) (eU.trans e) he' hR' hrJ' hc'

omit [Finite G] in
/-- An equivariant embedding of the natural module suffices; fixed summands
of the original module do not affect the actual omega-center vector. -/
theorem omega_span_moved_of_embedding (V R A : Subgroup G)
    [V.Normal] [IsElementaryAbelian 2 V] (hVR : V ≤ R) (q : G →* Sym)
    (f : Multiplicative (BinaryPermutation.natural (Fin 7)) →* V)
    (hf : Function.Injective f)
    (he : ∀ (g : G) (v : BinaryPermutation.natural (Fin 7)),
      f (Multiplicative.ofAdd (BinaryPermutation.naturalRepresentation (Fin 7) (q g) v)) =
        MulAut.conjNormal g (f (Multiplicative.ofAdd v)))
    (hR : R.map q ≤ pairElementary) (hrA : swap01 ∈ A.map q)
    (hcG : cubic ∈ q.range) :
    ¬A ≤ centralizer (normalClosure (omegaOneCenterAmbient R : Set G) : Set G) := by
  let u := f (Multiplicative.ofAdd pairPoint)
  have huR : (u:G) ∈ omegaOneCenterAmbient R := by
    apply (mem_omegaOneCenterAmbient_iff R (u:G)).mpr
    refine ⟨hVR u.property,elemPow_eq_one_of_isElementaryAbelian (u:G) u.property,?_⟩
    intro a ha
    have hfix : MulAut.conjNormal a u=u := by
      rw [←he]
      exact congrArg f (congrArg Multiplicative.ofAdd
        (pairPoint_fixed ⟨q a,hR (mem_map_of_mem q ha)⟩))
    have hh := congrArg (fun z : V => (z:G)) hfix
    change a*(u:G)*a⁻¹=(u:G) at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  obtain ⟨g,hg⟩ := hcG
  let w : V := MulAut.conjNormal g u
  have hw : (w:G) ∈ normalClosure (omegaOneCenterAmbient R : Set G) :=
    normalClosure_normal.conj_mem _ (subset_normalClosure huR) g
  have hwcoord : w=f (Multiplicative.ofAdd
      (BinaryPermutation.naturalRepresentation (Fin 7) cubic pairPoint)) := by
    change MulAut.conjNormal g (f (Multiplicative.ofAdd pairPoint))=_
    rw [←he,hg]
  obtain ⟨a,ha,hqa⟩ := hrA
  intro hA
  have hfix : MulAut.conjNormal a w=w := by
    apply Subtype.ext
    change a*(w:G)*a⁻¹=(w:G)
    rw [←hA ha (w:G) hw]
    group
  rw [hwcoord,←he,hqa] at hfix
  exact reflection_moves_cubic_pairPoint (congrArg Multiplicative.toAdd (hf hfix))

omit [Finite G] in
/-- The embedded natural module restricts to the actual cubic preimage. -/
theorem selected_omega_movement_of_embedding (R V : Subgroup G)
    [V.Normal] [IsElementaryAbelian 2 V] (hVR : V ≤ R)
    (M : Subgroup (G ⧸ pCore 2 G)) (q : G →* Sym)
    (hR : R.map q ≤ pairElementary)
    (hrJ : swap01 ∈ (elementaryAbelianMaxJ R).map q)
    (hcH : cubic ∈ (selectedGroup R M).map q)
    (f : Multiplicative (BinaryPermutation.natural (Fin 7)) →* V)
    (hf : Function.Injective f)
    (he : ∀ (g : G) (v : BinaryPermutation.natural (Fin 7)),
      f (Multiplicative.ofAdd (BinaryPermutation.naturalRepresentation (Fin 7) (q g) v)) =
        MulAut.conjNormal g (f (Multiplicative.ofAdd v))) :
    ¬elementaryAbelianMaxJ (R.subgroupOf (selectedGroup R M)) ≤
      centralizer (normalClosure (omegaOneCenterAmbient
        (R.subgroupOf (selectedGroup R M)) : Set (selectedGroup R M)) : Set (selectedGroup R M)) := by
  let H := selectedGroup R M
  let V' := V.subgroupOf H
  let eV : V' ≃* V := subgroupOfEquivOfLe (hVR.trans (le_selectedGroup R M))
  let : IsElementaryAbelian 2 V' := IsElementaryAbelian.subgroupOf (hVR.trans (le_selectedGroup R M))
  let f' := eV.symm.toMonoidHom.comp f
  have he' : ∀ (g : H) (v : BinaryPermutation.natural (Fin 7)),
      f' (Multiplicative.ofAdd (BinaryPermutation.naturalRepresentation (Fin 7) ((q.comp H.subtype) g) v)) =
        MulAut.conjNormal g (f' (Multiplicative.ofAdd v)) := by
    intro g v
    apply eV.injective
    exact he g v
  have hR' : (R.subgroupOf H).map (q.comp H.subtype) ≤ pairElementary := by
    rw [←map_map,map_subgroupOf_eq_of_le (le_selectedGroup R M)]
    exact hR
  have hrJ' : swap01 ∈ (elementaryAbelianMaxJ (R.subgroupOf H)).map (q.comp H.subtype) := by
    rw [←map_map,←elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective,
      map_subgroupOf_eq_of_le (le_selectedGroup R M)]
    exact hrJ
  have hc' : cubic ∈ (q.comp H.subtype).range := by
    obtain ⟨x,hx,hxc⟩ := hcH
    exact ⟨⟨x,hx⟩,hxc⟩
  exact omega_span_moved_of_embedding V' (R.subgroupOf H)
    (elementaryAbelianMaxJ (R.subgroupOf H)) (comap_mono hVR) (q.comp H.subtype) f'
    (eV.symm.injective.comp hf) he' hR' hrJ' hc'
end CFSG.Quasithin.ChapterC.RankOne.SevenSource.Natural
