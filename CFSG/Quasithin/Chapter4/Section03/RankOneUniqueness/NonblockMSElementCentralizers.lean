module
public import Theory.Representation.SL3.DualLiftCentralizers
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockMSSpecialCore

/-!
# Element centralizers in the original nonblock MS core

The common natural/dual marking gives |Z(Q)| = 2^(3n) and |Q| = 2^(9n).
For a noncentral element of the first elementary dual lift, the second
coordinate of any commuting element is a scalar multiple of its coordinate.
Consequently its centralizer in Q has order 2^(7n), index 2^n over the
first lift, and index 2^(2n) in Q. All maps are the original MS quotient
and subgroup inclusions; Q = O₂(KS) is not an input.

This supplies the element-centralizer calculation in the C.1.35 rank
argument. The remaining larger-core argument, construction of MSData,
component geometry and terminal exclusion remain with
qt-d-1222-rankone-uniqueness-nonblock.
Source: Aschbacher--Smith, C.1.35(2)--(3), printed pp.137--139,
applied in original 4.3.11, printed p.617.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open Representation.SL3ParabolicNatural
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] {T : Sylow 2 G} {L : Subgroup G}
  {c : SourceConfiguration T L} {n : ℕ}

private theorem center_subgroupOf : (U c).subgroupOf (Q c) = center (Q c) :=
  (center (Q c)).comap_map_eq_self_of_injective (Q c).subtype_injective


/-- The original natural center has order 2^(3n). -/
theorem MSData.center_card (d : MSData c n) : Nat.card (center (Q c)) = 2^(3*n) := by
  have hm := d.natural
  rw [HasSectionModel,bot_subgroupOf] at hm
  obtain ⟨_,_,_,hn,e,_⟩ := hm
  let := hn
  rw [←center_subgroupOf, Nat.card_congr (subgroupOfEquivOfLe d.doubleDual.1).toEquiv,
    Nat.card_congr (QuotientGroup.quotientBot.symm.trans e).toEquiv]
  change Nat.card (Fin 3 → d.field.Carrier) = _
  rw [Nat.card_fun,Nat.card_fin,d.field.card_eq,d.degree_eq,←pow_mul]
  congr 1
  omega


/-- The full special core has the three original natural/dual factors. -/
theorem MSData.core_card (d : MSData c n) : Nat.card (Q c) = 2^(9*n) := by
  obtain ⟨p,hp,hk,_,_⟩ := d.exists_elementary_dual_lifts
  have hh := p.ker.index_mul_card
  rw [index_ker,MonoidHom.range_eq_top.mpr hp,Nat.card_congr (topEquiv).toEquiv,
    hk,center_subgroupOf,d.center_card] at hh
  change Nat.card (Module.Dual d.field.Carrier (Fin 3 → d.field.Carrier) ×
    Module.Dual d.field.Carrier (Fin 3 → d.field.Carrier)) * 2^(3*n) = Nat.card (Q c) at hh
  rw [Nat.card_prod,Module.natCard_eq_pow_finrank (K := d.field.Carrier),
    Subspace.dual_finrank_eq,Module.finrank_fin_fun,d.field.card_eq,d.degree_eq,
    ←pow_mul,←pow_add,←pow_add] at hh
  convert hh.symm using 1
  congr 1
  omega


private theorem centralizer_map (w : Q c) :
    (Subgroup.centralizer ({w} : Set (Q c))).map (Q c).subtype =
      Q c ⊓ Subgroup.centralizer ({(w : G)} : Set G) := by
  ext z
  constructor
  · rintro ⟨x,hx,rfl⟩
    refine ⟨x.property,?_⟩
    intro a ha
    have he : a = (w : G) := Set.mem_singleton_iff.mp ha
    subst a
    exact congrArg Subtype.val (hx w (Set.mem_singleton w))
  · rintro ⟨hz,hzw⟩
    refine ⟨⟨z,hz⟩,?_,rfl⟩
    intro a ha
    have he : a = w := Set.mem_singleton_iff.mp ha
    subst a
    exact Subtype.ext (hzw w (Set.mem_singleton (w : G)))


/-- The literal MS quotient gives the element-centralizer part of C.1.35(2).
For each noncentral element of the first elementary lift, the other
coordinate of a commuting element is a scalar multiple of its coordinate.
Its full centralizer has order 2^(7n), and index 2^n over that lift. -/
theorem MSData.exists_element_centralizers (d : MSData c n) :
    ∃ p : Q c →* Multiplicative
        (Module.Dual d.field.Carrier (Fin 3 → d.field.Carrier) ×
          Module.Dual d.field.Carrier (Fin 3 → d.field.Carrier)),
      Function.Surjective p ∧ p.ker = (U c).subgroupOf (Q c) ∧
      (∀ a b : d.field.Carrier,
        IsElementaryAbelian 2 (dualLift d p a b) ∧
        U c ≤ dualLift d p a b ∧ dualLift d p a b ≤ Q c ∧
        K c ≤ normalizer (dualLift d p a b : Set G) ∧
        (a ≠ 0 ∨ b ≠ 0 → Nat.card (dualLift d p a b) = 2^(6*n))) ∧
      ∀ w : Q c, (w : G) ∈ dualLift d p 1 0 → (w : G) ∉ U c →
        (∀ z : Q c, Commute (w : G) (z : G) ↔
          ∃ a : d.field.Carrier, (p z).toAdd.2 = a • (p w).toAdd.1) ∧
        Nat.card (Q c ⊓ Subgroup.centralizer ({(w : G)} : Set G) : Subgroup G) = 2^(7*n) ∧
        (dualLift d p 1 0).relIndex (Q c ⊓ Subgroup.centralizer ({(w : G)} : Set G)) = 2^n ∧
        (Q c ⊓ Subgroup.centralizer ({(w : G)} : Set G)).relIndex (Q c) = 2^(2*n) := by
  obtain ⟨p,hp,hk,he,hl⟩ := d.exists_elementary_dual_lifts
  refine ⟨p,hp,hk,hl,?_⟩
  let := conjMulDistribMulActionOfLeNormalizer (K c) (Q c) d.doubleDual.2.1
  have hker : p.ker = center (Q c) := hk.trans center_subgroupOf
  have hel (a b : d.field.Carrier) :
      IsElementaryAbelian 2 ((dualDiagonal a b).range.comap p) := by
    let A := (dualDiagonal a b).range.comap p
    let : IsElementaryAbelian 2 (A.map (Q c).subtype) := (hl a b).1
    let e := A.equivMapOfInjective (Q c).subtype (Q c).subtype_injective
    exact IsElementaryAbelian.of_injective e.toMonoidHom e.injective
  have hact (k : K c) (q : Q c) : (p (k • q)).toAdd =
      ((Representation.specialLinearNatural 3).dual.prod
        (Representation.specialLinearNatural 3).dual) (linearThreeActor d.model k) (p q).toAdd :=
    he k q (k • q) rfl
  have hs := d.model.surjective.comp (QuotientGroup.mk'_surjective _)
  intro w hw hwu
  have hwa : p w ∈ (dualDiagonal (1:d.field.Carrier) 0).range :=
    (mem_map_iff_mem (Q c).subtype_injective).mp hw
  obtain ⟨f,hf⟩ := hwa
  have hwf : (p w).toAdd = (f.toAdd,0) := by
    have hh := (congrArg Multiplicative.toAdd hf).symm
    change (p w).toAdd = (1 • f.toAdd,0 • f.toAdd) at hh
    simpa only [one_smul,zero_smul] using hh
  have hf0 : f.toAdd ≠ 0 := by
    intro h0
    have hh : p w = 1 := by
      apply Multiplicative.toAdd.injective
      rw [hwf,h0]
      rfl
    have hwk : w ∈ p.ker := hh
    rw [hk] at hwk
    exact hwu hwk
  have hcomm (z : Q c) : Commute (w : G) (z : G) ↔
      ∃ a : d.field.Carrier, (p z).toAdd.2 = a • (p w).toAdd.1 := by
    have hh := dual_first_axis_centralizer_iff (linearThreeActor d.model) hs p hp hker
      hact hel w z f.toAdd hf0 hwf
    rw [hwf]
    exact (show Commute (w : G) (z : G) ↔ Commute w z from
      ⟨fun h => Subtype.ext h.eq,fun h => congrArg Subtype.val h.eq⟩).trans hh
  have hcard : Nat.card (Q c ⊓ Subgroup.centralizer ({(w : G)} : Set G) : Subgroup G) = 2^(7*n) := by
    rw [←centralizer_map w,
      ←Nat.card_congr ((Subgroup.centralizer ({w} : Set (Q c))).equivMapOfInjective
        (Q c).subtype (Q c).subtype_injective).toEquiv,
      dual_first_axis_centralizer_card (linearThreeActor d.model) hs p hp hker
        hact hel w f.toAdd hf0 hwf,d.center_card,d.field.card_eq,d.degree_eq,←pow_mul,←pow_add]
    congr 1
    omega
  refine ⟨hcomm,hcard,?_,?_⟩
  ·
    have hle : dualLift d p 1 0 ≤ Q c ⊓ Subgroup.centralizer ({(w : G)} : Set G) := by
      intro z hz
      have hzQ : z ∈ Q c := (hl 1 0).2.2.1 hz
      refine ⟨hzQ,?_⟩
      intro a ha
      have heq : a = (w : G) := Set.mem_singleton_iff.mp ha
      subst a
      let := (hl 1 0).1
      exact congrArg Subtype.val (mul_comm' (⟨w,hw⟩ : dualLift d p 1 0) ⟨z,hz⟩)
    have hh := ((dualLift d p 1 0).subgroupOf
      (Q c ⊓ Subgroup.centralizer ({(w : G)} : Set G))).index_mul_card
    rw [Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv,
      (hl 1 0).2.2.2.2 (Or.inl one_ne_zero),hcard] at hh
    change (dualLift d p 1 0).relIndex _ * 2^(6*n) = 2^(7*n) at hh
    apply Nat.eq_of_mul_eq_mul_right (show 0 < 2^(6*n) from by positivity)
    rw [hh,←pow_add]
    congr 1
    omega
  · have hh := ((Q c ⊓ Subgroup.centralizer ({(w : G)} : Set G)).subgroupOf (Q c)).index_mul_card
    rw [Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv,hcard,d.core_card] at hh
    change (Q c ⊓ Subgroup.centralizer ({(w : G)} : Set G)).relIndex (Q c) * 2^(7*n) = 2^(9*n) at hh
    apply Nat.eq_of_mul_eq_mul_right (show 0 < 2^(7*n) from by positivity)
    rw [hh,←pow_add]
    congr 1
    omega


end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
end
