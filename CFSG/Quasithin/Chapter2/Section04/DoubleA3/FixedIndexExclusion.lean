module
public import CFSG.Quasithin.Chapter2.Section05.Overcomponents.A6QuotientSource
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.FieldFixedResidual.Index
public import Theory.SpecificGroups.BinaryLinear.SixSubgroupCentralizers
public import Theory.SpecificGroups.BinaryLinear.SixSylowActors.Five.FixedGeometry

/-!
# The small Sylow fixed-index screen in the paired cubic branch

The intrinsic fixed-A₆ census has four possible quotient models. In the
PSL₅(2) row, the original fixed A₆ has trivial centralizer in the natural
binary model, so the involution is outer and its fixed group is S₆. Its
fixed subgroup therefore has index at least 64 in every Sylow two-subgroup.
The marked field involution of Sp₄(4) has index at least 16. The marked HS
involution has fixed group of order 2880 and Sylow order 512, giving index
at least eight. Thus an index bound of four leaves precisely A₈.

The final consumer retains the literal fixed A₆ subgroup, the actual actor,
and all marks from the full quotient census. The Sylow subgroup need not
be invariant under the actor. No ambient exclusion from Chapter E is used.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the component
inspection in 2.4.36, printed p.549; the intrinsic fixed-A₆ census of 2.5.19,
printed pp.560–563, and E.6.23, printed p.254.
-/

public section
open Subgroup Theory.GroupTheory BinaryLinear.OuterCyclic
namespace CFSG.Quasithin.Chapter2.DoubleA3
open Section05.Overcomponents
open Chapter16.OtherPreliminaries.JankoTwoHigmanSims

private theorem fixed_intersection_card_dvd {D : Type*} [Group D] [Finite D]
    (a : MulAut D) (P : Subgroup D) :
    Nat.card (a.fixedSubgroup.subgroupOf P) ∣
      Nat.gcd (Nat.card P) (Nat.card a.fixedSubgroup) := by
  let f : a.fixedSubgroup.subgroupOf P →* a.fixedSubgroup :=
    { toFun x := ⟨x.val.val, x.property⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
  have hf : Function.Injective f := fun _ _ h => Subtype.ext (Subtype.ext
    (congrArg (fun z : a.fixedSubgroup => (z : D)) h))
  exact Nat.dvd_gcd (a.fixedSubgroup.subgroupOf P).card_subgroup_dvd_card
    (card_dvd_of_injective f hf)

private theorem fixed_index_congr {D E : Type*} [Group D] [Group E]
    (e : D ≃* E) (a : MulAut D) (P : Subgroup D) :
    ((MulAut.congr e a).fixedSubgroup.subgroupOf (P.map e.toMonoidHom)).index =
      (a.fixedSubgroup.subgroupOf P).index := by
  have hf : a.fixedSubgroup.map e.toMonoidHom = (MulAut.congr e a).fixedSubgroup := by
    ext x
    rw [mem_map_equiv, MulAut.mem_fixedSubgroup, MulAut.mem_fixedSubgroup]
    change a (e.symm x) = e.symm x ↔ e (a (e.symm x)) = x
    constructor
    · intro h
      rw [h, e.apply_symm_apply]
    · intro h
      apply e.injective
      rwa [e.apply_symm_apply]
  change (MulAut.congr e a).fixedSubgroup.relIndex
    (P.map e.toMonoidHom) = a.fixedSubgroup.relIndex P
  rw [← hf]
  exact relIndex_map_map_of_injective _ _ e.injective

private theorem linear_five_fixed_card {D : Type*} [Group D] [Finite D]
    (hm : ClassicalGroup.IsPSL D 5 2) (a : MulAut D) (ha : orderOf a = 2)
    (B : Subgroup a.fixedSubgroup) (eB : B ≃* alternatingGroup (Fin 6)) :
    Nat.card D = 9999360 ∧ Nat.card a.fixedSubgroup = 720 := by
  obtain ⟨F, _, _, hF, ⟨eF⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  have hcard : Fintype.card F = Fintype.card (ZMod 2) := by
    simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hF
  let e : D ≃* LinearGroup 5 :=
    (eF.trans (Atlas.fieldEquivPSL 5 (FiniteField.ringEquivOfCardEq hcard))).trans
      (projectiveEquivLinear (by decide : 0 < 5))
  let τ := MulAut.congr e a
  let j := MulAut.fixedSubgroupCongr e a
  let f : B →* LinearGroup 5 := e.toMonoidHom.comp (a.fixedSubgroup.subtype.comp B.subtype)
  have hf : Function.Injective f := e.injective.comp
    (a.fixedSubgroup.subtype_injective.comp B.subtype_injective)
  let U := f.range
  let eU : U ≃* alternatingGroup (Fin 6) := (MonoidHom.ofInjective hf).symm.trans eB
  have hU : Nat.card U = 360 := by
    rw [Nat.card_congr eU.toEquiv, nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hz : center U = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    have he := (centerCongr eU ⟨x, hx⟩).property
    change eU x ∈ center (alternatingGroup (Fin 6)) at he
    rw [alternatingGroup.center_eq_bot (by simp), mem_bot] at he
    exact mem_bot.mpr (eU.map_eq_one_iff.mp he)
  have hc := BinaryLinear.SixSubgroupCentralizers.centralizer_eq_bot (Or.inr rfl) U hU hz
  have ht : orderOf τ = 2 := ((MulAut.congr e).orderOf_eq a).trans ha
  have hout : τ ∉ MulAut.innerSubgroup (LinearGroup 5) := by
    rintro ⟨g, hg⟩
    have hgc : g ∈ centralizer (U : Set (LinearGroup 5)) := by
      rintro _ ⟨x, rfl⟩
      have hfix : τ (f x) = f x := by
        change e (a (e.symm (e (x.val.val : D)))) = e (x.val.val : D)
        rw [e.symm_apply_apply, (MulAut.mem_fixedSubgroup _ _).mp x.val.property]
      rw [← hg] at hfix
      exact (mul_inv_eq_iff_eq_mul.mp hfix).symm
    have hg1 : g = 1 := mem_bot.mp (hc ▸ hgc)
    have ht1 : τ = 1 := by rw [← hg, hg1, map_one]
    rw [ht1, orderOf_one] at ht
    norm_num at ht
  obtain ⟨m⟩ := BinaryLinear.SixSylowActors.Five.exists_fixedModel τ
    (by simpa only [ht] using pow_orderOf_eq_one τ) hout
  constructor
  · calc
      Nat.card D = Nat.card (LinearGroup 5) := Nat.card_congr e.toEquiv
      _ = Nat.card (Matrix.GeneralLinearGroup (Fin 5) (ZMod 2)) :=
        (Nat.card_congr (matrixEquivLinear 5).toEquiv).symm
      _ = ∏ i : Fin 5, (Fintype.card (ZMod 2) ^ 5 - Fintype.card (ZMod 2) ^ i.val) :=
        Matrix.card_GL_field (𝔽 := ZMod 2) 5
      _ = 9999360 := by decide
  · rw [Nat.card_congr j.toEquiv, Nat.card_congr m.equiv.toEquiv,
      Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    norm_num [Nat.factorial]

/-- A fixed A₆ forces the degree-five involution to be outer, whose full fixed
subgroup is S₆. Thus the fixed subgroup has index at least 64 in every Sylow two-subgroup. -/
theorem linear_five_fixed_index {D : Type*} [Group D] [Finite D]
    (hm : ClassicalGroup.IsPSL D 5 2) (a : MulAut D) (ha : orderOf a = 2)
    (B : Subgroup a.fixedSubgroup) (eB : B ≃* alternatingGroup (Fin 6))
    (P : Sylow 2 D) : 64 ≤ (a.fixedSubgroup.subgroupOf P).index := by
  obtain ⟨hD, hf⟩ := linear_five_fixed_card hm a ha B eB
  have hP : Nat.card P = 1024 := by
    rw [P.card_eq_multiplicity, hD,
      show 9999360 = 2 ^ 10 * 9765 by decide,
      Nat.factorization_mul (by decide) (by decide), Finsupp.add_apply,
      Nat.prime_two.factorization_pow, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 9765)]
    rfl
  have hd := fixed_intersection_card_dvd a (P : Subgroup D)
  rw [hP, hf] at hd
  norm_num at hd
  have hb := Nat.le_of_dvd (by decide : 0 < 16) hd
  have he := (a.fixedSubgroup.subgroupOf P).card_mul_index
  rw [hP] at he
  nlinarith

/-- The marked field involution on Sp₄(4) has Sylow fixed index at least 16. -/
theorem symplectic_four_fixed_index {D : Type*} [Group D] [Finite D]
    (a : MulAut D) {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 4) (e : D ≃* Theory.SpecificGroups.SymplecticFour.Sp F)
    (he : MulAut.congr e a =
      Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.FieldFixedResidual.representative 1)
    (P : Sylow 2 D) : 16 ≤ (a.fixedSubgroup.subgroupOf P).index := by
  have hh : 16 ≤
      ((Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.FieldFixedResidual.representative
        (F := F) 1).fixedSubgroup.subgroupOf ((P : Subgroup D).map e.toMonoidHom)).index :=
    Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.FieldFixedResidual.fixed_index_lower_bound
      (m := 1) (by decide) (by norm_num; exact hF)
      (P.mapSurjective (f := e.toMonoidHom) e.surjective)
  rw [← he, fixed_index_congr] at hh
  exact hh

/-- The marked inner HS row has fixed order 2880 and Sylow order 512. -/
theorem hs_fixed_index {D : Type*} [Group D] [Finite D]
    (a : MulAut D) (e : D ≃* _root_.Sporadic.LeechRelated.HS.Carrier)
    (he : MulAut.congr e a = MulAut.conj HSInner.ClassCoverage.t)
    (P : Sylow 2 D) : 8 ≤ (a.fixedSubgroup.subgroupOf P).index := by
  have hD : Nat.card D = 44352000 :=
    (Nat.card_congr e.toEquiv).trans _root_.Sporadic.LeechRelated.HS.NormalizerIndex.card_carrier
  have hf : Nat.card a.fixedSubgroup = 2880 := by
    rw [Nat.card_congr (MulAut.fixedSubgroupCongr e a).toEquiv, he, MulAut.fixedSubgroup_conj]
    obtain ⟨f⟩ := HSInner.ClassCoverage.product_centralizer_equiv
    exact (Nat.card_congr f.toEquiv).trans HSInner.ClassCoverage.product_card
  have hP : Nat.card P = 512 := by
    rw [P.card_eq_multiplicity, hD,
      show 44352000 = 2 ^ 9 * 86625 by decide,
      Nat.factorization_mul (by decide) (by decide), Finsupp.add_apply,
      Nat.prime_two.factorization_pow, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 86625)]
    rfl
  have hd := fixed_intersection_card_dvd a (P : Subgroup D)
  rw [hP, hf] at hd
  norm_num at hd
  have hb := Nat.le_of_dvd (by decide : 0 < 64) hd
  have hi := (a.fixedSubgroup.subgroupOf P).card_mul_index
  rw [hP] at hi
  nlinarith

/-- The guarded intrinsic A₆ census leaves only A₈ under the actual Sylow
fixed-index bound. The original fixed A₆ is retained in the binary linear row. -/
theorem alternating_eight_of_fixed_index {D : Type*} [Group D] [Finite D]
    (a : MulAut D) (ha : orderOf a = 2) (hm : A6FixedQuotientModels D a)
    (B : Subgroup a.fixedSubgroup) (eB : B ≃* alternatingGroup (Fin 6))
    (P : Sylow 2 D) (hi : (a.fixedSubgroup.subgroupOf P).index ≤ 4) :
    Nonempty (D ≃* alternatingGroup (Fin 8)) := by
  rcases hm with h8 | h5 | hsp | hhs
  · exact h8
  · have hb := linear_five_fixed_index h5 a ha B eB P
    omega
  · obtain ⟨F, _, _, _, hF, e, he⟩ := hsp
    have hb := symplectic_four_fixed_index a hF e he P
    omega
  · obtain ⟨e, he⟩ := hhs
    have hb := hs_fixed_index a e he P
    omega

end CFSG.Quasithin.Chapter2.DoubleA3
