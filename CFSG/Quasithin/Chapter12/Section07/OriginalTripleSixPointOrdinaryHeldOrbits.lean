module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixPointOrdinaryHeldImage
public import Theory.Representation.SL2FourNaturalOrbits.Model
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Original natural-four orbit counts in the proposed Held quotient

The nonzero fibers of the actual natural quotient have equal intersection
sizes with any conjugacy-invariant set. Their total is therefore a multiple
of15. The original central kernel and fixed four-group give the remaining
small fiber. All maps retain the same original point residual and U.

Source: Aschbacher--Smith12.7.4--5, printed pp.839--840.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped BigOperators IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource

private theorem card_predicate_preimage
    {X Y : Type*} [Group X] [Finite X] [Group Y] [Finite Y]
    (f : X →* Y) (hf : Function.Surjective f) (P : Y → Prop) :
    Nat.card {x : X // P (f x)} = Nat.card f.ker * Nat.card {y : Y // P y} := by
  classical
  let : Fintype {y : Y // P y} := Fintype.ofFinite _
  let m : {x : X // P (f x)} → {y : Y // P y} := fun x => ⟨f x,x.property⟩
  have he (y : {y : Y // P y}) : {x : {x : X // P (f x)} // m x = y} ≃
      f ⁻¹' {y.val} := {
    toFun x := ⟨x.val.val,congrArg Subtype.val x.property⟩
    invFun x := ⟨⟨x.val,by rw [show f x.val = y.val from x.property]; exact y.property⟩,
      Subtype.ext x.property⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  have hcard (y : {y : Y // P y}) :
      Nat.card {x : {x : X // P (f x)} // m x = y} = Nat.card f.ker :=
    Nat.card_congr ((he y).trans (MonoidHom.fiberEquivKerOfSurjective hf y.val))
  have hh := Nat.card_congr (Equiv.sigmaFiberEquiv m)
  rw [Nat.card_sigma] at hh
  simp only [hcard,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
    ←Nat.card_eq_fintype_card] at hh
  exact hh.symm.trans (Nat.mul_comm _ _)

private theorem nonzero_fiber_count
    {X Y : Type*} [Finite X] [Finite Y] [Zero Y]
    (f : X → Y) (P : X → Prop) (v : Y) (_hv : v ≠ 0)
    (hy : Nat.card {y : Y // y ≠ 0} = 15)
    (htrans : ∀ y : Y, y ≠ 0 →
      Nonempty ({x : X // P x ∧ f x = y} ≃ {x : X // P x ∧ f x = v})) :
    ∃ k, Nat.card {x : X // P x} =
      15*k + Nat.card {x : X // P x ∧ f x = 0} := by
  classical
  let : Fintype Y := Fintype.ofFinite Y
  let S := {x : X // P x}
  let m : S → Y := fun x => f x.val
  let k := Nat.card {x : X // P x ∧ f x = v}
  have he (y : Y) : {x : S // m x = y} ≃ {x : X // P x ∧ f x = y} := {
    toFun x := ⟨x.val.val,x.val.property,x.property⟩
    invFun x := ⟨⟨x.val,x.property.1⟩,x.property.2⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  have hc (y : Y) (hy : y ≠ 0) : Nat.card {x : S // m x = y} = k :=
    Nat.card_congr ((he y).trans (htrans y hy).some)
  have hh := Nat.card_congr (Equiv.sigmaFiberEquiv m)
  rw [Nat.card_sigma] at hh
  have hsum : (∑ y : Y, Nat.card {x : S // m x = y}) =
      Nat.card {x : X // P x ∧ f x = 0} + 15*k := by
    rw [←Finset.sum_filter_add_sum_filter_not (s := Finset.univ) (p := fun y => y = 0)]
    have hzero : (∑ y ∈ (Finset.univ.filter fun y : Y => y = 0),
        Nat.card {x : S // m x = y}) = Nat.card {x : X // P x ∧ f x = 0} := by
      rw [show (Finset.univ.filter fun y : Y => y = 0) = {0} by ext; simp]
      simpa only [Finset.sum_singleton] using Nat.card_congr (he 0)
    rw [hzero]
    congr 1
    rw [Finset.sum_congr rfl (fun y hy => hc y (Finset.mem_filter.mp hy).2)]
    rw [Finset.sum_const,nsmul_eq_mul]
    have hsize : (Finset.univ.filter fun y : Y => y ≠ 0).card = 15 := by
      simpa only [Nat.card_eq_fintype_card,Fintype.card_subtype] using hy
    rw [hsize]
    rfl
  exact ⟨k,hh.symm.trans (hsum.trans (Nat.add_comm _ _))⟩

private theorem natural_invariant_count
    {G Y : Type*} [Group G] [Finite G] [Group Y] [Finite Y]
    {A U V : Subgroup G} (σ : A →* SL2FourNatural.SL)
    (hσ : Function.Surjective σ)
    (c : BinaryConjugationSection A U V (SL2FourNatural.naturalRepresentation.comp σ))
    (q : U →* Y) (hq : Function.Surjective q) (hker : q.ker ≤ c.coordinates.ker)
    (hV : Nat.card V = 4) (P : Y → Prop) (hPone : ¬ P 1)
    (hP : ∀ (a : A) (u : U),
      P (q (U.normalizerMonoidHom (inclusion c.normalized a) u)) ↔ P (q u)) :
    ∃ k z, Nat.card q.ker * Nat.card {y : Y // P y} = 15*k + z ∧
      z + Nat.card q.ker ≤ 4 := by
  classical
  let f : U → SL2FourNatural.V := fun u => (c.coordinates u).toAdd
  let v : SL2FourNatural.V := ![1,0]
  have hv : v ≠ 0 := by intro hh; have := congrFun hh 0; norm_num [v] at this
  have hy : Nat.card {y : SL2FourNatural.V // y ≠ 0} = 15 := by
    rw [Nat.card_eq_fintype_card,Fintype.card_subtype_compl]
    simp only [Fintype.card_unique,SL2FourNatural.card_vector]
  have htrans (y : SL2FourNatural.V) (hy : y ≠ 0) :
      Nonempty ({u : U // P (q u) ∧ f u = y} ≃ {u : U // P (q u) ∧ f u = v}) := by
    obtain ⟨s,hs⟩ := SL2FourNatural.transitive_nonzero y v hy hv
    obtain ⟨a,rfl⟩ := hσ s
    let e : MulAut U := U.normalizerMonoidHom (inclusion c.normalized a)
    have he (u : U) : f (e u) = SL2FourNatural.action (σ a) (f u) := c.equivariant a u
    refine ⟨Equiv.subtypeEquiv e.toEquiv (fun u => ?_)⟩
    refine and_congr (hP a u).symm ?_
    change f u = y ↔ f (e u) = v
    rw [he,←hs]
    exact (SL2FourNatural.action (σ a)).injective.eq_iff.symm
  obtain ⟨k,hk⟩ := nonzero_fiber_count f (fun u => P (q u)) v hv hy htrans
  let Z := {u : U // P (q u) ∧ f u = 0}
  have hZ : Nat.card Z + Nat.card q.ker ≤ 4 := by
    let m : Z ⊕ q.ker → c.coordinates.ker := fun x => match x with
      | Sum.inl z => ⟨z.val,z.property.2⟩
      | Sum.inr u => ⟨u.val,hker u.property⟩
    have hm : Function.Injective m := by
      intro x y hxy
      have he := congrArg Subtype.val hxy
      cases x with
      | inl x =>
        cases y with
        | inl y => exact congrArg Sum.inl (Subtype.ext he)
        | inr y =>
          have hp := x.property.1
          rw [show x.val = y.val from he,show q y.val = 1 from y.property] at hp
          exact (hPone hp).elim
      | inr x =>
        cases y with
        | inl y =>
          have hp := y.property.1
          rw [←show x.val = y.val from he,show q x.val = 1 from x.property] at hp
          exact (hPone hp).elim
        | inr y => exact congrArg Sum.inr (Subtype.ext he)
    have hh := Nat.card_le_card_of_injective m hm
    rw [Nat.card_sum,c.kernel_eq,
      Nat.card_congr (subgroupOfEquivOfLe c.kernel_le).toEquiv,hV] at hh
    exact hh
  refine ⟨k,Nat.card Z,?_,hZ⟩
  rw [←card_predicate_preimage q hq P]
  exact hk

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- The literal Held image of the original module has a restricted number
of involutions in the native `a` class. This is forced by the actual natural
quotient and the full central kernel, before any Held subgroup placement. -/
theorem original_tripleSix_ordinary_held_involution_count
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K)
    (J : Subgroup (centralizer ({(t : G)} : Set G)))
    (hJ : IsComponent (centralizer ({(t : G)} : Set G)) J)
    (e : J ⧸ center J ≃* Held.He) :
    let H := centralizer ({(t : G)} : Set G)
    let j := H.subtype.comp J.subtype
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (center J))
    let E := (U.comap j).map q
    let n := Nat.card {x : E // IsConj Held.a (x : Held.He)}
    (Nat.card E = 16 → 15 ∣ n) ∧ (Nat.card E = 32 → n ≠ 6 ∧ n ≠ 10) := by
  let H := centralizer ({(t : G)} : Set G)
  let Lt := (pResidual 2 (K ⊓ H : Subgroup G)).map (K ⊓ H).subtype
  let j := H.subtype.comp J.subtype
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center J))
  let W := U.comap j
  let E := W.map q
  have hj : Function.Injective j := H.subtype_injective.comp J.subtype_injective
  have hjr : j.range = J.map H.subtype := by rw [MonoidHom.range_comp,range_subtype]
  have hc := original_tripleSix_pushingUp_at h structural D a t ht heven
  have hLH : Lt ≤ H := (map_subtype_le _).trans inf_le_right
  have hLJ : Lt ≤ J.map H.subtype := by
    have hh := map_mono (f := H.subtype) (hc.ordinary_component_contains_original J hJ)
    rwa [map_subgroupOf_eq_of_le hLH] at hh
  have hUL := (tripleSixPointCentralizerResidual_commutator D a t ht heven).2
  have hWmap : W.map j = U := map_comap_eq_self ((hUL.trans hLJ).trans_eq hjr.symm)
  let w : W ≃* U := (W.equivMapOfInjective j hj).trans (MulEquiv.subgroupCongr hWmap)
  let ι : U →* J := W.subtype.comp w.symm.toMonoidHom
  have hι (u : U) : j (ι u) = (u : G) := congrArg Subtype.val (w.apply_symm_apply u)
  let qU : U →* E := (q.subgroupMap W).comp w.symm.toMonoidHom
  have hqU : Function.Surjective qU := (q.subgroupMap_surjective W).comp w.symm.surjective
  have hqUcoe (u : U) : (qU u : Held.He) = q (ι u) := rfl
  obtain ⟨σ,⟨c⟩⟩ := tripleSixPointResidual_quotient_natural D a t ht heven
  let σ₀ : Lt →* SL2FourNatural.SL := σ.toMonoidHom.comp (QuotientGroup.mk' _)
  have hσ₀ : Function.Surjective σ₀ := σ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : qU.ker ≤ c.coordinates.ker := by
    intro u hu
    apply (c.coordinates_eq_one_iff u).mpr
    rw [←tripleSixPoint_residual_fixed D a t ht heven]
    refine ⟨u.property,?_⟩
    have hcentral : ι u ∈ center J := by
      have hq : q (ι u) = 1 := congrArg Subtype.val hu
      apply (QuotientGroup.eq_one_iff _).mp
      exact e.injective (hq.trans e.map_one.symm)
    intro l hl
    obtain ⟨lJ,hlJ⟩ := show l ∈ j.range from hjr.symm ▸ hLJ hl
    rw [←hlJ,←hι u]
    exact congrArg j (mem_center_iff.mp hcentral lJ)
  let P : E → Prop := fun x => IsConj Held.a (x : Held.He)
  have hPone : ¬ P 1 := by exact fun hp => Held.a_ne_one (isConj_one_left.mp hp)
  have hP (l : Lt) (u : U) :
      P (qU (U.normalizerMonoidHom (inclusion c.normalized l) u)) ↔ P (qU u) := by
    let d : MulAut U := U.normalizerMonoidHom (inclusion c.normalized l)
    obtain ⟨lJ,hlJ⟩ := show (l : G) ∈ j.range from hjr.symm ▸ hLJ l.property
    have heq : ι (d u) = lJ * ι u * lJ⁻¹ := by
      apply hj
      rw [hι,map_mul,map_mul,map_inv,hlJ,hι]
      rfl
    have hconj : IsConj (qU u : Held.He) (qU (d u) : Held.He) := by
      apply isConj_iff.mpr
      refine ⟨q lJ,?_⟩
      rw [hqUcoe,hqUcoe,heq,map_mul,map_mul,map_inv]
    exact ⟨fun hp => hp.trans hconj.symm,fun hp => hp.trans hconj⟩
  obtain ⟨k,z,hcount,hsmall⟩ := natural_invariant_count σ₀ hσ₀ c qU hqU hker
    (tripleSixPoint_properties D a t ht).2.2.1 P hPone hP
  have hUc : Nat.card U = 64 :=
    (Nat.card_congr (tripleSixPointCoordinates D a).toEquiv).trans Atlas.Codes.hexacode_card
  have hproduct : Nat.card E * Nat.card qU.ker = 64 := by
    rw [←hUc,card_eq_card_quotient_mul_card_subgroup qU.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective qU hqU).toEquiv]
  constructor
  · intro hE
    have hkc : Nat.card qU.ker = 4 := by rw [hE] at hproduct; omega
    have hz : z = 0 := by omega
    rw [hkc,hz,add_zero] at hcount
    have hd : 15 ∣ 4 * Nat.card {x : E // P x} := ⟨k,hcount⟩
    exact (show Nat.Coprime 15 4 from by decide).dvd_mul_left.mp hd
  · intro hE
    have hkc : Nat.card qU.ker = 2 := by rw [hE] at hproduct; omega
    rw [hkc] at hcount hsmall
    constructor <;> intro he <;> change Nat.card {x : E // P x} = _ at he <;>
      rw [he] at hcount <;> omega

end CFSG.Quasithin.Chapter12.Section07
