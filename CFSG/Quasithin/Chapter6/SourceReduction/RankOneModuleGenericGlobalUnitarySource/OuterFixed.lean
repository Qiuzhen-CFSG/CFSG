module
public import Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourOuterFixed
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.NormalizerGrowth

/-!
# The fixed core of every original outer unitary involution

Transport conjugation on the literal quotient L/O₂(L) and on O₂(L)
together. The proved field kernel makes every involution of T outside
L an outer quotient actor. Its actual core fixed subgroup has order q³.
Since a nontrivial inner two-group fixes at most q² core elements, the
inner Sylow centralizer of that fixed subgroup lies in O₂(L).
Consequently the center–derived subgroup of the FULL C_T(u) lies in
O₂(L) and is elementary abelian, including with additional field actors.

Source: Aschbacher–Smith F.4.29(7),37, printed pp.289,293. Ordinary and
degree-two comparisons, both orientations and q=4 remain included.
No dimension or long-root intersection for the full center is assumed.
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels.UnitaryFour UnitaryCompletion
open Representation.OrthogonalFourMinus.FiniteModel
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H A C : Subgroup G} {n : ℕ}
variable (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (sourceS L H) m hm)
include d h hH hp hm hc

/-- Every actual outer involution fixes exactly q³ elements of the original core. -/
theorem Preparation.unitaryFour_outer_core_fixed_card_eq
    (u : T) (hu : orderOf u=2) (ho : u.val ∉ L) :
    Nat.card (L.pCoreIn 2 ⊓ centralizer ({u.val} : Set G) : Subgroup G) = (2^m)^3 := by
  let : NeZero m := ⟨by omega⟩
  obtain ⟨e,f,hf⟩ := d.unitary_core_hermitian_model h hH hp m hm hc
  let Q := L.pCoreIn 2
  let a : normalizer (L : Set G) := ⟨u.val,h.sylow_normalizes u.property⟩
  let c := L.normalizerMonoidHom a
  have hN : normalizer (L : Set G) ≤ normalizer (Q : Set G) :=
    normalizer_le_normalizer_characteristic_image L (pCore 2 L)
  let b := Q.normalizerMonoidHom (inclusion hN a)
  let k := f.symm.trans (b.trans f)
  let E : Space m ≃+ Space m :=
    { toFun x := (k (Multiplicative.ofAdd x)).toAdd
      invFun x := (k.symm (Multiplicative.ofAdd x)).toAdd
      left_inv x := congrArg Multiplicative.toAdd (k.symm_apply_apply (Multiplicative.ofAdd x))
      right_inv x := congrArg Multiplicative.toAdd (k.apply_symm_apply (Multiplicative.ofAdd x))
      map_add' x y := congrArg Multiplicative.toAdd (k.map_mul (Multiplicative.ofAdd x) (Multiplicative.ofAdd y)) }
  let φ := (MulAut.congr e).toMonoidHom.comp
    ((quotientAut (pCore 2 L)).comp L.normalizerMonoidHom)
  let α := φ a
  have ha2 : a^2=1 := Subtype.ext (by
    have hh := congrArg (fun t : T => t.val) (pow_orderOf_eq_one u)
    rwa [hu] at hh)
  have hα : α^2=1 := by change (φ a)^2=1; rw [←map_pow,ha2,map_one]
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  let coord : Space m → G := fun x => (f.symm (Multiplicative.ofAdd x)).val
  have hcoord : Function.Injective coord :=
    Q.subtype_injective.comp (f.symm.injective.comp Multiplicative.ofAdd.injective)
  have hcoordf (x : Q) : coord (f x).toAdd=x.val :=
    congrArg Subtype.val (f.symm_apply_apply x)
  have hcoordE (x : Space m) : coord (E x)=u.val*coord x*u.val⁻¹ := by
    change (f.symm (f (b (f.symm (Multiplicative.ofAdd x))))).val = _
    rw [f.symm_apply_apply]
    exact normalizerMonoidHom_apply_apply_coe _ _ _
  have hcoordAct (l : L) (x : Space m) :
      coord (action m (q l) x)=l.val*coord x*l.val⁻¹ := by
    have hh := hf l (f.symm (Multiplicative.ofAdd x))
    rw [f.apply_symm_apply] at hh
    exact hh
  have hαq (l : L) : α (q l)=q (c l) := by
    change e ((quotientAut (pCore 2 L) c)
      (e.symm (e (QuotientGroup.mk' (pCore 2 L) l)))) = _
    rw [e.symm_apply_apply,quotientAut_apply_mk]
    rfl
  have hinter (g : Matrix.SpecialLinearGroup (Fin 2) (Field m)) (x : Space m) :
      E (action m g x)=action m (α g) (E x) := by
    obtain ⟨l,rfl⟩ := e.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 L)) g
    change E (action m (q l) x)=action m (α (q l)) (E x)
    apply hcoord
    rw [hcoordE,hcoordAct,hαq,hcoordAct,hcoordE]
    have hcval : (c l).val=u.val*l.val*u.val⁻¹ :=
      normalizerMonoidHom_apply_apply_coe _ _ _
    rw [hcval]
    group
  have houter : ¬ ∃ g, α=MulAut.conj g := by
    rintro ⟨g,hg⟩
    apply ho
    let e' := e.trans (Theory.PSL2.sl2QuotientEquiv (Field m))
    have hker := d.unitaryFour_sylow_field_kernel h hH hp m hm hc e'
    change u ∈ L.subgroupOf (T : Subgroup G)
    rw [←hker]
    change Theory.PSL2.fieldProjection (Field m)
      ((MulAut.congr (Theory.PSL2.sl2QuotientEquiv (Field m))) α)=1
    rw [hg,MulAut.congr_conj]
    apply MonoidHom.mem_ker.mp
    rw [Theory.PSL2.fieldProjection_ker]
    exact ⟨_,rfl⟩
  have hE2 : Function.Involutive E := by
    intro x
    apply hcoord
    rw [hcoordE,hcoordE]
    have hu2 : u.val*u.val=1 := by
      have hh : u^2=1 := (congrArg (fun k : ℕ => u^k) hu).symm.trans (pow_orderOf_eq_one u)
      have hh' : u.val^2=1 := congrArg (fun t : T => t.val) hh
      simpa only [pow_two] using hh'
    calc
      _ = (u.val*u.val)*coord x*(u.val*u.val)⁻¹ := by group
      _ = coord x := by rw [hu2,inv_one,one_mul,mul_one]
  let j : (Q ⊓ centralizer ({u.val} : Set G) : Subgroup G) →
      {x : Space m // E x=x} := fun x => ⟨(f ⟨x.val,x.property.1⟩).toAdd,by
        apply hcoord
        rw [hcoordE,hcoordf]
        exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp x.property.2).symm⟩
  have hj : Function.Injective j := by
    intro x y hh
    apply Subtype.ext
    have he := congrArg (fun z : {x : Space m // E x=x} => coord z.val) hh
    change coord (f ⟨x.val,x.property.1⟩).toAdd = coord (f ⟨y.val,y.property.1⟩).toAdd at he
    simpa only [hcoordf] using he
  have hsurj : Function.Surjective j := by
    intro x
    let v := f.symm (Multiplicative.ofAdd x.val)
    have hv : v.val ∈ centralizer ({u.val} : Set G) := by
      apply mem_centralizer_singleton_iff.mpr
      have hh := hcoordE x.val
      rw [x.property] at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh.symm).symm
    refine ⟨⟨v.val,⟨v.property,hv⟩⟩,?_⟩
    apply Subtype.ext
    exact congrArg Multiplicative.toAdd (f.apply_symm_apply (Multiplicative.ofAdd x.val))
  exact (Nat.card_congr (Equiv.ofBijective j ⟨hj,hsurj⟩)).trans
    (Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourOuterFixed.outer_fixed_card m α hα houter E hE2 hinter)

/-- A two-subgroup of L fixing more than q² core elements is itself in the core. -/
theorem Preparation.unitaryFour_inner_fixer_of_large_core
    (U B : Subgroup G) (hU : IsPGroup 2 U) (hUL : U ≤ L)
    (hB : B ≤ L.pCoreIn 2) (hcard : (2^m)^2 < Nat.card B)
    (hfix : U ≤ centralizer (B : Set G)) : U ≤ L.pCoreIn 2 := by
  let : NeZero m := ⟨by omega⟩
  obtain ⟨e,f,hf⟩ := d.unitary_core_hermitian_model h hH hp m hm hc
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  let j := q.comp (inclusion hUL)
  let P := j.range
  have hP : IsPGroup 2 P := hU.of_surjective j.rangeRestrict j.rangeRestrict_surjective
  have hz : P=⊥ := by
    by_contra hne
    have hbound := Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourOuterFixed.inner_two_group_fixed_card m P hP hne
    let coord : B → Space m := fun x => (f ⟨x.val,hB x.property⟩).toAdd
    have hcoord : Function.Injective coord := by
      intro x y he
      apply Subtype.ext
      exact congrArg (fun v : L.pCoreIn 2 => v.val) (f.injective (congrArg Multiplicative.ofAdd he))
    have hfixed (x : B) (g : P) : action m g.val (coord x)=coord x := by
      obtain ⟨a,ha⟩ := g.property
      rw [←ha]
      let v : L.pCoreIn 2 := ⟨x.val,hB x.property⟩
      have hh := hf (inclusion hUL a) v
      have hab := mem_centralizer_iff.mp (hfix a.property) x.val x.property
      have hac : a.val*x.val*a.val⁻¹=x.val := by rw [←hab,mul_inv_cancel_right]
      have he : f.symm (Multiplicative.ofAdd (action m (j a) (coord x)))=v :=
        Subtype.ext (hh.trans hac)
      have hx := congrArg (fun v => (f v).toAdd) he
      rw [f.apply_symm_apply] at hx
      exact hx
    let k : B → {x : Space m // ∀ g : P, action m g.val x=x} :=
      fun x => ⟨coord x,hfixed x⟩
    have hk : Function.Injective k := fun x y he => hcoord (congrArg Subtype.val he)
    exact (not_lt_of_ge ((Nat.card_le_card_of_injective k hk).trans hbound)) hcard
  intro x hx
  have hj : j ⟨x,hx⟩=1 := by
    have hh : j ⟨x,hx⟩ ∈ P := ⟨_,rfl⟩
    rwa [hz,mem_bot] at hh
  have hxQ : (⟨x,hUL hx⟩ : L) ∈ pCore 2 L := by
    apply (QuotientGroup.eq_one_iff (N := pCore 2 L) _).mp
    apply e.injective
    exact hj.trans e.map_one.symm
  exact mem_map_of_mem L.subtype hxQ

/-- The full inner Sylow centralizer of an outer involution's fixed core
contains only core elements. No source-Sylow equality is used. -/
theorem Preparation.unitaryFour_outer_fixed_core_centralizer
    (u : T) (hu : orderOf u=2) (ho : u.val ∉ L) :
    ((T : Subgroup G) ⊓ L) ⊓
      centralizer ((L.pCoreIn 2 ⊓ centralizer ({u.val} : Set G) : Subgroup G) : Set G) ≤
        L.pCoreIn 2 := by
  apply d.unitaryFour_inner_fixer_of_large_core h hH hp m hm hc _ _
    (T.isPGroup'.to_le (inf_le_left.trans inf_le_left))
    (inf_le_left.trans inf_le_right) inf_le_left _ inf_le_right
  rw [d.unitaryFour_outer_core_fixed_card_eq h hH hp m hm hc u hu ho]
  exact Nat.pow_lt_pow_right (Nat.one_lt_pow (by omega) (by decide)) (by decide)

/-- The center–derived subgroup of the actual full C_T(u) is elementary,
via containment in the original Hermitian core. -/
theorem Preparation.unitaryFour_outer_derived_center_le_core
    (u : T) (hu : orderOf u=2) (ho : u.val ∉ L) :
    let P := (T : Subgroup G) ⊓ centralizer ({u.val} : Set G)
    let Z := (center P ⊓ _root_.commutator P).map P.subtype
    Z ≤ L.pCoreIn 2 ∧ IsElementaryAbelian 2 Z := by
  let P := (T : Subgroup G) ⊓ centralizer ({u.val} : Set G)
  let Z := (center P ⊓ _root_.commutator P).map P.subtype
  have hQT : L.pCoreIn 2 ≤ (T : Subgroup G) := by
    rw [←d.unitary_thompson h hH hp m hm hc]
    exact sSup_le fun _ hA => hA.1
  have hZ := d.unitaryFour_centralizer_derived_center h hH hp m hm hc u
  have hZQ : Z ≤ L.pCoreIn 2 := by
    intro z hz
    apply d.unitaryFour_outer_fixed_core_centralizer h hH hp m hm hc u hu ho
    refine ⟨(hZ.1 hz).1,?_⟩
    obtain ⟨w,hw,rfl⟩ := hz
    apply mem_centralizer_iff.mpr
    intro v hv
    exact congrArg Subtype.val (mem_center_iff.mp hw.1 (⟨v,hQT hv.1,hv.2⟩ : P))
  let : IsElementaryAbelian 2 (pCore 2 L) :=
    (d.unitary_core_structure h hH.1.1.2 hp m hm hc).2.2.1
  let : IsElementaryAbelian 2 (L.pCoreIn 2) := IsElementaryAbelian.map L.subtype
  exact ⟨hZQ,IsElementaryAbelian.of_injective (inclusion hZQ) (inclusion_injective hZQ)⟩


end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
