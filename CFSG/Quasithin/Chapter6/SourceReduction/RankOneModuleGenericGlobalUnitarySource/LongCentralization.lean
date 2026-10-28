module
public import Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourLongFixed
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.SingularCenter

/-!
# Pointwise long-root fixation in the selected full unitary centralizer

An outer involution acts linearly on the Hermitian core over its defining
field. The original right-residual center is the invariant inner-Sylow
fixed line, so the involution fixes it pointwise. This puts the entire
original long-root group R in its full centralizer P=C_T(f).

If Z(P)∩P′ has trivial intersection with R, the finite two-group normal
intersection theorem gives P′∩R=1 and [P,R]=1. Pointwise fixation of the
whole defining-field line forces every element of P to have inner square.
The cyclic field quotient therefore has order at most two, and the same
outer involution makes its order exactly two. For the actual selected
degree-two actor, ambient nonfusion and the escaping normalizer already
supply the trivial intersection. Maximality then gives |P∩L|≥q⁴ and at
least q images in the literal L/O₂(L) quotient.

All statements retain the FULL P, the original R, both orientations and
q=4. The actual selected consumer retains the same escaping V and both
full-endpoint Sylow conditions. The remaining source contradiction is to
produce a nontrivial long-root commutator in this same P. Ordinary-even
selection and unconditional recognition remain separate obligations.
Source: Aschbacher–Smith F.4.29(7),37, pp.289,293, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels.UnitaryFour UnitaryCompletion
open Representation.OrthogonalFourMinus.FiniteModel
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H A C : Subgroup G} {n : ℕ}
namespace UnitarySource
open scoped commutatorElement
private theorem central_derived_disjoint
    (P R : Subgroup G) (hp : IsPGroup 2 P)
    (hRP : R ≤ P) (hn : P ≤ normalizer (R : Set G))
    (hz : ((center P ⊓ _root_.commutator P).map P.subtype) ⊓ R=⊥) :
    (_root_.commutator P).map P.subtype ⊓ R=⊥ ∧ P ≤ centralizer (R : Set G) := by
  let N := R.subgroupOf P
  let : N.Normal := normal_subgroupOf_of_le_normalizer hn
  let D := _root_.commutator P ⊓ N
  have hD : D=⊥ := by
    by_contra hne
    apply center_inf_ne_bot_of_normal hp D hne
    apply bot_unique
    intro x hx
    have hm : x.val ∈ ((center P ⊓ _root_.commutator P).map P.subtype) ⊓ R :=
      ⟨⟨x,⟨hx.1,hx.2.1⟩,rfl⟩,hx.2.2⟩
    rw [hz,mem_bot] at hm
    exact Subtype.ext hm
  have hd : (_root_.commutator P).map P.subtype ⊓ R=⊥ := by
    apply bot_unique
    rintro x ⟨⟨y,hy,rfl⟩,hx⟩
    have hh : y ∈ D := ⟨hy,hx⟩
    rw [hD,mem_bot] at hh
    exact congrArg Subtype.val hh
  refine ⟨hd,?_⟩
  intro x hx
  apply mem_centralizer_iff.mpr
  intro y hy
  let a : P := ⟨x,hx⟩
  let b : P := ⟨y,hRP hy⟩
  have hb : b ∈ N := hy
  have hcomm : ⁅a,b⁆ ∈ D :=
    ⟨commutator_mem_commutator (mem_top a) (mem_top b),
      commutator_le_right (⊤ : Subgroup P) N
        (commutator_mem_commutator (mem_top a) hb)⟩
  rw [hD,mem_bot] at hcomm
  have hh := commutatorElement_eq_one_iff_mul_comm.mp hcomm
  exact (congrArg Subtype.val hh).symm
end UnitarySource

variable (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (sourceS L H) m hm)
include d h hH hp hm hc

theorem Preparation.unitaryFour_outer_centralizes_right_center
    (u : T) (hu : orderOf u=2) (ho : u.val ∉ L) :
    u.val ∈ centralizer (((center (residual H)).map (residual H).subtype) : Set G) := by
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
  obtain ⟨P,hP⟩ := exists_sylow_component h.sylow_normalizes
  let S := (T : Subgroup G) ⊓ L
  let R := (center (residual H)).map (residual H).subtype
  let Pq := P.mapSurjective (show Function.Surjective q from
    e.surjective.comp (QuotientGroup.mk'_surjective _))
  let U := Representation.invariants ((action m).comp (Pq : Subgroup _).subtype)
  have hR : R=Q ⊓ centralizer (S : Set G) :=
    (d.unitaryFour_inner_fixed_core_eq_right_center h hH hp m hm hc).symm
  have hcoords (x : Space m) : coord x ∈ R ↔ x ∈ U := by
    rw [hR]
    constructor
    · intro hx g
      obtain ⟨l,hl,he⟩ := g.property
      change action m g.val x=x
      rw [←he]
      apply hcoord
      rw [hcoordAct]
      have hlS : l.val ∈ S := by
        change l.val ∈ (T : Subgroup G) ⊓ L
        rw [←hP]
        exact mem_map_of_mem L.subtype hl
      exact mul_inv_eq_iff_eq_mul.mpr
        (mem_centralizer_iff.mp hx.2 l.val hlS)
    · intro hx
      refine ⟨(f.symm (Multiplicative.ofAdd x)).property,mem_centralizer_iff.mpr ?_⟩
      intro l hl
      have hmap : l ∈ (P : Subgroup L).map L.subtype := by
        rw [hP]
        exact hl
      obtain ⟨k,hk,rfl⟩ := hmap
      have hh := congrArg coord (hx (⟨q k,⟨k,hk,rfl⟩⟩ : Pq))
      change coord (action m (q k) x)=coord x at hh
      rw [hcoordAct] at hh
      exact mul_inv_eq_iff_eq_mul.mp hh
  have hTR : (T : Subgroup G) ≤ normalizer (R : Set G) :=
    (hH.1.1.2.trans (le_normalizer_residual H)).trans
      (normalizer_le_normalizer_characteristic_image (residual H) (center (residual H)))
  have hstable (x : Space m) (hx : x ∈ U) : E x ∈ U := by
    apply (hcoords _).mp
    rw [hcoordE]
    exact (mem_normalizer_iff.mp (hTR u.property) _).mp ((hcoords x).mpr hx)
  have hfixed := Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourLongFixed.outer_fixes_line
    m α hα houter E hE2 hinter U
    (Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourLongFixed.sylow_fixed_finrank m Pq)
    hstable
  apply mem_centralizer_iff.mpr
  intro z hz
  have hzQ : z ∈ Q := by
    have hh : z ∈ R := hz
    rw [hR] at hh
    exact hh.1
  let x : Space m := (f ⟨z,hzQ⟩).toAdd
  have hzx : coord x=z := hcoordf ⟨z,hzQ⟩
  have hh := congrArg coord (hfixed x ((hcoords x).mp (hzx.symm ▸ hz)))
  rw [hcoordE,hzx] at hh
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm

/-- Every original Sylow involution centralizes the full original long-root group. -/
theorem Preparation.unitaryFour_involution_centralizes_right_center
    (u : T) (hu : orderOf u=2) :
    u.val ∈ centralizer (((center (residual H)).map (residual H).subtype) : Set G) := by
  by_cases ho : u.val ∈ L
  · rw [←d.unitaryFour_inner_fixed_core_eq_right_center h hH hp m hm hc]
    apply mem_centralizer_iff.mpr
    intro z hz
    exact (mem_centralizer_iff.mp hz.2 u.val ⟨u.property,ho⟩).symm
  · exact d.unitaryFour_outer_centralizes_right_center h hH hp m hm hc u hu ho

/-- A trivial long-root intersection forces the same full centralizer to
centralize the whole long-root group, and its full derived group avoids it. -/
theorem Preparation.unitaryFour_outer_centralizes_long_of_disjoint
    (u : T) (hu : orderOf u=2)
    (hz : let P := (T : Subgroup G) ⊓ centralizer ({u.val} : Set G)
      ((center P ⊓ _root_.commutator P).map P.subtype) ⊓
        (center (residual H)).map (residual H).subtype=⊥) :
    let P := (T : Subgroup G) ⊓ centralizer ({u.val} : Set G)
    let R := (center (residual H)).map (residual H).subtype
    (_root_.commutator P).map P.subtype ⊓ R=⊥ ∧ P ≤ centralizer (R : Set G) := by
  let P := (T : Subgroup G) ⊓ centralizer ({u.val} : Set G)
  let R := (center (residual H)).map (residual H).subtype
  have hTR : (T : Subgroup G) ≤ normalizer (R : Set G) :=
    (hH.1.1.2.trans (le_normalizer_residual H)).trans
      (normalizer_le_normalizer_characteristic_image (residual H) (center (residual H)))
  have hRQ : R ≤ L.pCoreIn 2 := by
    dsimp only [R]
    rw [←d.unitaryFour_inner_fixed_core_eq_right_center h hH hp m hm hc]
    exact inf_le_left
  have hQT : L.pCoreIn 2 ≤ (T : Subgroup G) := by
    rw [←d.unitary_thompson h hH hp m hm hc]
    exact sSup_le fun _ hA => hA.1
  have hRP : R ≤ P := by
    intro z hz
    refine ⟨hQT (hRQ hz),mem_centralizer_singleton_iff.mpr ?_⟩
    exact mem_centralizer_iff.mp
      (d.unitaryFour_involution_centralizes_right_center h hH hp m hm hc u hu) z hz
  exact UnitarySource.central_derived_disjoint P R
    (T.isPGroup'.to_le inf_le_left) hRP (inf_le_left.trans hTR) hz


/-- An actor centralizing the original long-root group has inner square;
its field coefficient can retain only the quadratic involution. -/
theorem Preparation.unitaryFour_square_mem_left_of_centralizes_right_center
    (u : T)
    (hfix : u.val ∈ centralizer (((center (residual H)).map (residual H).subtype) : Set G)) :
    (u.val)^2 ∈ L := by
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
  obtain ⟨P,hP⟩ := exists_sylow_component h.sylow_normalizes
  let S := (T : Subgroup G) ⊓ L
  let R := (center (residual H)).map (residual H).subtype
  let Pq := P.mapSurjective (show Function.Surjective q from
    e.surjective.comp (QuotientGroup.mk'_surjective _))
  let U := Representation.invariants ((action m).comp (Pq : Subgroup _).subtype)
  have hR : R=Q ⊓ centralizer (S : Set G) :=
    (d.unitaryFour_inner_fixed_core_eq_right_center h hH hp m hm hc).symm
  have hcoords (x : Space m) : coord x ∈ R ↔ x ∈ U := by
    rw [hR]
    constructor
    · intro hx g
      obtain ⟨l,hl,he⟩ := g.property
      change action m g.val x=x
      rw [←he]
      apply hcoord
      rw [hcoordAct]
      have hlS : l.val ∈ S := by
        change l.val ∈ (T : Subgroup G) ⊓ L
        rw [←hP]
        exact mem_map_of_mem L.subtype hl
      exact mul_inv_eq_iff_eq_mul.mpr
        (mem_centralizer_iff.mp hx.2 l.val hlS)
    · intro hx
      refine ⟨(f.symm (Multiplicative.ofAdd x)).property,mem_centralizer_iff.mpr ?_⟩
      intro l hl
      have hmap : l ∈ (P : Subgroup L).map L.subtype := by
        rw [hP]
        exact hl
      obtain ⟨k,hk,rfl⟩ := hmap
      have hh := congrArg coord (hx (⟨q k,⟨k,hk,rfl⟩⟩ : Pq))
      change coord (action m (q k) x)=coord x at hh
      rw [hcoordAct] at hh
      exact mul_inv_eq_iff_eq_mul.mp hh
  let : Nontrivial U := Module.nontrivial_of_finrank_eq_succ
    (Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourLongFixed.sylow_fixed_finrank m Pq)
  obtain ⟨X,hX⟩ := exists_ne (0 : U)
  have hXne : X.val ≠ 0 := fun hh => hX (Subtype.ext hh)
  have hfixed (a : fixedField m) : E (a • X.val)=a • X.val := by
    apply hcoord
    rw [hcoordE]
    exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_iff.mp hfix _
      ((hcoords _).mpr (U.smul_mem a X.property))).symm
  obtain ⟨g,hg⟩ := Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourLongFixed.square_inner_of_fixed_line
    m α E hinter X.val hXne hfixed
  let e' := e.trans (Theory.PSL2.sl2QuotientEquiv (Field m))
  have hker := d.unitaryFour_sylow_field_kernel h hH hp m hm hc e'
  change u^2 ∈ L.subgroupOf (T : Subgroup G)
  rw [←hker]
  change Theory.PSL2.fieldProjection (Field m)
    ((MulAut.congr (Theory.PSL2.sl2QuotientEquiv (Field m))) (φ (a^2)))=1
  rw [map_pow]
  change Theory.PSL2.fieldProjection (Field m)
    ((MulAut.congr (Theory.PSL2.sl2QuotientEquiv (Field m))) (α^2))=1
  rw [hg,MulAut.congr_conj]
  apply MonoidHom.mem_ker.mp
  rw [Theory.PSL2.fieldProjection_ker]
  exact ⟨_,rfl⟩

/-- Inside the original Sylow, pointwise fixation of the original long-root
group leaves at most quadratic outer degree. -/
theorem Preparation.unitaryFour_long_fixer_index_le_two
    (P : Subgroup G) (hPT : P ≤ (T : Subgroup G))
    (hPR : P ≤ centralizer (((center (residual H)).map (residual H).subtype) : Set G)) :
    L.relIndex P ≤ 2 := by
  classical
  let : NeZero m := ⟨by omega⟩
  obtain ⟨e,_,_⟩ := d.unitary_core_hermitian_model h hH hp m hm hc
  let e' := e.trans (Theory.PSL2.sl2QuotientEquiv (Field m))
  let φ := unitaryFourSylowFieldAction h.sylow_normalizes e'
  let ψ := φ.comp (inclusion hPT)
  have hker : ψ.ker=L.subgroupOf P := by
    ext x
    change inclusion hPT x ∈ φ.ker ↔ x.val ∈ L
    rw [d.unitaryFour_sylow_field_kernel h hH hp m hm hc e']
    rfl
  let I := ψ.range
  let : IsCyclic (Field m ≃+* Field m) := Theory.PSL2.OuterSolvable.finiteFieldAut_isCyclic
  let : Finite (Field m ≃+* Field m) := Finite.of_injective
    (fun σ : Field m ≃+* Field m => (σ : Field m → Field m)) DFunLike.coe_injective
  let := Fintype.ofFinite I
  have hsquare (x : I) : x^2=1 := by
    obtain ⟨a,ha⟩ := x.property
    apply Subtype.ext
    change x.val^2=1
    rw [←ha,←map_pow]
    apply MonoidHom.mem_ker.mp
    rw [hker]
    exact d.unitaryFour_square_mem_left_of_centralizes_right_center h hH hp m hm hc
      (inclusion hPT a) (hPR a.property)
  have hb := IsCyclic.card_pow_eq_one_le (α := I) (n := 2) (by decide)
  have he : (Finset.univ.filter (fun a : I => a^2=1))=Finset.univ := by
    ext x
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,hsquare]
  rw [he,Finset.card_univ] at hb
  calc
    L.relIndex P = ψ.ker.index := by rw [hker]; rfl
    _ = Nat.card I := index_ker ψ
    _ ≤ 2 := by simpa only [Nat.card_eq_fintype_card] using hb

/-- For the same selected outer actor, disjointness forces the FULL
centralizer's quotient by its inner part to have exactly order two. -/
theorem Preparation.unitaryFour_outer_index_two_of_disjoint
    (u : T) (hu : orderOf u=2) (ho : u.val ∉ L)
    (hz : let P := (T : Subgroup G) ⊓ centralizer ({u.val} : Set G)
      ((center P ⊓ _root_.commutator P).map P.subtype) ⊓
        (center (residual H)).map (residual H).subtype=⊥) :
    L.relIndex ((T : Subgroup G) ⊓ centralizer ({u.val} : Set G))=2 := by
  let P := (T : Subgroup G) ⊓ centralizer ({u.val} : Set G)
  have hb := d.unitaryFour_long_fixer_index_le_two h hH hp m hm hc P inf_le_left
    (d.unitaryFour_outer_centralizes_long_of_disjoint h hH hp m hm hc u hu hz).2
  have hne : L.relIndex P ≠ 1 := by
    intro hh
    exact ho (relIndex_eq_one.mp hh ⟨u.property,mem_centralizer_singleton_iff.mpr rfl⟩)
  have hpos : 0 < L.relIndex P := Nat.pos_of_ne_zero (L.subgroupOf P).index_ne_zero_of_finite
  change L.relIndex P=2
  omega

omit hc in
/-- Once the same maximal outer centralizer has quadratic outer quotient,
its inner fixed subgroup has order at least q⁴. This comparison uses the
marked graph actor only for its independently proved order lower bound. -/
theorem Preparation.unitaryFour_degreeTwo_maximal_inner_card_lower
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (Extension.amalgam m hm)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (Extension.amalgam m hm).reverse))
    (u : T) (hu : orderOf u=2) (ho : u.val ∉ L)
    (hmax : ∀ g : T, orderOf g=2 → g.val ∉ L →
      Nat.card (centralizer ({g} : Set T)) ≤ Nat.card (centralizer ({u} : Set T)))
    (hz : let P := (T : Subgroup G) ⊓ centralizer ({u.val} : Set G)
      ((center P ⊓ _root_.commutator P).map P.subtype) ⊓
        (center (residual H)).map (residual H).subtype=⊥) :
    (2^m)^4 ≤ Nat.card ((((T : Subgroup G) ⊓ L) ⊓
      centralizer ({u.val} : Set G)) : Subgroup G) := by
  let P := (T : Subgroup G) ⊓ centralizer ({u.val} : Set G)
  have hi := d.unitaryFour_outer_index_two_of_disjoint h hH hp m hm (.inr he) u hu ho hz
  obtain ⟨_,_,g,_,hgT,hg2,hgo,_,hgc,_⟩ := d.unitary_graph_local_sylow h hH hp m hm he
  let gT : T := ⟨g.val,hgT⟩
  have hgT2 : orderOf gT=2 := (Subgroup.orderOf_coe gT).symm.trans hg2
  have hcards (x : T) : Nat.card (centralizer ({x} : Set T)) =
      Nat.card ((T : Subgroup G) ⊓ centralizer ({x.val} : Set G) : Subgroup G) := by
    rw [←map_subtype_centralizer_singleton,card_map_of_injective (T : Subgroup G).subtype_injective]
  have hmax' := hmax gT hgT2 hgo
  rw [hcards gT,hcards u] at hmax'
  have hgC : Nat.card (sourceS L H ⊓ centralizer ({g.val} : Set G) : Subgroup G) ≤
      Nat.card ((T : Subgroup G) ⊓ centralizer ({g.val} : Set G) : Subgroup G) :=
    card_le_of_le (inf_le_inf_right _ (sourceS_le_sylow h.sylow_normalizes hH.1.1.2))
  rw [hgc] at hgC
  have hb : 2*(2^m)^4 ≤ Nat.card P := hgC.trans hmax'
  have hmul := (L.subgroupOf P).card_mul_index
  change Nat.card (L.subgroupOf P) * L.relIndex P=Nat.card P at hmul
  rw [hi] at hmul
  have hinner : Nat.card (L.subgroupOf P) =
      Nat.card ((((T : Subgroup G) ⊓ L) ⊓ centralizer ({u.val} : Set G)) : Subgroup G) := by
    rw [←card_map_of_injective (K := L.subgroupOf P) P.subtype_injective,subgroupOf_map_subtype]
    congr 1
    dsimp only [P]
    ac_rfl
  rw [hinner] at hmul
  omega

omit hc in
/-- The selected inner fixed group has at least q distinct images in the
literal L/O₂(L) quotient, not merely nontrivial image. -/
theorem Preparation.unitaryFour_degreeTwo_maximal_inner_quotient_lower
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (Extension.amalgam m hm)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (Extension.amalgam m hm).reverse))
    (u : T) (hu : orderOf u=2) (ho : u.val ∉ L)
    (hmax : ∀ g : T, orderOf g=2 → g.val ∉ L →
      Nat.card (centralizer ({g} : Set T)) ≤ Nat.card (centralizer ({u} : Set T)))
    (hz : let P := (T : Subgroup G) ⊓ centralizer ({u.val} : Set G)
      ((center P ⊓ _root_.commutator P).map P.subtype) ⊓
        (center (residual H)).map (residual H).subtype=⊥) :
    2^m ≤ (L.pCoreIn 2).relIndex
      (((T : Subgroup G) ⊓ L) ⊓ centralizer ({u.val} : Set G)) := by
  let Q := L.pCoreIn 2
  let I := ((T : Subgroup G) ⊓ L) ⊓ centralizer ({u.val} : Set G)
  have hQS : Q ≤ (T : Subgroup G) ⊓ L := by
    dsimp only [Q]
    rw [←d.unitary_inner_thompson h hH hp m hm (.inr he)]
    exact sSup_le fun _ hA => hA.1
  have hcard : Nat.card (Q.subgroupOf I)=(2^m)^3 := by
    rw [←card_map_of_injective (K := Q.subgroupOf I) I.subtype_injective,subgroupOf_map_subtype]
    change Nat.card (Q ⊓ (((T : Subgroup G) ⊓ L) ⊓ centralizer ({u.val} : Set G)) : Subgroup G)=_
    rw [←inf_assoc,inf_eq_left.mpr hQS]
    exact d.unitaryFour_outer_core_fixed_card_eq h hH hp m hm (.inr he) u hu ho
  have hb := d.unitaryFour_degreeTwo_maximal_inner_card_lower h hH hp m hm he u hu ho hmax hz
  have hmul := (Q.subgroupOf I).card_mul_index
  change Nat.card (Q.subgroupOf I) * Q.relIndex I=Nat.card I at hmul
  rw [hcard] at hmul
  have hh : (2^m)^3 * (2^m) ≤ (2^m)^3 * Q.relIndex I := by
    rw [hmul,←pow_succ]
    exact hb
  exact Nat.le_of_mul_le_mul_left hh (by positivity)

omit hc in
/-- The maximizing degree-two actor has a full centralizer which fixes the
entire original long-root group and whose derived group avoids it. The
same escaping two-group and both local Sylow conditions are retained. -/
theorem Preparation.unitaryFour_degreeTwo_selected_long_centralization
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (Extension.amalgam m hm)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (Extension.amalgam m hm).reverse)) :
    ∃ f : T,
      (∀ g : T, orderOf g=2 → g.val ∉ L →
        Nat.card (centralizer ({g} : Set T)) ≤ Nat.card (centralizer ({f} : Set T))) ∧
      orderOf f=2 ∧ f.val ∉ L ∧ f.val ∉ residual H ∧
      (∀ i : Fin 2, Chapter1.IsSylowIn 2
        ((T : Subgroup G) ⊓ centralizer ({f.val} : Set G))
        (normalizer (![L,residual H] i : Set G) ⊓ centralizer ({f.val} : Set G))) ∧
      ∃ V : Subgroup G, IsPGroup 2 V ∧
        (T : Subgroup G) ⊓ centralizer ({f.val} : Set G) < V ∧
        V ≤ centralizer ({f.val} : Set G) ∧
        V ≤ normalizer (((T : Subgroup G) ⊓ centralizer ({f.val} : Set G) : Subgroup G) : Set G) ∧
        (∀ i : Fin 2, ¬ V ≤ normalizer (![L,residual H] i : Set G)) ∧
        (∀ B : Subgroup G, B ≤ (center (residual H)).map (residual H).subtype →
          V ≤ normalizer (B : Set G) → B=⊥) ∧
        let P := (T : Subgroup G) ⊓ centralizer ({f.val} : Set G)
        let R := (center (residual H)).map (residual H).subtype
        let Z := (center P ⊓ _root_.commutator P).map P.subtype
        Z ≠ ⊥ ∧ IsElementaryAbelian 2 Z ∧ Z ≤ L.pCoreIn 2 ∧
          V ≤ normalizer (Z : Set G) ∧
          (_root_.commutator P).map P.subtype ⊓ R=⊥ ∧ P ≤ centralizer (R : Set G) ∧
          L.relIndex P=2 ∧
          (2^m)^4 ≤ Nat.card ((((T : Subgroup G) ⊓ L) ⊓
            centralizer ({f.val} : Set G)) : Subgroup G) ∧
          2^m ≤ (L.pCoreIn 2).relIndex
            (((T : Subgroup G) ⊓ L) ⊓ centralizer ({f.val} : Set G)) := by
  obtain ⟨f,hmax,hf,ho,hor,hs,V,hV,hPV,hVC,hVN,hout,_,hno,hZ,hZe,hZQ,hVZ,_,hzero⟩ :=
    d.unitaryFour_degreeTwo_selected_singular_center h hH hp m hm he
  have hcentral := d.unitaryFour_outer_centralizes_long_of_disjoint h hH hp m hm (.inr he) f hf hzero
  exact ⟨f,hmax,hf,ho,hor,hs,V,hV,hPV,hVC,hVN,hout,hno,hZ,hZe,hZQ,hVZ,hcentral.1,hcentral.2,
    d.unitaryFour_outer_index_two_of_disjoint h hH hp m hm (.inr he) f hf ho hzero,
    d.unitaryFour_degreeTwo_maximal_inner_card_lower h hH hp m hm he f hf ho hmax hzero,
    d.unitaryFour_degreeTwo_maximal_inner_quotient_lower h hH hp m hm he f hf ho hmax hzero⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
