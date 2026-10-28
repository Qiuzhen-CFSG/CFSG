module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.NativeSource16.OddResidual.NoBorel

/-!
# The original odd residual in a unitary circle

Restrict the original R and its involution to the containing circle F,
then transport through its actual special or projective unitary equivalence.
Subgroup equivalences preserve the full commutator, oddness, noncyclicity and
orders. Conjugation by an ambient element normalizing F gives the precise
operator on the carrier, preserving both marked order-nine equations.

Source: GLS IV, Chapter 2, Proposition 16.5. Recognition of the actual circle
and construction of its two witnesses remain with the source assembly.
-/

noncomputable section
namespace BenderSuzuki.ZD.NativeSource16
open Subgroup Theory.GroupTheory _root_.BenderSuzuki.MatrixGroups
variable {G H : Type*} [Group G] [Group H]

private theorem model_full_commutator (F R : Subgroup G) (hRF : R≤F)
    (e : F ≃* H) (t : G) (htF : t∈F) (htR : t∈normalizer R)
    (hcomm : ⁅R,zpowers t⁆=R) :
    e ⟨t,htF⟩∈normalizer ((R.subgroupOf F).map e.toMonoidHom) ∧
      ⁅(R.subgroupOf F).map e.toMonoidHom,zpowers (e ⟨t,htF⟩)⁆=
        (R.subgroupOf F).map e.toMonoidHom := by
  let tF : F := ⟨t,htF⟩
  have hnt : tF∈normalizer (R.subgroupOf F) := by
    apply mem_normalizer_iff.mpr
    intro x
    exact mem_normalizer_iff.mp htR x
  refine ⟨le_normalizer_map e.toMonoidHom (mem_map_of_mem _ hnt),?_⟩
  have he : ⁅R.subgroupOf F,zpowers tF⁆=R.subgroupOf F := by
    apply map_injective F.subtype_injective
    rw [map_commutator,MonoidHom.map_zpowers,map_subgroupOf_eq_of_le hRF]
    exact hcomm
  simpa only [map_commutator,MonoidHom.map_zpowers,tF,MulEquiv.coe_toMonoidHom] using
    congrArg (Subgroup.map e.toMonoidHom) he

private def residualModelEquiv (F R : Subgroup G) (hRF : R≤F) (e : F ≃* H) :
    R ≃* (R.subgroupOf F).map e.toMonoidHom :=
  (subgroupOfEquivOfLe hRF).symm.trans
    ((R.subgroupOf F).equivMapOfInjective e.toMonoidHom e.injective)

private theorem model_conj_equation (F : Subgroup G) (e : F ≃* H)
    {t x : G} (htF : t∈F) (hxF : x∈F) (hx : t*x*t⁻¹=x⁻¹) :
    e ⟨t,htF⟩ * e ⟨x,hxF⟩ * (e ⟨t,htF⟩)⁻¹=(e ⟨x,hxF⟩)⁻¹ := by
  have he : (⟨t,htF⟩ : F)*⟨x,hxF⟩*(⟨t,htF⟩ : F)⁻¹=(⟨x,hxF⟩ : F)⁻¹ :=
    Subtype.ext hx
  simpa only [map_mul,map_inv] using congrArg e he

private theorem model_opposite_operator (F : Subgroup G) (e : F ≃* H)
    {u x y : G} (huF : u∈normalizer F) (hxF : x∈F) (hyF : y∈F)
    (hux : u*x*u⁻¹=x) (huy : u*y*u⁻¹=y⁻¹) :
    ∃ a : H →* H, a (e ⟨x,hxF⟩)=e ⟨x,hxF⟩ ∧
      a (e ⟨y,hyF⟩)=(e ⟨y,hyF⟩)⁻¹ := by
  let c := F.normalizerMonoidHom ⟨u,huF⟩
  let a := (e.symm.trans c).trans e
  have hx : c ⟨x,hxF⟩=⟨x,hxF⟩ := Subtype.ext hux
  have hy : c ⟨y,hyF⟩=(⟨y,hyF⟩ : F)⁻¹ := Subtype.ext huy
  refine ⟨a.toMonoidHom,?_,?_⟩
  · change e (c (e.symm (e ⟨x,hxF⟩)))=e ⟨x,hxF⟩
    rw [e.symm_apply_apply,hx]
  · change e (c (e.symm (e ⟨y,hyF⟩)))=(e ⟨y,hyF⟩)⁻¹
    rw [e.symm_apply_apply,hy,map_inv]

variable {E : Type*} [Field E] [Finite E]

/-- The original p-residual is cyclic in an actual special-unitary circle,
for p distinct from two and three; no Borel placement is assumed. -/
public theorem special_ambient_full_commutator_isCyclic
    (J : HermitianForm 3 E) {n : ℕ} (hn : 2≤n)
    (hc : Nat.card E=(2^n)^2) (hf : Nat.card {x:E // J.conj x=x}=2^n)
    (hJ : J.form=!![0,0,1;0,1,0;1,0,0])
    (F R : Subgroup G) (hRF : R≤F) (e : F ≃* J.specialSubgroup)
    {p : ℕ} [Fact p.Prime] (hp2 : p≠2) (hp3 : p≠3) (hR : IsPGroup p R)
    (t : G) (htF : t∈F) (ht : orderOf t=2)
    (htR : t∈normalizer R) (hcomm : ⁅R,zpowers t⁆=R) : IsCyclic R := by
  let Rm := (R.subgroupOf F).map e.toMonoidHom
  let tm := e ⟨t,htF⟩
  let eR := residualModelEquiv F R hRF e
  have hRm : IsPGroup p Rm := hR.of_equiv eR
  have htm : orderOf tm=2 := by
    exact (e.orderOf_eq ⟨t,htF⟩).trans ((Subgroup.orderOf_coe (⟨t,htF⟩ : F)).symm.trans ht)
  obtain ⟨hnt,hcmt⟩ := model_full_commutator F R hRF e t htF htR hcomm
  exact eR.isCyclic.mpr (special_pSubgroup_full_commutator_isCyclic
    J hn hc hf hJ Rm hp2 hp3 hRm tm htm hnt hcmt)

/-- The original ambient order-nine witnesses are incompatible with the
actual special-unitary circle containing the noncyclic source residual. -/
public theorem special_ambient_full_commutator_false_of_opposite_order_nine
    (J : HermitianForm 3 E) {n : ℕ} (hn : 2≤n)
    (hc : Nat.card E=(2^n)^2) (hf : Nat.card {x:E // J.conj x=x}=2^n)
    (hJ : J.form=!![0,0,1;0,1,0;1,0,0])
    (F R : Subgroup G) (hRF : R≤F) (e : F ≃* J.specialSubgroup)
    (hodd : Odd (Nat.card R)) (hnoncyclic : ¬ IsCyclic R)
    (t : G) (htF : t∈F) (ht : orderOf t=2)
    (htR : t∈normalizer R) (hcomm : ⁅R,zpowers t⁆=R)
    (u : G) (huF : u∈normalizer F) (x y : G) (hxR : x∈R) (hyR : y∈R)
    (hx : orderOf x=9) (hy : orderOf y=9)
    (htx : t*x*t⁻¹=x⁻¹) (hty : t*y*t⁻¹=y⁻¹)
    (hux : u*x*u⁻¹=x) (huy : u*y*u⁻¹=y⁻¹) : False := by
  let Rm := (R.subgroupOf F).map e.toMonoidHom
  let tm := e ⟨t,htF⟩
  let xm := e ⟨x,hRF hxR⟩
  let ym := e ⟨y,hRF hyR⟩
  let eR := residualModelEquiv F R hRF e
  have hom : Odd (Nat.card Rm) := (Nat.card_congr eR.toEquiv) ▸ hodd
  have hnc : ¬ IsCyclic Rm := fun hh => hnoncyclic (eR.isCyclic.mpr hh)
  have htm : orderOf tm=2 := by
    exact (e.orderOf_eq ⟨t,htF⟩).trans ((Subgroup.orderOf_coe (⟨t,htF⟩ : F)).symm.trans ht)
  have hxm : orderOf xm=9 := by
    exact (e.orderOf_eq ⟨x,hRF hxR⟩).trans ((Subgroup.orderOf_coe (⟨x,hRF hxR⟩ : F)).symm.trans hx)
  have hym : orderOf ym=9 := by
    exact (e.orderOf_eq ⟨y,hRF hyR⟩).trans ((Subgroup.orderOf_coe (⟨y,hRF hyR⟩ : F)).symm.trans hy)
  obtain ⟨hnt,hcmt⟩ := model_full_commutator F R hRF e t htF htR hcomm
  obtain ⟨a,hax,hay⟩ := model_opposite_operator F e huF (hRF hxR) (hRF hyR) hux huy
  exact special_full_commutator_false_of_opposite_order_nine J hn hc hf hJ Rm hom hnc
    tm htm hnt hcmt xm ym
    (mem_map_of_mem _ (show (⟨x,hRF hxR⟩ : F)∈R.subgroupOf F from hxR))
    (mem_map_of_mem _ (show (⟨y,hRF hyR⟩ : F)∈R.subgroupOf F from hyR))
    hxm hym (model_conj_equation F e htF (hRF hxR) htx)
    (model_conj_equation F e htF (hRF hyR) hty) a hax hay

/-- The original p-residual is cyclic in an actual projective-unitary circle,
for p distinct from two and three; no Borel placement is assumed. -/
public theorem projective_ambient_full_commutator_isCyclic
    (J : HermitianForm 3 E) {n : ℕ} (hn : 2≤n)
    (hc : Nat.card E=(2^n)^2) (hf : Nat.card {x:E // J.conj x=x}=2^n)
    (hJ : J.form=!![0,0,1;0,1,0;1,0,0])
    (F R : Subgroup G) (hRF : R≤F) (e : F ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    {p : ℕ} [Fact p.Prime] (hp2 : p≠2) (hp3 : p≠3) (hR : IsPGroup p R)
    (t : G) (htF : t∈F) (ht : orderOf t=2)
    (htR : t∈normalizer R) (hcomm : ⁅R,zpowers t⁆=R) : IsCyclic R := by
  let Rm := (R.subgroupOf F).map e.toMonoidHom
  let tm := e ⟨t,htF⟩
  let eR := residualModelEquiv F R hRF e
  have hRm : IsPGroup p Rm := hR.of_equiv eR
  have htm : orderOf tm=2 := by
    exact (e.orderOf_eq ⟨t,htF⟩).trans ((Subgroup.orderOf_coe (⟨t,htF⟩ : F)).symm.trans ht)
  obtain ⟨hnt,hcmt⟩ := model_full_commutator F R hRF e t htF htR hcomm
  exact eR.isCyclic.mpr (projective_pSubgroup_full_commutator_isCyclic
    J hn hc hf hJ Rm hp2 hp3 hRm tm htm hnt hcmt)

/-- The original ambient order-nine witnesses are incompatible with the
actual projective-unitary circle containing the noncyclic source residual. -/
public theorem projective_ambient_full_commutator_false_of_opposite_order_nine
    (J : HermitianForm 3 E) {n : ℕ} (hn : 2≤n)
    (hc : Nat.card E=(2^n)^2) (hf : Nat.card {x:E // J.conj x=x}=2^n)
    (hJ : J.form=!![0,0,1;0,1,0;1,0,0])
    (F R : Subgroup G) (hRF : R≤F) (e : F ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (hodd : Odd (Nat.card R)) (hnoncyclic : ¬ IsCyclic R)
    (t : G) (htF : t∈F) (ht : orderOf t=2)
    (htR : t∈normalizer R) (hcomm : ⁅R,zpowers t⁆=R)
    (u : G) (huF : u∈normalizer F) (x y : G) (hxR : x∈R) (hyR : y∈R)
    (hx : orderOf x=9) (hy : orderOf y=9)
    (htx : t*x*t⁻¹=x⁻¹) (hty : t*y*t⁻¹=y⁻¹)
    (hux : u*x*u⁻¹=x) (huy : u*y*u⁻¹=y⁻¹) : False := by
  let Rm := (R.subgroupOf F).map e.toMonoidHom
  let tm := e ⟨t,htF⟩
  let xm := e ⟨x,hRF hxR⟩
  let ym := e ⟨y,hRF hyR⟩
  let eR := residualModelEquiv F R hRF e
  have hom : Odd (Nat.card Rm) := (Nat.card_congr eR.toEquiv) ▸ hodd
  have hnc : ¬ IsCyclic Rm := fun hh => hnoncyclic (eR.isCyclic.mpr hh)
  have htm : orderOf tm=2 := by
    exact (e.orderOf_eq ⟨t,htF⟩).trans ((Subgroup.orderOf_coe (⟨t,htF⟩ : F)).symm.trans ht)
  have hxm : orderOf xm=9 := by
    exact (e.orderOf_eq ⟨x,hRF hxR⟩).trans ((Subgroup.orderOf_coe (⟨x,hRF hxR⟩ : F)).symm.trans hx)
  have hym : orderOf ym=9 := by
    exact (e.orderOf_eq ⟨y,hRF hyR⟩).trans ((Subgroup.orderOf_coe (⟨y,hRF hyR⟩ : F)).symm.trans hy)
  obtain ⟨hnt,hcmt⟩ := model_full_commutator F R hRF e t htF htR hcomm
  obtain ⟨a,hax,hay⟩ := model_opposite_operator F e huF (hRF hxR) (hRF hyR) hux huy
  exact projective_full_commutator_false_of_opposite_order_nine J hn hc hf hJ Rm hom hnc
    tm htm hnt hcmt xm ym
    (mem_map_of_mem _ (show (⟨x,hRF hxR⟩ : F)∈R.subgroupOf F from hxR))
    (mem_map_of_mem _ (show (⟨y,hRF hyR⟩ : F)∈R.subgroupOf F from hyR))
    hxm hym (model_conj_equation F e htF (hRF hxR) htx)
    (model_conj_equation F e htF (hRF hyR) hty) a hax hay

end BenderSuzuki.ZD.NativeSource16
