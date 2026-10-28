module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.ComponentElevenCommutator
public import Theory.SpecificGroups.PSL2.InvolutionCentralizerInversion

/-!
# The original cubic commutator has order at most 512

The literal PSL₂(11) component marking supplies a conjugate of the original
V-star involution inverting P_K-star. A cubic generator is a commutator
with this conjugate. Its displacement on the same U_H/V₁ section is at
most twice the original rank-four displacement, hence at most eight.
Counting the actual subgroup image and its point kernel gives
|[O₂(L₁),P_K]| = |[U_H,P_K]| ≤ 2⁹.

The source application constructs the component and action marking and
retains every original geometric hypothesis and quotient map. The source
block recognition must still identify this commutator with all O₂(L₁)
to contradict the already proved lower bound 2¹¹. Neither point-span
abelianness nor universal NaturalReduction is asserted here.
Source: Aschbacher--Smith, proof of 12.6.26, printed p.833.
-/

public section
namespace CFSG.Quasithin.Chapter12.Section06
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
set_option backward.isDefEq.respectTransparency false
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)
  (hz : z ≠ 1)
  (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
  (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
  (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
    Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
  {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
  (hn : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH H))
  (c : (D.fullSetup hZ T z).SelectedComponent H) (a : c.ActionMarking)


include hz hTV hTz hbound hH hn a in
/-- A conjugate of the actual V-star involution inverts the original P_K-star. -/
theorem SourceHypothesis.original_selectedComponent_cubic_inverter
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    (P : Sylow 3 (D.fullSetup hZ T z).L₁) :
    let E := D.fullSetup hZ T z
    let PK := ((P : Subgroup E.L₁).map E.L₁.subtype) ⊓ c.K
    ∃ u ∈ Nonabelian.Setup.star H V, ∃ k : Nonabelian.Setup.star H c.K,
      ∀ x ∈ Nonabelian.Setup.star H PK,
        (k.val*u*k.val⁻¹)*x*(k.val*u*k.val⁻¹)⁻¹ = x⁻¹ := by
  let E := D.fullSetup hZ T z
  let B := Nonabelian.Setup.star H c.K
  let PK := ((P : Subgroup E.L₁).map E.L₁.subtype) ⊓ c.K
  obtain ⟨F,hfield,hfinite,hF,⟨e⟩⟩ :=
    S.original_selectedComponent_linearTwoEleven D hZ z hz hTV hTz hbound hH hn c a hTI hns
  let := hfield
  let := hfinite
  obtain ⟨b,hb,hb2,_,_⟩ := S.original_selectedComponent_model_fixed_cubic
    D hZ z hz hTV hTz hbound hH hn c a hTI hns e
  have hb2' : orderOf b = 2 := ((MulAut.congr e).orderOf_eq b).symm.trans hb2
  obtain ⟨t,ht⟩ := S.original_linearTwo_module_inner D hZ z hz hTV hTz hbound hH hn c a
    hTI hns (p := 11) (n := 1) (by decide) (by decide) (by decide) (by simpa using hF) e b hb hb2'
  have ht2 : orderOf t = 2 :=
    (MulAut.conj_orderOf_of_center_eq_bot (GorensteinWalter.psl2_center_eq_bot F) t).symm.trans
      (ht ▸ hb2)
  obtain ⟨v,hv,he⟩ := hb
  let u := QuotientGroup.mk' (pCore 2 H) (inclusion a.local_le v)
  have hu : u ∈ Nonabelian.Setup.star H V := mem_map_of_mem _ hv
  have hact (y : B) : e (a.action v y) = t*e y*t⁻¹ := by
    have hh := DFunLike.congr_fun ht (e y)
    change e (b (e.symm (e y))) = t*e y*t⁻¹ at hh
    simpa only [he,e.symm_apply_apply] using hh
  obtain ⟨g,hg⟩ := Theory.PSL2.conjugate_inverts_odd_centralizer
    (show GorensteinWalter.IsOddPrimePower (Nat.card F) from
      ⟨11,1,by decide,by decide,by decide,by simpa using hF⟩) t ht2
  let k : B := e.symm g
  refine ⟨u,hu,k,?_⟩
  intro x hx
  have hxB : x ∈ B := map_mono (comap_mono inf_le_right) hx
  let y : B := ⟨x,hxB⟩
  have hxL : x ∈ Nonabelian.Setup.star H E.L₁ :=
    map_mono (comap_mono (inf_le_left.trans (map_subtype_le _))) hx
  have hxc : u*x=x*u := S.original_point_residual_star_centralizes
    D hZ z hz hTV hTz hbound hH hn hxL u hu
  have hfixed : a.action v y = y := by
    apply Subtype.ext
    rw [a.conjugation]
    change u*x*u⁻¹=x
    rw [hxc,mul_inv_cancel_right]
  have hyt : Commute (e y) t := by
    have hh := hact y
    rw [hfixed] at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh.symm).symm
  have hcard := (S.original_selectedComponent_sylow_intersection_star
    D hZ z hz hTV hTz hbound hH hn c a hTI hns P).1
  have ho : Odd (orderOf (e y)) := by
    rw [e.orderOf_eq,←Subgroup.orderOf_coe]
    exact (show Odd (Nat.card (Nonabelian.Setup.star H PK)) from hcard ▸ (by decide)).of_dvd_nat
      ((Nonabelian.Setup.star H PK).orderOf_dvd_natCard hx)
  have hmodel := hg (e y) ho hyt
  have heq : k * a.action v (k⁻¹*y*k) * k⁻¹ = y⁻¹ := by
    apply e.injective
    simp only [map_mul,map_inv,hact,show e k = g from e.apply_symm_apply g]
    calc
      _ = (g*t*g⁻¹)*e y*(g*t*g⁻¹)⁻¹ := by group
      _ = (e y)⁻¹ := hmodel
  have hh := congrArg Subtype.val heq
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hh
  rw [a.conjugation] at hh
  change k.val * (u * (k.val⁻¹*x*k.val) * u⁻¹) * k.val⁻¹ = x⁻¹ at hh
  calc
    _ = k.val * (u * (k.val⁻¹*x*k.val) * u⁻¹) * k.val⁻¹ := by group
    _ = x⁻¹ := hh

include hz hTV hTz hbound hH hn a in
/-- The original rank-four involution displacement bounds the actual cubic
commutator on the same marked U_H/V₁ by eight. -/
theorem SourceHypothesis.original_selectedComponent_cubic_displacement
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    (P : Sylow 3 (D.fullSetup hZ T z).L₁)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (σ : Representation (ZMod 2) (Nonabelian.Setup.Hstar H) W)
    (κ : Representation.BinaryConjugationSection H ((D.fullSetup hZ T z).UH H)
      ((D.fullSetup hZ T z).V₁) (σ.comp (QuotientGroup.mk' (pCore 2 H)))) :
    let E := D.fullSetup hZ T z
    let PK := ((P : Subgroup E.L₁).map E.L₁.subtype) ⊓ c.K
    Module.finrank (ZMod 2) (Representation.BinaryOffender.subspaceCommutator σ ⊤
      (Nonabelian.Setup.star H PK)) ≤ 8 := by
  let E := D.fullSetup hZ T z
  let PK := ((P : Subgroup E.L₁).map E.L₁.subtype) ⊓ c.K
  let A := Nonabelian.Setup.star H PK
  have hcard : Nat.card A = 3 := (S.original_selectedComponent_sylow_intersection_star
    D hZ z hz hTV hTz hbound hH hn c a hTI hns P).1
  have hne : A ≠ ⊥ := by intro he; rw [he,card_bot] at hcard; omega
  obtain ⟨x,hx,hxne⟩ := A.bot_or_exists_ne_one.resolve_left hne
  have hgen : zpowers x = A := by
    apply le_antisymm (zpowers_le.mpr hx)
    intro y hy
    have hy' : (⟨y,hy⟩ : A) ∈ zpowers (⟨x,hx⟩ : A) :=
      mem_zpowers_of_prime_card hcard (show (⟨x,hx⟩ : A) ≠ 1 from
        fun hh => hxne (congrArg Subtype.val hh))
    obtain ⟨n,hn⟩ := mem_zpowers_iff.mp hy'
    exact mem_zpowers_iff.mpr ⟨n,congrArg Subtype.val hn⟩
  have hx3 : x^3=1 := by
    have hh := pow_card_eq_one' (x := (⟨x,hx⟩ : A))
    rw [hcard] at hh
    exact congrArg Subtype.val hh
  obtain ⟨u,hu,k,hk⟩ := S.original_selectedComponent_cubic_inverter
    D hZ z hz hTV hTz hbound hH hn c a hTI hns P
  let t := k.val*u*k.val⁻¹
  have hi : t*x*t⁻¹=x⁻¹ := hk x hx
  have hcomm : t*x*t⁻¹*x⁻¹=x := by
    rw [hi]
    have hh : x*x*x=1 := by simpa only [pow_succ,pow_zero,one_mul] using hx3
    calc
      x⁻¹*x⁻¹ = (x*x)⁻¹ := (mul_inv_rev x x).symm
      _ = x := inv_eq_of_mul_eq_one_right hh
  have hd := Representation.BinaryOffender.fixedCodim_commutator_le_twice σ t x
  rw [hcomm,Representation.BinaryOffender.fixedCodim_zpowers_conj] at hd
  have hu4 := S.original_binary_displacement_bound D hZ z hz hTV hTz hbound hH hn σ κ u hu
  rw [Representation.BinaryOffender.fixedCodim_zpowers_eq_displacement_rank] at hd
  have hxrank : Module.finrank (ZMod 2) (σ x - LinearMap.id).range ≤ 8 := by
    rw [Representation.BinaryOffender.fixedCodim_zpowers_eq_displacement_rank] at hd
    omega
  change Module.finrank (ZMod 2) (Representation.BinaryOffender.subspaceCommutator σ ⊤ A) ≤ 8
  rw [←hgen,Representation.CyclicFixedRank.commutator_eq_range]
  exact hxrank

include hz hTV hTz hbound hH hn a in
/-- Count the actual cubic core commutator, retaining its point kernel. -/
theorem SourceHypothesis.original_selectedComponent_cubic_core_card_le
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    (P : Sylow 3 (D.fullSetup hZ T z).L₁) :
    let E := D.fullSetup hZ T z
    let PK := ((P : Subgroup E.L₁).map E.L₁.subtype) ⊓ c.K
    Nat.card (⁅E.L₁.pCoreIn 2,PK⁆ : Subgroup G) ≤ 2^9 := by
  let E := D.fullSetup hZ T z
  let PK := ((P : Subgroup E.L₁).map E.L₁.subtype) ⊓ c.K
  let C := ⁅E.UH H,PK⁆
  have h := S.original_f9_of_earlier_geometry D hZ z hz hTV hTz hbound hH
  let _ : (E.V₁.subgroupOf (E.UH H)).Normal := h.point_normal_in_UH
  let _ : IsElementaryAbelian 2 (E.UH H ⧸ E.V₁.subgroupOf (E.UH H)) := h.point_quotient_elementary
  let W := Additive (E.UH H ⧸ E.V₁.subgroupOf (E.UH H))
  obtain ⟨σ,κ,hσ,_⟩ := h.faithful_point_quotient
  change Representation (ZMod 2) (Nonabelian.Setup.Hstar H) W at σ
  change Representation.BinaryConjugationSection H (E.UH H) E.V₁
    (σ.comp (QuotientGroup.mk' (pCore 2 H))) at κ
  have hPH : PK ≤ H := inf_le_right.trans c.le_H
  have hCU : C ≤ E.UH H := le_normalizer_iff_commutator_le_left.mp (hPH.trans κ.normalized)
  have him : κ.imageSpace C = Representation.BinaryOffender.subspaceCommutator σ ⊤
      (Nonabelian.Setup.star H PK) := by
    rw [show C = ⁅PK,E.UH H⁆ from commutator_comm _ _,κ.imageSpace_commutator PK (E.UH H) hPH le_rfl,
      κ.imageSpace_self,Representation.BinaryOffender.subspaceCommutator_comp_map]
    rfl
  have hd : Module.finrank (ZMod 2) (κ.imageSpace C) ≤ 8 := by
    rw [him]
    exact S.original_selectedComponent_cubic_displacement
      D hZ z hz hTV hTz hbound hH hn c a hTI hns P (W := W) σ κ
  have hi : E.V₁.relIndex C ≤ 2^8 := by
    rw [←κ.imageSpace_card_eq_relIndex C hCU,Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
    exact Nat.pow_le_pow_right (by decide) hd
  have hzC : Nat.card (E.V₁.subgroupOf C) ≤ 2 := by
    let f : E.V₁.subgroupOf C → E.V₁ := fun x => ⟨x.val.val,x.property⟩
    have hf : Function.Injective f := by
      intro x y he
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun v : E.V₁ => (v : G)) he
    exact (Nat.card_le_card_of_injective f hf).trans_eq (E.point_card hz)
  have hcount := (E.V₁.subgroupOf C).card_mul_index
  change Nat.card (E.V₁.subgroupOf C) * E.V₁.relIndex C = Nat.card C at hcount
  change Nat.card (⁅E.L₁.pCoreIn 2,PK⁆ : Subgroup G) ≤ 2^9
  rw [S.original_selectedComponent_cubic_core_commutator D hZ z hz hTV hTz hbound hH hn c a hTI hns P]
  change Nat.card C ≤ 2^9
  rw [←hcount]
  exact (Nat.mul_le_mul hzC hi).trans (by norm_num)


include hz hTV hTz hbound hH hn in
/-- Original-source application: select the actual component and action, then
bound the commutator for every original Sylow three-subgroup. No component,
inverter, displacement or cardinality witness is an additional premise. -/
theorem SourceHypothesis.original_nonabelian_point_span_cubic_bounds
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L) :
    let E := D.fullSetup hZ T z
    ∃ c : E.SelectedComponent H, Nonempty c.ActionMarking ∧
      E.UH H ≤ E.L₁.pCoreIn 2 ∧ E.L₁.pCoreIn 2 ≤ H.pCoreIn 2 ∧
      2^11 ≤ Nat.card (E.L₁.pCoreIn 2) ∧
      ∀ P : Sylow 3 E.L₁,
        let PK := ((P : Subgroup E.L₁).map E.L₁.subtype) ⊓ c.K
        Nat.card PK = 3 ∧
        ⁅E.L₁.pCoreIn 2,PK⁆ = ⁅E.UH H,PK⁆ ∧
        Nat.card (⁅E.L₁.pCoreIn 2,PK⁆ : Subgroup G) ≤ 2^9 := by
  obtain ⟨c,_,_,⟨a⟩⟩ := S.original_selectedComponent_with_action
    D hZ z hz hTV hTz hbound hns hH hn
  obtain ⟨hu,hr,hl⟩ := S.original_nonabelian_point_span_core_bounds
    D hZ z hz hTV hTz hbound hH hn hTI hns
  refine ⟨c,⟨a⟩,hu,hr,hl,fun P => ?_⟩
  exact ⟨S.original_selectedComponent_sylow_intersection_card
      D hZ z hz hTV hTz hbound hH hn c a hTI hns P,
    S.original_selectedComponent_cubic_core_commutator
      D hZ z hz hTV hTz hbound hH hn c a hTI hns P,
    S.original_selectedComponent_cubic_core_card_le
      D hZ z hz hTV hTz hbound hH hn c a hTI hns P⟩

end CFSG.Quasithin.Chapter12.Section06
