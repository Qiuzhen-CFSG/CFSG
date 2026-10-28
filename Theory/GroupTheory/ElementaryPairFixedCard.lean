module
public import Theory.GroupTheory.ElementaryPairFixedDerived
public import Mathlib.GroupTheory.QuotientGroup.Basic
/-!
# Counting the fixed group of an exchanged elementary pair

For an involution exchanging elementary factors U and V of R, central
coboundaries correct each diagonal norm to a fixed point. Restriction of
R → R/V is therefore surjective both on U and on the fixed group. Its
kernels are U∩V and the fixed part of that intersection, respectively.
The two quotient formulas give the exact fixed-group cardinality ratio.

Source application: the Suzuki row in Aschbacher–Smith, Lemma 2.4.14(2),
printed p.533. No classification or finite-field model is used.
-/
public section
open Subgroup
open scoped Pointwise IsMulCommutative commutatorElement
namespace Subgroup
variable {G : Type*} [Group G]
theorem elementary_pair_fixed_card_mul
    (R U V Z : Subgroup G) [IsElementaryAbelian 2 U] [IsElementaryAbelian 2 V]
    (hgen : U ⊔ V = R) (hRU : R ≤ normalizer (U : Set G))
    (hZ : U ⊓ V = Z) (hder : ⁅R,R⁆ ≤ Z)
    (a : MulAut G) (ha : ∀ x, a (a x)=x) (hUV : U.map a.toMonoidHom=V)
    (htrace : ∀ z ∈ Z, a z=z → ∃ w ∈ Z, z=w*(a w)⁻¹) :
    Nat.card (R ⊓ a.toMonoidHom.eqLocus (MonoidHom.id G) : Subgroup G) * Nat.card Z =
      Nat.card U * Nat.card (Z ⊓ a.toMonoidHom.eqLocus (MonoidHom.id G) : Subgroup G) := by
  let C := R ⊓ a.toMonoidHom.eqLocus (MonoidHom.id G)
  have hUR : U ≤ R := le_sup_left.trans_eq hgen
  have hVR : V ≤ R := le_sup_right.trans_eq hgen
  have hZU : Z ≤ U := hZ ▸ inf_le_left
  have hZR : Z ≤ R := hZU.trans hUR
  have hau {u : G} (hu : u ∈ U) : a u ∈ V := hUV ▸ mem_map_of_mem a.toMonoidHom hu
  have hav {v : G} (hv : v ∈ V) : a v ∈ U := by
    obtain ⟨u,hu,he⟩ := (show v ∈ U.map a.toMonoidHom from hUV.symm ▸ hv)
    have he' : a u=v := he
    rw [←he',ha]
    exact hu
  have hzInv {z : G} (hz : z ∈ Z) : z⁻¹=z := inv_eq_of_mul_eq_one_left (by
    simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p:=2) z (hZU hz))
  have hcross {x y : G} (hx : x ∈ R) (hy : y ∈ R) : ⁅x,y⁆ ∈ Z :=
    hder (commutator_mem_commutator hx hy)
  have hcorrect (u : G) (hu : u ∈ U) : ∃ z ∈ Z, u*a u*z ∈ C := by
    let q := ⁅u,a u⁆
    have hq : q ∈ Z := hcross (hUR hu) (hVR (hau hu))
    have hqfix : a q=q := by
      change a ⁅u,a u⁆=⁅u,a u⁆
      rw [map_commutatorElement,ha,←commutatorElement_inv]
      exact hzInv hq
    obtain ⟨z,hz,hztrace⟩ := htrace q hq hqfix
    have hui : u⁻¹=u := inv_eq_of_mul_eq_one_left (by
      simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p:=2) u hu)
    have haui : (a u)⁻¹=a u := by rw [←map_inv,hui]
    have haz : a z=q*z := by
      have hh : q*a z=z := by rw [hztrace];group
      calc
        a z=q⁻¹*(q*a z) := by group
        _=q*z := by rw [hzInv hq,hh]
    refine ⟨z,hz,R.mul_mem (R.mul_mem (hUR hu) (hVR (hau hu))) (hZR hz),?_⟩
    change a (u*a u*z)=u*a u*z
    rw [map_mul,map_mul,ha,haz]
    change (a u*u)*(⁅u,a u⁆*z)=(u*a u)*z
    have haN : a u*u=(u*a u)⁻¹ := by simp only [mul_inv_rev,hui,haui]
    have hqN : ⁅u,a u⁆=(u*a u)*(u*a u) := by rw [commutatorElement_def,hui,haui];group
    rw [haN,hqN]
    group
  have hRV : R ≤ normalizer (V : Set G) := by
    apply le_normalizer_iff_commutator_le_left.mpr
    exact (commutator_mono hVR le_rfl).trans (hder.trans (hZ ▸ inf_le_right))
  let N := V.subgroupOf R
  let _ : N.Normal := normal_subgroupOf_of_le_normalizer hRV
  let π : R →* R ⧸ N := QuotientGroup.mk' N
  let f : U →* R ⧸ N := π.comp (inclusion hUR)
  let g : C →* R ⧸ N := π.comp (inclusion (show C ≤ R from inf_le_left))
  let J := Z ⊓ a.toMonoidHom.eqLocus (MonoidHom.id G)
  have hJC : J ≤ C := inf_le_inf_right _ hZR
  have hfactor (r : R) : ∃ u : U, f u=π r := by
    have hp : (r:G) ∈ (U : Set G)*(V : Set G) := by
      rw [←coe_mul_of_right_le_normalizer_left U V (hVR.trans hRU),hgen]
      exact r.property
    obtain ⟨u,hu,v,hv,he⟩ := hp
    refine ⟨⟨u,hu⟩,?_⟩
    have hr : r=(⟨u,hUR hu⟩ : R)*⟨v,hVR hv⟩ := Subtype.ext he.symm
    rw [hr,map_mul]
    have hvπ : π ⟨v,hVR hv⟩=1 := (QuotientGroup.eq_one_iff _).mpr hv
    rw [hvπ,mul_one]
    rfl
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨r,rfl⟩ := QuotientGroup.mk'_surjective N q
    exact hfactor r
  have hg : Function.Surjective g := by
    intro q
    obtain ⟨u,rfl⟩ := hf q
    obtain ⟨z,hz,huz⟩ := hcorrect u u.property
    refine ⟨⟨(u:G)*a u*z,huz⟩,?_⟩
    have he : (⟨(u:G)*a u*z,huz.1⟩ : R)=
        (⟨u,hUR u.property⟩ : R)*⟨a u,hVR (hau u.property)⟩*⟨z,hZR hz⟩ := rfl
    change π ⟨(u:G)*a u*z,huz.1⟩=f u
    rw [he,map_mul,map_mul]
    have hauπ : π ⟨a u,hVR (hau u.property)⟩=1 :=
      (QuotientGroup.eq_one_iff _).mpr (hau u.property)
    have hzπ : π ⟨z,hZR hz⟩=1 :=
      (QuotientGroup.eq_one_iff _).mpr ((hZ ▸ inf_le_right) hz)
    rw [hauπ,hzπ,mul_one,mul_one]
    rfl
  have hkf : f.ker=Z.subgroupOf U := by
    ext u
    change π (inclusion hUR u)=1 ↔ (u:G)∈Z
    rw [show π (inclusion hUR u)=1 ↔ inclusion hUR u∈N from QuotientGroup.eq_one_iff _]
    change (u:G)∈V ↔ (u:G)∈Z
    constructor
    · intro hv
      exact hZ ▸ (show (u:G)∈U⊓V from ⟨u.property,hv⟩)
    · exact fun hz => (show Z ≤ V from hZ ▸ inf_le_right) hz
  have hkg : g.ker=J.subgroupOf C := by
    ext c
    change π (inclusion (show C≤R from inf_le_left) c)=1 ↔ (c:G)∈J
    rw [show π (inclusion (show C≤R from inf_le_left) c)=1 ↔
      inclusion (show C≤R from inf_le_left) c∈N from QuotientGroup.eq_one_iff _]
    change (c:G)∈V ↔ (c:G)∈J
    constructor
    · intro hv
      have hfix : a (c:G)=(c:G) := c.property.2
      refine ⟨?_,c.property.2⟩
      exact hZ ▸ (show (c:G)∈U⊓V from ⟨hfix ▸ hav hv,hv⟩)
    · intro hc
      exact (hZ ▸ inf_le_right) hc.1
  have hcU : Nat.card U=Nat.card (R ⧸ N)*Nat.card Z := by
    have hh := card_eq_card_quotient_mul_card_subgroup f.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv,hkf,
      Nat.card_congr (subgroupOfEquivOfLe hZU).toEquiv] at hh
    exact hh
  have hcC : Nat.card C=Nat.card (R ⧸ N)*Nat.card J := by
    have hh := card_eq_card_quotient_mul_card_subgroup g.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective g hg).toEquiv,hkg,
      Nat.card_congr (subgroupOfEquivOfLe hJC).toEquiv] at hh
    exact hh
  change Nat.card C*Nat.card Z=Nat.card U*Nat.card J
  rw [hcC,hcU]
  ac_rfl
end Subgroup
