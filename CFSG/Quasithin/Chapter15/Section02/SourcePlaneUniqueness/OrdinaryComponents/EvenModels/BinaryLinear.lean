module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.OrdinaryComponents.FullRank
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.NaturalDualCentralizer.IncidentStructure.Core
public import Theory.SpecificGroups.BinaryLinear.SmallLeviRank
public import Theory.SpecificGroups.BinaryLinear.SmallCubicRank
public import Theory.SpecificGroups.BinaryLinear.OuterTwo
public import Theory.SpecificGroups.BinaryLinear.SylowTransvections
public import Theory.GroupTheory.SylowSubnormalIntersection

/-!
# Binary linear ordinary components in original 15.2.24

Restriction of the original Sylow of I to its subnormal component shows that
z centralizes a Sylow of that component. For the actual binary linear models,
the inducing inner involution is therefore a transvection. Its fixed subgroup
is the stabilizer of the incident vector and covector, with two-core quotient
PSL_(n-2)(2). For n = 4 or 5 this bounds its three-rank by one.

The original K has three-rank two and lies in that same fixed subgroup by
A.3.18 and the proved outer-two calculation. This excludes both literal model
rows, using no terminal classification or different Section15.3 hypotheses.
Source: Aschbacher--Smith,15.2.24, printed p.1117, refs/quasithin.pdf;
the incident quotient is the intrinsic calculation used in B.5.1(6).
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02.OrdinaryComponents
open Section01 Section03 Candidates.ComponentStructure ClassificationModels
open BinaryLinear BinaryLinear.OuterCyclic BinaryNaturalDual.VectorStabilizers
open ChapterB.QuasisimpleSource.NaturalDualCentralizer

private theorem transvection_fixed_eq_pair {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {w : V} {f : V →ₗ[ZMod 2] ZMod 2} (hw : w ≠ 0) (hf : f ≠ 0) (hfw : f w = 0) :
    (MulAut.conj (transvection w f hfw)).fixedSubgroup = pairStabilizer w f := by
  ext g
  constructor
  · intro hg
    have he : transvection w f hfw * g = g * transvection w f hfw :=
      mul_inv_eq_iff_eq_mul.mp ((MulAut.mem_fixedSubgroup _ _).mp hg)
    have hc (v : V) : f (g v) • w = f v • g w := by
      have hh := congrArg (fun a : BinaryLinear.GL V => a v) he
      change g v + f (g v) • w = g (v + f v • w) at hh
      simpa only [map_add,map_smul,add_right_inj] using hh
    obtain ⟨b,hb⟩ := LinearMap.range_eq_top.mp (Module.Dual.range_eq_top_of_ne_zero hf) 1
    have hgb := hc b
    rw [hb,one_smul] at hgb
    have hs : f (g b) ≠ 0 := by
      intro hz
      rw [hz,zero_smul] at hgb
      exact hw (g.map_eq_zero_iff.mp hgb.symm)
    have h1 : f (g b) = 1 := (by decide : ∀ a : ZMod 2,a ≠ 0 → a=1) _ hs
    have hgw : g w = w := by simpa only [h1,one_smul] using hgb.symm
    refine ⟨hgw,fun v => ?_⟩
    have hh := hc v
    rw [hgw] at hh
    exact (smul_left_injective _ hw) hh
  · intro hg
    apply (MulAut.mem_fixedSubgroup _ _).mpr
    apply mul_inv_eq_iff_eq_mul.mpr
    ext v
    change g v + f (g v) • w = g (v + f v • w)
    rw [map_add,map_smul,hg.1,hg.2]

private theorem binary_fixed_rank {n : ℕ} (hn : n = 4 ∨ n = 5)
    (t : LinearGroup n) (ht : t ≠ 1)
    (Q : Sylow 2 (LinearGroup n))
    (hQ : ∀ x ∈ Q, x * t = t * x) :
    primeRank 3 (MulAut.conj t).fixedSubgroup ≤ 1 := by
  obtain ⟨w,f,hw,hf,hfw,hact⟩ := central_sylow_eq_transvection
    (V := Space n) (by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
      have hd : Module.finrank (ZMod 2) (Space n) = n := Module.finrank_fin_fun _
      rw [hd]
      exact dvd_pow_self 2 (by omega : n ≠ 0))
    (by simpa only [Space,Module.finrank_fin_fun] using (show 1 < n by omega)) Q ht hQ
  have he : t = transvection w f hfw := LinearEquiv.ext hact
  rw [he,transvection_fixed_eq_pair hw hf hfw]
  let : Finite (LinearGroup n) := Finite.of_injective
    (fun g : LinearGroup n => (g : Space n → Space n)) DFunLike.coe_injective
  rw [← primeRank_quotient_eq_of_isTwoGroup 3 (by decide)
    (pCore 2 (pairStabilizer w f)) pCore_isPGroup,
    primeRank_equiv 3 (IncidentStructure.incidentQuotientEquiv (by omega) hw hf hfw)]
  exact SmallLeviRank.interior hn

variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
variable {P : Sylow 2 I} {z : G}
variable (c : ComponentData (T := T) (Mc := Mc) I P z)
include d

/-- The original central involution fixes a Sylow of the actual component. -/
theorem marked_component_twoCentral
    (hI : PlaneEscapes Mc ZS I)
    (hP : (P : Subgroup I).map I.subtype = planeSylow T ZS)
    (hz : z ∈ centralInvolutions T) (hzne : z ≠ 1)
    (a : MulAut c.component)
    (ha : ∀ x : c.component, ((a x : I) : G) = z * (x : G) * z⁻¹)
    (hi : a ∈ (MulAut.conj (G := c.component)).range) : TwoCentralInner a := by
  obtain ⟨Q,hQ⟩ := P.exists_subgroupOf_eq_of_subnormal c.component c.isComponent.1
  refine ⟨hi,marked_component_action_order_two c (marked_centralizer d hI hz hzne).1 hz hzne a ha,Q,?_⟩
  intro x
  apply Subtype.ext
  apply Subtype.ext
  rw [ha]
  have hxP : (x.val : I) ∈ P := by
    have hh : x.val ∈ (Q : Subgroup c.component) := x.property
    rw [hQ] at hh
    exact hh
  have hxT : ((x.val : I) : G) ∈ (T : Subgroup G) :=
    (show planeSylow T ZS ≤ (T : Subgroup G) from inf_le_left)
      (hP ▸ mem_map_of_mem I.subtype hxP)
  have hc := centralInvolutions_le_centralizer_sylow T hz _ hxT
  rw [←hc,mul_inv_cancel_right]

open scoped MatrixGroups
/-- Both binary linear rows of15.2.24 are impossible on the original component. -/
theorem not_binary_linear_component
    (hI : PlaneEscapes Mc ZS I)
    (hP : (P : Subgroup I).map I.subtype = planeSylow T ZS)
    (hz : z ∈ centralInvolutions T) (hzne : z ≠ 1)
    (a : MulAut c.component)
    (ha : ∀ x : c.component, ((a x : I) : G) = z * (x : G) * z⁻¹)
    {n : ℕ} (hn : n = 4 ∨ n = 5)
    (hm : ClassicalGroup.IsPSL c.component n 2)
    (hi : a ∈ (MulAut.conj (G := c.component)).range) : False := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  let ef : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card,Nat.card_zmod] using hF)
  let eq := (e.trans (Atlas.fieldEquivPSL n ef)).trans (projectiveEquivLinear (by omega))
  let : Finite (LinearGroup n) := Finite.of_equiv c.component eq.toEquiv
  have hc : center c.component = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    have hh := (centerCongr (eq.trans (slEquivLinear n).symm) ⟨x,hx⟩).property
    change (slEquivLinear n).symm (eq x) ∈ center SL(n,ZMod 2) at hh
    rw [binary_center_eq_bot (by omega : 0 < n),mem_bot] at hh
    exact (eq.trans (slEquivLinear n).symm).map_eq_one_iff.mp hh
  have hr : 2 ≤ primeRank 3 c.component := by
    rw [primeRank_equiv 3 (eq.trans (slEquivLinear n).symm)]
    exact SmallCubicRank.four_or_five hn
  have ho := (linear_outer_isTwoGroup hn).of_equiv (MulAut.outerCongr eq).symm
  have hlow := fixed_three_rank_of_full_component d c hI hz hzne hc hr ho a ha
  obtain ⟨_,horder,Q,hQ⟩ := marked_component_twoCentral d c hI hP hz hzne a ha hi
  let b := MulAut.congr eq a
  have hb : orderOf b = 2 := (MulAut.congr eq).orderOf_eq a |>.trans horder
  obtain ⟨t,ht⟩ : ∃ t, b = MulAut.conj t := by
    apply (MulAut.congr_inner_iff eq a).mpr
    obtain ⟨x,hx⟩ := hi
    exact ⟨x,hx.symm⟩
  have htne : t ≠ 1 := by
    intro he
    rw [ht,he,map_one,orderOf_one] at hb
    omega
  let R := Q.mapSurjective (f := eq.toMonoidHom) eq.surjective
  have hRt : ∀ x ∈ R, x*t=t*x := by
    rintro x ⟨y,hy,rfl⟩
    have hh := congrArg eq (hQ ⟨y,hy⟩)
    have hbfix : b (eq y) = eq y := by
      change eq (a (eq.symm (eq y))) = eq y
      rwa [eq.symm_apply_apply]
    rw [ht] at hbfix
    exact (mul_inv_eq_iff_eq_mul.mp hbfix).symm
  have hu := binary_fixed_rank hn t htne R hRt
  rw [←ht,←primeRank_equiv 3 (MulAut.fixedSubgroupCongr eq a)] at hu
  omega
end CFSG.Quasithin.Chapter15.Section02.OrdinaryComponents
