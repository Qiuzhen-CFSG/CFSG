module
public import Theory.GroupTheory.CComponent.CentralClosure
public import Theory.GroupTheory.DisjointCommutingProduct

/-!
# The literal simple pair above a two-core quotient

Distinct C-components with simple intrinsic two-core quotients remain
centerless simple components after quotienting by the ambient two-core.
Their multiplication gives an internal direct product, and their original
exchanger remains outside the index-two component normalizer. A Sylow-central
element normalizes each even simple component, by its nontrivial Sylow
intersection and the commutation of distinct components.

The partner-chief consumer retains these original quotient maps and the
specified exchanger in its Clifford restriction.
Source: Aschbacher–Smith, component calculus in A.3.3 and the recognition
step of 15.2.27(2), printed p.1119.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- A Sylow-central element fixes each even simple component. -/
theorem mem_normalizer_of_central_sylow_simple_component
    (A : Subgroup G) (hA : IsComponent G A) [IsSimpleGroup A]
    (hdiv : 2 ∣ Nat.card A) (S : Sylow 2 G) (z : G)
    (hc : ∀ s ∈ S, Commute z s) : z ∈ normalizer (A : Set G) := by
  let := hA.2
  have hz : center A = ⊥ := by
    exact (inferInstance : (center A).Normal).eq_bot_or_eq_top.resolve_right
      (fun he => Group.IsPerfect.not_isMulCommutative A (center_eq_top_iff.mp he))
  apply mem_normalizer_iff_map_conj_eq.mpr
  by_contra hn
  have hcomm := hA.commutator_eq_bot_of_ne (hA.map_conj z) (Ne.symm hn)
  obtain ⟨P,hP⟩ := S.exists_subgroupOf_eq_of_subnormal A hA.1
  let : Nontrivial (P : Subgroup A) := (Subgroup.nontrivial_iff_ne_bot _).mpr
    (P.ne_bot_of_dvd_card hdiv)
  obtain ⟨x,hx,hx1⟩ := (P : Subgroup A).exists_ne_one_of_nontrivial
  have hxS : (x : G) ∈ S := by rw [hP] at hx; exact hx
  have hfix : MulAut.conj z (x : G) = x := by
    change z * (x : G) * z⁻¹ = x
    rw [(hc x hxS).eq,mul_inv_cancel_right]
  have hxconj : (x : G) ∈ A.conjBy z :=
    hfix ▸ mem_map_of_mem (MulAut.conj z).toMonoidHom x.property
  have hxcenter : x ∈ center A := mem_center_iff.mpr fun y => Subtype.ext
    (((commutator_eq_bot_iff_le_centralizer.mp hcomm y.property) x hxconj).symm)
  exact hx1 (mem_bot.mp (hz ▸ hxcenter))

/-- The original component images form an internal simple direct product.
The original exchanging element lies outside their index-two normalizer. -/
theorem simpleCore_pair_quotient_structure
    (B : Subgroup G) (hB : B.IsCComponent) [IsSimpleGroup (B ⧸ pCore 2 B)]
    (t : G) (hne : B ≠ B.conjBy t) [(B ⊔ B.conjBy t).Normal]
    (hdiv : 2 ∣ Nat.card (B ⧸ pCore 2 B)) :
    let q := QuotientGroup.mk' (pCore 2 G)
    let A := B.map q
    IsComponent (G ⧸ pCore 2 G) A ∧ IsSimpleGroup A ∧ center A = ⊥ ∧
      2 ∣ Nat.card A ∧
      (B.conjBy t).map q = A.conjBy (q t) ∧
      (A ⊔ A.conjBy (q t)).Normal ∧ A ≠ A.conjBy (q t) ∧
      Disjoint A (A.conjBy (q t)) ∧ ⁅A,A.conjBy (q t)⁆ = ⊥ ∧
      (normalizer (A : Set (G ⧸ pCore 2 G))).index = 2 ∧
      q t ∉ normalizer (A : Set (G ⧸ pCore 2 G)) ∧
      ∃ e : A × A.conjBy (q t) ≃* (A ⊔ A.conjBy (q t) : Subgroup (G ⧸ pCore 2 G)),
        ∀ a b, (e (a,b) : G ⧸ pCore 2 G) = (a : G ⧸ pCore 2 G) * b := by
  let q := QuotientGroup.mk' (pCore 2 G)
  let A := B.map q
  let : Group.IsNilpotent (pCore 2 G) := pCore_isPGroup.isNilpotent
  have hAc := hB.map_quotient (pCore 2 G)
  let := hAc.perfect
  let : IsSimpleGroup A := (cComponentTwoCoreQuotientEquiv hB).symm.isSimpleGroup
  have hz : center A = ⊥ := by
    exact (inferInstance : (center A).Normal).eq_bot_or_eq_top.resolve_right
      (fun he => Group.IsPerfect.not_isMulCommutative A (center_eq_top_iff.mp he))
  have hA : IsComponent (G ⧸ pCore 2 G) A :=
    ⟨hAc.subnormal, ⟨((QuotientGroup.quotientMulEquivOfEq hz).trans
      QuotientGroup.quotientBot).isSimpleGroup⟩⟩
  have hconj : (B.conjBy t).map q = A.conjBy (q t) := by
    change (B.map (MulAut.conj t).toMonoidHom).map q =
      (B.map q).map (MulAut.conj (q t)).toMonoidHom
    rw [Subgroup.map_map,Subgroup.map_map]
    congr 1
  have hn : A ≠ A.conjBy (q t) := by
    intro he
    exact hne (hB.eq_of_map_quotient_eq (hB.map_equiv (MulAut.conj t)) (pCore 2 G)
      (he.trans hconj.symm))
  have hp : (A ⊔ A.conjBy (q t)).Normal := by
    rw [←hconj,show A=B.map q from rfl,←Subgroup.map_sup]
    exact Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  let := hp
  have hd : 2 ∣ Nat.card A := by
    rw [←Nat.card_congr (cComponentTwoCoreQuotientEquiv hB).toEquiv]
    exact hdiv
  have hc := hA.commutator_eq_bot_of_ne (hA.map_conj (q t)) hn
  have hdis : Disjoint A (A.conjBy (q t)) := by
    apply disjoint_def.mpr
    intro x hx hy
    have hxz : (⟨x,hx⟩ : A) ∈ center A := mem_center_iff.mpr fun y =>
      Subtype.ext (((commutator_eq_bot_iff_le_centralizer.mp hc y.property) x hy).symm)
    have he : (⟨x,hx⟩ : A) = 1 := mem_bot.mp (hz ▸ hxz)
    exact congrArg (fun a : A => (a : G ⧸ pCore 2 G)) he
  refine ⟨hA,inferInstance,hz,hd,hconj,hp,hn,hdis,hc,
    ComponentPairRankDescent.component_normalizer_index_two_of_normal_pair A hA (q t) hn,
    fun ht => hn (mem_normalizer_iff_map_conj_eq.mp ht).symm,?_⟩
  exact exists_mulEquiv_prod_sup_of_disjoint_of_commuting A _ hdis
    (commutator_eq_bot_iff_le_centralizer.mp hc)
end Theory.GroupTheory
