module
public import Stellmacher.Recognition.Parrott.ElementaryJoin
public import Stellmacher.Recognition.Parrott.DerivedTCentralizerCore
public import Stellmacher.Recognition.Parrott.DerivedVHyperplane
public import Theory.GroupAction.FiveFourInvariantHyperplane

/-!
# Core involutions in the order-1024 derived-involution centralizer

Retain the supplied second elementary subgroup F and Sylow subgroup T. For
noncentral t in E∩F with |C_T(t)|=1024, every square-one element of C_J(t)
lies in E∨F. The image C_J(t)/J′ is an invariant hyperplane in J/J′ for
an order-four element of H/J. The five-point involution orbit meets this
hyperplane only at aJ′, since the actor fixes that coset by normalizing F.
Equality of the actual quotient cosets then gives membership in E∨F.

This is the local containment needed to turn an involution in the normalizer
core outside E∨F into an involution outside the original core. No fusion or
omega-structure conclusion is assumed.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
pp.674 and 677, especially the implication from absence of involutions in
T−J to Ω₁(K)=A.
-/

open Subgroup
namespace Stellmacher.Recognition.ParrottSecondElementaryData
variable {G : Type*} [Group G] [Finite G] {z : G}

omit [Finite G] in
private theorem fixed_join_map (d : ParrottSecondElementaryData z) :
    let H := centralizer ({z} : Set G)
    let DH := (commutator (pCore 2 H)).map (pCore 2 H).subtype
    (zpowers d.a ⊔ (DH ⊓ centralizer ({d.a} : Set H))).map H.subtype = d.F := by
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  let DH := (commutator J).map J.subtype
  let E := (commutator J).map (H.subtype.comp J.subtype)
  have hDH : DH.map H.subtype = E := map_map _ _ _
  have hfixed : (DH ⊓ centralizer ({d.a} : Set H)).map H.subtype =
      E ⊓ centralizer ({(d.a : G)} : Set G) := by
    apply le_antisymm
    · rintro b ⟨c, hc, rfl⟩
      exact ⟨hDH ▸ mem_map_of_mem H.subtype hc.1,
        mem_centralizer_singleton_iff.mpr
          (congrArg H.subtype (mem_centralizer_singleton_iff.mp hc.2))⟩
    · intro b hb
      obtain ⟨c, hc, rfl⟩ := hDH.symm ▸ hb.1
      refine ⟨c, ⟨hc, ?_⟩, rfl⟩
      exact mem_centralizer_singleton_iff.mpr
        (Subtype.ext (mem_centralizer_singleton_iff.mp hb.2))
  change (zpowers d.a ⊔ (DH ⊓ centralizer ({d.a} : Set H))).map H.subtype = d.F
  rw [Subgroup.map_sup, MonoidHom.map_zpowers, hfixed]
  exact d.fixed_join.symm

private theorem sylow_fixes_core_coset (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let D := commutator J
    let q := QuotientGroup.mk' D
    ∀ f : (H ⧸ J) →* MulAut (J ⧸ D),
      (∀ (g : H) (b b' : J), (b' : H) = g * (b : H) * g⁻¹ →
        f (QuotientGroup.mk' J g) (q b) = q b') →
      ∀ y : H, (y : G) ∈ (d.sylow : Subgroup G) →
        f (QuotientGroup.mk' J y) (q ⟨d.a, d.a_mem_core⟩) = q ⟨d.a, d.a_mem_core⟩ := by
  intro H J D q f heval y hy
  let DH := D.map J.subtype
  let FH := zpowers d.a ⊔ (DH ⊓ centralizer ({d.a} : Set H))
  have hFHmap : FH.map H.subtype = d.F := d.fixed_join_map
  have hFH : d.F.subgroupOf H = FH := by
    rw [← hFHmap]
    exact comap_map_eq_self_of_injective H.subtype_injective _
  have hFHle : d.F ≤ H := d.le_core.trans (map_subtype_le _)
  have hyN : y ∈ normalizer (FH : Set H) := by
    rw [← hFH, ← subgroupOf_normalizer_eq hFHle]
    exact d.sylow_le_normalizer hy
  let : IsElementaryAbelian 2 D := (parrott_centralizer_structure z h).2.2.2.2.2.1
  let : IsElementaryAbelian 2 DH := IsElementaryAbelian.map J.subtype
  rw [elementary_involution_fixed_join_normalizer DH d.a d.a_order d.a_not_mem_derived] at hyN
  have hycomm := mem_centralizer_singleton_iff.mp hyN
  let aJ : J := ⟨d.a, d.a_mem_core⟩
  let b : J := ⟨y * d.a * y⁻¹, (inferInstance : J.Normal).conj_mem d.a d.a_mem_core y⟩
  rw [heval y aJ b rfl]
  have hquot : QuotientGroup.mk' DH (b : H) = QuotientGroup.mk' DH d.a := by
    change QuotientGroup.mk' DH (y * d.a * y⁻¹) = _
    rw [map_mul, map_mul, map_inv]
    exact mul_inv_eq_iff_eq_mul.mpr hycomm
  obtain ⟨v, hv, heq⟩ := QuotientGroup.eq_iff_div_mem.mp hquot
  apply QuotientGroup.eq_iff_div_mem.mpr
  exact (show v = b / aJ from Subtype.ext heq) ▸ hv

/-- All square-one elements of the original core centralizing the supplied
noncentral t belong to the join of the supplied elementary subgroups, when
its centralizer in the supplied Sylow has order 1024. -/
public theorem t_centralizer_core_involution_mem_elementary_join
    (d : ParrottSecondElementaryData z) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    ∀ t ∈ E ⊓ d.F, t ∉ zpowers z →
      Nat.card ((d.sylow : Subgroup G) ⊓ centralizer ({t} : Set G) : Subgroup G) = 1024 →
      ∀ x ∈ J.map H.subtype ⊓ centralizer ({t} : Set G),
        x ^ 2 = 1 → x ∈ E ⊔ d.F := by
  classical
  intro H J E t ht htz hC x hx hx2
  by_cases hxE : x ∈ E
  · exact mem_sup_left hxE
  obtain ⟨bH, hbJ, rfl⟩ := hx.1
  let b : J := ⟨bH, hbJ⟩
  let a : J := ⟨d.a, d.a_mem_core⟩
  let D := commutator J
  let i := H.subtype.comp J.subtype
  let q := QuotientGroup.mk' D
  let V := J ⧸ D
  let C := (centralizer ({t} : Set G)).comap i
  let U := C.map q
  have hbD : b ∉ D := fun hh => hxE (mem_map_of_mem i hh)
  have hbne : q b ≠ 1 := fun hh => hbD ((QuotientGroup.eq_one_iff (N := D) b).mp hh)
  have hane : q a ≠ 1 := by
    intro hh
    exact d.a_not_mem_derived (mem_map_of_mem J.subtype
      ((QuotientGroup.eq_one_iff (N := D) a).mp hh))
  obtain ⟨hElem, hV⟩ := parrott_core_abelianization_structure z h
  let : IsElementaryAbelian 2 V := hElem
  obtain ⟨f, hf, heval⟩ := parrott_core_quotient_action z h
  obtain ⟨y, hy, hy4⟩ := d.t_centralizer_exists_quotient_order_four h t ht.1 htz hC
  obtain ⟨φ, hφ, ⟨e⟩⟩ := h.quotient_model
  let fM := f.comp e.symm.toMonoidHom
  let g := e (QuotientGroup.mk' J y)
  have hg : orderOf g = 4 := (e.orderOf_eq _).trans hy4
  have hfM : Function.Injective fM := hf.comp e.symm.injective
  have hfg : fM g = f (QuotientGroup.mk' J y) := by
    dsimp only [fM, g, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [e.symm_apply_apply]
  have hU : Nat.card U = 8 :=
    (parrott_derived_core_centralizer_hyperplane z h t ht.1 htz).2.2
  have hstable : ∀ v ∈ U, fM g v ∈ U := by
    rintro v ⟨c, hc, rfl⟩
    let c' : J := ⟨y * (c : H) * y⁻¹, (inferInstance : J.Normal).conj_mem c c.property y⟩
    have hc' : c' ∈ C :=
      (centralizer ({t} : Set G)).mul_mem
        ((centralizer ({t} : Set G)).mul_mem hy.2 hc)
        ((centralizer ({t} : Set G)).inv_mem hy.2)
    rw [hfg, heval y c c' rfl]
    exact mem_map_of_mem q hc'
  have haF : (d.a : G) ∈ d.F := by
    rw [d.fixed_join]
    exact mem_sup_left (mem_zpowers _)
  have haU : q a ∈ U := by
    apply mem_map_of_mem q
    let : IsElementaryAbelian 2 d.F := d.elementary
    exact mem_centralizer_singleton_iff.mpr (setLike_mul_comm haF ht.2)
  have hafix : fM g (q a) = q a := by
    rw [hfg]
    exact d.sylow_fixes_core_coset h f heval y hy.1
  have horbit (v : V) : Set.range (fun k => fM k v) = Set.range (fun k => f k v) := by
    ext w
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨e.symm k, rfl⟩
    · rintro ⟨k, rfl⟩
      exact ⟨e k, by simp [fM]⟩
  have ha5 : (Set.range (fun k => fM k (q a))).ncard = 5 := by
    rw [horbit]
    exact (centralizer_index_eq_subgroup_quotient_orbit_card J D f heval a).symm.trans
      d.coset_index
  have hb2 : orderOf bH = 2 := orderOf_eq_prime
    (Subtype.ext hx2) (fun hh => hxE (by rw [hh]; exact E.one_mem))
  have hbDH : bH ∉ D.map J.subtype := by
    rintro ⟨c, hc, heq⟩
    exact hbD ((show c = b from Subtype.ext heq) ▸ hc)
  have hb5 : (Set.range (fun k => fM k (q b))).ncard = 5 := by
    rw [horbit]
    exact (centralizer_index_eq_subgroup_quotient_orbit_card J D f heval b).symm.trans
      (parrott_core_involution_coset_centralizer_index z h bH hbJ hb2 hbDH)
  have hba : q b = q a :=
    Theory.GroupAction.five_four_invariant_hyperplane_orbit_intersection hV φ hφ
      fM hfM g hg U hU hstable (q a) hane haU hafix ha5 (q b)
      (mem_map_of_mem q hx.2) hbne hb5
  have hdiv : (bH : G) / (d.a : G) ∈ E :=
    mem_map_of_mem i (QuotientGroup.eq_iff_div_mem.mp hba)
  have hmul := (E ⊔ d.F).mul_mem (mem_sup_left hdiv) (mem_sup_right haF)
  change (bH : G) ∈ E ⊔ d.F
  simpa only [div_mul_cancel] using hmul

end Stellmacher.Recognition.ParrottSecondElementaryData
