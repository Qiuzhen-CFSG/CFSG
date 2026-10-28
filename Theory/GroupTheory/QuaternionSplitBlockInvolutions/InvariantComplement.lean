module

public import Theory.GroupTheory.QuaternionSplitBlockInvolutions

/-!
# An invariant four-group complement for a marked quaternion swap

Let Q be the central product of two quaternion eights, and let an involutory
automorphism α interchange its actual factors. An α-invariant elementary
eight V containing Z(Q), on which α acts nontrivially, has an α-invariant
elementary four-group complement.

Choose a square-one element x whose displacement x⁻¹α(x) is outside V.
Such an x exists: otherwise generation by involutions makes every displacement
belong to V, forcing the fixed diagonal of order eight into V and hence making
α trivial on V. The a₂ square calculation shows x and α(x) commute. Thus
D = ⟨x, α(x)⟩ is an invariant four-group, and all three nonidentity elements
of D lie outside V. The orders eight, four and thirty-two give complementation.

The ambient application uses the literal normalizer action on an embedded U
and maps D through U.subtype. It obtains the containment, disjointness,
generation and normalization premises of
`Subgroup.isComplement_sup_zpowers_of_invariant`. The marking C_G(V) ≤ U
and a ∉ U supplies nontriviality on V; no identification of U with a two-core
is required. The chapter owner retains the final Sylow and block assembly.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
Lemma 14.4.4, printed p.1007, the a₂ invariant-complement step before Gaschütz.
-/

open scoped Pointwise commutatorElement
namespace Subgroup.QuaternionCentralProductData
variable {Q : Type*} [Group Q] [Finite Q] (d : QuaternionCentralProductData Q)

include d in
private theorem marked_normal (V : Subgroup Q) (hZV : center Q ≤ V) : V.Normal := by
  constructor
  intro v hv g
  have hc : ⁅g, v⁆ ∈ center Q := by
    let := d.quotient_elementary
    apply (QuotientGroup.eq_one_iff _).mp
    change (QuotientGroup.mk' (center Q)) ⁅g, v⁆ = 1
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr
      ((IsMulCommutative.is_comm (M := Q ⧸ center Q)).comm _ _)
  have h := V.mul_mem (hZV hc) hv
  simpa only [commutatorElement_def, mul_assoc, inv_mul_cancel, mul_one] using h

private theorem exists_moved_involution (α : MulAut Q) (hα : α ^ 2 = 1)
    (hswap : d.left.map α.toMonoidHom = d.right)
    (V : Subgroup Q) (hV : Nat.card V = 8) (hZV : center Q ≤ V)
    (hmoved : ∃ v ∈ V, α v ≠ v) :
    ∃ x : Q, x ^ 2 = 1 ∧ x⁻¹ * α x ∉ V := by
  classical
  by_contra! h
  let := d.marked_normal V hZV
  let π := QuotientGroup.mk' V
  let K := (π.comp α.toMonoidHom).eqLocus π
  have hgen := quaternion_central_product_involutions_generate d.left d.right
    d.left_model d.right_model d.intersection_card d.commute
  have hK : ⊤ ≤ K := by
    rw [← d.span, ← hgen]
    apply (closure_le _).mpr
    intro x hx
    change π (α x) = π x
    exact (QuotientGroup.eq.mpr (h x hx.2)).symm
  have hall (x : Q) : x⁻¹ * α x ∈ V := by
    have hx : π (α x) = π x := hK (mem_top x)
    exact QuotientGroup.eq.mp hx.symm
  let θ : d.left ≃* d.right :=
    (α.subgroupMap d.left).trans (MulEquiv.subgroupCongr hswap)
  let F := quaternionDiagonal d.left d.right θ d.commute
  have hFV : F ≤ V := by
    apply sup_le ?_ (d.center_eq ▸ hZV)
    rintro _ ⟨b, rfl⟩
    change (b : Q) * α b ∈ V
    have hh := V.mul_mem (hZV (d.square_mem_center b)) (hall b)
    simpa only [pow_two, mul_assoc, mul_inv_cancel_left] using hh
  have hFcard : Nat.card F = 8 :=
    (quaternion_diagonal_elementary_eight d.left d.right d.left_model.some θ
      d.intersection_card d.commute).2.1
  have heq : F = V := eq_of_le_of_card_ge hFV (by rw [hFcard, hV])
  have hfixed : α.toMonoidHom.eqLocus (MonoidHom.id Q) = F :=
    quaternion_diagonal_eq_fixed_of_involution_swap d.left d.right θ
      d.intersection_card d.commute d.span α hα (fun _ => rfl)
  obtain ⟨v, hv, hnv⟩ := hmoved
  have hvF : v ∈ α.toMonoidHom.eqLocus (MonoidHom.id Q) := (hfixed.trans heq).symm ▸ hv
  exact hnv hvF

private theorem displacement_square (α : MulAut Q) (hα : α ^ 2 = 1)
    (hswap : d.left.map α.toMonoidHom = d.right) (x : Q) :
    (x⁻¹ * α x) ^ 2 = 1 := by
  have ha := d.isA2Action_of_swap α hα hswap
  have hm : d.quotientDisplacement α (QuotientGroup.mk' (center Q) x) ∈
      d.fixedSquareQuotient α := by
    rw [← d.displacement_range_eq_fixed α ha.1 ha.2.1]
    exact ⟨_, rfl⟩
  have hs := congrArg Subtype.val (ha.2.2 _ hm)
  have he : d.quotientDisplacement α (QuotientGroup.mk' (center Q) x) =
      QuotientGroup.mk' (center Q) (x⁻¹ * α x) := by
    change (QuotientGroup.mk' (center Q) x)⁻¹ *
      quotientAut (center Q) α (QuotientGroup.mk' (center Q) x) = _
    rw [quotientAut_apply_mk, map_mul, map_inv]
  rwa [he, d.square_mk] at hs

end Subgroup.QuaternionCentralProductData

namespace Subgroup
variable {Q : Type*} [Group Q]

private theorem square_one_zpowers_cases {x y : Q} (hx : x ^ 2 = 1)
    (hy : y ∈ zpowers x) : y = 1 ∨ y = x := by
  by_cases hx1 : x = 1
  · simpa [hx1] using hy
  have ho : orderOf x = 2 := orderOf_eq_prime hx hx1
  have hf : IsOfFinOrder x := isOfFinOrder_iff_pow_eq_one.mpr ⟨2, by decide, hx⟩
  classical
  rw [hf.mem_zpowers_iff_mem_range_orderOf, ho] at hy
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hy
  have hn2 := Finset.mem_range.mp hn
  have hn' : n = 0 ∨ n = 1 := by omega
  rcases hn' with rfl | rfl <;> simp

private theorem invariant_four_of_displacement (α : MulAut Q) (hα : α ^ 2 = 1)
    (V : Subgroup Q) (hVα : V.map α.toMonoidHom = V)
    (x : Q) (hx : x ^ 2 = 1) (hout : x⁻¹ * α x ∉ V)
    (hsq : (x⁻¹ * α x) ^ 2 = 1) :
    ∃ D : Subgroup Q, Disjoint V D ∧ Nat.card D = 4 ∧
      IsElementaryAbelian 2 D ∧ D.map α.toMonoidHom = D := by
  have ha2 (q : Q) : α (α q) = q := by
    simpa only [pow_two, MulAut.mul_apply, MulAut.one_apply] using DFunLike.congr_fun hα q
  have hvα {v : Q} (hv : v ∈ V) : α v ∈ V :=
    hVα.le (mem_map_of_mem α.toMonoidHom hv)
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hx)
  have hy : (α x) ^ 2 = 1 := by rw [← map_pow, hx, map_one]
  have hyi : (α x)⁻¹ = α x := by rw [← map_inv, hxi]
  rw [hxi] at hout hsq
  have hc : Commute x (α x) := by
    change x * α x = α x * x
    have hi : (x * α x)⁻¹ = x * α x :=
      inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hsq)
    simpa only [mul_inv_rev, hxi, hyi] using hi.symm
  have hxout : x ∉ V := fun h => hout (V.mul_mem h (hvα h))
  have hyout : α x ∉ V := fun h => hxout (ha2 x ▸ hvα h)
  have hxne : x ≠ 1 := fun h => hxout (h ▸ V.one_mem)
  have hyne : α x ≠ 1 := fun h => hyout (h ▸ V.one_mem)
  have hxy : α x ≠ x := by
    intro h
    apply hout
    rw [h, ← pow_two, hx]
    exact V.one_mem
  have hn : α x ∈ centralizer (zpowers x : Set Q) := by
    intro y hy'
    rcases square_one_zpowers_cases hx hy' with rfl | rfl
    · simp
    · exact hc.eq
  have hnorm := centralizer_le_normalizer (zpowers x : Set Q) hn
  let D := zpowers x ⊔ zpowers (α x)
  have hdisj : Disjoint V D := by
    apply disjoint_def.mpr
    intro y hyV hyD
    have hm : y ∈ (zpowers x : Set Q) * (zpowers (α x) : Set Q) := by
      rw [← coe_mul_of_right_le_normalizer_left _ _ (zpowers_le.mpr hnorm)]
      exact hyD
    obtain ⟨b, hb, c, hc', rfl⟩ := hm
    rcases square_one_zpowers_cases hx hb with rfl | rfl <;>
      rcases square_one_zpowers_cases hy hc' with rfl | rfl
    · simp
    · exact (hyout (by simpa using hyV)).elim
    · exact (hxout (by simpa using hyV)).elim
    · exact (hout hyV).elim
  have hcard : Nat.card D = 4 := by
    rw [card_sup_zpowers_of_normalizing_involution (zpowers x) (α x) hy
      (fun h => (square_one_zpowers_cases hx h).elim hyne hxy) hnorm,
      Nat.card_zpowers, orderOf_eq_prime hx hxne]
  let : IsElementaryAbelian 2 (zpowers x) := IsElementaryAbelian.zpowers_of_pow_eq_one hx
  let : IsElementaryAbelian 2 (zpowers (α x)) := IsElementaryAbelian.zpowers_of_pow_eq_one hy
  refine ⟨D, hdisj, hcard,
    IsElementaryAbelian.sup_of_le_centralizer (zpowers_le.mpr hn), ?_⟩
  dsimp [D]
  rw [map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
  change zpowers (α x) ⊔ zpowers (α (α x)) = _
  rw [ha2, sup_comm]

end Subgroup

namespace Subgroup.QuaternionCentralProductData
variable {Q : Type*} [Group Q] [Finite Q] (d : QuaternionCentralProductData Q)

/-- A swapping involution has an invariant elementary four-group complement
to every invariant marked elementary eight on which it acts nontrivially. -/
public theorem exists_invariant_complement_of_swap (α : MulAut Q) (hα : α ^ 2 = 1)
    (hswap : d.left.map α.toMonoidHom = d.right)
    (V : Subgroup Q) [IsElementaryAbelian 2 V] (hV : Nat.card V = 8)
    (hZV : center Q ≤ V) (hVα : V.map α.toMonoidHom = V)
    (hmoved : ∃ v ∈ V, α v ≠ v) :
    ∃ D : Subgroup Q, V.IsComplement' D ∧ Nat.card D = 4 ∧
      IsElementaryAbelian 2 D ∧ D.map α.toMonoidHom = D := by
  obtain ⟨x, hx, hout⟩ := d.exists_moved_involution α hα hswap V hV hZV hmoved
  obtain ⟨D, hd, hc, he, ha⟩ := invariant_four_of_displacement α hα V hVα x hx hout
    (d.displacement_square α hα hswap x)
  refine ⟨D, isComplement'_of_card_mul_and_disjoint ?_ hd, hc, he, ha⟩
  rw [hV, hc, d.card]

end Subgroup.QuaternionCentralProductData

namespace Subgroup.QuaternionCentralProductData
variable {G : Type*} [Group G] [Finite G]

/-- Transport the invariant four-group to the ambient group with its actual
conjugation action. The centralizer marking ensures that the outside involution
acts nontrivially on V. These are precisely the core-complement inputs for
`Subgroup.isComplement_sup_zpowers_of_invariant`. -/
public theorem exists_invariant_complement_of_normalizing_involution
    (U V : Subgroup G) (d : QuaternionCentralProductData U)
    (hVU : V ≤ U) [IsElementaryAbelian 2 V] (hV : Nat.card V = 8)
    (hZV : (center U).map U.subtype ≤ V)
    (a : G) (ha : a ^ 2 = 1) (hout : a ∉ U)
    (haU : a ∈ normalizer (U : Set G)) (haV : a ∈ normalizer (V : Set G))
    (hswap : (d.left.map U.subtype).map (MulAut.conj a).toMonoidHom =
      d.right.map U.subtype)
    (hCV : centralizer (V : Set G) ≤ U) :
    ∃ D : Subgroup G, D ≤ U ∧ Disjoint V D ∧ V ⊔ D = U ∧
      Nat.card D = 4 ∧ IsElementaryAbelian 2 D ∧ a ∈ normalizer (D : Set G) := by
  let α := U.normalizerMonoidHom ⟨a, haU⟩
  have hα2 : α ^ 2 = 1 := by
    change U.normalizerMonoidHom ⟨a, haU⟩ ^ 2 = 1
    rw [← map_pow, show (⟨a, haU⟩ : normalizer (U : Set G)) ^ 2 = 1 from Subtype.ext ha,
      map_one]
  have htransport (E : Subgroup U) :
      (E.map α.toMonoidHom).map U.subtype =
        (E.map U.subtype).map (MulAut.conj a).toMonoidHom := by
    rw [map_map, map_map]
    rfl
  have hswap' : d.left.map α.toMonoidHom = d.right := by
    apply map_injective U.subtype_injective
    rw [htransport, hswap]
  let W := V.subgroupOf U
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.subgroupOf hVU
  have hW : Nat.card W = 8 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hVU).toEquiv, hV]
  have hWmap : W.map U.subtype = V := by
    rw [subgroupOf_map_subtype, inf_eq_left.mpr hVU]
  have hZW : center U ≤ W := fun z hz => hZV (mem_map_of_mem U.subtype hz)
  have hWα : W.map α.toMonoidHom = W := by
    apply map_injective U.subtype_injective
    rw [htransport, hWmap]
    exact mem_normalizer_iff_map_conj_eq.mp haV
  have hmoved : ∃ v ∈ W, α v ≠ v := by
    by_contra! h
    apply hout
    apply hCV
    intro v hv
    have he := congrArg (fun u : U => (u : G)) (h ⟨v, hVU hv⟩ hv)
    change a * v * a⁻¹ = v at he
    exact ((mul_inv_eq_iff_eq_mul).mp he).symm
  obtain ⟨D, hD, hDc, hDe, hDa⟩ := d.exists_invariant_complement_of_swap
    α hα2 hswap' W hW hZW hWα hmoved
  let := hDe
  refine ⟨D.map U.subtype, ?_, ?_, ?_, ?_, IsElementaryAbelian.map_subtype, ?_⟩
  · rintro _ ⟨u, _, rfl⟩
    exact u.property
  · rw [← hWmap]
    exact disjoint_map U.subtype_injective hD.disjoint
  · rw [← hWmap, ← map_sup, hD.sup_eq_top, ← MonoidHom.range_eq_map, U.range_subtype]
  · rw [card_map_of_injective U.subtype_injective, hDc]
  · apply mem_normalizer_iff_map_conj_eq.mpr
    change (D.map U.subtype).map (MulAut.conj a).toMonoidHom = D.map U.subtype
    rw [← htransport, hDa]

end Subgroup.QuaternionCentralProductData
