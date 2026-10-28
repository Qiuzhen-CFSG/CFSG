module

public import Theory.GroupTheory.QuaternionCentralProductResidualRecognition.SymmetricThreeSquare
public import Theory.GroupTheory.Recognition.UnitaryFourThree.Orbit
public import Theory.GroupTheory.PCoreActionSplitting
public import Theory.GroupTheory.CentralizerResidualProducts

/-!
# Constructing the U₄(3) centralizer configuration from its two-core

The characteristic-two involution centralizer has an actual quaternion
central-product two-core and quotient S₃ × S₃. Its independent cubic actors
construct the two normal SL₂(3) factors required by Hypothesis45.1. Their
join is the literal two-residual, and its embedded two-core is the original
two-core of the whole centralizer.

No factor recognition or type hypothesis is assumed. The noncentral conjugate
of the distinguished involution remains the explicit source fusion witness.
Source: Aschbacher–Smith,13.5.15–16, printed pp.920–921; Aschbacher,
Sporadic Groups (1994), Hypothesis45.1, printed p.242.
-/

@[expose] public section
open Subgroup
namespace Theory.GroupTheory.Recognition.UnitaryFourThree
variable {G : Type*} [Group G] [Finite G] {z : G}

private theorem center_of_core_is_marked_line
    (hz : orderOf z = 2)
    (d : QuaternionCentralProductData (pCore 2 (centralizer z))) :
    ((center (pCore 2 (centralizer z))).map
      ((centralizer z).subtype.comp (pCore 2 (centralizer z)).subtype)) = zpowers z := by
  let C := centralizer z
  let zC : C := ⟨z, mem_centralizer_singleton_iff.mpr rfl⟩
  have hzc : zC ∈ center C := mem_center_iff.mpr (fun a =>
    Subtype.ext (mem_centralizer_singleton_iff.mp a.property))
  have hZ : zpowers zC ≤ center C := zpowers_le.mpr hzc
  have hn : (zpowers zC).Normal := by
    constructor
    intro a ha g
    have he := mem_center_iff.mp (hZ ha) g
    simpa only [he, mul_inv_cancel_right] using ha
  have hp : IsPGroup 2 (zpowers zC) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, ← orderOf_injective C.subtype C.subtype_injective]
    exact hz)
  have hq : zC ∈ pCore 2 C := (le_sSup ⟨hn, hp⟩ : zpowers zC ≤ pCore 2 C)
    (mem_zpowers zC)
  have hle : zpowers z ≤ ((center (pCore 2 C)).map
      (C.subtype.comp (pCore 2 C).subtype)) := by
    apply zpowers_le.mpr
    refine ⟨⟨zC, hq⟩, mem_center_iff.mpr ?_, rfl⟩
    intro a
    apply Subtype.ext
    exact mem_center_iff.mp hzc a
  apply (eq_of_le_of_card_ge hle ?_).symm
  have hinj : Function.Injective (C.subtype.comp (pCore 2 C).subtype) := by
    intro a b hab
    exact (pCore 2 C).subtype_injective (C.subtype_injective hab)
  rw [card_map_of_injective hinj, d.center_card, Nat.card_zpowers, hz]

/-- The two SL₂(3) factors are constructed in the original involution
centralizer; the residual two-core is also identified with its original core. -/
theorem factors_of_quaternion_core
    (hz : orderOf z = 2)
    (d : QuaternionCentralProductData (pCore 2 (centralizer z)))
    (hc : generalizedFitting (centralizer z) = pCore 2 (centralizer z))
    (e : ((centralizer z) ⧸ pCore 2 (centralizer z)) ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) :
    Nonempty (Factors z) ∧ core z = (centralizer z).pCoreIn 2 := by
  let C := centralizer z
  let Q := pCore 2 C
  have hself : Subgroup.centralizer (Q : Set C) ≤ Q := by
    change Subgroup.centralizer (pCore 2 (centralizer z) : Set (centralizer z)) ≤
      pCore 2 (centralizer z)
    rw [← hc]
    exact centralizer_generalizedFitting_le C
  obtain ⟨c⟩ := quaternion_residual_central_product_of_symmetricThree_square Q d rfl hself e
  let L := c.left.map C.subtype
  let R := c.right.map C.subtype
  have hspan : L ⊔ R = residual z := by
    rw [← Subgroup.map_sup, c.span]
    rfl
  have hcomm : ∀ l ∈ L, ∀ r ∈ R, l * r = r * l := by
    rintro _ ⟨l, hl, rfl⟩ _ ⟨r, hr, rfl⟩
    exact congrArg Subtype.val (c.commute l hl r hr)
  have hnL : residual z ≤ normalizer (L : Set G) := by
    rw [← hspan]
    exact sup_le L.le_normalizer
      ((show R ≤ Subgroup.centralizer (L : Set G) from
        fun r hr l hl => hcomm l hl r hr).trans (centralizer_le_normalizer _))
  have hnR : residual z ≤ normalizer (R : Set G) := by
    rw [← hspan]
    exact sup_le
      ((show L ≤ Subgroup.centralizer (R : Set G) from
        fun l hl r hr => (hcomm l hl r hr).symm).trans (centralizer_le_normalizer _))
      R.le_normalizer
  have hinter : L ⊓ R = zpowers z := by
    rw [← map_inf _ _ C.subtype C.subtype_injective, c.intersection, map_map]
    exact center_of_core_is_marked_line hz d
  have hQres : Q ≤ pResidual 2 C := by
    have hj : d.left.map Q.subtype ⊔ d.right.map Q.subtype = Q := by
      rw [← Subgroup.map_sup, d.span, ← MonoidHom.range_eq_map, range_subtype]
    rw [← hj, ← c.span]
    exact sup_le_sup c.left_contains c.right_contains
  have hcore : core z = C.pCoreIn 2 := by
    change ((pResidual 2 C).map C.subtype).pCoreIn 2 = (pCore 2 C).map C.subtype
    rw [← map_pCoreIn_of_injective 2 (pResidual 2 C) C.subtype C.subtype_injective,
      ← pCore_eq_map_of_normal_of_le 2 (pResidual 2 C) hQres]
  exact ⟨⟨{
    left := L
    right := R
    span := hspan
    normal_left := normal_subgroupOf_of_le_normalizer hnL
    normal_right := normal_subgroupOf_of_le_normalizer hnR
    left_model := ⟨(c.left.equivMapOfInjective C.subtype C.subtype_injective).symm.trans
      c.left_model.some⟩
    right_model := ⟨(c.right.equivMapOfInjective C.subtype C.subtype_injective).symm.trans
      c.right_model.some⟩
    intersection := hinter }⟩, hcore⟩

/-- Construct every field of Hypothesis45.1 from the actual core and quotient.
The explicit fusion witness is on that core in the original ambient group. -/
theorem centralizerHypothesis_of_quaternion_core
    (hz : orderOf z = 2)
    (d : QuaternionCentralProductData (pCore 2 (centralizer z)))
    (hc : generalizedFitting (centralizer z) = pCore 2 (centralizer z))
    (e : ((centralizer z) ⧸ pCore 2 (centralizer z)) ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))
    (hfused : ∃ g : G, g⁻¹ * z * g ∈ (centralizer z).pCoreIn 2 ∧
      g⁻¹ * z * g ∉ zpowers z) :
    CentralizerHypothesis z := by
  obtain ⟨⟨f⟩, hcore⟩ := factors_of_quaternion_core hz d hc e
  refine {
    involution := hz
    factors := ⟨f.left, f.right, f.span, f.normal_left, f.normal_right,
      f.left_model, f.right_model, f.intersection⟩
    generalizedFitting_eq := ?_
    fused := ?_ }
  · rw [hc, hcore]
    rfl
  · simpa only [hcore] using hfused

/-- Residual transitivity on the noncentral core involutions propagates the
single source intersection to every conjugate required in the type definition. -/
theorem CentralizerHypothesis.isType_of_one_intersection
    (h : CentralizerHypothesis z)
    (hcard : Nat.card (centralizer z) = 2 ^ 7 * 3 ^ 2)
    (y : G) (hy : y⁻¹ * z * y ∈ core z) (hyZ : y⁻¹ * z * y ∉ zpowers z)
    (hpair : Nat.card (core z ⊓ conjugate (core z) y : Subgroup G) = 4) :
    IsType z := by
  refine { toCentralizerHypothesis := h
           centralizer_card := hcard
           intersection_card := ?_ }
  intro g hg hgZ
  have ho (a : G) : orderOf (a⁻¹ * z * a) = 2 := by
    simpa only [MulAut.conj_apply, inv_inv] using
      ((MulAut.conj a⁻¹).orderOf_eq z).trans h.involution
  obtain ⟨k, hk, hkg⟩ := h.core_involution_orbit _ _ hg hy (ho g) (ho y) hgZ hyZ
  let e := MulAut.conj k
  have hek : e z = z := by
    change k * z * k⁻¹ = z
    have hh := mem_centralizer_singleton_iff.mp
      ((map_subtype_le _ : residual z ≤ centralizer z) hk)
    rw [hh, mul_inv_cancel_right]
  have hmap (a : G) : (core a).map e.toMonoidHom = core (e a) :=
    Theory.GroupTheory.map_centralizerResidualCore e a
  have hconj (a : G) : conjugate (core z) a = core (a⁻¹ * z * a) := by
    have hh : conjugate (core z) a = core ((MulAut.conj a⁻¹) z) :=
      Theory.GroupTheory.map_centralizerResidualCore (MulAut.conj a⁻¹) z
    have he : (MulAut.conj a⁻¹) z = a⁻¹ * z * a := by
      simp only [MulAut.conj_apply, inv_inv]
    rw [he] at hh
    exact hh
  have hleft : (core z).map e.toMonoidHom = core z := by rw [hmap, hek]
  have hright : (conjugate (core z) g).map e.toMonoidHom = conjugate (core z) y := by
    rw [hconj, hmap]
    change core (k * (g⁻¹ * z * g) * k⁻¹) = conjugate (core z) y
    rw [hkg, hconj]
  calc
    Nat.card (core z ⊓ conjugate (core z) g : Subgroup G) =
        Nat.card ((core z ⊓ conjugate (core z) g).map e.toMonoidHom) :=
      (card_map_of_injective e.injective).symm
    _ = 4 := by rw [map_inf _ _ _ e.injective, hleft, hright]; exact hpair

/-- The original quaternion two-core, characteristic-two centralizer,
symmetric-three-square quotient and one marked returning intersection
construct the full Asc94 type. No type or factor-recognition premise remains. -/
theorem isType_of_quaternion_core_and_one_intersection
    (hz : orderOf z = 2)
    (d : QuaternionCentralProductData (pCore 2 (centralizer z)))
    (hc : generalizedFitting (centralizer z) = pCore 2 (centralizer z))
    (e : ((centralizer z) ⧸ pCore 2 (centralizer z)) ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))
    (y : G) (hy : y⁻¹ * z * y ∈ (centralizer z).pCoreIn 2)
    (hyZ : y⁻¹ * z * y ∉ zpowers z)
    (hpair : Nat.card ((centralizer z).pCoreIn 2 ⊓
      conjugate ((centralizer z).pCoreIn 2) y : Subgroup G) = 4) :
    IsType z := by
  have h := centralizerHypothesis_of_quaternion_core hz d hc e ⟨y, hy, hyZ⟩
  have hcore := (factors_of_quaternion_core hz d hc e).2
  have hcard : Nat.card (centralizer z) = 2 ^ 7 * 3 ^ 2 :=
    card_eq_1152_of_quaternion_product_quotient_symmetricThree_square _ d e
  apply h.isType_of_one_intersection hcard y
  · rwa [hcore]
  · exact hyZ
  · simpa only [hcore] using hpair

end Theory.GroupTheory.Recognition.UnitaryFourThree
end
