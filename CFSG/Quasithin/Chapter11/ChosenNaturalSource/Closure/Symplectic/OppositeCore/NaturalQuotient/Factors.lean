module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.OppositeCore.NaturalQuotient.Elementary
public import Mathlib.GroupTheory.NoncommCoprod

/-!
# The two actual factors of the opposite-core quotient

The complementary lifted subspaces of V show that
(WV) ∩ (WʸV) = (W ∩ Wʸ)V. No disjointness of the lifted preimages is
required. After restriction to Q, the two factors generate Q and intersect
in N. Their images in the literal elementary quotient Q/N are complementary,
and multiplication gives the displayed direct-product isomorphism.

This is a decomposition of the underlying elementary group. Its fixed-space
identification and recognition as natural modules for the induced I-action
remain separate assertions.
Source: Aschbacher--Smith 11.5.7, printed p.783.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise commutatorElement IsMulCommutative

private theorem intersection_mod_seed {G : Type*} [Group G]
    (W Z V C D : Subgroup G)
    (hWV : W ≤ normalizer (V : Set G)) (hZV : Z ≤ normalizer (V : Set G))
    (hC : C ≤ W) (hD : D ≤ Z) (hsplit : V = C ⊔ D)
    (hCD : C ≤ normalizer (D : Set G)) :
    (W ⊔ V) ⊓ (Z ⊔ V) = (W ⊓ Z) ⊔ V := by
  apply le_antisymm _ (sup_le (le_inf (inf_le_left.trans le_sup_left)
    (inf_le_right.trans le_sup_left)) (le_inf le_sup_right le_sup_right))
  intro x hx
  have hleft : x ∈ (W : Set G) * (V : Set G) := by
    rw [← coe_mul_of_left_le_normalizer_right W V hWV]
    exact hx.1
  have hright : x ∈ (V : Set G) * (Z : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left V Z hZV, sup_comm]
    exact hx.2
  obtain ⟨w, hw, v, hv, hwv⟩ := hleft
  obtain ⟨u, hu, z, hz, huz⟩ := hright
  have hVprod : (V : Set G) = (C : Set G) * (D : Set G) := by
    rw [hsplit, coe_mul_of_left_le_normalizer_right C D hCD]
  rw [hVprod] at hv hu
  obtain ⟨c, hc, d, hd, rfl⟩ := hv
  obtain ⟨c', hc', d', hd', rfl⟩ := hu
  have hEq : c'⁻¹ * (w * c) = (d' * z) * d⁻¹ := by
    have hh : w * (c * d) = (c' * d') * z := hwv.trans huz.symm
    calc
      c'⁻¹ * (w * c) = c'⁻¹ * (w * (c * d)) * d⁻¹ := by group
      _ = c'⁻¹ * ((c' * d') * z) * d⁻¹ := by rw [hh]
      _ = (d' * z) * d⁻¹ := by group
  have hj : c'⁻¹ * (w * c) ∈ W ⊓ Z := by
    refine ⟨W.mul_mem (W.inv_mem (hC hc')) (W.mul_mem hw (hC hc)), ?_⟩
    rw [hEq]
    exact Z.mul_mem (Z.mul_mem (hD hd') hz) (Z.inv_mem (hD hd))
  have hcV : c' ∈ V := hsplit.ge (mem_sup_left hc')
  have hdV : d ∈ V := hsplit.ge (mem_sup_right hd)
  have hh := ((W ⊓ Z) ⊔ V).mul_mem
    (((W ⊓ Z) ⊔ V).mul_mem (mem_sup_right hcV) (mem_sup_left hj))
    (mem_sup_right hdV)
  have he : c' * (c'⁻¹ * (w * c)) * d = x := by
    simpa only [mul_inv_cancel_left, mul_assoc] using hwv
  exact he ▸ hh

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.NaturalQuotient
open CFSG.Quasithin.Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (E : Geometry D)

/-- The lifted opposite factors intersect precisely in the source denominator. -/
theorem opposite_factors_intersection (m : MarkedFlag E) {y : G} (hy : y ∈ L)
    (hW : E.W ≤ E.G₁.pCoreIn 2)
    (hsplit : V = E.V₃ ⊔ E.V₁.map (MulAut.conj y).toMonoidHom) :
    (auxiliaryW E ⊔ V) ⊓ ((auxiliaryW E).map (MulAut.conj y).toMonoidHom ⊔ V) =
      pairDenominator E y := by
  let : IsElementaryAbelian 2 V := D.elementary
  have hn := oppositeJoin_normalizes_seed E m hy hW
  have hCD : E.V₃ ≤ normalizer (E.V₁.map (MulAut.conj y).toMonoidHom : Set G) := by
    apply le_normalizer_iff.mpr
    intro c hc d hd
    have hcV : c ∈ V := hsplit.ge (mem_sup_left hc)
    have hdV : d ∈ V := hsplit.ge (mem_sup_right hd)
    have hcomm : c * d = d * c :=
      congrArg Subtype.val (@mul_comm V _ ⟨c,hcV⟩ ⟨d,hdV⟩)
    simpa only [hcomm, mul_assoc, mul_inv_cancel, mul_one] using hd
  exact intersection_mod_seed _ _ _ _ _ (le_sup_left.trans hn) (le_sup_right.trans hn)
    (threeSpace_le_auxiliaryW E)
    (map_mono (m.point_lt_threeSpace.le.trans (threeSpace_le_auxiliaryW E))) hsplit hCD

private theorem quotient_complements {H : Type*} [Group H]
    (A B N : Subgroup H) [N.Normal] (hgen : A ⊔ B = ⊤) (hint : A ⊓ B = N) :
    IsCompl (A.map (QuotientGroup.mk' N)) (B.map (QuotientGroup.mk' N)) := by
  have hnA : (QuotientGroup.mk' N).ker ≤ A := by
    rw [QuotientGroup.ker_mk', ← hint]
    exact inf_le_left
  have hnB : (QuotientGroup.mk' N).ker ≤ B := by
    rw [QuotientGroup.ker_mk', ← hint]
    exact inf_le_right
  constructor
  · rw [disjoint_iff]
    apply Subgroup.comap_injective (QuotientGroup.mk'_surjective N)
    rw [comap_inf, comap_map_eq_self hnA, comap_map_eq_self hnB,
      MonoidHom.comap_bot, QuotientGroup.ker_mk', hint]
  · rw [codisjoint_iff, ← Subgroup.map_sup, hgen,
      map_top_of_surjective _ (QuotientGroup.mk'_surjective N)]

/-- The literal images of WV∩Q and WʸV∩Q are complementary in Q/N. -/
theorem quotient_factors_complementary (m : MarkedFlag E) {y : G} (hy : y ∈ L)
    (hW : E.W ≤ E.G₁.pCoreIn 2)
    (hPhi : (frattini (auxiliaryW E)).map (auxiliaryW E).subtype ≤ E.V₁)
    (hsplit : V = E.V₃ ⊔ E.V₁.map (MulAut.conj y).toMonoidHom) :
    let Q := corePair (auxiliaryW E) y
    let N := pairDenominator E y
    let _ := denominator_normal_in_corePair E m hy hW hPhi
    let π := QuotientGroup.mk' (N.subgroupOf Q)
    IsCompl ((((auxiliaryW E ⊔ V) ⊓ Q).subgroupOf Q).map π)
      (((((auxiliaryW E).map (MulAut.conj y).toMonoidHom ⊔ V) ⊓ Q).subgroupOf Q).map π) := by
  let Q := corePair (auxiliaryW E) y
  let N := pairDenominator E y
  let A := (auxiliaryW E ⊔ V) ⊓ Q
  let B := ((auxiliaryW E).map (MulAut.conj y).toMonoidHom ⊔ V) ⊓ Q
  let _ := denominator_normal_in_corePair E m hy hW hPhi
  have hNQ : N ≤ Q := denominator_le_corePair E m hy hW hPhi hsplit
  have hgen : A ⊔ B = Q := by
    apply le_antisymm (sup_le inf_le_right inf_le_right)
    apply sup_le
    · exact (le_inf (inf_le_left.trans le_sup_left) le_sup_left).trans le_sup_left
    · exact (le_inf (inf_le_left.trans le_sup_left) le_sup_right).trans le_sup_right
  have hint : A ⊓ B = N := by
    apply le_antisymm
    · exact (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)).trans
        (opposite_factors_intersection E m hy hW hsplit).le
    · have hh := (opposite_factors_intersection E m hy hW hsplit).ge
      exact le_inf (le_inf (hh.trans inf_le_left) hNQ)
        (le_inf (hh.trans inf_le_right) hNQ)
  apply quotient_complements
  · rw [← subgroupOf_sup (show A ≤ Q from inf_le_right) (show B ≤ Q from inf_le_right),
      hgen, subgroupOf_self]
  · change A.comap Q.subtype ⊓ B.comap Q.subtype = N.comap Q.subtype
    rw [← comap_inf, hint]

private theorem product_of_complements {H : Type*} [CommGroup H]
    (A B : Subgroup H) (h : IsCompl A B) :
    ∃ e : H ≃* A × B, ∀ a : A, ∀ b : B, e.symm (a,b) = (a : H) * b := by
  let comm : ∀ a : A, ∀ b : B, Commute (a : H) (b : H) :=
    fun a b => Commute.all (a : H) (b : H)
  let f := A.subtype.noncommCoprod B.subtype comm
  have hf : Function.Injective f := by
    apply (MonoidHom.noncommCoprod_injective _ _ _).mpr
    simpa using And.intro A.subtype_injective (And.intro B.subtype_injective h.disjoint)
  have hr : f.range = ⊤ := by
    exact (MonoidHom.noncommCoprod_range A.subtype B.subtype comm).trans
      (by simpa using h.codisjoint.eq_top)
  exact ⟨(MulEquiv.ofBijective f ⟨hf, MonoidHom.range_eq_top.mp hr⟩).symm, fun _ _ => rfl⟩

/-- The source two-factor decomposition, with inverse given by multiplication. -/
theorem quotient_two_factor_decomposition (m : MarkedFlag E) {y : G} (hy : y ∈ L)
    (hW : E.W ≤ E.G₁.pCoreIn 2)
    (hPhi : (frattini (auxiliaryW E)).map (auxiliaryW E).subtype ≤ E.V₁)
    (hsplit : V = E.V₃ ⊔ E.V₁.map (MulAut.conj y).toMonoidHom)
    (hcore : (oppositeJoin (auxiliaryW E) y).pCoreIn 2 ≤
      (L ⊔ (T : Subgroup G)).pCoreIn 2) :
    let Q := corePair (auxiliaryW E) y
    let N := pairDenominator E y
    let _ := denominator_normal_in_corePair E m hy hW hPhi
    let π := QuotientGroup.mk' (N.subgroupOf Q)
    let A := (((auxiliaryW E ⊔ V) ⊓ Q).subgroupOf Q).map π
    let B := ((((auxiliaryW E).map (MulAut.conj y).toMonoidHom ⊔ V) ⊓ Q).subgroupOf Q).map π
    ∃ e : (Q ⧸ N.subgroupOf Q) ≃* A × B,
      ∀ a : A, ∀ b : B, e.symm (a,b) = (a : Q ⧸ N.subgroupOf Q) * b := by
  let _ := denominator_normal_in_corePair E m hy hW hPhi
  let := quotient_elementary E m hy hW hPhi hcore
  exact product_of_complements _ _ (quotient_factors_complementary E m hy hW hPhi hsplit)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.NaturalQuotient
