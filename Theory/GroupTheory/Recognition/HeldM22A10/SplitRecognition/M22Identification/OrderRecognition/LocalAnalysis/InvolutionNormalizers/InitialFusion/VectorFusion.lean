module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.InitialFusion.VectorFusion.Coordinates


/-!
# Janko's elementary-subgroup fusion lemma

Suppose the distinguished involution is conjugate to printed z₂. Every such
conjugator normalizes E: pull E back to the centralizer model, where the
order-three actor c rules out the alternative elementary sixteen F.

The local vector classes have sizes 1, 8 and 6. Both z₃ and z₁z₃ lie in the
last class, while their product is z₁. Conjugating this product to z₂ and
using the coordinate multiplication obstruction joins the last class to
the first two. Thus all nonidentity elements of E are conjugate in G.

This proves the full conclusion of Z. Janko, *A characterization of the
Mathieu simple groups, I*, J. Algebra 9 (1968), Section 2, Lemma 4, p.5,
by an alternative argument using the actual normalizer. Simplicity is
unnecessary for this implication. Source subscripts are one-based;
printed z₂ is `CaseII.z 1`.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.M22Identification
open LocalModelDichotomy

universe u
namespace CaseII
variable {G : Type u} [Group G]

private theorem modelE_image_of_order_three_normalizer
    (f : TwistedModel →* G) (hf : Function.Injective f)
    (A : Subgroup G) (hA : IsElementaryAbelian 2 A) (hcard : Nat.card A = 16)
    (hArange : A ≤ f.range) (r : TwistedModel) (hr : orderOf r = 3)
    (hn : f r ∈ normalizer (A : Set G)) : modelE.map f = A := by
  let B := A.comap f
  have hmap : B.map f = A := map_comap_eq_self hArange
  have hBc : Nat.card B = 16 := by
    rw [Nat.card_congr (B.equivMapOfInjective f hf).toEquiv, hmap, hcard]
  have hBe : IsElementaryAbelian 2 B := by
    have hs (x : B) : x ^ 2 = 1 := by
      apply Subtype.ext
      apply hf
      let := hA
      simpa only [Subgroup.coe_pow, Subgroup.coe_one, map_pow, map_one] using
        elemPow_eq_one_of_isElementaryAbelian (p := 2) (f x) x.property
    refine
      { is_comm := ?_
        exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hs }
    exact ⟨fun x y => (Commute.of_orderOf_dvd_two
      (fun x => orderOf_dvd_of_pow_eq_one (hs x)) x y).eq⟩
  have hrN : r ∈ normalizer (B : Set TwistedModel) :=
    le_normalizer_comap f hn
  rw [← model_elementary_sixteen_of_order_three_normalizer B hBe hBc r hr hrN]
  exact hmap

variable (D : LocalData G) (k : TwistedModel ≃* D.centralizer)

private theorem into_normalizes_E (x : TwistedModel) :
    into D k x ∈ normalizer (E D k : Set G) := by
  rw [← modelE_map D k]
  apply le_normalizer_map _
  apply mem_map_of_mem
  let : modelE.Normal := by unfold modelE; infer_instance
  rw [normalizer_eq_top]
  trivial

/-- Every conjugator from the marked involution to printed z₂ normalizes E. -/
public theorem z_one_conjugator_normalizes_E (g : G)
    (hg : g * D.z * g⁻¹ = into D k (z 1)) :
    g ∈ normalizer (E D k : Set G) := by
  let f : TwistedModel →* G := (MulAut.conj g).toMonoidHom.comp (into D k)
  have hf : Function.Injective f := (MulAut.conj g).injective.comp (into_injective D k)
  have hrange : ∀ x : G, x * into D k (z 1) = into D k (z 1) * x → x ∈ f.range := by
    intro x hx
    have hc : (MulAut.conj g).symm x ∈ D.centralizer := by
      apply mem_centralizer_singleton_iff.mpr
      apply (MulAut.conj g).injective
      simpa only [map_mul, MulEquiv.apply_symm_apply, MulAut.conj_apply, hg] using hx
    obtain ⟨v, hv⟩ := k.surjective ⟨(MulAut.conj g).symm x, hc⟩
    refine ⟨v, ?_⟩
    change (MulAut.conj g) (into D k v) = x
    rw [show into D k v = (MulAut.conj g).symm x from congrArg Subtype.val hv]
    exact (MulAut.conj g).apply_symm_apply x
  have hErange : E D k ≤ f.range := by
    intro x hx
    apply hrange
    let := E_elementary D k
    exact setLike_mul_comm hx (by
      rw [← modelE_map D k]
      exact mem_map_of_mem _ (z_mem_modelE 1))
  have hc : into D k c ∈ f.range := by
    apply hrange
    have h : c * z 1 = z 1 * c := by
      have hc := conjugation_c 1
      simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at hc
      calc
        c * z 1 = c * (c⁻¹ * z 1 * c) := congrArg (c * ·) hc.symm
        _ = z 1 * c := by group
    simpa only [map_mul] using congrArg (into D k) h
  obtain ⟨r, hr⟩ := hc
  have hr3 : orderOf r = 3 := by
    rw [← orderOf_injective f hf, hr]
    rw [orderOf_injective (into D k) (into_injective D k)]
    exact actor_orders.2.2.1
  have he := modelE_image_of_order_three_normalizer f hf (E D k)
    (E_elementary D k) (E_card D k) hErange r hr3 (hr ▸ into_normalizes_E D k c)
  apply mem_normalizer_iff_map_conj_eq.mpr
  rw [← modelE_map D k, map_map]
  exact he.trans (modelE_map D k).symm

variable [Finite G]

private theorem z_two_fusion_of_normalizing_conjugator
    (g : G) (hgN : g ∈ normalizer (E D k : Set G))
    (hg : g * D.z * g⁻¹ = into D k (z 1)) :
    IsConj D.z (into D k (z 2)) := by
  have hmem (v : TwistedModel) (hv : v ∈ modelE) :
      into D k v ∈ E D k := by
    rw [← modelE_map D k]
    exact mem_map_of_mem _ hv
  have hconjmem (v : TwistedModel) (hv : v ∈ modelE) :
      g * into D k v * g⁻¹ ∈ modelE.map (into D k) := by
    rw [modelE_map D k]
    exact (mem_normalizer_iff.mp hgN _).mp (hmem v hv)
  obtain ⟨x, hx, hxg⟩ := hconjmem (z 2) (z_mem_modelE 2)
  obtain ⟨y, hy, hyg⟩ := hconjmem (z 0 * z 2)
    (modelE.mul_mem (z_mem_modelE 0) (z_mem_modelE 2))
  have hxC : IsConj (into D k x) (into D k (z 2)) :=
    (isConj_iff.mpr ⟨g, hxg.symm⟩).symm
  have hyC : IsConj (into D k y) (into D k (z 2)) :=
    (isConj_iff.mpr ⟨g, hyg.symm⟩).symm.trans
      ((into D k).map_isConj z_zero_mul_z_two_conj)
  have hne (v : TwistedModel) (hv : IsConj (into D k v) (into D k (z 2))) : v ≠ 1 := by
    intro he
    obtain ⟨t, ht⟩ := isConj_iff.mp hv
    rw [he, map_one, mul_one, mul_inv_cancel] at ht
    have hv1 : z 2 = 1 := into_injective D k (ht.symm.trans (map_one _).symm)
    have ho := z_order 2
    simp [hv1] at ho
  have hxy : x * y = z 1 := by
    apply into_injective D k
    rw [map_mul, hxg, hyg, map_mul, into_z_zero D k]
    have hs : into D k (z 2) * into D k (z 2) = 1 := by
      rw [← pow_two, ← map_pow]
      have h2 : z 2 ^ 2 = 1 := by simpa only [z_order 2] using pow_orderOf_eq_one (z 2)
      rw [h2, map_one]
    have hc : into D k (z 2) * D.z = D.z * into D k (z 2) :=
      mem_centralizer_singleton_iff.mp (k (z 2)).property
    calc
      g * into D k (z 2) * g⁻¹ * (g * (D.z * into D k (z 2)) * g⁻¹) =
          g * (into D k (z 2) * D.z * into D k (z 2)) * g⁻¹ := by group
      _ = g * D.z * g⁻¹ := by rw [hc, mul_assoc D.z, hs, mul_one]
      _ = into D k (z 1) := hg
  have h01 : IsConj D.z (into D k (z 1)) := isConj_iff.mpr ⟨g, hg⟩
  have finish (v : TwistedModel) (hv : IsConj (into D k v) (into D k (z 2)))
      (hlocal : IsConj v (z 0) ∨ IsConj v (z 1)) : IsConj D.z (into D k (z 2)) := by
    rcases hlocal with h0 | h1
    · have hh := (into D k).map_isConj h0
      rw [into_z_zero D k] at hh
      exact hh.symm.trans hv
    · exact h01.trans (((into D k).map_isConj h1).symm.trans hv)
  rcases modelE_product_z_one x y hx hy (hne x hxC) (hne y hyC) hxy with h | h | h | h
  · exact finish x hxC (Or.inl h)
  · exact finish x hxC (Or.inr h)
  · exact finish y hyC (Or.inl h)
  · exact finish y hyC (Or.inr h)

end CaseII

/-- Janko's Lemma 4: fusion with printed z₂ fuses every nonidentity vector in E.
The conjugator normalizes E, and the multiplication of the three local
vector classes forces fusion with printed z₃. -/
public theorem elementary_fusion_of_z_one_fusion
    {G : Type u} [Group G] [Finite G] (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer)
    (h : IsConj D.z (CaseII.into D k (CaseII.z 1))) :
    ∀ x y : CaseII.E D k, x ≠ 1 → y ≠ 1 → IsConj (x : G) (y : G) := by
  obtain ⟨g, hg⟩ := isConj_iff.mp h
  have h02 := CaseII.z_two_fusion_of_normalizing_conjugator D k g
    (CaseII.z_one_conjugator_normalizes_E D k g hg) hg
  have hall (x : CaseII.E D k) (hx : x ≠ 1) : IsConj (x : G) D.z := by
    have hxE := x.property
    have hxmap : (x : G) ∈ CaseII.modelE.map (CaseII.into D k) := by
      simpa only [CaseII.modelE_map D k] using hxE
    obtain ⟨v, hv, hvx⟩ := hxmap
    have hv1 : v ≠ 1 := by
      intro he
      apply hx
      apply Subtype.ext
      rw [← hvx, he, map_one]
      rfl
    rcases CaseII.modelE_three_classes v hv hv1 with h0 | h1 | h2
    · simpa only [hvx, CaseII.into_z_zero D k] using (CaseII.into D k).map_isConj h0
    · exact (hvx ▸ (CaseII.into D k).map_isConj h1).trans h.symm
    · exact (hvx ▸ (CaseII.into D k).map_isConj h2).trans h02.symm
  exact fun x y hx hy => (hall x hx).trans (hall y hy).symm

end Theory.GroupTheory.HeldM22A10.M22Identification
