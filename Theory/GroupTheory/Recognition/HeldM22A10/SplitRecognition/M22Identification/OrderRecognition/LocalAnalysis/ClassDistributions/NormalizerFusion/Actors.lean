module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.Contracts
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.Elementary

/-!
# Conjugating the two actors inside the elementary normalizer

The images of `a` and `d` in `N(E)/E ≃ A₆` are nontrivial involutions,
hence conjugate. Every involution in the coset `Ed` is conjugate to `d`
by an element of `E`, as checked in the original Case II coordinates.
Thus quotient conjugacy lifts to a genuine conjugator in the actual `N(E)`.
No marking of an arbitrary complement is required.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 5, pp.9–10.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.M22Identification
open LocalModelDichotomy
namespace CaseII.Distribution

private theorem alternating_six_involutions_conjugate
    (s t : alternatingGroup (Fin 6))
    (hs : s ^ 2 = 1) (hs1 : s ≠ 1) (ht : t ^ 2 = 1) (ht1 : t ≠ 1) :
    IsConj s t := by
  have h : ∀ s : alternatingGroup (Fin 6), s ^ 2 = 1 → s ≠ 1 →
      (s : Equiv.Perm (Fin 6)).cycleType = {2, 2} ∧
      (s : Equiv.Perm (Fin 6)).support.card + 2 ≤ 6 := by decide +kernel
  exact alternatingGroup.isConj_of
    (Equiv.Perm.isConj_iff_cycleType_eq.mpr ((h s hs hs1).1.trans (h t ht ht1).1.symm))
    (h s hs hs1).2

local instance : DecidableEq TwistedModel := fun x y =>
  decidable_of_iff (x.left = y.left ∧ x.right = y.right) SemidirectProduct.ext_iff.symm
local instance : Fintype TwistedModel := Fintype.ofEquiv
  (BinaryFour × SymmetricFour) SemidirectProduct.equivProd.symm

private theorem involutions_in_Ed : ∀ x : TwistedModel,
    x.right = d.right → x ^ 2 = 1 →
    ∃ v : BinaryFour, SemidirectProduct.inl v * x * (SemidirectProduct.inl v)⁻¹ = d := by
  decide +kernel

universe u
variable {G : Type u} [Group G] (D : LocalData G)
  (k : TwistedModel ≃* D.centralizer)

private theorem into_mem_normalizerE (x : TwistedModel) :
    into D k x ∈ normalizer (E D k : Set G) := by
  rw [← modelE_map D k]
  have : modelE.Normal := by unfold modelE; infer_instance
  exact (le_normalizer_map (into D k)) (mem_map_of_mem _ (le_normalizer_of_normal (mem_top x)))

private theorem into_mem_E_iff (x : TwistedModel) :
    into D k x ∈ E D k ↔ x.right = 1 := by
  rw [← modelE_map D k, mem_map]
  constructor
  · rintro ⟨y, hy, he⟩
    have hxy : y = x := into_injective D k he
    subst y
    exact hy
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- The two source actors are conjugate in the actual normalizer of `E`.
Only the genuine relative `A₆` complement is used. -/
public theorem normalizer_a_d_conjugate
    (hE : ∃ K : Subgroup (normalizer (E D k : Set G)),
      ((E D k).subgroupOf (normalizer (E D k : Set G))).IsComplement' K ∧
        Nonempty (K ≃* alternatingGroup (Fin 6))) :
    ∃ n : G, n ∈ normalizer (E D k : Set G) ∧
      (MulAut.conj n) (into D k a) = into D k d := by
  let N := normalizer (E D k : Set G)
  let B := (E D k).subgroupOf N
  let aN : N := ⟨into D k a, into_mem_normalizerE D k a⟩
  let dN : N := ⟨into D k d, into_mem_normalizerE D k d⟩
  have ha2 : aN ^ 2 = 1 := by
    apply Subtype.ext
    change (into D k a) ^ 2 = 1
    rw [← map_pow, show a ^ 2 = 1 from by decide +kernel, map_one]
  have hd2 : dN ^ 2 = 1 := by
    apply Subtype.ext
    change (into D k d) ^ 2 = 1
    rw [← map_pow, show d ^ 2 = 1 from by decide +kernel, map_one]
  have haB : aN ∉ B := by
    intro h
    have h' := (into_mem_E_iff D k a).mp h
    have hn : a.right ≠ 1 := by decide +kernel
    exact hn h'
  have hdB : dN ∉ B := by
    intro h
    have h' := (into_mem_E_iff D k d).mp h
    have hn : d.right ≠ 1 := by decide +kernel
    exact hn h'
  obtain ⟨K, hK, ⟨eK⟩⟩ := hE
  let e : N ⧸ B ≃* alternatingGroup (Fin 6) := hK.symm.QuotientMulEquiv.trans eK
  let q : N →* N ⧸ B := QuotientGroup.mk' B
  have hqa : q aN ≠ 1 := fun h => haB ((QuotientGroup.eq_one_iff aN).mp h)
  have hqd : q dN ≠ 1 := fun h => hdB ((QuotientGroup.eq_one_iff dN).mp h)
  have hc : IsConj (e (q aN)) (e (q dN)) :=
    alternating_six_involutions_conjugate _ _
      (by rw [← map_pow, ← map_pow, ha2, map_one, map_one])
      (fun h => hqa (e.injective (h.trans e.map_one.symm)))
      (by rw [← map_pow, ← map_pow, hd2, map_one, map_one])
      (fun h => hqd (e.injective (h.trans e.map_one.symm)))
  have hcq : IsConj (q aN) (q dN) := by
    simpa only [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] using
      e.symm.toMonoidHom.map_isConj hc
  obtain ⟨u, hu⟩ := isConj_iff.mp hcq
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective u
  have hgq : q (g * aN * g⁻¹) = q dN := by
    simpa only [map_mul, map_inv, show q g = u from hg] using hu
  have hvB : (g * aN * g⁻¹) / dN ∈ B := QuotientGroup.eq_iff_div_mem.mp hgq
  have hvE : ((g : G) * into D k a * (g : G)⁻¹) / into D k d ∈ E D k := hvB
  rw [← modelE_map D k] at hvE
  obtain ⟨v, hv, he⟩ := hvE
  let x := v * d
  have hxg : into D k x = (g : G) * into D k a * (g : G)⁻¹ := by
    simp only [x, map_mul, he, div_mul_cancel]
  have hxr : x.right = d.right := by
    change v.right * d.right = d.right
    change v.right = 1 at hv
    rw [hv, one_mul]
  have hx2 : x ^ 2 = 1 := by
    apply into_injective D k
    rw [map_pow, hxg, map_one]
    have haG : (into D k a) ^ 2 = 1 := congrArg Subtype.val ha2
    calc
      ((g : G) * into D k a * (g : G)⁻¹) ^ 2 =
          (g : G) * (into D k a) ^ 2 * (g : G)⁻¹ :=
            (map_pow (MulAut.conj (g : G)) _ _).symm
      _ = 1 := by rw [haG]; group
  obtain ⟨v', hv'⟩ := involutions_in_Ed x hxr hx2
  refine ⟨into D k (SemidirectProduct.inl v') * (g : G),
    N.mul_mem (into_mem_normalizerE D k _) g.property, ?_⟩
  change (into D k (SemidirectProduct.inl v') * (g : G)) * into D k a *
    (into D k (SemidirectProduct.inl v') * (g : G))⁻¹ = into D k d
  calc
    _ = into D k (SemidirectProduct.inl v') * into D k x *
        (into D k (SemidirectProduct.inl v'))⁻¹ := by rw [hxg]; group
    _ = into D k d := by simpa only [map_mul, map_inv] using congrArg (into D k) hv'

end CaseII.Distribution
end Theory.GroupTheory.HeldM22A10.M22Identification
