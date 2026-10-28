module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SurvivingIntersections.MathieuCovers.M22Normalization
public import Theory.GroupTheory.PResidual.NormalizerCore


/-!
# The canonical square projection in the binary M₂₂ source geometry

The unique square in t Z(L), supplied by I.2.2(6b), selects an actual
projection of the original z. Projections in this coset have identical
centralizers, hence identical two-residual cores. Naturality of those cores
makes the selected projection fixed by N_G(L) ∩ C_G(z). The proved
H-normalization of L therefore puts this projection in Z(S), and its square
root lies in the original component Sylow S ∩ L.

This is an ambient consequence of the square calculation, not the binary
cover exclusion in 2.3.9(7)(f). The forced kernel-moving element of N_T(S)
is not known to normalize L or this residual core; none of those properties
is inferred here. In particular Z(S) is not replaced by Z(T).

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
I.2.2(6b), printed pp.410,412, and 2.3.7–2.3.9, printed pp.523–526.
The original source setup, its selected T, and its Mathieu quotient/action
remain unchanged. The earlier universal inputs are those of qt-1-01 and
qt-c-01, retained by the source assembly owner.
-/

public section

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers
namespace CFSG.Quasithin.Chapter2.ComponentRefinement
namespace BinaryAmbient
variable {K : Type*} [Group K]

private theorem same_conjugation_iff (a b : K) :
    (∀ x : K, a * x * a⁻¹ = b * x * b⁻¹) ↔
      QuotientGroup.mk' (center K) a = QuotientGroup.mk' (center K) b := by
  change (∀ x : K, a * x * a⁻¹ = b * x * b⁻¹) ↔
    (a : K ⧸ center K) = (b : K ⧸ center K)
  rw [QuotientGroup.eq]
  constructor
  · intro h
    apply mem_center_iff.mpr
    intro x
    calc
      x * (a⁻¹ * b) = a⁻¹ * (a * x * a⁻¹) * b := by group
      _ = a⁻¹ * (b * x * b⁻¹) * b := by rw [h x]
      _ = (a⁻¹ * b) * x := by group
  · intro h x
    have hc := mem_center_iff.mp h x
    calc
      a * x * a⁻¹ = a * (x * (a⁻¹ * b)) * b⁻¹ := by group
      _ = a * ((a⁻¹ * b) * x) * b⁻¹ := by rw [hc]
      _ = b * x * b⁻¹ := by group

private theorem centralizer_eq_of_quotient_eq {a b : K}
    (he : QuotientGroup.mk' (center K) a = QuotientGroup.mk' (center K) b) :
    centralizer ({a} : Set K) = centralizer ({b} : Set K) := by
  have h := (same_conjugation_iff a b).mpr he
  ext x
  rw [mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  constructor
  · intro hx
    have ha : a * x * a⁻¹ = x := by rw [← hx, mul_inv_cancel_right]
    have hb := (h x).symm.trans ha
    exact (mul_inv_eq_iff_eq_mul.mp hb).symm
  · intro hx
    have hb : b * x * b⁻¹ = x := by rw [← hx, mul_inv_cancel_right]
    exact (mul_inv_eq_iff_eq_mul.mp ((h x).trans hb)).symm

private theorem core_eq_of_quotient_eq {a b : K}
    (he : QuotientGroup.mk' (center K) a = QuotientGroup.mk' (center K) b) :
    centralizerCore a = centralizerCore b := by
  unfold centralizerCore centralizerTwoResidual
  rw [centralizer_eq_of_quotient_eq he]

variable {G : Type*} [Group G] {L : Subgroup G} {z : G}

private theorem projection_iff_quotient_eq {t u : L}
    (ht : IsConjugationProjection L z t) :
    IsConjugationProjection L z u ↔
      QuotientGroup.mk' (center L) u = QuotientGroup.mk' (center L) t := by
  rw [← same_conjugation_iff]
  constructor
  · intro hu x
    exact Subtype.ext ((hu x).symm.trans (ht x))
  · intro hu x
    exact (ht x).trans (congrArg Subtype.val (hu x)).symm

/-- The unique core square in the central coset is itself an inner projection. -/
theorem exists_unique_square_projection {t : L}
    (ht : IsConjugationProjection L z t) (hsq : HasUniqueCoreSquareLift t) :
    ∃! u : L, IsConjugationProjection L z u ∧
      ∃ x ∈ centralizerCore u, x ^ 2 = u := by
  obtain ⟨u, ⟨hu, x, hx, hs⟩, huniq⟩ := hsq
  refine ⟨u, ⟨(projection_iff_quotient_eq ht).mpr hu, x, ?_, hs⟩, ?_⟩
  · rwa [core_eq_of_quotient_eq hu]
  · rintro v ⟨hv, y, hy, he⟩
    have hq := (projection_iff_quotient_eq ht).mp hv
    exact huniq v ⟨hq, y, (core_eq_of_quotient_eq hq) ▸ hy, he⟩

private theorem projection_conjugate {t : L} (ht : IsConjugationProjection L z t)
    {s : G} (hs : s ∈ normalizer (L : Set G)) (hz : s * z = z * s) :
    IsConjugationProjection L z ((L.normalizerMonoidHom ⟨s, hs⟩) t) := by
  let a := L.normalizerMonoidHom ⟨s, hs⟩
  have ha (x : L) : (a x : G) = s * (x : G) * s⁻¹ := rfl
  have hai (x : L) : (a.symm x : G) = s⁻¹ * (x : G) * s := by
    calc
      (a.symm x : G) = s⁻¹ * (s * (a.symm x : G) * s⁻¹) * s := by group
      _ = s⁻¹ * (x : G) * s := by rw [← ha, a.apply_symm_apply]
  intro x
  have he := congrArg (fun y : G => s * y * s⁻¹) (ht (a.symm x))
  simp only [hai, Subgroup.coe_mul, Subgroup.coe_inv] at he
  change z * (x : G) * z⁻¹ = (a t : G) * (x : G) * (a t : G)⁻¹
  rw [ha]
  have hsz : s * z * s⁻¹ = z := by rw [hz, mul_inv_cancel_right]
  calc
    z * (x : G) * z⁻¹ =
        (s * z * s⁻¹) * (x : G) * (s * z * s⁻¹)⁻¹ := by rw [hsz]
    _ = s * (z * (s⁻¹ * (x : G) * s) * z⁻¹) * s⁻¹ := by group
    _ = s * ((t : G) * (s⁻¹ * (x : G) * s) * (t : G)⁻¹) * s⁻¹ := he
    _ = (s * (t : G) * s⁻¹) * (x : G) * (s * (t : G) * s⁻¹)⁻¹ := by group

/-- Naturality of the literal residual/core makes the selected projection fixed. -/
theorem square_projection_fixed [Finite G] {t : L}
    (ht : IsConjugationProjection L z t)
    (hroot : ∃ x ∈ centralizerCore t, x ^ 2 = t)
    (huniq : ∀ u : L, IsConjugationProjection L z u →
      (∃ x ∈ centralizerCore u, x ^ 2 = u) → u = t)
    {s : G} (hs : s ∈ normalizer (L : Set G)) (hz : s * z = z * s) :
    s * (t : G) = (t : G) * s := by
  let a := L.normalizerMonoidHom ⟨s, hs⟩
  have he : a t = t := by
    apply huniq _ (projection_conjugate ht hs hz)
    obtain ⟨x, hx, hx2⟩ := hroot
    refine ⟨a x, ?_, (map_pow a x 2).symm.trans (congrArg a hx2)⟩
    have hm := mem_map_of_mem a.toMonoidHom hx
    change a x ∈ (centralizerResidualCore t).map a.toMonoidHom at hm
    rw [map_centralizerResidualCore] at hm
    exact hm
  exact mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val he)

/-- A square root in the residual core already lies in any Sylow centralized by t. -/
private theorem centralizerCore_le_sylow [Finite K] (t : K) (R : Sylow 2 K)
    (ht : t ∈ centralizer (R : Set K)) : centralizerCore t ≤ (R : Subgroup K) := by
  have hRC : (R : Subgroup K) ≤ centralizer ({t} : Set K) := by
    intro r hr
    exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp ht r hr)
  have hc : centralizerCore t ≤ (centralizer ({t} : Set K)).pCoreIn 2 :=
    pCoreIn_mono_of_normalizes (centralizerTwoResidual_le t)
      (le_normalizer_embedded_pResidual 2 (centralizer ({t} : Set K)))
  have hR := pCoreIn_le_sylow _ (R.subtype hRC)
  rw [Sylow.coe_subtype, map_subgroupOf_eq_of_le hRC] at hR
  exact hc.trans hR

variable [Finite G] {H M : Subgroup G} {S : Sylow 2 H}

/-- Source application: the distinguished projection is central in the full
original S, with its root in the original component Sylow and residual core. -/
theorem source_square_projection {C : GroupClass}
    (c : MathieuSourceSetup H L M S z) (hG : IsSimpleQTKE C G)
    (source115 : Structural115Input G) (sourceC : LocalC129Input C G)
    (d : SporadicQuotientInput L z .m22) (hc : Nat.card (pCore 2 L) = 2) :
    ∃ t : L, IsConjugationProjection L z t ∧ orderOf t = 2 ∧ t ∉ center L ∧
      (t : G) ∈ centralizer ((S : Subgroup H).map H.subtype : Set G) ∧
      HasUniqueCoreSquareLift t ∧
      (∀ s ∈ normalizer (L : Set G) ⊓ centralizer ({z} : Set G),
        s * (t : G) = (t : G) * s) ∧
      ∃ R : Sylow 2 L,
        (R : Subgroup L) = ((S : Subgroup H).map H.subtype).subgroupOf L ∧
        t ∈ (R : Subgroup L) ∧
        ∃ x ∈ (R : Subgroup L), x ∈ centralizerCore t ∧ x ^ 2 = t := by
  have h := c.localSetup hG source115 sourceC
  obtain ⟨t₀, hp₀, ho₀, hn₀, hs₀, R, hR, _, _⟩ :=
    mathieuTwentyTwo_binary_projection h d hc
  obtain ⟨t, ⟨ht, hroot⟩, huniq⟩ := exists_unique_square_projection hp₀ hs₀
  have hq := (projection_iff_quotient_eq hp₀).mp ht
  have htn : t ∉ center L := by
    intro hz
    apply hn₀
    apply (QuotientGroup.eq_one_iff _).mp
    exact hq.symm.trans ((QuotientGroup.eq_one_iff _).mpr hz)
  let eZ := h.mathieuTwentyTwo_centerQuotient d.quotientIso
  have hZ : Nat.card (center L) = 2 := by
    simpa only [h.mathieuTwentyTwo_center_eq d.quotientIso] using hc
  have ht2 : t ^ 2 = 1 := by
    apply Sporadic.Mathieu.M22CentralCover.square_eq_one eZ hZ t
    change (eZ (QuotientGroup.mk' (center L) t)) ^ 2 = 1
    rw [hq, ← map_pow, ← map_pow, show t₀ ^ 2 = 1 from ho₀ ▸ pow_orderOf_eq_one t₀,
      map_one, map_one]
  have hto : orderOf t = 2 :=
    orderOf_eq_prime ht2 (fun he => htn (he ▸ (center L).one_mem))
  have hf : ∀ s ∈ normalizer (L : Set G) ⊓ centralizer ({z} : Set G),
      s * (t : G) = (t : G) * s := by
    intro s hs
    exact square_projection_fixed ht hroot (fun u hu hx => huniq u ⟨hu, hx⟩)
      hs.1 (mem_centralizer_singleton_iff.mp hs.2)
  have hk : pCore 2 L ≠ ⊥ := by
    intro he
    rw [he, Subgroup.card_bot] at hc
    omega
  have hn := h.mathieuTwentyTwo_normalized hG.quasithin d.quotientIso hk
  have htc : (t : G) ∈ centralizer ((S : Subgroup H).map H.subtype : Set G) := by
    apply mem_centralizer_iff.mpr
    intro s hs
    exact hf s ⟨hn (map_subtype_le _ hs), mem_centralizer_singleton_iff.mpr (h.central s hs)⟩
  refine ⟨t, ht, hto, htn, htc,
    h.mathieuTwentyTwo_binary_uniqueCoreSquare d.quotientIso hc t hto htn,
    hf, R, hR, h.projection_mem_sylow ht hto R hR, ?_⟩
  obtain ⟨x, hx, hx2⟩ := hroot
  exact ⟨x, centralizerCore_le_sylow t R (h.projection_centralizes_sylow ht R hR) hx,
    hx, hx2⟩

end BinaryAmbient
end CFSG.Quasithin.Chapter2.ComponentRefinement

end
