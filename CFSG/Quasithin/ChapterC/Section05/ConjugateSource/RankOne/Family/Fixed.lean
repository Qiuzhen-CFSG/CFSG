module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.Assembly

/-!
# Full fixed subgroups in the natural two-member family

After Φ(D)=1, the source product Q=UD is elementary and D centralizes S.
Every element outside Q has a nonzero upper-root parameter. Its fixed
subgroup in U is therefore the full preimage of the same natural line.
The already proved commutator equality puts that subgroup in Uˣ, so the
fixed subgroup in Q is exactly Q∩Qˣ. The full central layer is retained.

Source: Aschbacher–Smith, C.5.6(5) and C.5.7, printed pp.157,160.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
variable {G : Type*} [Group G] [Finite G] {R L : Subgroup G} {F : Type*} [Field F]

noncomputable abbrev Phi (R L : Subgroup G) : Subgroup G :=
  (frattini (D R L)).map (D R L).subtype

/-- The actual core becomes elementary when the source obstruction kills Φ(D). -/
theorem Setup.core_elementary (h : Setup R L F) {x : G}
    (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (U L).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U L : Set G))
    (hphi : Phi R L = ⊥) : IsElementaryAbelian 2 (Q R L) := by
  have hp := h.factorization hx hnc
  have hDQ : D R L ≤ Q R L := hp.core ▸ le_sup_right
  have hDtwo := (isPGroup_pCoreIn 2 (L ⊔ S R)).to_le hDQ
  let : Fact (IsPGroup 2 (D R L)) := ⟨hDtwo⟩
  have hph : frattini (D R L) = ⊥ :=
    (map_injective (D R L).subtype_injective) (hphi.trans (map_bot (D R L).subtype).symm)
  let : IsElementaryAbelian 2 (D R L) :=
    (frattini_eq_bot_iff_isElementaryAbelian (p := 2)).mp hph
  let := h.elementary
  rw [hp.core]
  exact IsElementaryAbelian.sup_of_le_centralizer
    (hDQ.trans (h.core ▸ inf_le_right))

/-- Once D is elementary it is central in the whole Baumann group. -/
theorem Setup.centralizer_centralizes_baumann (h : Setup R L F) {x : G}
    (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (U L).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U L : Set G))
    (hphi : Phi R L = ⊥) : D R L ≤ centralizer (S R : Set G) := by
  have hp := h.factorization hx hnc
  let := h.core_elementary hx hnc hphi
  rw [hp.span]
  apply le_centralizer_iff.mpr
  exact sup_le (le_centralizer_iff.mp hp.centralizes)
    (le_centralizer_iff.mp ((hp.core ▸ le_sup_right).trans (le_centralizer (Q R L))))

/-- The full centralizer in Q of any nontrivial natural actor is Q∩Qˣ. -/
theorem Setup.core_fixed_singleton (h : Setup R L F) {x : G}
    (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (U L).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U L : Set G))
    (hphi : Phi R L = ⊥) (s : G) (hs : s ∈ S R) (hsq : s ∉ Q R L) :
    Q R L ⊓ centralizer ({s} : Set G) =
      Q R L ⊓ (Q R L).map (MulAut.conj x⁻¹).toMonoidHom := by
  let Q' := (Q R L).map (MulAut.conj x⁻¹).toMonoidHom
  have hp := h.factorization hx hnc
  let := h.core_elementary hx hnc hphi
  let : IsElementaryAbelian 2 Q' := IsElementaryAbelian.map (MulAut.conj x⁻¹).toMonoidHom
  have hDQ' : D R L ≤ Q' := by
    dsimp only [Q']
    rw [h.conjugate_core hx]
    exact le_inf inf_le_left hp.centralizes
  have hDfix := h.centralizer_centralizes_baumann hx hnc hphi
  apply le_antisymm
  · rintro q ⟨hq, hqfix⟩
    refine ⟨hq, ?_⟩
    have hqprod : q ∈ (U L : Set G) * (D R L : Set G) := by
      rw [← coe_mul_of_left_le_normalizer_right]
      · exact hp.core ▸ hq
      · exact (le_centralizer_iff.mp ((hp.core ▸ le_sup_right).trans
          (h.core ▸ inf_le_right))).trans (Subgroup.centralizer_le_normalizer _)
    obtain ⟨u, hu, d, hd, rfl⟩ := hqprod
    have hdfix : d ∈ centralizer ({s} : Set G) :=
      (centralizer_le (Set.singleton_subset_iff.mpr hs)) (hDfix hd)
    have hufix : u ∈ centralizer ({s} : Set G) :=
      ((centralizer ({s} : Set G)).mul_mem_cancel_right hdfix).mp hqfix
    let s₀ : S R := ⟨s, hs⟩
    let u₀ : U L := ⟨u, hu⟩
    have hparam : (h.coordinates.parameter s₀).toAdd ≠ 0 := by
      intro he
      apply hsq
      rw [h.core]
      exact ⟨hs, (h.coordinates.parameter_kernel s₀).mp (Multiplicative.toAdd.injective he)⟩
    have hfix : moduleConjugate h.coordinates.normalizes s₀ u₀ = u₀ := by
      apply Subtype.ext
      change s * u * s⁻¹ = u
      rw [← mem_centralizer_singleton_iff.mp hufix, mul_inv_cancel_right]
    have hzero : (h.coordinates.projection u₀).toAdd 1 = 0 := by
      have hh := congrArg (fun v : Multiplicative (Fin 2 → F) => v.toAdd 0)
        (congrArg h.coordinates.projection hfix)
      rw [h.coordinates.equivariant] at hh
      have hz : (h.coordinates.parameter s₀).toAdd * (h.coordinates.projection u₀).toAdd 1 = 0 := by
        simpa using hh
      exact (mul_eq_zero.mp hz).resolve_left hparam
    have huS := centralizes_of_second_zero h.coordinates h.fixedLift u₀ hzero
    have huQ' : u ∈ Q' := by
      dsimp only [Q']
      rw [h.conjugate_core hx]
      exact ⟨h.module_le hu, (centralizer_le (h.conjugate_le hx)) huS⟩
    exact Q'.mul_mem huQ' (hDQ' hd)
  · rintro q ⟨hq, hq'⟩
    refine ⟨hq, ?_⟩
    have hc : q ∈ centralizer (S R : Set G) := by
      rw [h.core_span hx hnc, sup_eq_closure, centralizer_closure]
      intro z hz
      rcases hz with hz | hz
      · exact mem_centralizer_iff.mp (le_centralizer (Q R L) hq) z hz
      · exact mem_centralizer_iff.mp (le_centralizer Q' hq') z hz
    exact (centralizer_le (Set.singleton_subset_iff.mpr hs)) hc
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
end
