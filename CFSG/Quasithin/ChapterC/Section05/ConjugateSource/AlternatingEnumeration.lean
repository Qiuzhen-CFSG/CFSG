module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.AlternatingFamilyKernel
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.AlternatingFamily.Enumeration.Lifts

/-!
# The four maximum elementary subgroups in the A₅ source action

The original marked action and central factor D determine the complete
fixed-point profile of the actual core Q. The factorization supplies
an elementary opposite UˣD of exactly the same order once Φ(D)=1.
The proved generic four-family lift theorem then enumerates the entire
maximum-order family in S; no fixed profile, maximality, equal-order or
exhaustion assertion is assumed from the source.

The generic E.6 enumeration leaf used here imports neither Chapter 2,
Chapter 3 nor the C.5 section, so it is independent of this source assembly.
Source: Aschbacher–Smith, C.5.6(5),(7) and C.5.7, printed pp.157–160.
-/

public section
open Subgroup BinaryPermutation Representation.BinaryOffender
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource
open CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.AlternatingFamily
open CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.AlternatingFamily.Enumeration
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem sup_inf_of_normalizes (U D C : Subgroup G)
    (hn : D ≤ normalizer (U : Set G)) (hd : D ≤ C) :
    (U ⊔ D) ⊓ C = (U ⊓ C) ⊔ D := by
  apply le_antisymm
  · rintro g ⟨hg, hc⟩
    have hp : g ∈ (U : Set G) * (D : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left U D hn]
      exact hg
    obtain ⟨u, hu, d, hd', rfl⟩ := hp
    have huC : u ∈ C := by simpa using C.mul_mem hc (C.inv_mem (hd hd'))
    exact mul_mem_sup ⟨hu, huC⟩ hd'
  · exact sup_le (inf_le_inf le_sup_left le_rfl) (le_inf le_sup_right hd)

private theorem card_sup_fixed (U D C : Subgroup G)
    (hn : D ≤ centralizer (U : Set G)) (hd : D ≤ C)
    (n : ℕ) (hc : Nat.card (U ⊓ C : Subgroup G) * n = Nat.card U) :
    Nat.card ((U ⊔ D) ⊓ C : Subgroup G) * n = Nat.card (U ⊔ D : Subgroup G) := by
  have hnorm := hn.trans (Subgroup.centralizer_le_normalizer _)
  have hnorm' : D ≤ normalizer ((U ⊓ C : Subgroup G) : Set G) :=
    (hn.trans (centralizer_le (show (U ⊓ C : Subgroup G) ≤ U from inf_le_left))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hi : (U ⊓ C) ⊓ D = U ⊓ D :=
    le_antisymm (inf_le_inf_right _ inf_le_left)
      (le_inf (le_inf inf_le_left (inf_le_right.trans hd)) inf_le_right)
  have h1 := card_mul_eq_card_inf_mul_card_sup_of_normalizes U D hnorm
  have h2 := card_mul_eq_card_inf_mul_card_sup_of_normalizes (U ⊓ C) D hnorm'
  rw [hi] at h2
  rw [sup_inf_of_normalizes U D C hnorm hd]
  apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := ↥(U ⊓ D)))
  calc
    _ = (Nat.card (U ⊓ C : Subgroup G) * Nat.card D) * n := by rw [← mul_assoc, ← h2]
    _ = Nat.card U * Nat.card D := by rw [mul_right_comm, hc]
    _ = _ := h1

private theorem fixed_card_mul_index (B : Subgroup FivePerm)
    (hB : B ≤ ChapterB.Offenders.D 5) :
    Nat.card (fixedSpace (coreRepresentation (Fin 5)) B) * fixedIndex B =
      Nat.card (BinaryPermutation.core (Fin 5)) := by
  rcases subgroup_cases B hB with rfl | rfl | rfl | rfl | rfl
  · rw [fixedSpace_bot, fixedIndex_bot, mul_one]
    exact Nat.card_congr (Submodule.topEquiv :
      (⊤ : Submodule (ZMod 2) (BinaryPermutation.core (Fin 5))) ≃ₗ[ZMod 2] _).toEquiv
  · rw [fixed_line_card, fixedIndex_line, vector_card]
  · rw [fixed_line_card, fixedIndex_line, vector_card]
  · rw [fixed_diagonal_card, fixedIndex_diagonal, vector_card]
  · rw [fixed_actor_card, fixedIndex_actor, vector_card]

/-- The literal central elementary supplement supplies all fixed profiles. -/
theorem marked_kernel_fixedProfile (σ : G →* FivePerm) (U D : Subgroup G)
    (hker : σ.ker = U ⊔ D) (hrange : σ.range = ChapterB.Offenders.D 5)
    (hD : D ≤ center G)
    (e : U ≃* Multiplicative (BinaryPermutation.core (Fin 5)))
    (he : ∀ (s : G) (u : U),
      (e.symm (Multiplicative.ofAdd
        (coreRepresentation (Fin 5) (σ s) (e u).toAdd)) : G) = s * (u : G) * s⁻¹) :
    FixedProfile σ σ.ker := by
  have hDC (B : Subgroup G) : D ≤ centralizer (B : Set G) :=
    hD.trans (center_le_centralizer _)
  have hc (B : Subgroup G) : Nat.card (σ.ker ⊓ centralizer (B : Set G) : Subgroup G) *
      fixedIndex (B.map σ) = Nat.card σ.ker := by
    rw [hker]
    apply card_sup_fixed U D (centralizer (B : Set G)) (hDC U) (hDC B)
    let a := σ.comp B.subtype
    have ha : a.range = B.map σ := by rw [MonoidHom.range_comp, range_subtype]
    rw [marked_centralizer_card B U a e (fun s u => he s u), ha]
    have hcard : Nat.card U = Nat.card (BinaryPermutation.core (Fin 5)) :=
      (Nat.card_congr e.toEquiv).trans (Nat.card_congr Multiplicative.toAdd)
    rw [hcard]
    exact fixed_card_mul_index (B.map σ) ((B.map_le_range σ).trans hrange.le)
  refine ⟨hc, ?_⟩
  intro B b hb hB hdiag
  have h1 := hc B
  have h2 := hc (zpowers b)
  rw [hB, fixedIndex_actor] at h1
  rw [MonoidHom.map_zpowers, hdiag, ← diagonal, fixedIndex_diagonal,
    zpowers_eq_closure, centralizer_closure] at h2
  apply eq_of_le_of_card_ge
  · exact inf_le_inf_left _ (centralizer_le (Set.singleton_subset_iff.mpr hb))
  · exact (Nat.eq_of_mul_eq_mul_right (by decide : 0 < 4) (h2.trans h1.symm)).le
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource

namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource
open CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.AlternatingFamily
open CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.AlternatingFamily.Enumeration
variable {G : Type*} [Group G] [Finite G] {R K L : Subgroup G}

omit [Finite G] in
private theorem restrict_image (S N B : Subgroup G) (hSN : S ≤ N) (hBS : B ≤ S)
    (a : N →* FivePerm) :
    (B.subgroupOf S).map (a.comp (inclusion hSN)) = (B.subgroupOf N).map a := by
  ext p
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact ⟨inclusion hSN b, hb, rfl⟩
  · rintro ⟨b, hb, rfl⟩
    exact ⟨⟨b, hBS hb⟩, hb, rfl⟩

end CFSG.Quasithin.ChapterC.Section05.ConjugateSource

namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource
open CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.AlternatingFamily
open CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.AlternatingFamily.Enumeration
variable {G : Type*} [Group G] [Finite G] {R K L : Subgroup G}

theorem AlternatingPairSetup.intrinsic_fixedProfile
    (h : AlternatingPairSetup R K L) (x : G) (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (sourceModule K : Set G))
    (hphi : let D := ChapterB.baumann R ⊓ centralizer (K : Set G)
      (frattini D).map D.subtype = ⊥) :
    FixedProfile (h.action.comp (inclusion (show ChapterB.baumann R ≤ K ⊔ ChapterB.baumann R from le_sup_right)))
      (((K ⊔ ChapterB.baumann R).pCoreIn 2).subgroupOf (ChapterB.baumann R)) := by
  let S := ChapterB.baumann R
  let U := sourceModule K
  let D := S ⊓ centralizer (K : Set G)
  let Q := (K ⊔ S).pCoreIn 2
  let σ := h.action.comp (inclusion (show S ≤ K ⊔ S from le_sup_right))
  let Ui := U.subgroupOf S
  let Di := D.subgroupOf S
  let Qi := Q.subgroupOf S
  have hUS : U ≤ S := h.module_le
  have hDS : D ≤ S := inf_le_left
  have hQS : Q ≤ S := h.core.le.trans inf_le_left
  have hk : σ.ker = Qi := by
    ext s
    change h.action (inclusion le_sup_right s) = 1 ↔ (s : G) ∈ Q
    change inclusion le_sup_right s ∈ h.action.ker ↔ _
    rw [h.action_kernel]
    change (s : G) ∈ centralizer (U : Set G) ↔ (s : G) ∈ Q
    have hcore : Q = S ⊓ centralizer (U : Set G) := h.core
    rw [hcore]
    exact (and_iff_right s.property).symm
  have hk' : σ.ker = Ui ⊔ Di := by
    rw [hk]
    have hprod : Q = U ⊔ D := h.product
    change Q.subgroupOf S = _
    rw [hprod, subgroupOf_sup hUS hDS]
  have hr : σ.range = ChapterB.Offenders.D 5 := by
    have hh := restrict_image S (K ⊔ S) S le_sup_right le_rfl h.action
    rw [subgroupOf_self, ← MonoidHom.range_eq_map] at hh
    exact hh.trans h.baumann_image
  have hDcentral := (h.elementary_factor_pair x hx hnc hphi).2.2.2
  have hDi : Di ≤ center S := by
    intro d hd
    apply mem_center_iff.mpr
    intro s
    apply Subtype.ext
    exact hDcentral hd s s.property
  let e : Ui ≃* Multiplicative (BinaryPermutation.core (Fin 5)) :=
    (subgroupOfEquivOfLe hUS).trans h.coordinates
  have he (s : S) (u : Ui) :
      (e.symm (Multiplicative.ofAdd (coreRepresentation (Fin 5) (σ s) (e u).toAdd)) : S) =
        s * (u : S) * s⁻¹ := by
    apply Subtype.ext
    exact h.equivariant (inclusion le_sup_right s) ((subgroupOfEquivOfLe hUS) u)
  change FixedProfile σ Qi
  rw [← hk]
  exact marked_kernel_fixedProfile σ Ui Di hk' hr hDi e he

theorem AlternatingPairSetup.intrinsic_family_eq_four
    (h : AlternatingPairSetup R K L) (x : G) (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (sourceModule K : Set G))
    (hphi : let D := ChapterB.baumann R ⊓ centralizer (K : Set G)
      (frattini D).map D.subtype = ⊥) :
    let S := ChapterB.baumann R
    let U := sourceModule K
    let V := U.map (MulAut.conj x⁻¹).toMonoidHom
    let Q := (K ⊔ S).pCoreIn 2
    let D := S ⊓ centralizer (K : Set G)
    let σ := h.action.comp (inclusion (show S ≤ K ⊔ S from le_sup_right))
    ∃ B₀ B₁ : Subgroup S,
      Stellmacher.elementaryAbelianMaxSubgroups (⊤ : Subgroup S) =
        {Q.subgroupOf S, (V ⊔ D).subgroupOf S, B₀, B₁} ∧
      B₀.map σ = line 0 ∧ B₁.map σ = line 1 := by
  let S := ChapterB.baumann R
  let U := sourceModule K
  let V := U.map (MulAut.conj x⁻¹).toMonoidHom
  let Q := (K ⊔ S).pCoreIn 2
  let D := S ⊓ centralizer (K : Set G)
  let W := V ⊔ D
  let σ := h.action.comp (inclusion (show S ≤ K ⊔ S from le_sup_right))
  have hSmap : S.map (MulAut.conj x⁻¹).toMonoidHom = S :=
    mem_normalizer_iff_map_conj_eq.mp
      (Stellmacher.normalizer_le_normalizer_baumann R ((normalizer (R : Set G)).inv_mem hx))
  have hVS : V ≤ S := (map_mono h.module_le).trans_eq hSmap
  have hWS : W ≤ S := sup_le hVS inf_le_left
  have hQS : Q ≤ S := h.core.le.trans inf_le_left
  have hk : σ.ker = Q.subgroupOf S := by
    ext s
    change h.action (inclusion le_sup_right s) = 1 ↔ (s : G) ∈ Q
    change inclusion le_sup_right s ∈ h.action.ker ↔ _
    rw [h.action_kernel]
    change (s : G) ∈ centralizer (U : Set G) ↔ (s : G) ∈ Q
    have hcore : Q = S ⊓ centralizer (U : Set G) := h.core
    rw [hcore]
    exact (and_iff_right s.property).symm
  have hr : σ.range = ChapterB.Offenders.D 5 := by
    have hh := restrict_image S (K ⊔ S) S le_sup_right le_rfl h.action
    rw [subgroupOf_self, ← MonoidHom.range_eq_map] at hh
    exact hh.trans h.baumann_image
  have hWmap : (W.subgroupOf S).map σ = ChapterB.Offenders.D 5 := by
    apply le_antisymm ((map_le_range _ _).trans hr.le)
    rw [← h.conjugate_action_image x hx hnc,
      ← restrict_image S (K ⊔ S) V le_sup_right hVS h.action]
    exact map_mono (subgroupOf_mono S le_sup_left)
  have hh := h.elementary_factor_pair x hx hnc hphi
  let : IsElementaryAbelian 2 Q := hh.1
  let : IsElementaryAbelian 2 W := hh.2.1
  have hcard : Nat.card (W.subgroupOf S) = Nat.card (Q.subgroupOf S) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hWS).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe hQS).toEquiv]
    exact hh.2.2.1
  exact exists_maxFamily_eq_four σ (Q.subgroupOf S) (W.subgroupOf S)
    (IsElementaryAbelian.subgroupOf hQS) (IsElementaryAbelian.subgroupOf hWS)
    hk hr hWmap hcard (h.intrinsic_fixedProfile x hx hnc hphi)
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource
