module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.Family.Pair
public import Theory.ElementaryAbelian.Quotient

/-!
# The genuine quotient by the centralizer's Frattini subgroup

The central elementary supplement U identifies Φ(Q) with Φ(D). Thus Φ(D)
is S-normal, lies in both conjugate cores, and its quotient makes both cores
elementary. These facts retain the original natural cover and its radical.

Source: Aschbacher–Smith, C.5.6(4),(5), printed pp.156–157.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
variable {G : Type*} [Group G] [Finite G] {R L : Subgroup G} {F : Type*} [Field F]

/-- The Frattini subgroup removed in the source is exactly Φ(Q). -/
theorem Setup.core_frattini (h : Setup R L F) {x : G}
    (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (U L).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U L : Set G)) :
    (frattini (Q R L)).map (Q R L).subtype = Phi R L :=
  frattini_map_eq_of_central_elementary_supplement (Q R L) (D R L) (U L)
    (isPGroup_pCoreIn 2 (L ⊔ S R)) h.elementary
    (le_centralizer_iff.mp (h.core ▸ inf_le_right)) (h.factorization hx hnc).core

/-- Φ(D) is normal in the actual Baumann group. -/
theorem Setup.phi_normal (h : Setup R L F) {x : G}
    (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (U L).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U L : Set G)) :
    ((Phi R L).subgroupOf (S R)).Normal := by
  apply normal_subgroupOf_of_le_normalizer
  rw [← h.core_frattini hx hnc]
  exact (S_normalizes_Q R L).trans
    (normalizer_le_normalizer_characteristic_image (Q R L) (frattini (Q R L)))

omit [Finite G] in
/-- Image of an ambient subgroup under a homomorphism defined on S. -/
noncomputable def baumannImage {T : Type*} [Group T] (R : Subgroup G) (f : S R →* T)
    (B : Subgroup G) : Subgroup T := (B.subgroupOf (S R)).map f

variable {T : Type*} [Group T]

private theorem elementary_image_of_frattini_le_ker {P : Type*} [Group P] [Finite P]
    (hp : IsPGroup 2 P) (f : P →* T) (hk : frattini P ≤ f.ker) :
    IsElementaryAbelian 2 f.range := by
  let : Fact (IsPGroup 2 P) := ⟨hp⟩
  let : IsElementaryAbelian 2 (P ⧸ frattini P) := isElementaryAbelian_quotient_frattini
  let g := QuotientGroup.lift (frattini P) f hk
  have hg : g.range = f.range := by
    ext a
    constructor
    · rintro ⟨q, rfl⟩
      obtain ⟨p, rfl⟩ := QuotientGroup.mk'_surjective (frattini P) q
      exact ⟨p, rfl⟩
    · rintro ⟨p, rfl⟩
      exact ⟨QuotientGroup.mk' (frattini P) p, rfl⟩
  rw [← hg]
  exact IsElementaryAbelian.of_surjective g.rangeRestrict g.rangeRestrict_surjective

/-- The actual image of Q is elementary in the quotient by Φ(D). -/
theorem Setup.quotient_core_elementary (h : Setup R L F) {x : G}
    (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (U L).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U L : Set G))
    (f : S R →* T) (hk : f.ker = (Phi R L).subgroupOf (S R)) :
    IsElementaryAbelian 2 (baumannImage R f (Q R L)) := by
  have hQS : Q R L ≤ S R := h.core ▸ inf_le_left
  let g := f.comp (inclusion hQS)
  have hg : g.range = baumannImage R f (Q R L) := by
    ext t
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨inclusion hQS q, q.property, rfl⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨⟨s, hs⟩, rfl⟩
  rw [← hg]
  apply elementary_image_of_frattini_le_ker (isPGroup_pCoreIn 2 (L ⊔ S R))
  intro q hq
  change f (inclusion hQS q) = 1
  apply MonoidHom.mem_ker.mp
  rw [hk]
  exact h.core_frattini hx hnc ▸ mem_map_of_mem (Q R L).subtype hq

omit [Finite G] in
/-- Fixed points modulo Φ(D) lift on the original full module U. -/
theorem Setup.fixed_lift_mod_phi (h : Setup R L F)
    (f : S R →* T) (hk : f.ker = (Phi R L).subgroupOf (S R))
    (s : S R) (u : U L)
    (hu : f (inclusion h.module_le (moduleConjugate h.coordinates.normalizes s u)) =
      f (inclusion h.module_le u)) :
    moduleConjugate h.coordinates.normalizes s u = u := by
  apply h.fixedLift
  have hdiff : moduleConjugate h.coordinates.normalizes s u / u ∈ h.coordinates.projection.ker := by
    apply (h.coordinates.projection_kernel _).mpr
    have hker : inclusion h.module_le (moduleConjugate h.coordinates.normalizes s u / u) ∈ f.ker := by
      change f _ = 1
      rw [map_div, map_div, hu, div_self']
    rw [hk] at hker
    exact (inf_le_right : D R L ≤ centralizer (L : Set G))
      ((map_subtype_le (frattini (D R L))) hker)
  have he : h.coordinates.projection (moduleConjugate h.coordinates.normalizes s u) /
      h.coordinates.projection u = 1 := by
    simpa only [MonoidHom.mem_ker, map_div] using hdiff
  exact div_eq_one.mp he
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
end

public section
open Subgroup
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
variable {G : Type*} [Group G] [Finite G] {R L : Subgroup G} {F : Type*} [Field F]

/-- The opposite product VD is the literal conjugate core, before quotienting. -/
theorem Setup.opposite_eq_conjugate (h : Setup R L F) {x : G}
    (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (U L).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U L : Set G)) :
    (U L).map (MulAut.conj x⁻¹).toMonoidHom ⊔ D R L =
      (Q R L).map (MulAut.conj x⁻¹).toMonoidHom := by
  let V := (U L).map (MulAut.conj x⁻¹).toMonoidHom
  let Q' := (Q R L).map (MulAut.conj x⁻¹).toMonoidHom
  have hp := h.factorization hx hnc
  have hDQ' : D R L ≤ Q' := by
    dsimp only [Q']
    rw [h.conjugate_core hx]
    exact le_inf inf_le_left hp.centralizes
  have hVQ' : V ≤ Q' := map_mono h.module_le_core
  apply le_antisymm (sup_le hVQ' hDQ')
  intro q hq
  have hqS := ((h.conjugate_core hx).le.trans inf_le_left) hq
  have hqprod : q ∈ (V : Set G) * (Q R L : Set G) := by
    rw [← coe_mul_of_left_le_normalizer_right V (Q R L)
      ((h.conjugate_le hx).trans (S_normalizes_Q R L))]
    exact hp.span ▸ hqS
  obtain ⟨v, hv, a, ha, rfl⟩ := hqprod
  have haQ' : a ∈ Q' := by
    have hh := Q'.mul_mem (Q'.inv_mem (hVQ' hv)) hq
    simpa only [inv_mul_cancel_left] using hh
  have haprod : a ∈ (U L : Set G) * (D R L : Set G) := by
    rw [← coe_mul_of_left_le_normalizer_right (U L) (D R L)
      ((le_centralizer_iff.mp ((hp.core ▸ le_sup_right).trans (h.core ▸ inf_le_right))).trans
        (Subgroup.centralizer_le_normalizer _))]
    exact hp.core ▸ ha
  obtain ⟨u, hu, d, hd, rfl⟩ := haprod
  have huC : u ∈ centralizer (V : Set G) :=
    ((centralizer (V : Set G)).mul_mem_cancel_right (hp.centralizes hd)).mp
      (((h.conjugate_core hx).le.trans inf_le_right) haQ')
  have huV : u ∈ V :=
    (h.commutator_eq_fixed hx hnc).2 ▸
      ((h.commutator_eq_fixed hx hnc).1.symm ▸ (show u ∈ U L ⊓ centralizer (V : Set G) from ⟨hu, huC⟩)) |>.2
  exact (V ⊔ D R L).mul_mem (mem_sup_left hv) (mul_mem_sup huV hd)

variable {T : Type*} [Group T]

omit [Finite G] in
/-- Subgroups containing the actual kernel are recovered from their images. -/
theorem baumannImage_mem_iff (f : S R →* T)
    (hk : f.ker = (Phi R L).subgroupOf (S R)) (B : Subgroup G)
    (hNB : Phi R L ≤ B) (s : S R) : f s ∈ baumannImage R f B ↔ (s : G) ∈ B := by
  change f s ∈ (B.subgroupOf (S R)).map f ↔ _
  rw [← mem_comap, comap_map_eq, hk]
  have hn : (Phi R L).subgroupOf (S R) ≤ B.subgroupOf (S R) := subgroupOf_mono _ hNB
  rw [sup_eq_left.mpr hn]
  rfl

/-- The two image cores have equal order in the genuine Φ(D) quotient. -/
theorem Setup.quotient_core_card (h : Setup R L F) {x : G}
    (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (U L).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U L : Set G))
    (f : S R →* T) (hk : f.ker = (Phi R L).subgroupOf (S R)) :
    Nat.card (baumannImage R f (Q R L)) =
      Nat.card (baumannImage R f ((Q R L).map (MulAut.conj x⁻¹).toMonoidHom)) := by
  let N := (Phi R L).subgroupOf (S R)
  let Q₀ := (Q R L).subgroupOf (S R)
  let Q' := (Q R L).map (MulAut.conj x⁻¹).toMonoidHom
  let E₀ := Q'.subgroupOf (S R)
  have hNQ : Phi R L ≤ Q R L :=
    (map_subtype_le (frattini (D R L))).trans ((h.factorization hx hnc).core ▸ le_sup_right)
  have hNE : Phi R L ≤ Q' := by
    have hh := map_mono (f := (MulAut.conj x⁻¹).toMonoidHom) hNQ
    have hp : (Phi R L).map (MulAut.conj x⁻¹).toMonoidHom = Phi R L := h.frattini_invariant hx hnc
    exact hp ▸ hh
  have hNQ₀ : N ≤ Q₀ := subgroupOf_mono _ hNQ
  have hNE₀ : N ≤ E₀ := subgroupOf_mono _ hNE
  have hc : Nat.card Q₀ = Nat.card E₀ := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (h.core ▸ inf_le_left)).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe ((h.conjugate_core hx).le.trans inf_le_left)).toEquiv,
      card_map_of_injective (MulAut.conj x⁻¹).injective]
  have h1 := relIndex_mul_relIndex (⊥ : Subgroup (S R)) N Q₀ bot_le hNQ₀
  have h2 := relIndex_mul_relIndex (⊥ : Subgroup (S R)) N E₀ bot_le hNE₀
  rw [relIndex_bot_left, relIndex_bot_left] at h1 h2
  have hi : N.relIndex Q₀ = N.relIndex E₀ := by
    have hp : 0 < Nat.card N := Nat.card_pos
    nlinarith
  simpa only [baumannImage, ← relIndex_ker, hk] using hi
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
end
