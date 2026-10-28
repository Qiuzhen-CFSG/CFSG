module

public import Theory.GroupTheory.SaturatedCentralProjection
public import Theory.GroupTheory.ComponentLocalOrbitCore

/-!
# Saturation across permuted components

An invariant p-subgroup of a component, normalized by its stabilizer in A,
has a p-group orbit under A: distinct component conjugates commute. Thus
A-saturation also controls such stabilizer-invariant subgroups of each
component. Applying the actual quotient by the centralizer inside the
component normalizer yields noncentral intersection from an inner marker.
Unique Sylow containment then gives the full component Sylow intersection.
The actor need not normalize the component.

Source: Aschbacher--Smith 2.5.3(3--4), printed pp.552--553.
-/

public section
namespace Theory.GroupTheory
open Subgroup
open scoped Pointwise
variable {G : Type*} [Group G] [Finite G] {p : ℕ}

/-- Saturation for the full actor also controls p-subgroups of a component
invariant under its stabilizer, even when that component is permuted. -/
theorem IsComponent.stabilizer_saturation {L A Q : Subgroup G}
    (hL : IsComponent G L)
    (hsat : ∀ P : Subgroup G, IsPGroup p P →
      A ≤ normalizer (P : Set G) → P ≤ Q)
    (P : Subgroup G) (hPL : P ≤ L) (hp : IsPGroup p P)
    (hn : A ⊓ normalizer (L : Set G) ≤ normalizer (P : Set G)) : P ≤ Q := by
  have horbit : IsPGroup p (componentOrbit P A) :=
    isPGroup_iSup_of_normalizes _ (fun _ => hp.map _)
      (fun a b => hL.local_conjugates_normalize hPL hn b a)
  exact (le_componentOrbit P A).trans
    (hsat _ horbit (le_normalizer_componentOrbit P A))

/-- A nontrivial inner marker gives a noncentral point of the literal
component intersection, using only its actual stabilizer and quotient. -/
theorem IsComponent.exists_noncentral_intersection_of_saturation
    {L A Q : Subgroup G} (hL : IsComponent G L)
    (hZ : IsPGroup p (center L)) (hQ : IsPGroup p Q)
    (hAQ : A ≤ normalizer (Q : Set G))
    (hsat : ∀ P : Subgroup G, IsPGroup p P →
      A ≤ normalizer (P : Set G) → P ≤ Q)
    {z : G} (hzQ : z ∈ Q)
    (hzinner : z ∈ L ⊔ centralizer (L : Set G))
    (hznc : z ∉ centralizer (L : Set G)) :
    ∃ d ∈ L ⊓ Q, d ∉ centralizer (L : Set G) := by
  let N := normalizer (L : Set G)
  let D := L.subgroupOf N
  let C := centralizer (D : Set N)
  let R := Q.subgroupOf N
  let B := A.subgroupOf N
  let : D.Normal := normal_subgroupOf_of_le_normalizer (show N ≤ normalizer (L : Set G) from le_rfl)
  let e : D ≃* L := subgroupOfEquivOfLe L.le_normalizer
  have hZD : IsPGroup p (center D) := hZ.of_equiv (centerCongr e).symm
  let P := D ⊓ (R ⊔ C)
  have hPp : IsPGroup p P := isPGroup_inf_sup_centralizer D R hZD hQ.comap_subtype
  have hBR : B ≤ normalizer (R : Set N) := by
    intro a ha x
    exact hAQ ha (x : G)
  have hBP : B ≤ normalizer (P : Set N) :=
    (le_inf le_normalizer_of_normal
      (hBR.trans normalizer_le_normalizer_sup_normal)).trans
      inf_normalizer_le_normalizer_inf
  have hPL : P.map N.subtype ≤ L := by
    rintro x ⟨y, hy, rfl⟩
    exact hy.1
  have hAP : A ⊓ N ≤ normalizer (P.map N.subtype : Set G) := by
    rintro a ⟨ha, hn⟩
    exact P.le_normalizer_map N.subtype ⟨⟨a, hn⟩, hBP ha, rfl⟩
  have hPQ : P.map N.subtype ≤ Q :=
    hL.stabilizer_saturation hsat _ hPL (hPp.map N.subtype) hAP
  have hzprod : z ∈ (L : Set G) * (centralizer (L : Set G) : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left L _ (centralizer_le_normalizer _)]
    exact hzinner
  obtain ⟨d, hdL, c, hc, hdc⟩ := hzprod
  have hcN : c ∈ N := centralizer_le_normalizer _ hc
  have hdN : d ∈ N := L.le_normalizer hdL
  have hzN : z ∈ N := hdc ▸ N.mul_mem hdN hcN
  have hcC : (⟨c, hcN⟩ : N) ∈ C := by
    intro x hx
    exact Subtype.ext (hc x hx)
  have hdP : (⟨d, hdN⟩ : N) ∈ P := by
    refine ⟨hdL, ?_⟩
    have he : (⟨d, hdN⟩ : N) = ⟨z, hzN⟩ * (⟨c, hcN⟩ : N)⁻¹ := by
      apply Subtype.ext
      change d = z * c⁻¹
      rw [← hdc]; group
    rw [he]
    exact mul_mem (mem_sup_left hzQ) (mem_sup_right (inv_mem hcC))
  refine ⟨d, ⟨hdL, hPQ (mem_map_of_mem N.subtype hdP)⟩, ?_⟩
  intro hdcen
  exact hznc (hdc ▸ (centralizer (L : Set G)).mul_mem hdcen hc)

/-- Sylow uniqueness inside a component is enough for the full actor's
saturation to identify the component intersection with an actual Sylow. -/
theorem IsComponent.exists_sylow_eq_inf_of_saturation [Fact p.Prime]
    {L A Q : Subgroup G} (hL : IsComponent G L)
    (hQ : IsPGroup p Q) (hAQ : A ≤ normalizer (Q : Set G))
    (hsat : ∀ P : Subgroup G, IsPGroup p P →
      A ≤ normalizer (P : Set G) → P ≤ Q)
    (hunique : ∀ P R : Sylow p L, Q.subgroupOf L ≤ P →
      Q.subgroupOf L ≤ R → P = R) :
    ∃ P : Sylow p L, (P : Subgroup L).map L.subtype = L ⊓ Q := by
  obtain ⟨P, hQP⟩ := (hQ.comap_subtype (K := L)).exists_le_sylow
  have hn : A ⊓ normalizer (L : Set G) ≤
      normalizer ((P : Subgroup L).map L.subtype : Set G) := by
    rintro a ⟨ha, han⟩
    let e : MulAut L := L.normalizerMonoidHom ⟨a, han⟩
    let R := P.mapSurjective (f := e.toMonoidHom) e.surjective
    have hQR : Q.subgroupOf L ≤ R := by
      intro q hq
      refine ⟨e.symm q, hQP ?_, e.apply_symm_apply q⟩
      change a⁻¹ * (q : G) * (a⁻¹)⁻¹ ∈ Q
      exact ((hAQ (A.inv_mem ha)) q).mp hq
    have hRP : R = P := (hunique P R hQP hQR).symm
    apply mem_normalizer_iff_map_conj_eq.mpr
    change ((P : Subgroup L).map L.subtype).map (MulAut.conj a).toMonoidHom = _
    have he : ((P : Subgroup L).map e.toMonoidHom).map L.subtype =
        ((P : Subgroup L).map L.subtype).map (MulAut.conj a).toMonoidHom := by
      rw [map_map, map_map]
      rfl
    rw [← he]
    exact congrArg (fun R : Sylow p L => (R : Subgroup L).map L.subtype) hRP
  refine ⟨P, le_antisymm (le_inf (map_subtype_le _)
    (hL.stabilizer_saturation hsat _ (map_subtype_le _) (P.isPGroup'.map L.subtype) hn)) ?_⟩
  intro x hx
  exact ⟨⟨x, hx.1⟩, hQP hx.2, rfl⟩

end Theory.GroupTheory
