module

public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.Choice
public import CFSG.Quasithin.Chapter16.Section04To05.RelativeSylow
public import Theory.GroupTheory.GeneralizedFitting.StandardComponent

/-!
# Transport of Δ and Δ₀ under conjugation

An ambient automorphism transports centralizers, relative normalizers and
actual Sylow subgroups. It preserves the omega containment defining Δ₀.
Consequently Δ₀ is empty for L exactly when it is empty for a conjugate of L,
and the order assertion in 16.4.9(1) transports to that conjugate as well.
These are the changes of base needed when exchanging K and K′ in the proof.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
16.4.9, printed pp.1189–1190. All conjugations here are left conjugations.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter16.Intersections

variable {G : Type*} [Group G]

private theorem map_conj (H : Subgroup G) (e : G ≃* G) (g : G) :
    (H.conjBy g).map e.toMonoidHom = (H.map e.toMonoidHom).conjBy (e g) := by
  change (H.map (MulAut.conj g).toMonoidHom).map e.toMonoidHom =
    (H.map e.toMonoidHom).map (MulAut.conj (e g)).toMonoidHom
  rw [map_map, map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply]

/-- The family Δ is preserved by ambient automorphisms. -/
theorem mem_delta_map {L J : Subgroup G} (hJ : J ∈ delta L) (e : G ≃* G) :
    J.map e.toMonoidHom ∈ delta (L.map e.toMonoidHom) := by
  have hC : (centralizer (L : Set G)).map e.toMonoidHom =
      centralizer (L.map e.toMonoidHom : Set G) := map_centralizer_equiv _ e
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨g, hg⟩ := hJ.1
    exact ⟨e g, by rw [hg, map_conj, hC]⟩
  · intro he
    apply hJ.2.1
    exact map_injective e.injective (he.trans hC.symm)
  · rw [← hC, ← map_equiv_normalizer_eq, ← map_inf _ _ _ e.injective,
      card_map_of_injective e.injective]
    exact hJ.2.2

/-- The family Δ₀ is preserved, including its actual Sylow witness. -/
theorem mem_deltaZero_map [Finite G] {L J : Subgroup G} (hJ : J ∈ deltaZero L) (e : G ≃* G) :
    J.map e.toMonoidHom ∈ deltaZero (L.map e.toMonoidHom) := by
  obtain ⟨hd, R, hR, hinner⟩ := hJ
  have hC : (centralizer (L : Set G)).map e.toMonoidHom =
      centralizer (L.map e.toMonoidHom : Set G) := map_centralizer_equiv _ e
  refine ⟨mem_delta_map hd e, R.map e.toMonoidHom, ?_, ?_⟩
  · have hs := SylowIn.map hR e
    rwa [map_inf _ _ _ e.injective, map_equiv_normalizer_eq, hC] at hs
  · have ho : omegaOneAmbient (R.map e.toMonoidHom) ≤
        (centralizer (L : Set G) ⊔ L).map e.toMonoidHom := by
      apply (omegaOneAmbient_le_iff _ _).mpr
      rintro y ⟨x, hx, rfl⟩ hy
      have hx2 : x ^ 2 = 1 := e.injective (by simpa using hy)
      exact ⟨x, (omegaOneAmbient_le_iff _ _).mp hinner x hx hx2, rfl⟩
    rwa [Subgroup.map_sup, hC] at ho

/-- Simultaneous conjugation preserves membership in Δ. -/
theorem mem_delta_conjBy_iff {L J : Subgroup G} (g : G) :
    J.conjBy g ∈ delta (L.conjBy g) ↔ J ∈ delta L := by
  constructor
  · intro h
    have hh := mem_delta_map h (MulAut.conj g⁻¹)
    change (J.conjBy g).conjBy g⁻¹ ∈ delta ((L.conjBy g).conjBy g⁻¹) at hh
    simpa only [conjBy_inv] using hh
  · exact fun h => mem_delta_map h (MulAut.conj g)

/-- Simultaneous conjugation preserves membership in Δ₀. -/
theorem mem_deltaZero_conjBy_iff [Finite G] {L J : Subgroup G} (g : G) :
    J.conjBy g ∈ deltaZero (L.conjBy g) ↔ J ∈ deltaZero L := by
  constructor
  · intro h
    have hh := mem_deltaZero_map h (MulAut.conj g⁻¹)
    change (J.conjBy g).conjBy g⁻¹ ∈ deltaZero ((L.conjBy g).conjBy g⁻¹) at hh
    simpa only [conjBy_inv] using hh
  · exact fun h => mem_deltaZero_map h (MulAut.conj g)

/-- The empty-family assumption transports when K and K′ are exchanged. -/
theorem deltaZero_conjBy_nonempty_iff [Finite G] {L : Subgroup G} (g : G) :
    (deltaZero (L.conjBy g)).Nonempty ↔ (deltaZero L).Nonempty := by
  constructor
  · rintro ⟨J, hJ⟩
    refine ⟨J.conjBy g⁻¹, ?_⟩
    have hh := mem_deltaZero_map hJ (MulAut.conj g⁻¹)
    change J.conjBy g⁻¹ ∈ deltaZero ((L.conjBy g).conjBy g⁻¹) at hh
    simpa only [conjBy_inv] using hh
  · rintro ⟨J, hJ⟩
    exact ⟨J.conjBy g, (mem_deltaZero_conjBy_iff g).mpr hJ⟩


/-- The order assertion for L supplies the same assertion for its conjugates. -/
theorem OrderTwoOutsideDeltaZero.conjBy [Finite G] {L : Subgroup G}
    (h : OrderTwoOutsideDeltaZero L) (g : G) : OrderTwoOutsideDeltaZero (L.conjBy g) := by
  intro J hJ hnot R hR
  let e := MulAut.conj g⁻¹
  have hLm : (L.conjBy g).map e.toMonoidHom = L := conjBy_inv L g
  have hC : (centralizer (L.conjBy g : Set G)).map e.toMonoidHom =
      centralizer (L : Set G) := by
    have hc : (centralizer (L.conjBy g : Set G)).map e.toMonoidHom =
        centralizer ((L.conjBy g).map e.toMonoidHom : Set G) := map_centralizer_equiv _ e
    rwa [hLm] at hc
  have hJ' : J.conjBy g⁻¹ ∈ delta L := by
    have hh := mem_delta_map hJ e
    rwa [hLm] at hh
  have hnot' : J.conjBy g⁻¹ ∉ deltaZero L := by
    intro hh
    have hm := mem_deltaZero_map hh (MulAut.conj g)
    change (J.conjBy g⁻¹).conjBy g ∈ deltaZero (L.conjBy g) at hm
    exact hnot (by simpa only [conjBy_inv'] using hm)
  have hR' : SylowIn (R.conjBy g⁻¹)
      (J.conjBy g⁻¹ ⊓ normalizer (centralizer (L : Set G) : Set G)) := by
    have hh := SylowIn.map hR e
    rwa [map_inf _ _ _ e.injective, map_equiv_normalizer_eq, hC] at hh
  have hc := h (J.conjBy g⁻¹) hJ' hnot' (R.conjBy g⁻¹) hR'
  change Nat.card (R.map e.toMonoidHom) = 2 at hc
  rwa [card_map_of_injective e.injective] at hc

/-- Equality of the component and centralizer normalizers transports to conjugates. -/
theorem normalizers_eq_conjBy {L : Subgroup G}
    (hn : normalizer (centralizer (L : Set G) : Set G) = normalizer (L : Set G))
    (g : G) : normalizer (centralizer (L.conjBy g : Set G) : Set G) =
      normalizer (L.conjBy g : Set G) := by
  let e := MulAut.conj g
  have hC : (centralizer (L : Set G)).map e.toMonoidHom =
      centralizer (L.conjBy g : Set G) := map_centralizer_equiv _ e
  have hh := congrArg (fun Q : Subgroup G => Q.map e.toMonoidHom) hn
  rw [map_equiv_normalizer_eq, map_equiv_normalizer_eq, hC] at hh
  exact hh


end CFSG.Quasithin.Chapter16.Intersections
