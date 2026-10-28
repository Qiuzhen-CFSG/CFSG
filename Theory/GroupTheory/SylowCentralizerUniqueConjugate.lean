module
public import Theory.GroupTheory.SylowCentralizerConjugacy
public import Theory.GroupAction.SubgroupConjugation
/-!
# Sylow centralizers from unique conjugate containment

Let T be a Sylow two-subgroup contained in M. Suppose C_T(u) is Sylow
in C_M(u), has index at most two in T, and C_M(u) lies in a unique conjugate
of M, with its conjugator in M. If every T-central conjugate of u has its
full centralizer in M, then C_T(u) is Sylow in C_G(u).

A larger centralizer two-subgroup would have ambient Sylow order. Conjugate
it to T, apply centralizer containment and conjugate rigidity, and contradict
Sylow maximality in C_M(u). The case C_T(u)=T is immediate by restriction.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
13.1.12(3), printed p.873, first paragraph of the Sylow upgrade.
-/

open Subgroup
open scoped Pointwise

/-- Unique conjugate containment upgrades the local index-at-most-two
centralizer Sylow subgroup to the full centralizer. -/
public theorem Sylow.exists_sylow_centralizer_eq_of_unique_conjugate {G : Type*} [Group G] [Finite G] (T : Sylow 2 G)
    (M : Subgroup G) (hTM : (T : Subgroup G) ≤ M) (u : G)
    (hlocal : ∃ S : Sylow 2 (M ⊓ centralizer ({u} : Set G) : Subgroup G),
      (S : Subgroup (M ⊓ centralizer ({u} : Set G) : Subgroup G)) =
        (T : Subgroup G).subgroupOf (M ⊓ centralizer ({u} : Set G)))
    (hindex : ((centralizer ({u} : Set G)).subgroupOf (T : Subgroup G)).index ≤ 2)
    (hcentral : ∀ g : G,
      (T : Subgroup G) ≤ centralizer ({g * u * g⁻¹} : Set G) →
        centralizer ({g * u * g⁻¹} : Set G) ≤ M)
    (hunique : ∀ g : G, M ⊓ centralizer ({u} : Set G) ≤ M.conjBy g → g ∈ M) :
    ∃ S : Sylow 2 (centralizer ({u} : Set G)),
      (S : Subgroup (centralizer ({u} : Set G))) =
        (T : Subgroup G).subgroupOf (centralizer ({u} : Set G)) := by
  let C := centralizer ({u} : Set G)
  by_cases hTC : (T : Subgroup G) ≤ C
  · exact ⟨T.subtype hTC, rfl⟩
  let P := (T : Subgroup G).subgroupOf C
  let D := C.subgroupOf (T : Subgroup G)
  have hP : IsPGroup 2 P := T.isPGroup'.comap_subtype
  obtain ⟨S, hPS⟩ := hP.exists_le_sylow
  refine ⟨S, ?_⟩
  by_contra hne
  have hlt : Nat.card P < Nat.card S := by
    by_contra! h
    exact hne (eq_of_le_of_card_ge hPS h).symm
  let K := (S : Subgroup C).map C.subtype
  have hKp : IsPGroup 2 K := S.isPGroup'.map C.subtype
  obtain ⟨R, hKR⟩ := hKp.exists_le_sylow
  have hRS : Nat.card R = Nat.card T := Nat.card_congr (R.equiv T).toEquiv
  have hKcard : Nat.card K = Nat.card S := card_map_of_injective C.subtype_injective
  have hPcard : Nat.card P = Nat.card D := by
    have he : P.map C.subtype = D.map (T : Subgroup G).subtype := by
      rw [subgroupOf_map_subtype, subgroupOf_map_subtype, inf_comm]
    have hh := congrArg (fun U : Subgroup G => Nat.card U) he
    simpa only [card_map_of_injective C.subtype_injective,
      card_map_of_injective (T : Subgroup G).subtype_injective] using hh
  have hcard : Nat.card T ≤ 2 * Nat.card P := by
    have hh := D.card_mul_index
    change D.index ≤ 2 at hindex
    rw [← hh, hPcard]
    nlinarith
  have hKeq : K = (R : Subgroup G) := by
    apply eq_of_le_of_card_ge hKR
    have he : Nat.card R = Nat.card K := Nat.eq_of_dvd_of_lt_two_mul Nat.card_pos.ne'
      (card_dvd_of_le hKR) (by rw [hRS, hKcard]; omega)
    exact he.le
  have hRC : (R : Subgroup G) ≤ C := hKeq ▸ map_subtype_le (S : Subgroup C)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G R T
  let f : G ≃* G := MulAut.conj g
  have hmap : (R : Subgroup G).map f.toMonoidHom = (T : Subgroup G) := by
    exact congrArg Sylow.toSubgroup hg
  have hTCg : (T : Subgroup G) ≤ centralizer ({f u} : Set G) := by
    rw [← hmap]
    rintro _ ⟨r, hr, rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    change f r * f u = f u * f r
    simpa only [map_mul] using congrArg f (mem_centralizer_singleton_iff.mp (hRC hr))
  have hCgM : centralizer ({f u} : Set G) ≤ M := hcentral g hTCg
  have hMu : M ⊓ C ≤ M.conjBy g⁻¹ := by
    intro x hx
    have hfx : f x ∈ M := hCgM (mem_centralizer_singleton_iff.mpr (by
      simpa only [map_mul] using congrArg f (mem_centralizer_singleton_iff.mp hx.2)))
    refine ⟨f x, hfx, ?_⟩
    change g⁻¹ * (g * x * g⁻¹) * (g⁻¹)⁻¹ = x
    group
  have hgM : g ∈ M := by
    simpa only [inv_mem_iff] using hunique g⁻¹ hMu
  have hRM : (R : Subgroup G) ≤ M := by
    intro r hr
    have hfr : f r ∈ M := hTM (hmap ▸ mem_map_of_mem f.toMonoidHom hr)
    have hh := M.mul_mem (M.mul_mem (M.inv_mem hgM) hfr) hgM
    change g⁻¹ * (g * r * g⁻¹) * g ∈ M at hh
    simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using hh
  let Mu := M ⊓ C
  obtain ⟨Q, hQ⟩ := hlocal
  have hRQ : R.subgroupOf Mu = (Q : Subgroup Mu) := by
    apply Q.is_maximal' (R.isPGroup'.comap_subtype (K := Mu))
    rw [hQ]
    intro x hx
    apply hKR
    exact mem_map_of_mem C.subtype (hPS (show (⟨(x : G), x.property.2⟩ : C) ∈ P from hx))
  have hRT : (R : Subgroup G) ≤ (T : Subgroup G) := by
    intro r hr
    have hh : (⟨r, hRM hr, hRC hr⟩ : Mu) ∈ R.subgroupOf Mu := hr
    rw [hRQ, hQ] at hh
    exact hh
  exact hTC ((R.is_maximal' T.isPGroup' hRT).symm ▸ hRC)
