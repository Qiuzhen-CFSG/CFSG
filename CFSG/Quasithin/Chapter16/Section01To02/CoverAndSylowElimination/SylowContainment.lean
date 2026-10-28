module

public import CFSG.Quasithin.Chapter16.Section01To02.CoverAndSylowElimination.Kernel
public import CFSG.Quasithin.Chapter16.Section01To02.CoverAndSylowElimination.PairAction
public import CFSG.Quasithin.Chapter16.Section01To02.CoverAndSylowElimination.Sylow
public import Theory.GroupTheory.PResidual.PrimeTo

/-!
# Containment of a third Sylow component

A conjugate of T_L contained in T and distinct from T_L centralizes T_L by
I.7.6. Adjoining z gives a two-subgroup R of twice its order. The actual
normalizer action on the conjugate component is inner by the explicit 16.1.6
input. Counting forces a nontrivial centralizer in R, and normalizer control
then places the component in H.

The earlier identity L₀ = O^{p′}(H), together with p′-perfectness of L,
strengthens this to containment in L₀. All residuals are prime-to-p residuals.
This supplies an alternative to the source's brief second-component step:
tight embedding in the commuting product will force a factor.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 16.2.9(1) and proof of Lemma 16.2.12, printed pp.1175–1176.
-/

public section

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter16 CFSG.Quasithin.ChapterI.Section06To08
namespace CFSG.Quasithin.Chapter16.CoverAndSylowElimination
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {z u : G} {L : Subgroup G}

/-- A distinct conjugate Sylow contained in T has its component in H. The
inner-action input is precisely 16.1.6 for that actual component. -/
theorem third_component_le (h : EarlierConclusions T z u L)
    (htight : IsTightlyEmbedded L) (hc : center L = ⊥)
    (hsize : 2 < Nat.card (componentSylow T L))
    {g : G} (hgT : conjSubgroup (componentSylow T L) g ≤ T)
    (hne : conjSubgroup (componentSylow T L) g ≠ componentSylow T L)
    (hinner : SylowCentralizingInner (conjSubgroup L g)) :
    conjSubgroup L g ≤ localComponentNormalizer z L := by
  let Q := componentSylow T L
  let S := conjSubgroup Q g
  let M := conjSubgroup L g
  let R := Q ⊔ zpowers z
  obtain ⟨hRT, hRp, hRc⟩ := h.enlarged_sylow_card hc
  have hQne : Q ≠ ⊥ := by
    intro he
    have he' : componentSylow T L = ⊥ := he
    rw [he'] at hsize
    simp at hsize
  have hSN : normalizer (S : Set G) ≤ normalizer (M : Set G) := by
    have hh := conjSubgroup_mono
      (htight.normalizer_le (T.isPGroup'.to_le inf_le_left) hQne inf_le_right) g
    simpa only [conjSubgroup, map_equiv_normalizer_eq, S, M, Q, componentSylow] using hh
  have hRS : R ≤ centralizer (S : Set G) := by
    refine sup_le (first_centralization h htight hsize hgT hne) (zpowers_le.mpr ?_)
    intro x hx
    exact mem_centralizer_singleton_iff.mp (h.localSetup.sylow_centralizes (hgT hx))
  have hRN : R ≤ normalizer (M : Set G) :=
    hRS.trans ((centralizer_le_normalizer _).trans hSN)
  obtain ⟨P₀, hP₀⟩ := h.localSetup.exists_component_sylow
  let e : L ≃* M := (MulAut.conj g).subgroupMap L
  let P : Sylow 2 M := P₀.mapSurjective (f := e.toMonoidHom) e.surjective
  have hPS : (P : Subgroup M).map M.subtype = S := by
    change ((P₀ : Subgroup L).map e.toMonoidHom).map M.subtype = _
    rw [map_map]
    have he : M.subtype.comp e.toMonoidHom = (MulAut.conj g).toMonoidHom.comp L.subtype := rfl
    rw [he, ← map_map, hP₀]
    have hmap : ((T : Subgroup G).subgroupOf L).map L.subtype = Q := by
      ext x
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨hx, x.property⟩
      · rintro ⟨hxT, hxL⟩
        exact ⟨⟨x, hxL⟩, hxT, rfl⟩
    rw [hmap]
    rfl
  have hPc : Nat.card P = Nat.card Q := by
    calc
      Nat.card P = Nat.card ((P : Subgroup M).map M.subtype) :=
        (Subgroup.card_map_of_injective M.subtype_injective).symm
      _ = Nat.card S := by rw [hPS]
      _ = Nat.card Q := card_conjSubgroup Q g
  have hMc : center M = ⊥ := by
    apply (center M).eq_bot_iff_card.mpr
    rw [← Nat.card_congr (centerCongr e).toEquiv, hc]
    simp
  have hi : ∀ r : R, ∃ m : M, actorHom R M hRN r = MulAut.conj m := by
    intro r
    apply hinner P (actorHom R M hRN r)
    · obtain ⟨n, hn⟩ := hRp r
      exact ⟨n, by rw [← map_pow, hn, map_one]⟩
    · intro x hx
      have hxS : (x : G) ∈ S := hPS ▸ mem_map_of_mem M.subtype hx
      apply Subtype.ext
      change (r : G) * (x : G) * (r : G)⁻¹ = (x : G)
      exact mul_inv_eq_iff_eq_mul.mpr (hRS r.property x hxS).symm
  have hCne : R ⊓ centralizer (M : Set G) ≠ ⊥ := by
    apply inner_centralizer_ne_bot R M hRN hRp hMc P hi
    rw [hPc, hRc]
    change Nat.card Q < 2 * Nat.card Q
    have hp : 0 < Nat.card Q := Nat.card_pos
    omega
  have hCH := h.normalizer_control (R ⊓ centralizer (M : Set G))
    (hRp.to_le inf_le_left) hCne
    (inf_le_left.trans (sup_le (inf_le_right.trans le_sup_right) le_sup_left))
  exact (le_centralizer_iff.mpr inf_le_right).trans ((centralizer_le_normalizer _).trans hCH)

private theorem residual_map_le {A B : Type*} [Group A] [Group B]
    (p : ℕ) (f : A →* B) : (primeToResidual p A).map f ≤ primeToResidual p B := by
  apply le_sInf
  rintro N ⟨hN, hc⟩
  let := hN
  rw [map_le_iff_le_comap]
  apply primeToResidual_le
  rw [N.index_comap]
  exact hc.coprime_dvd_right (N.relIndex_dvd_index_of_normal f.range)

/-- The preceding residual identity places this component in the actual
local component closure, retaining the prime and residual conventions. -/
theorem third_component_le_closure (h : EarlierConclusions T z u L)
    (htight : IsTightlyEmbedded L) (hc : center L = ⊥)
    (hsize : 2 < Nat.card (componentSylow T L))
    (p : ℕ) (hself : primeToResidual p L = ⊤)
    (hres : (primeToResidual p (localComponentNormalizer z L)).map
      (localComponentNormalizer z L).subtype = localComponentClosure z L)
    {g : G} (hgT : conjSubgroup (componentSylow T L) g ≤ T)
    (hne : conjSubgroup (componentSylow T L) g ≠ componentSylow T L)
    (hinner : SylowCentralizingInner (conjSubgroup L g)) :
    conjSubgroup L g ≤ localComponentClosure z L := by
  let M := conjSubgroup L g
  let H := localComponentNormalizer z L
  have hMH : M ≤ H := third_component_le h htight hc hsize hgT hne hinner
  let e : L ≃* M := (MulAut.conj g).subgroupMap L
  have hMself : primeToResidual p M = ⊤ := by
    rw [← map_primeToResidual e, hself, map_top_of_surjective _ e.surjective]
  have hm := residual_map_le p (inclusion hMH)
  rw [hMself, ← MonoidHom.range_eq_map] at hm
  rw [← hres]
  intro x hx
  exact ⟨⟨x, hMH hx⟩, hm ⟨⟨x, hx⟩, rfl⟩, rfl⟩

end CFSG.Quasithin.Chapter16.CoverAndSylowElimination
