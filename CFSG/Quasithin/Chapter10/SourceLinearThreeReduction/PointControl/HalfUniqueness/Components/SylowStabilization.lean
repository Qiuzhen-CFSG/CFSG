module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.Components.Stabilization
public import Theory.GroupTheory.PairNormalizerIndex

/-!
# Stabilization before containing-component distinctness

The original maximal local M permutes the two T-conjugates of L. If H ∩ M
exchanged them, its stabilizer would have index two. But H ∩ M contains
the prescribed Sylow N_T(L) of H, which fixes L. Sylow index rules out
that exchange. Thus the intersection fixes both factors before A.3.12
establishes distinctness of their containing components.

These statements retain the original half-join, exchanger and relative Sylow.
Source: Aschbacher--Smith, the setup of 10.2.6, printed pp.748--749.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {H : Subgroup G} {t : G} {K₁ K₂ : Subgroup H}

/-- The prescribed Sylow fixes the original pair, so the whole intersection fixes L.
No distinctness of the containing components is needed. -/
theorem ContainingPair.intersection_normalizes_left_of_sylow (C : ContainingPair D H t K₁ K₂)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    H ⊓ D.maximalLocal ≤ normalizer (L : Set G) := by
  let R := (T : Subgroup G) ⊓ normalizer (L : Set G)
  let A := H ⊓ D.maximalLocal
  have hRH : R ≤ H := le_sup_right.trans C.half_le
  have hRA : R ≤ A := le_inf hRH (inf_le_left.trans (le_normalizer_componentOrbit L T))
  by_contra hnA
  obtain ⟨x,hx,hxn⟩ := SetLike.not_le_iff_exists.mp hnA
  have hi := normalizer_relIndex_eq_two_of_pair A L
    (L.map (MulAut.conj t).toMonoidHom)
    (fun m hm => source_nonnormal_maximal_pair D hn C.t_mem C.t_not_normalizes m hm.2)
    x hx (fun he => hxn (mem_normalizer_iff_map_conj_eq.mpr he))
  have hd : 2 ∣ R.relIndex A := hi ▸ relIndex_dvd_of_le_left A
    (show R ≤ normalizer (L : Set G) from inf_le_right)
  have hdH : R.relIndex A ∣ R.relIndex H :=
    dvd_of_mul_right_eq (A.relIndex H) (relIndex_mul_relIndex R A H hRA inf_le_left)
  obtain ⟨P,hP⟩ := C.sylow
  change (P : Subgroup H).map H.subtype = R at hP
  have he : R.subgroupOf H = (P : Subgroup H) := by
    rw [←hP]
    exact comap_map_eq_self_of_injective H.subtype_injective _
  have hiP : R.relIndex H = (P : Subgroup H).index := by
    change (R.subgroupOf H).index = _
    rw [he]
  exact P.not_dvd_index (hiP ▸ hd.trans hdH)
/-- The same Sylow argument fixes the actual opposite factor. -/
theorem ContainingPair.intersection_normalizes_right_of_sylow
    (C : ContainingPair D H t K₁ K₂)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    H ⊓ D.maximalLocal ≤ normalizer (L.map (MulAut.conj t).toMonoidHom : Set G) :=
  (le_inf (C.intersection_normalizes_left_of_sylow hn) inf_le_right).trans
    (source_nonnormal_component_normalizer_fixes_opposite D hn C.t_mem C.t_not_normalizes)

/-- Both alternatives for any original T-conjugate are fixed by H ∩ M. -/
theorem ContainingPair.intersection_normalizes_conjugate_of_sylow
    (C : ContainingPair D H t K₁ K₂)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {s : G} (hs : s ∈ (T : Subgroup G)) :
    H ⊓ D.maximalLocal ≤ normalizer (L.map (MulAut.conj s).toMonoidHom : Set G) := by
  rcases source_nonnormal_maximal_pair D hn C.t_mem C.t_not_normalizes s
      (le_normalizer_componentOrbit L T hs) with he | he
  · rw [he]
    exact C.intersection_normalizes_left_of_sylow hn
  · rw [he]
    exact C.intersection_normalizes_right_of_sylow hn

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
