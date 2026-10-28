module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.SuzukiContainment.OddBorel
public import Theory.GroupTheory.Amalgam.LocalStructure

/-!
# Odd local outer action with finite stabilizers

Restrict the source S and local factor to their finite full parabolic.
Transport the actual local quotient and Sylow through the inclusion, apply
the coprime outer-action normalizer theorem there, and return its conclusion
to the original ambient group. This removes the unnecessary finite ambient
hypothesis from the odd-degree linear Borel calculation.

The binary triality restoration uses this for the original field degrees
three and one. Source: DGS (1985), (15.2), pp.226–228; Aschbacher–Smith
F.1.9–12, pp.261–264. Only finite stabilizers are needed.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension

/-- Odd linear field degree normalizes the original S using only a finite
parabolic, without assuming that the source completion is finite. -/
theorem odd_linear_borel_normalizes_of_finite_parabolics
    {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
    (h : HypothesisF11 L S) (i : Fin 2) {n : ℕ} (hn : Odd n)
    (he : ClassicalGroup.IsPSL (L i ⧸ pCore 2 (L i)) 2 (2^n)) :
    borel (L i) S ≤ normalizer (S : Set G) := by
  let D := parabolic L S i
  let : Finite D := h.finite_parabolic i
  let : Finite (L i) := h.finite_local i
  have hLD : L i ≤ D := le_sup_left.trans le_sup_left
  have hSD : S ≤ D := le_sup_right.trans le_sup_left
  let K := (L i).subgroupOf D
  let R := S.subgroupOf D
  let v : K ≃* L i := subgroupOfEquivOfLe hLD
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := he
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let q := (LocalCoreTransport.quotientEquiv 2 v).trans e
  have hz : center (K ⧸ pCore 2 K) = ⊥ := by
    apply bot_unique
    intro x hx
    have hx' : q x ∈ center (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
      (centerCongr q ⟨x,hx⟩).property
    rw [GorensteinWalter.psl2_center_eq_bot F, mem_bot] at hx'
    exact mem_bot.mpr (q.injective (hx'.trans (map_one q).symm))
  have ho : Nat.Coprime 2 (Nat.card (MulAut.Outer (K ⧸ pCore 2 K))) := by
    rw [Nat.card_congr (MulAut.outerCongr q).toEquiv,
      Theory.PSL2.outer_card_eq_field_degree F hF]
    exact hn.coprime_two_left
  obtain ⟨U,hU⟩ := h.sylow i
  let U' := U.mapSurjective (f := v.symm.toMonoidHom) v.symm.surjective
  have hUR : (U' : Subgroup K).map K.subtype ≤ R := by
    rintro x ⟨y,hy,rfl⟩
    obtain ⟨u,hu,rfl⟩ := hy
    have hs : u.val ∈ S ⊓ L i := hU ▸ mem_map_of_mem (L i).subtype hu
    exact hs.1
  have hRK : R ≤ normalizer (K : Set D) := by
    rw [← subgroupOf_normalizer_eq hLD]
    exact comap_mono (h.S_normalizes i)
  have hN := pGroup_sylow_normalizer_le_of_coprime_outer R K
    h.S_isP.comap_subtype hRK hz ho U' hUR
  have hUeq : (U : Subgroup (L i)) = (S ⊓ L i).subgroupOf (L i) := by
    apply map_injective (L i).subtype_injective
    rw [hU,map_subgroupOf_eq_of_le inf_le_right]
  intro x hx
  let xL : L i := ⟨x,hx.1⟩
  have hxN : xL ∈ normalizer (U : Set (L i)) := by
    change xL ∈ normalizer ((U : Subgroup (L i)) : Set (L i))
    rw [hUeq,← subgroupOf_normalizer_eq inf_le_right]
    exact hx.2
  have hxN' : v.symm xL ∈ normalizer (U' : Set K) := by
    change v.symm xL ∈ normalizer
      (((U : Subgroup (L i)).map v.symm.toMonoidHom) : Set K)
    rw [← map_equiv_normalizer_eq]
    exact mem_map_of_mem v.symm.toMonoidHom hxN
  have hh := hN (mem_map_of_mem K.subtype hxN')
  rw [← subgroupOf_normalizer_eq hSD] at hh
  exact hh

end CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension
