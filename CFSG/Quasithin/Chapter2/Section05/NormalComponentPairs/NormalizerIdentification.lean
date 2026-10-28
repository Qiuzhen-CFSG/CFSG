module
public import CFSG.Quasithin.Chapter2.Section05.NormalComponentPairs.NormalizerSource
public import Theory.GroupTheory.SixActionSylowOvergroup
public import Theory.GroupTheory.SpecificGroups.KleinFourAut

/-!
# Largest local pairs are four-group normalizers

A normal four in a largest local pair has its centralizer inside the source
Sylow subgroup. Its normalizer is therefore characteristic two, and the
largest-pair cardinal bound makes the original base a Sylow subgroup of
that normalizer. The action on the four-group has two-group kernel and
image in S₃; the local pair has an odd part, forcing normalizer equality.
Source: Aschbacher--Smith 2.5.12(1), printed pp.557--558.
-/

public section
namespace CFSG.Quasithin.Chapter2.Section05
open Subgroup Theory.GroupTheory A6Shadow.Frattini
variable {G : Type*} [Group G] [Finite G]
  {M H Y U L E : Subgroup G}

/-- The normal four determines both coordinates of the largest pair. -/
theorem largest_pair_eq_four_normalizer
    (hp : (U,L) ∈ largestLocalPairs M H) (hUY : U ≤ Y)
    (hY : IsPGroup 2 Y) (hYM : Y ≤ M) (hYH : Y ≤ H) (hEH : E ≤ H)
    [IsKleinFour E] (hLN : L ≤ normalizer (E : Set G))
    (hC : H ⊓ centralizer (E : Set G) ≤ Y) :
    L = H ⊓ normalizer (E : Set G) ∧ U = Y ⊓ normalizer (E : Set G) := by
  let N := H ⊓ normalizer (E : Set G)
  have hLN' : L ≤ N := le_inf hp.1.2 hLN
  have hUN : U ≤ N := hp.1.1.2.2.2.1.trans hLN'
  have hEN : E ≤ N := le_inf hEH E.le_normalizer
  let f : N →* MulAut E := E.normalizerMonoidHom.comp (inclusion inf_le_right)
  have hfker : f.ker = (centralizer (E : Set G)).subgroupOf N := by
    ext x
    change E.normalizerMonoidHom (inclusion inf_le_right x) = 1 ↔ _
    rw [← MonoidHom.mem_ker, normalizerMonoidHom_ker]
    rfl
  have hkerY : f.ker ≤ Y.subgroupOf N := by
    rw [hfker]
    intro x hx
    exact hC ⟨x.property.1, hx⟩
  have hk : IsPGroup 2 f.ker := hY.comap_subtype.to_le hkerY
  let : IsElementaryAbelian 2 E := {
    toIsMulCommutative := IsKleinFour.isMulCommutative
    exponent_dvd_p := by simp }
  have hEp : IsPGroup 2 E := IsElementaryAbelian.isPGroup 2 E
  have hEn : (E.subgroupOf N).Normal :=
    (normal_subgroupOf_iff_le_normalizer hEN).mpr inf_le_right
  let := hEn
  have hEc : E.subgroupOf N ≤ pCore 2 N := le_sSup ⟨inferInstance,hEp.comap_subtype⟩
  have hkc : f.ker ≤ pCore 2 N := le_sSup ⟨inferInstance,hk⟩
  have hN : N ∈ Chapter1.He G := by
    apply Chapter1.mem_He_iff.mpr
    intro x hx
    apply hkc
    rw [hfker]
    intro e he
    exact congrArg Subtype.val (hx (⟨e,hEN he⟩ : N) (hEc he))
  have hcore : twoCore N ≠ ⊥ := by
    intro hh
    have hEbot : E = ⊥ := bot_unique ((le_pCoreIn_of_normalizes hEp hEN inf_le_right).trans
      (le_of_eq hh))
    have hc := IsKleinFour.card_four (G := E)
    simp [hEbot] at hc
  have hpair : (U,N) ∈ localPairs (Chapter1.He G) M :=
    ⟨hp.1.1.1,hN,hcore,hUN,fun hn => hp.1.1.2.2.2.2 (hLN'.trans hn)⟩
  obtain ⟨P,hUP,hPb⟩ := beta_exists_sylow hpair.1 hpair.2.2.2.1
  have hp' : ((P : Subgroup N).map N.subtype,N) ∈ localPairs (Chapter1.He G) M :=
    ⟨hPb,hN,hcore,map_subtype_le _,hpair.2.2.2.2⟩
  have hPU : (P : Subgroup N).map N.subtype = U :=
    (eq_of_le_of_card_ge hUP (hp.2 _ ⟨N,hp'⟩)).symm
  have hPL : (P : Subgroup N) ≤ L.subgroupOf N := by
    intro x hx
    exact hp.1.1.2.2.2.1 (hPU ▸ mem_map_of_mem N.subtype hx)
  have hLP : ¬ IsPGroup 2 (L.subgroupOf N) := by
    intro hh
    have heq : (P : Subgroup N) = L.subgroupOf N := (P.is_maximal' hh hPL).symm
    have hLU : L ≤ U := by
      intro x hx
      rw [← hPU]
      exact mem_map_of_mem N.subtype (heq ▸ (show (⟨x,hLN' hx⟩ : N) ∈ L.subgroupOf N from hx))
    exact hp.1.1.2.2.2.2 (hLU.trans (hUY.trans hYM))
  have htop : L.subgroupOf N = ⊤ :=
    eq_top_of_sylow_le_of_six_action P _ hPL hLP f hk (IsKleinFour.card_mulAut E)
  have hNL : N ≤ L := subgroupOf_eq_top.mp htop
  have hNY : (Y ⊓ N).subgroupOf N = (P : Subgroup N) := by
    apply P.is_maximal' (hY.to_le inf_le_left).comap_subtype
    intro x hx
    exact ⟨hUY (hPU ▸ mem_map_of_mem N.subtype hx),x.property⟩
  refine ⟨le_antisymm hLN' hNL, le_antisymm (le_inf hUY (hUN.trans inf_le_right)) ?_⟩
  intro x hx
  have hxH : x ∈ H := hYH hx.1
  have hxN : x ∈ N := ⟨hxH,hx.2⟩
  rw [← hPU]
  exact mem_map_of_mem N.subtype (hNY ▸ (show (⟨x,hxN⟩ : N) ∈ (Y ⊓ N).subgroupOf N from ⟨hx.1,hxN⟩))
end CFSG.Quasithin.Chapter2.Section05
