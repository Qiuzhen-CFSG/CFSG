module
public import Theory.GroupTheory.ElementaryPairInvolutionUnion
public import Theory.GroupTheory.SaturatedCentralizerTransport

/-!
# A TI elementary subgroup cannot become a full fixed plane

Suppose every elementary subgroup of R lies in one of U and V. If each
fixed plane has order at most |Z|, a conjugate of the elementary TI subgroup
Z lying in that fixed part must equal a fixed plane. The nontrivial fixed
part of Z then forces that conjugate to be Z itself, contradicting the
properness of the fixed part of Z.

The fusion consumer aligns a two-subgroup inside the supplied Sylow
centralizer and uses strong involution closure to put it in R. This is the
outside linear fixed-group case of the source argument on printed p.539
of Aschbacher–Smith; no fixed-group isomorphism is required.
-/

public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

theorem no_conjugate_in_fixed_elementary_pair
    (R U V Z F : Subgroup G) [IsElementaryAbelian 2 Z]
    (hZU : Z ≤ U) (hZV : Z ≤ V)
    (hpair : ∀ E : Subgroup G, E ≤ R → IsElementaryAbelian 2 E → E ≤ U ∨ E ≤ V)
    (hTI : ∀ g : G, Z.map (MulAut.conj g).toMonoidHom = Z ∨
      Disjoint (Z.map (MulAut.conj g).toMonoidHom) Z)
    (hU : Nat.card (U ⊓ F : Subgroup G) ≤ Nat.card Z)
    (hV : Nat.card (V ⊓ F : Subgroup G) ≤ Nat.card Z)
    (hfixed : Z ⊓ F ≠ ⊥) (hproper : ¬ Z ≤ F)
    (g : G) (hER : Z.map (MulAut.conj g).toMonoidHom ≤ R)
    (hEF : Z.map (MulAut.conj g).toMonoidHom ≤ F) : False := by
  let E := Z.map (MulAut.conj g).toMonoidHom
  have hcard : Nat.card E = Nat.card Z := card_map_of_injective (MulAut.conj g).injective
  have hgen : Z ⊓ F ≤ E := by
    rcases hpair E hER (IsElementaryAbelian.map (MulAut.conj g).toMonoidHom) with hEU | hEV
    · have he : E = U ⊓ F := eq_of_le_of_card_ge (le_inf hEU hEF) (hcard ▸ hU)
      exact (inf_le_inf_right F hZU).trans_eq he.symm
    · have he : E = V ⊓ F := eq_of_le_of_card_ge (le_inf hEV hEF) (hcard ▸ hV)
      exact (inf_le_inf_right F hZV).trans_eq he.symm
  rcases hTI g with he | hd
  · exact hproper (he ▸ hEF)
  · apply hfixed
    exact eq_bot_iff.mpr (fun a ha => mem_bot.mpr (disjoint_def.mp hd (hgen ha) ha.1))

/-- Aligning in the actual Sylow centralizer and using involution closure
makes the preceding elementary-pair obstruction exclude fusion. -/
theorem not_conj_of_fixed_ti_elementary_pair
    (T : Sylow 2 G) (R U V Z : Subgroup G) [IsElementaryAbelian 2 Z]
    (hRT : R ≤ (T : Subgroup G)) (hZR : Z ≤ R) (hZU : Z ≤ U) (hZV : Z ≤ V)
    (hpair : ∀ E : Subgroup G, E ≤ R → IsElementaryAbelian 2 E → E ≤ U ∨ E ≤ V)
    (hTI : ∀ g : G, Z.map (MulAut.conj g).toMonoidHom = Z ∨
      Disjoint (Z.map (MulAut.conj g).toMonoidHom) Z)
    (hclosed : ∀ r t : T, orderOf r = 2 → (r : G) ∈ R →
      IsConj (r : G) (t : G) → (t : G) ∈ R)
    (s i : G)
    (hSylow : ∃ P : Sylow 2 (centralizer ({s} : Set G)),
      (P : Subgroup (centralizer ({s} : Set G))).map (centralizer ({s} : Set G)).subtype =
        (T : Subgroup G) ⊓ centralizer ({s} : Set G))
    (hiZ : Z ≤ centralizer ({i} : Set G))
    (hU : Nat.card (U ⊓ centralizer ({s} : Set G) : Subgroup G) ≤ Nat.card Z)
    (hV : Nat.card (V ⊓ centralizer ({s} : Set G) : Subgroup G) ≤ Nat.card Z)
    (hfixed : Z ⊓ centralizer ({s} : Set G) ≠ ⊥)
    (hproper : ¬ Z ≤ centralizer ({s} : Set G)) : ¬ IsConj i s := by
  intro his
  let Ts := (T : Subgroup G) ⊓ centralizer ({s} : Set G)
  have hmax (W : Subgroup G) (hWp : IsPGroup 2 W) (hTW : Ts ≤ W)
      (hWC : W ≤ centralizer ({s} : Set G)) : W = Ts := by
    obtain ⟨P,hP⟩ := hSylow
    have hPW : (P : Subgroup (centralizer ({s} : Set G))) ≤
        W.subgroupOf (centralizer ({s} : Set G)) := by
      intro a ha
      apply hTW
      change (a : G) ∈ (T : Subgroup G) ⊓ centralizer ({s} : Set G)
      rw [←hP]
      exact mem_map_of_mem _ ha
    have he := P.is_maximal' hWp.comap_subtype hPW
    have hh := congrArg (fun A : Subgroup (centralizer ({s} : Set G)) =>
      A.map (centralizer ({s} : Set G)).subtype) he
    change (W.subgroupOf (centralizer ({s} : Set G))).map
      (centralizer ({s} : Set G)).subtype = _ at hh
    rw [map_subgroupOf_eq_of_le hWC,hP] at hh
    exact hh
  obtain ⟨g,hg,hgZ⟩ := exists_conj_into_saturated_centralizer s i Ts Z
    (T.isPGroup'.to_le inf_le_left) (IsElementaryAbelian.isPGroup 2 Z) inf_le_right hiZ hmax his
  have hER : Z.map (MulAut.conj g).toMonoidHom ≤ R := by
    rintro y ⟨z,hz,rfl⟩
    by_cases hz1 : z=1
    · simp only [hz1,map_one]
      exact R.one_mem
    have hz2 : orderOf z = 2 := orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian z hz) hz1
    have hzT : z ∈ T := hRT (hZR hz)
    have hyT : (MulAut.conj g) z ∈ T := (hgZ (mem_map_of_mem _ hz)).1
    exact hclosed ⟨z,hzT⟩ ⟨(MulAut.conj g) z,hyT⟩
      ((orderOf_injective (T : Subgroup G).subtype (T : Subgroup G).subtype_injective _).symm.trans hz2)
      (hZR hz) (isConj_iff.mpr ⟨g,rfl⟩)
  exact no_conjugate_in_fixed_elementary_pair R U V Z (centralizer ({s} : Set G))
    hZU hZV hpair hTI hU hV hfixed hproper g hER (hgZ.trans inf_le_right)
end Subgroup
