module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension
public import Theory.SpecificGroups.PSL3Two.Parabolics.Subgroups
public import Theory.SpecificGroups.SymmetricThreeProduct.Parabolics.Structure

/-!
# Exhaustive local parabolics from the genuine quotient models

The two-core is contained in the Sylow subgroup. Quotient correspondence
therefore pulls back the exhaustive pair of model parabolics, including its
intersection. Any two distinct maximal overgroups of that Sylow subgroup
are this pair. The source still has to identify its marked subgroups as
maximal; these lemmas do not assume an A₃ assembly record.

Source: Aschbacher--Smith, 14.4.8(2) and 14.4.13, printed pp.1009 and 1012;
the model subgroup classifications are the existing I.5 parabolic modules.
-/

public section
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.LocalAction

open Subgroup
open CFSG.Quasithin.Chapter14.Section04.LargerDimension

variable {G D : Type*} [Group G] [Group D]

private theorem map_coatom (f : G →* D) (hf : Function.Surjective f)
    (P : Subgroup G) (hp : IsCoatom P) (hk : f.ker ≤ P) : IsCoatom (P.map f) := by
  have hpre : (P.map f).comap f = P := by rw [comap_map_eq, sup_eq_left.mpr hk]
  constructor
  · intro he
    apply hp.1
    rw [← hpre, he, comap_top]
  · intro Q hQ
    have hlt : P < Q.comap f := by
      rw [← hpre]
      exact lt_of_le_of_ne (comap_mono hQ.le)
        (fun he => hQ.ne (comap_injective hf he))
    have htop := congrArg (fun A : Subgroup G => A.map f) (hp.2 _ hlt)
    simpa only [map_comap_eq_self_of_surjective hf, map_top_of_surjective _ hf] using htop

private theorem lift_pair (f : G →* D) (hf : Function.Surjective f)
    (S : Sylow 2 G) (hk : f.ker ≤ (S : Subgroup G))
    (P R : Subgroup D)
    (hp : Quasithin.I5.RankTwoParabolics D
      ((S : Subgroup G).map f) P R) :
    Quasithin.I5.RankTwoParabolics G (S : Subgroup G) (P.comap f) (R.comap f) := by
  refine ⟨isCoatom_comap_of_surjective hf hp.left_maximal,
    isCoatom_comap_of_surjective hf hp.right_maximal,
    fun h => hp.distinct ((comap_injective hf) h), ?_, ?_⟩
  · rw [← comap_inf, hp.borel_eq, comap_map_eq, sup_eq_left.mpr hk]
  · intro U hSU hU
    have hm := map_coatom f hf U hU (hk.trans hSU)
    rcases hp.exhaustive (U.map f) (map_mono hSU) hm with he | he
    · left
      have hpre := congrArg (fun A : Subgroup D => A.comap f) he
      simpa only [comap_map_eq, sup_eq_left.mpr (hk.trans hSU)] using hpre
    · right
      have hpre := congrArg (fun A : Subgroup D => A.comap f) he
      simpa only [comap_map_eq, sup_eq_left.mpr (hk.trans hSU)] using hpre

private theorem any_pair {B P R : Subgroup G} (hp : IsCoatom P) (hr : IsCoatom R)
    (hne : P ≠ R) (hbP : B ≤ P) (hbR : B ≤ R)
    (hex : ∃ P₀ R₀, Quasithin.I5.RankTwoParabolics G B P₀ R₀) :
    Quasithin.I5.RankTwoParabolics G B P R := by
  obtain ⟨P₀, R₀, h⟩ := hex
  have hP := h.exhaustive P hbP hp
  have hR := h.exhaustive R hbR hr
  rcases hP with rfl | rfl <;> rcases hR with rfl | rfl
  · exact False.elim (hne rfl)
  · exact h
  · refine ⟨h.right_maximal, h.left_maximal, h.distinct.symm, ?_, ?_⟩
    · simpa only [inf_comm] using h.borel_eq
    · intro U hBU hU
      exact (h.exhaustive U hBU hU).symm
  · exact False.elim (hne rfl)

private theorem exists_psl_pair (S : Sylow 2 Matrix.PSL3Two.PSL) :
    ∃ P R, Quasithin.I5.RankTwoParabolics Matrix.PSL3Two.PSL (S : Subgroup _) P R := by
  obtain ⟨P,R,hP,hR,hne,hi,_,_,he⟩ := Matrix.PSL3Two.sylow_parabolics S
  exact ⟨P,R,hP,hR,hne,hi,fun U hSU hU => (he U hU).mp hSU⟩

private theorem exists_prod_pair (S : Sylow 2 SymmetricThreeProduct.G) :
    ∃ P R, Quasithin.I5.RankTwoParabolics SymmetricThreeProduct.G
      (S : Subgroup _) P R := by
  obtain ⟨P,R,hne,hi,he⟩ := SymmetricThreeProduct.exists_parabolics_over_sylow S
  exact ⟨P,R, ((he P).mpr (Or.inl rfl)).1, ((he R).mpr (Or.inr rfl)).1,
    hne,hi,fun U hSU hU => (he U).mp ⟨hU,hSU⟩⟩

private theorem pair_in_extension [Finite G] [Finite D]
    (e : (G ⧸ pCore 2 G) ≃* D)
    (hex : ∀ S : Sylow 2 D, ∃ P R,
      Quasithin.I5.RankTwoParabolics D (S : Subgroup D) P R)
    (S : Sylow 2 G) : ∃ P R,
      Quasithin.I5.RankTwoParabolics G (S : Subgroup G) P R := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 G))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker ≤ (S : Subgroup G) := by
    dsimp only [f]
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
    exact pCore_isPGroup.le_sylow_of_normal S
  obtain ⟨P,R,h⟩ := hex (S.mapSurjective hf)
  exact ⟨P.comap f,R.comap f,lift_pair f hf S hk P R h⟩

/-- In the PSL₃(2) vertex, two marked maximal subgroups over the Sylow
subgroup have all five rank-two parabolic properties. -/
theorem rankTwoParabolics_of_linear_quotient [Finite G]
    (e : (G ⧸ pCore 2 G) ≃* Matrix.PSL3Two.PSL) (S : Sylow 2 G)
    (P R : Subgroup G) (hp : IsCoatom P) (hr : IsCoatom R)
    (hne : P ≠ R) (hSP : (S : Subgroup G) ≤ P) (hSR : (S : Subgroup G) ≤ R) :
    Quasithin.I5.RankTwoParabolics G (S : Subgroup G) P R := by
  exact any_pair hp hr hne hSP hSR (pair_in_extension e exists_psl_pair S)

/-- The same full conclusion in the S₃ × S₃ vertex, with its literal
quotient and Sylow subgroup. -/
theorem rankTwoParabolics_of_product_quotient [Finite G]
    (e : (G ⧸ pCore 2 G) ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))
    (S : Sylow 2 G) (P R : Subgroup G) (hp : IsCoatom P) (hr : IsCoatom R)
    (hne : P ≠ R) (hSP : (S : Subgroup G) ≤ P) (hSR : (S : Subgroup G) ≤ R) :
    Quasithin.I5.RankTwoParabolics G (S : Subgroup G) P R := by
  exact any_pair hp hr hne hSP hSR (pair_in_extension e exists_prod_pair S)

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.LocalAction
