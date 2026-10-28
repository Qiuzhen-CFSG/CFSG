module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeChangedSylowMarking
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGeneric

/-!
# The marked changed-Sylow comparison in original 12.2.2

The actual chosen-module input supplies the common Sylow intersections
and a conjugator preserving L, the left Cartan and its prime actor. In
the larger-Sylow branch the selected right factor has a strict containing
C-component in the common-normal overgroup. Local maximality of that
factor therefore forces the smaller-Sylow alternative.

The maximality premise and the remaining source branches are obligations
of qt-d-1222-rankone-cartan-local-to-global and its earlier-source inputs.
No comparison of the two field parameters or final normalization is asserted.
Source: Aschbacher--Smith 5.2.2, pp.648--649, used in 12.2.2, p.795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric Chapter6.Source.RankOneGeneric.Prime
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B D R : Subgroup G} (C : ChosenModule T L V)
include C

/-- Retain the literal Cartan, prime actor, Sylow maps and strict common
component on the changed-Sylow witness of the original chosen-module problem. -/
theorem rankOne_prime_changedSylow_marked_comparison
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n p : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (d : LocalData T L H B D R)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥) :
    ∃ P : Sylow 2 (extension T L H B D R),
      let T₁ := (P : Subgroup (extension T L H B D R)).map (extension T L H B D R).subtype
      let X := normalizer (normalizingSylow T R : Set G) ⊔ H
      normalizingSylow T R ≤ T₁ ∧
      T₁ ⊓ L = (T : Subgroup G) ⊓ L ∧
      T₁ ⊓ residual H = (T : Subgroup G) ⊓ residual H ∧
      T₁ ⊓ R = (T : Subgroup G) ⊓ R ∧
      (T₁ = normalizingSylow T R ∨ ∃ U : Sylow 2 G,
        (U : Subgroup G) = T₁ ∧ localBorel U L = localBorel T L ∧
        A ≤ localBorel U L ∧ IsHallSubgroup OddHall.oddPrimes (A.subgroupOf (localBorel U L)) ∧
        ∃ (x : G) (I : Subgroup G),
          x ∈ normalizer (normalizingSylow T R : Set G) ∧
          x ∈ normalizer (L : Set G) ∧ x ∈ normalizer (A : Set G) ∧
          x ∈ normalizer (D : Set G) ∧
          (T : Subgroup G).map (MulAut.conj x).toMonoidHom = (U : Subgroup G) ∧
          ¬ R.map (MulAut.conj x).toMonoidHom ≤ extension T L H B D R ∧
          R < I ∧ I ≤ X ∧ (I.subgroupOf X).IsCComponent ∧
          normalizingSylow T R ≤ normalizer (I : Set G) ∧
          (∀ J : Subgroup G, J ≤ X → (J.subgroupOf X).IsCComponent → R ≤ J → J = I)) := by
  have hi := C.rankOne_generic_input_of_many h hmany hn hpsl
  obtain ⟨P,hTP,_,hcases⟩ := d.exists_changedSylow hH.1.1.2 c hd hz
  obtain ⟨hL,hK,hR⟩ := d.changedSylow_intersections hi hH P hTP
  refine ⟨P,hTP,hL,hK,hR,?_⟩
  rcases hcases with he | ⟨U,hU⟩
  · exact Or.inl he
  · have hb : localBorel U L = localBorel T L := by
      change L ⊓ normalizer (((U : Subgroup G) ⊓ L : Subgroup G) : Set G) = _
      rw [hU,hL]
    obtain ⟨x,hxN,hxL,hxA,hxD,hxT⟩ :=
      d.changedSylow_marked_conjugator hi hH c hd hz (hTP.trans_eq hU.symm)
    obtain ⟨I,hRI,hIX,hI,hTI,hu,_⟩ := d.common_normal_component hi hH c hd hz
    have hlt : R < I := lt_of_le_of_ne hRI (by
      intro he
      apply d.changedSylow_not_common_component hi hH c hd hz P hTP hU
      simpa only [he] using hI)
    refine Or.inr ⟨U,hU,hb,hb.symm ▸ c.left_le,hb.symm ▸ c.left_hall,
      x,I,hxN,hxL,hxA,hxD,hxT,?_,hlt,hIX,hI,hTI,hu⟩
    exact d.changedSylow_conjugate_outside hd hz P hU hxD hxT

/-- Local maximality discharges the entire larger changed-Sylow branch.
The moved-component maximality assertion of source 1.2.8(3) is the
upstream input; the original factor selection remains with the final owner. -/
theorem rankOne_prime_changedSylow_eq_of_right_maximal
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n p : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (d : LocalData T L H B D R)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥)
    (hR : R ∈ Chapter1.LStar G (T : Subgroup G)) :
    ∃ P : Sylow 2 (extension T L H B D R),
      (P : Subgroup (extension T L H B D R)).map (extension T L H B D R).subtype =
        normalizingSylow T R := by
  obtain ⟨P,hTP,_⟩ := d.exists_changedSylow hH.1.1.2 c hd hz
  exact ⟨P,d.changedSylow_eq_of_right_maximal
    (C.rankOne_generic_input_of_many h hmany hn hpsl) hH c hd hz hR P hTP⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
