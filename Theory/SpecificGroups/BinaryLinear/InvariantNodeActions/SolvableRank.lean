module
public import Theory.SpecificGroups.BinaryLinear.InvariantNodeActions.MiddleFour
public import Theory.SpecificGroups.BinaryLinear.FourPlaneRank
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.TwoNodes.Pairs

/-!
# Invariant solvable flags of three-rank two in binary dimensions four and five

The middle plane stabilizer in dimension four and the flag of dimensions
2 and 3 in dimension five have two-core quotient S₃ × S₃. They are
solvable and have three-rank two. Every automorphism preserving their full
Sylow flag preserves these partial flags: inner automorphisms fix the
cuts and inverse transpose reverses them.

These are the actual end-node parabolics used in Aschbacher--Smith
14.6.20, printed p.1037. No ambient classification hypotheses are needed.
-/

public section
open Subgroup Theory.GroupTheory
namespace BinaryLinear.InvariantNodeActions
open OuterCyclic SmallParabolicLevi SmallParabolicLevi.TwoNodes

private instance (n : ℕ) : Finite (LinearGroup n) :=
  Finite.of_injective (fun g : LinearGroup n => (g : Space n → Space n)) DFunLike.coe_injective

private theorem symmetricThree_solvable : Group.IsSolvable (Equiv.Perm (Fin 3)) := by
  let : Group.IsSolvable (alternatingGroup (Fin 3)) := Group.isSolvable_of_comm (by decide)
  apply Group.isSolvable_of_ker_le_range
    (alternatingGroup (Fin 3)).subtype Equiv.Perm.sign
  rw [Subgroup.range_subtype, ← alternatingGroup_eq_sign_ker]

private theorem symmetric_pair_rank :
    primeRank 3 (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) = 2 := by
  apply le_antisymm
  · apply primeRank_le_two_of_cube_not_dvd
    rw [Nat.card_prod,Nat.card_perm,Nat.card_fin]
    decide
  · rw [primeRank_prod_eq_add]
    have hne : primeRank 3 (Equiv.Perm (Fin 3)) ≠ 0 := by
      intro hz
      have hn := PrimeRank.eq_zero_iff_not_dvd_card.mp hz
      rw [Nat.card_perm,Nat.card_fin] at hn
      exact hn (by decide)
    omega

private theorem solvable_rank_of_quotient {D : Type*} [Group D] [Finite D]
    (e : (D ⧸ pCore 2 D) ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) :
    Group.IsSolvable D ∧ primeRank 3 D = 2 := by
  let := symmetricThree_solvable
  let : Group.IsSolvable (D ⧸ pCore 2 D) :=
    Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  let : Group.IsNilpotent (pCore 2 D) := pCore_isPGroup.isNilpotent
  refine ⟨(Group.isSolvable_iff_subgroup_quotient (pCore 2 D)).mpr
    ⟨inferInstance,inferInstance⟩,?_⟩
  rw [←primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 D) pCore_isPGroup,
    primeRank_equiv 3 e]
  exact symmetric_pair_rank

/-- A solvable three-rank-two overgroup of every binary-four Sylow is
invariant under all automorphisms preserving that Sylow. -/
theorem exists_invariant_solvable_rank_two_four (T : Sylow 2 (LinearGroup 4)) :
    ∃ J : Subgroup (LinearGroup 4), (T : Subgroup _) ≤ J ∧
      Group.IsSolvable J ∧ primeRank 3 J = 2 ∧
      ∀ a : MulAut (LinearGroup 4), (T : Subgroup _).map a.toMonoidHom = T →
        J.map a.toMonoidHom = J := by
  obtain ⟨W,hW,hTW,hinv⟩ := exists_sylow_invariant_middle T
  have hQ : Module.finrank (ZMod 2) (Space 4 ⧸ W) = 2 := by
    have hd : Module.finrank (ZMod 2) (Space 4) = 4 := by simp [Space]
    have h := W.finrank_quotient_add_finrank
    rw [hW,hd] at h
    omega
  let a : W ≃ₗ[ZMod 2] Space 2 := LinearEquiv.ofFinrankEq _ _ (by simpa [Space] using hW)
  let b : (Space 4 ⧸ W) ≃ₗ[ZMod 2] Space 2 :=
    LinearEquiv.ofFinrankEq _ _ (by simpa [Space] using hQ)
  let e := (quotientTwoCoreEquivOfCoordinates W a b).trans
    (linearTwoEquivSymmetricThree.prodCongr linearTwoEquivSymmetricThree)
  obtain ⟨hs,hr⟩ := solvable_rank_of_quotient e
  exact ⟨parabolic W,hTW,hs,hr,hinv⟩

private theorem five_middle_invariant (b : Basis 4) (a : MulAut (LinearGroup 5))
    (ha : (cutStabilizer b Set.univ).map a.toMonoidHom = cutStabilizer b Set.univ) :
    (cutStabilizer b ({0,3} : Set (Fin 4))ᶜ).map a.toMonoidHom =
      cutStabilizer b ({0,3} : Set (Fin 4))ᶜ := by
  obtain ⟨g,rfl | rfl⟩ := OuterCyclic.inner_graph (Or.inr rfl) a
  · exact inner_fixes_cutStabilizer b g ha _
  · let a := graphLinear 5 * MulAut.conj g
    have hp (i : Fin 4) : (parabolic (cutSpace b i)).map a.toMonoidHom =
        parabolic (cutSpace b i.rev) := by
      rw [graph_inner_map_parabolic,graph_inner_cutSpace_of_fullFlag b g ha]
    have hr (i : Fin 4) : i.rev ∈ ({0,3} : Set (Fin 4))ᶜ ↔
        i ∈ ({0,3} : Set (Fin 4))ᶜ := by fin_cases i <;> decide
    ext s
    rw [Subgroup.mem_map_equiv,mem_cutStabilizer,mem_cutStabilizer]
    have hm (i : Fin 4) : a.symm s ∈ parabolic (cutSpace b i) ↔
        s ∈ parabolic (cutSpace b i.rev) := by
      rw [←hp i,Subgroup.mem_map_equiv]
    constructor
    · intro hs i hi
      have hh := (hm i.rev).mp (hs i.rev ((hr i).mpr hi))
      change s ∈ parabolic (cutSpace b i)
      simpa only [Fin.rev_rev] using hh
    · intro hs i hi
      exact (hm i).mpr (hs i.rev ((hr i).mpr hi))

/-- The invariant binary-five flag has blocks 2+1+2, hence quotient
S₃ × S₃ and exact three-rank two. -/
theorem exists_invariant_solvable_rank_two_five (T : Sylow 2 (LinearGroup 5)) :
    ∃ J : Subgroup (LinearGroup 5), (T : Subgroup _) ≤ J ∧
      Group.IsSolvable J ∧ primeRank 3 J = 2 ∧
      ∀ a : MulAut (LinearGroup 5), (T : Subgroup _).map a.toMonoidHom = T →
        J.map a.toMonoidHom = J := by
  obtain ⟨b,hb⟩ := sylow_eq_cutStabilizer (m := 4) T
  let J := cutStabilizer b ({0,3} : Set (Fin 4))ᶜ
  have he : J = FiveFlagGeometry.flagStabilizer b ({0,3} : Set (Fin 4))ᶜ := rfl
  let e := (flagDiagonalQuotientEquiv b ({0,3} : Set (Fin 4))ᶜ).trans
    (pairFactorsEquiv 0 3 (Or.inl (by decide)))
  obtain ⟨hs,hr⟩ := solvable_rank_of_quotient e
  refine ⟨J,?_,he.symm ▸ hs,he.symm ▸ hr,?_⟩
  · rw [hb]
    exact (cutStabilizer_le_iff _ _ _).mpr (Set.subset_univ _)
  · intro a ha
    exact five_middle_invariant b a (by simpa only [hb] using ha)

end BinaryLinear.InvariantNodeActions
