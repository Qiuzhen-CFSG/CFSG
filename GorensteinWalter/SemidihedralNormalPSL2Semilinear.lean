module
public import GorensteinWalter.NormalPSL2SelfCentralizing
public import Theory.GroupTheory.CyclicIndexTwoSylowCentralizer
public import Stellmacher.MainDefs

/-!
# Prescribed semilinear embedding under semidihedral Sylow geometry

A finite group with a semidihedral Sylow two-subgroup, trivial odd core,
and a prescribed normal PSL2(K) subgroup embeds faithfully in PGammaL2(K).
The map agrees with the canonical inclusion on the supplied core model.
Ambient and field universes are independent, and field order three is kept.
No oddness assertion is made about the field-automorphism image.

The semidihedral rotation subgroup is cyclic of index two. A Klein four
subgroup in the actual PSL2 core and its centerlessness therefore force
the ambient centralizer to have odd order: a centralizing involution would
produce an elementary subgroup of order eight, contradicting the proved
cyclic-index-two bound. Normality and the trivial odd core kill this
centralizer. The shared self-centralizing normal-PSL realization then gives
the faithful map with the exact core equation.

This proves the normal-core embedding step of Alperin--Brauer--Gorenstein,
Chapter II, Section 3, Proposition 4, article page 29 (PDF page 30).
-/

namespace GorensteinWalter
universe u v

public theorem exists_semidihedral_normal_psl2_semilinear_embedding
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) (hS : Stellmacher.IsSemidihedralGroup S)
    (hO : pPrimeCore 2 G = ⊥)
    (N : Subgroup G) [N.Normal]
    (K : Type v) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (eN : N ≃* PSL2 K) :
    ∃ f : G →* PGammaL2 K, Function.Injective f ∧ ∀ n : N,
      f n = SemidirectProduct.inl (Matrix.ProjectiveSpecialLinearGroup.toPGL (eN n)) := by
  classical
  obtain ⟨m, hm, hScard, a, _b, ha, _hb, _hab, _hgen⟩ := hS
  let A := Subgroup.zpowers a
  have hAi : A.index = 2 := by
    have hcard := A.card_mul_index
    rw [Nat.card_zpowers, ha, hScard,
      show m = (m - 1) + 1 by omega, pow_succ] at hcard
    exact Nat.eq_of_mul_eq_mul_left (by positivity) hcard
  have hNd := hasDihedralSylowTwo_of_mulEquiv eN
    (psl2_odd_hasDihedralSylowTwo_model K hK)
  let P : Sylow 2 N := Classical.choice Sylow.nonempty
  obtain ⟨k, hk, ⟨eP⟩⟩ := hNd P
  obtain ⟨V, _hVP, hV⟩ := exists_kleinFour_le_of_dihedral_subgroup_mulEquiv
    (P : Subgroup N) hk eP
  have hZ : Subgroup.center N = ⊥ :=
    center_eq_bot_of_mulEquiv eN (psl2_center_eq_bot K)
  have hCc := Subgroup.centralizer_card_coprime_two_of_centerless_of_cyclic_sylow_index_two
    S A hAi N hZ V hV
  have hC : Subgroup.centralizer (N : Set G) = ⊥ :=
    pPrimeCore_eq_bot_iff.mp hO _ inferInstance hCc
  exact exists_normal_psl2_semilinear_embedding_of_centralizer_eq_bot N K hK eN hC

end GorensteinWalter
