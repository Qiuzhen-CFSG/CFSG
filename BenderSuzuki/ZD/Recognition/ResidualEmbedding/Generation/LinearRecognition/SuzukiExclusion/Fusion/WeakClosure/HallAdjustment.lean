module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.WeakClosure.Bounds
public import Theory.GroupTheory.Hall.Conjugacy

/-!
# Hall-conjugacy adjustment in the Suzuki complement argument

Suppose E and M°U are M-conjugate and E is normalized by a nontrivial
Y ≤ J. In R = C_M(M°) ∩ N_M(M°U), Hall conjugacy adjusts the conjugator
to normalize Y. Normalizer control then puts it in N_M(L). If this local
normalizer preserves M°U, the two original subgroups must coincide.

The correction element is constructed by the proved solvable Hall
conjugacy theorem. Only normality of C_M(M°) inside M is used. The Hall
property, solvability of R and preservation by N_M(L) remain explicit
local premises to be discharged in the source assembly.

This supplies the missing conjugator mechanism in the extracted end of
GLS4, Chapter 2, Lemma 14.8 (`refs/KGroup/GLS4/Chapter2.tex`). It does not
by itself assert Lemma 14.8 or assume its missing conjugator.
-/

open Subgroup Theory.GroupTheory

namespace BenderSuzuki.ZD.SuzukiExclusion
variable {G : Type*} [Group G] [Finite G]

private theorem hall_of_card_eq {π : Set Nat.Primes} {H K : Subgroup G}
    (hH : IsHallSubgroup π H) (hc : Nat.card K = Nat.card H) :
    IsHallSubgroup π K := by
  have hi : K.index = H.index := by
    have hK := K.card_mul_index
    have hH := H.card_mul_index
    rw [hc] at hK
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (hK.trans hH.symm)
  exact ⟨fun p hp => hH.p_in_pi_of_p_dvd_card p (hc ▸ hp),
    fun p hp => hH.p_in_pi_of_p_dvd_index p (hi ▸ hp)⟩

private theorem eq_of_hall_adjustment
    (M R E F Y : Subgroup G) (π : Set Nat.Primes)
    (hRM : R ≤ M) (hRF : R ≤ normalizer (F : Set G)) (hYR : Y ≤ R)
    (hRsol : Group.IsSolvable R) (hYhall : IsHallSubgroup π (Y.subgroupOf R))
    (hcontrol : M ⊓ normalizer (Y : Set G) ≤ normalizer (F : Set G))
    (x : G) (hxM : x ∈ M) (hEF : E.conjBy x = F)
    (hYxR : Y.conjBy x ≤ R) : E = F := by
  have hc : Nat.card ((Y.conjBy x).subgroupOf R) = Nat.card (Y.subgroupOf R) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hYxR).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe hYR).toEquiv]
    exact card_map_of_injective (MulAut.conj x).injective
  obtain ⟨r, hr⟩ := exists_conj_eq_of_isHallSubgroup_of_solvable hRsol
    (hall_of_card_eq hYhall hc) hYhall
  have hy : (Y.conjBy x).conjBy (r : G) = Y := by
    have hh := congrArg (fun H : Subgroup R => H.map R.subtype) hr
    rw [map_subgroupOf_eq_of_le hYR, map_subgroupOf_map_conj_eq hYxR] at hh
    exact hh.symm
  have hxy : (r : G) * x ∈ normalizer (Y : Set G) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    change Y.conjBy ((r : G) * x) = Y
    rw [conjBy_mul, hy]
  have hxf : F.conjBy ((r : G) * x) = F :=
    mem_normalizer_iff_map_conj_eq.mp (hcontrol ⟨M.mul_mem (hRM r.property) hxM, hxy⟩)
  have hef : E.conjBy ((r : G) * x) = F := by
    rw [conjBy_mul, hEF]
    exact mem_normalizer_iff_map_conj_eq.mp (hRF r.property)
  have hh := congrArg (fun H : Subgroup G => H.conjBy (((r : G) * x)⁻¹))
    (hef.trans hxf.symm)
  simpa only [conjBy_inv] using hh

end BenderSuzuki.ZD.SuzukiExclusion

namespace BenderSuzuki.ZD.SuzukiExclusion
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {m : ℕ}

/-- The Hall-conjugacy group occurring at the end of source Lemma 14.8. -/
@[expose] public def complementFusionGroup (g : LocalGeometry Z M z t m) : Subgroup G :=
  (M ⊓ centralizer (closure (Z ∩ (M : Set G)) : Set G)) ⊓
    normalizer ((closure (Z ∩ (M : Set G)) ⊔ g.U : Subgroup G) : Set G)

/-- Literal source application of the Hall adjustment, using relative normality in M. -/
public theorem complement_conjugate_eq_of_hall
    (g : LocalGeometry Z M z t m) (s : SylowGeometry g)
    (E Y : Subgroup G) (hYJ : Y ≤ centralizer (residualGenerated M z t : Set G))
    (hYne : Y ≠ ⊥) (hYE : Y ≤ normalizer (E : Set G))
    (hYR : Y ≤ complementFusionGroup g)
    (hsol : Group.IsSolvable (complementFusionGroup g))
    (hhall : IsHallSubgroup {p : Nat.Primes | p.val ≠ 2}
      (Y.subgroupOf (complementFusionGroup g)))
    (hLF : M ⊓ normalizer (residualGenerated M z t : Set G) ≤
      normalizer ((closure (Z ∩ (M : Set G)) ⊔ g.U : Subgroup G) : Set G))
    (x : G) (hxM : x ∈ M)
    (hEF : E.conjBy x = closure (Z ∩ (M : Set G)) ⊔ g.U) :
    E = closure (Z ∩ (M : Set G)) ⊔ g.U := by
  let C := (centralizer (closure (Z ∩ (M : Set G)) : Set G)).subgroupOf M
  let : C.Normal := s.centralizer_normal
  apply eq_of_hall_adjustment M (complementFusionGroup g) E _ Y
    {p : Nat.Primes | p.val ≠ 2} (inf_le_left.trans inf_le_left) inf_le_right
      hYR hsol hhall ?_ x hxM hEF ?_
  · intro y hy
    exact hLF ⟨hy.1, g.normalizer_control Y hYJ hYne hy.2⟩
  · have hnormal : Y.conjBy x ≤
        normalizer ((closure (Z ∩ (M : Set G)) ⊔ g.U : Subgroup G) : Set G) := by
      rw [← hEF]
      change Y.map (MulAut.conj x).toMonoidHom ≤
        normalizer (E.map (MulAut.conj x).toMonoidHom : Set G)
      rw [← map_normalizer_eq_of_bijective E
        (f := (MulAut.conj x).toMonoidHom) (MulAut.conj x).bijective]
      exact map_mono hYE
    intro y hy
    refine ⟨?_, hnormal hy⟩
    obtain ⟨v, hv, rfl⟩ := hy
    have hvR := hYR hv
    have hvM := hvR.1.1
    refine ⟨M.mul_mem (M.mul_mem hxM hvM) (M.inv_mem hxM), ?_⟩
    exact (inferInstance : C.Normal).conj_mem (⟨v, hvM⟩ : M) hvR.1.2 ⟨x, hxM⟩

end BenderSuzuki.ZD.SuzukiExclusion
