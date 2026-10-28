module
public import Theory.SpecificGroups.PSL2.BinaryTwentyFiveRatio
public import Theory.SpecificGroups.PSL2.BinaryElevenRatio
public import Theory.Representation.BinaryOffender.CubicConjugateBound
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSmall.PrimeDegreeEight.CyclicGeneration.InnerSeeds
public import Theory.SpecificGroups.SL2.OddOrderDivisibility
public import Theory.Representation.BinaryPrimeDegree
public import Mathlib.FieldTheory.Finite.GaloisField
/-!
# The fixed-free faithful PSL₂(19) exclusion for C.5.13

Four checked conjugates of an inner involution generate the actual group.
Cubic ratio at most two and the dihedral Sylow rank bound then give degree
at most sixteen. The defining prime nineteen forces binary degree at least
eighteen. The original action and its full fixed-space hypothesis are retained;
no irreducibility or outer-action condition is added.
Source: Aschbacher–Smith C.5.13 and K.2, printed pp.163 and453.
-/
public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl.DualOffender
private theorem order_two_nineteen : orderOf (2 : ZMod 19) = 18 := by
  apply (orderOf_eq_iff (by decide : 0 < 18)).mpr
  constructor
  · decide
  · intro m hm hpos
    interval_cases m <;> norm_num at * <;> decide
theorem two_lt_cubicRatio_of_nineteen_fixed {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    (hfix : fixedSpace ρ ⊤ = ⊥) (hm : ClassicalGroup.IsPSL G 2 19) : 2 < cubicRatio ρ := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : Fact (Nat.Prime 19) := ⟨by decide⟩
  let : Fintype F := Fintype.ofFinite F
  let eF : F ≃+* ZMod 19 := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card,hF,ZMod.card])
  let eg := e.trans (GorensteinWalter.psl2RingEquiv eF)
  have hr : primeRank 2 G ≤ 2 := by
    rw [primeRank_equiv 2 e]
    let P : Sylow 2 PSL(2,F) := Classical.choice inferInstance
    have hodd : GorensteinWalter.IsOddPrimePower (Nat.card F) :=
      ⟨19,1,by decide,by decide,by decide,by simpa using hF⟩
    obtain ⟨n,_,⟨en⟩⟩ := GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model F hodd P
    rw [P.primeRank_eq,primeRank_equiv 2 en]
    exact dihedral_rank_le_two n
  by_contra hn
  obtain ⟨t,ht,ht2,hd⟩ := exists_small_involution_of_cubicRatio_le (n := 2) ρ hr (le_of_not_gt hn)
  obtain ⟨s,hs,hs2,c,hc⟩ :=
    ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSmall.PrimeDegreeEight.CyclicGeneration.innerSeeds
      19 (Or.inr (Or.inr (Or.inl rfl)))
  obtain ⟨z,hz⟩ := isConj_iff.mp (Theory.PSL2.involutions_isConj (eg t) s
    ((eg.orderOf_eq t).trans (orderOf_eq_prime ht2 ht)) (orderOf_eq_prime hs2 hs))
  let d : Fin 4 → G := fun i => eg.symm (c i*z)
  have he (i : Fin 4) : eg.symm (c i*s*(c i)⁻¹) = d i*t*(d i)⁻¹ := by
    apply eg.injective
    simp only [map_mul,map_inv,MulEquiv.apply_symm_apply,d]
    rw [← hz]
    group
  have hg : (⊤ : Subgroup G) ≤ closure (Set.range fun i => d i*t*(d i)⁻¹) := by
    have hle : closure (Set.range fun i => c i*s*(c i)⁻¹) ≤
        (closure (Set.range fun i => d i*t*(d i)⁻¹)).comap eg.symm.toMonoidHom := by
      apply (closure_le _).mpr
      rintro _ ⟨i,rfl⟩
      change eg.symm (c i*s*(c i)⁻¹) ∈ closure (Set.range fun j => d j*t*(d j)⁻¹)
      rw [he]
      exact subset_closure ⟨i,rfl⟩
    intro g _
    have hh := hle (show eg g ∈ closure (Set.range fun i => c i*s*(c i)⁻¹) from hc ▸ mem_top _)
    change eg.symm (eg g) ∈ closure (Set.range fun i => d i*t*(d i)⁻¹) at hh
    simpa only [MulEquiv.symm_apply_apply] using hh
  have hdim : Module.finrank (ZMod 2) V ≤ 16 :=
    (finrank_le_mul_fixedCodim_of_conjugate_generation ρ ⊤ hfix t d hg).trans
      (Nat.mul_le_mul_left 4 hd)
  have hcard := Matrix.ProjectiveSpecialLinearGroup.psl2_card_twice
    (show Odd (Nat.card F) from hF ▸ (by decide : Odd 19))
  rw [← Nat.card_congr e.toEquiv,hF] at hcard
  have hdiv : 19 ∣ Nat.card G := by
    have hh : Nat.card G = 3420 := by omega
    rw [hh]
    decide
  have hlo := BinaryPrimeDegree.orderOf_le_finrank ρ hf
    (by decide : Nat.Prime 19) (by decide) hdiv
  rw [order_two_nineteen] at hlo
  omega
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl.DualOffender
