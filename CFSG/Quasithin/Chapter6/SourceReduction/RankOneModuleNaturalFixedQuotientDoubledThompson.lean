module
public import Theory.Representation.AlternatingFive.AmplifiedNatural.Bounds
public import Theory.SpecificGroups.PSL2.BinaryAutomorphismRank
public import Theory.Representation.BinaryOffender.NaturalTensorFixedCodimension.Basic
public import Theory.GroupTheory.PrimeRankElementary
public import CFSG.Quasithin.ChapterB.Section02.Thompson.NearMaximumAction

/-!
# No near-offenders on two natural rank-one copies

In a faithful almost-simple extension of SL₂(2ⁿ), an elementary actor has
rank at most n. Every nonidentity involution moves at least 2n binary
dimensions on two natural copies, including arbitrary mixing of the copies.
Thus n>1 excludes near-offenders. The marked component is the original
normal subgroup; no arbitrary normalizer or multiplicity actor is substituted.

This is the doubled-natural inequality in source 6.1.4, printed p.664.
-/
public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.BinaryOffender.NaturalTensor
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {E X F : Type*} [Group E] [Finite E]
  [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
  [AddCommGroup X] [Module (ZMod 2) X] [FiniteDimensional (ZMod 2) X]

/-- A self-centralizing normal SL₂ component acting on two natural copies
has no nontrivial elementary near-offender, even under mixed coordinates. -/
theorem doubled_natural_rank_add_one_lt_fixedCodim
    (L : Subgroup E) [L.Normal]
    (e : L ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (hC : centralizer (L : Set E) = ⊥)
    (ρ : Representation (ZMod 2) E X)
    (c : X ≃ₗ[ZMod 2] (Fin 2 → NaturalSpace F))
    (hc : ∀ (l : L) x, c (ρ l x) = naturalSumAction F (Fin 2) (e l) (c x))
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (A : Subgroup E) (hA : IsElementaryTwo A) :
    rank A + 1 < fixedCodim ρ A := by
  let a : E →* MulAut L := MulAut.conjNormal
  have ha : Function.Injective a := by
    apply (MonoidHom.ker_eq_bot_iff a).mp
    apply bot_unique
    intro x hx
    apply hC.le
    intro l hl
    have hh := congrArg (fun z : MulAut L => (z ⟨l,hl⟩ : E)) hx
    change x * l * x⁻¹ = l at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  have hrE : primeRank 2 E ≤ n := by
    apply (Theory.GroupTheory.primeRank_le_of_injective 2 a ha).trans
    rw [primeRank_equiv 2 (MulAut.congr e)]
    exact Theory.PSL2.BinaryAutomorphismRank.sl2_automorphism_two_rank_le hn hF
  have hrA : rank A ≤ n := by
    have hcA := (primeRank_le_iff_elementary_card_le E).mp hrE A hA.2
    have hh := Nat.log_mono_right (b := 2) hcA
    simpa only [rank, Nat.log_pow (by decide : 1 < 2)] using hh
  obtain ⟨x,hx,hx1⟩ := SetLike.not_le_iff_exists.mp (mt le_bot_iff.mp hA.1)
  have hxne : x ≠ 1 := by simpa only [mem_bot] using hx1
  let := hA.2
  have hx2 : x*x = 1 := by
    simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p:=2) x hx
  let b : MulAut (Matrix.SpecialLinearGroup (Fin 2) F) := (MulAut.congr e) (a x)
  have hb2 : b*b = 1 := by
    change (MulAut.congr e) (a x) * (MulAut.congr e) (a x) = 1
    rw [←map_mul,←map_mul,hx2,map_one,map_one]
  have hb : b ≠ 1 := by
    intro hh
    apply hxne
    apply ha
    apply (MulAut.congr e).injective
    simpa only [map_one] using hh
  let σ := (ρ.comp L.subtype).comp e.symm.toMonoidHom
  have hbound := AlternatingFive.AmplifiedNatural.automorphism_involution_bound F hF
    σ c (by
      intro g v
      change c (ρ (e.symm g : E) v) = naturalSumAction F (Fin 2) g (c v)
      simpa only [e.apply_symm_apply] using hc (e.symm g) v)
    (ρ x) (ρ.apply_bijective x).injective b hb2 hb (by
      intro g v
      change ρ x (ρ (e.symm g : E) v) =
        ρ (e.symm (b g) : E) (ρ x v)
      have he : (e.symm (b g) : E) = x * (e.symm g : E) * x⁻¹ := by
        change (e.symm (e (MulAut.conjNormal x (e.symm g))) : E) = _
        rw [e.symm_apply_apply]
        rfl
      rw [he,←Module.End.mul_apply,←Module.End.mul_apply,←map_mul,←map_mul]
      congr 1
      group)
  have hcod : 2*n ≤ fixedCodim ρ A := by
    have hb' : 2*n ≤ operatorFixedCodim (ρ x) := by
      simpa only [Fintype.card_fin] using hbound
    exact hb'.trans (operatorFixedCodim_le_fixedCodim ρ A hx)
  omega

/-- The actual image of every near-maximum elementary subgroup is trivial
on a doubled-natural module with a self-centralizing component image. -/
theorem doubled_natural_thompson_one_centralizes
    {D : Type*} [Group D] [Finite D]
    (S U : Subgroup E) [U.Normal] [IsElementaryAbelian 2 U] (hUS : U ≤ S)
    (q : E →* D) (hq : Function.Surjective q)
    (hk : q.ker = centralizer (U : Set E))
    (L : Subgroup D) [L.Normal]
    (e : L ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (hC : centralizer (L : Set D) = ⊥)
    (c : Additive U ≃ₗ[ZMod 2] (Fin 2 → NaturalSpace F))
    (hc : ∀ (l : L) x, c (NormalElementaryQuotient.representation U q hq hk l x) =
      naturalSumAction F (Fin 2) (e l) (c x))
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2 ^ n) :
    ChapterB.thompsonJ S 1 ≤ centralizer (U : Set E) := by
  apply sSup_le
  intro A hA
  by_contra hAC
  have hne : A.map q ≠ ⊥ := by
    intro hz
    exact hAC (hk ▸ (map_eq_bot_iff A).mp hz)
  let := hA.2.1
  have hlow := doubled_natural_rank_add_one_lt_fixedCodim L e hC
    (NormalElementaryQuotient.representation U q hq hk) c hc hn hF
    (A.map q) ⟨hne,IsElementaryAbelian.map q⟩
  have hup := ChapterB.near_maximum_action_codimension S U hUS q hq hk hA hne
  omega

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
