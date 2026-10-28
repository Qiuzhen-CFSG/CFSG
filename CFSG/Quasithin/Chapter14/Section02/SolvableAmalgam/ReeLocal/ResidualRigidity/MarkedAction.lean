module

public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.ReeLocal.ResidualRigidity.Assembly
public import Theory.GroupAction.PointStabilizerQuotient
/-!
# Extending the marked local action forces equality

The faithful marked representation constructs the actual equivalence Q/F with
the displacement group and its faithful M/Q conjugation action. Transported
local involution fusion supplies the intransitive orbit. The residual bound
then forces the embedding of the local group to be surjective.

All local premises concern the given maps and subgroups. The Ree and Tits
applications supply them from their verified marked parabolics.
Source: Aschbacher--Smith 14.2.21, printed p.989.
-/

open Subgroup Theory.LinearAlgebra.BinaryFivePointStabilizer
open Theory.GroupAction.PointStabilizerQuotient
open CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.ReeLocal.ResidualRigidity
namespace CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.ReeLocal.ResidualRigidity

/-- The actual translation image and fusion facts discharge the abstract action premises. -/
public theorem range_eq_top_of_extended_marked_action
    {H M E : Type*} [Group H] [Finite H] [Group M] [Finite M]
    [AddCommGroup E] [Module (ZMod 2) E] [FiniteDimensional (ZMod 2) E]
    (z : E) (hz : z ≠ 0) (hE : Module.finrank (ZMod 2) E = 5)
    (QH FH : Subgroup H) [QH.Normal] (hFH : FH ≤ QH)
    (r : H →* stabilizer z) (hrQ : QH.map r = kernel z)
    (i : H →* M) (hi : Function.Injective i)
    (Q : Subgroup M) [Q.Normal] (hQ : QH.map i = Q) [(FH.map i).Normal]
    (ρ : M ⧸ FH.map i →* stabilizer z) (hρ : Function.Injective ρ)
    (hres : ∀ h : H, ρ (QuotientGroup.mk' (FH.map i) (i h)) = r h)
    (hHq : Nat.card (H ⧸ QH) = 20)
    (hHcyc : ∀ T : Sylow 2 (H ⧸ QH), IsCyclic T)
    (hH : ¬ 3 ∣ Nat.card H)
    (S : Sylow 2 M) (hS : (S : Subgroup M) ≤ i.range)
    (hexists : ∃ x : H, x ∈ QH ∧ orderOf x = 2 ∧ x ∉ FH)
    (hfusion : ∀ x y : H, x ∈ QH → y ∈ QH → x ^ 2 = 1 → y ^ 2 = 1 →
      x ∉ FH → y ∉ FH → IsConj x y) : i.range = ⊤ := by
  have hFQ : FH.map i ≤ Q := by
    rw [← hQ]
    exact map_mono hFH
  have hQN : Q.map (ρ.comp (QuotientGroup.mk' (FH.map i))) = kernel z := by
    rw [← hQ, map_map]
    have he : (ρ.comp (QuotientGroup.mk' (FH.map i))).comp i = r := MonoidHom.ext hres
    rw [he, hrQ]
  let θ := translations z (FH.map i) Q ρ hQN
  let σ := action z hz (FH.map i) Q hFQ ρ hρ hQN
  let e := translationsEquiv z (FH.map i) Q ρ hρ hQN
  let : Finite (kernel z) := Finite.of_equiv (Q ⧸ (FH.map i).subgroupOf Q) e.toEquiv
  obtain ⟨x, hx, hxord, hxF⟩ := hexists
  let j : Q := ⟨i x, hQ.le (mem_map_of_mem i hx)⟩
  have hj : j ^ 2 = 1 := by
    apply Subtype.ext
    change (i x) ^ 2 = 1
    rw [← map_pow, ← hxord, pow_orderOf_eq_one, map_one]
  have hjθ : θ j ≠ 1 := by
    intro he
    have hk := MonoidHom.mem_ker.mpr he
    change j ∈ (translations z (FH.map i) Q ρ hQN).ker at hk
    rw [translations_ker z (FH.map i) Q ρ hρ hQN] at hk
    exact hxF ((mem_map_iff_mem hi).mp hk)
  exact range_eq_top_of_fusion i hi QH FH Q hQ hHq hHcyc hH S hS θ
    (translations_ker z (FH.map i) Q ρ hρ hQN) σ
    (action_injective z hz (FH.map i) Q hFQ ρ hρ hQN)
    (compatibility z hz (FH.map i) Q hFQ ρ hρ hQN) (natCard_kernel z hz hE)
    j hj hjθ hfusion
end CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.ReeLocal.ResidualRigidity
