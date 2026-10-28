module
public import Theory.Representation.SL2.PerfectCoreQuotientDegree
public import Theory.Representation.BinaryOffender.MarkedCentralQuotient
public import Theory.Representation.NormalElementaryQuotient.FixedIndex
public import Theory.SpecificGroups.SL2.TwoCore
public import GorensteinWalter.SL2ProjectiveCover

/-!
# Full fixed-index bounds for binary rank-one quotient actions

A nontrivial perfect SL2(2^n) action stays nontrivial after quotienting by
all fixed vectors. The checked irreducible-section degree bound therefore
gives fixed codimension at least 2n, without requiring the whole module
to be irreducible. The literal elementary quotient representation transfers
this bound to |U:C_U(G)|, retaining the entire fixed central subgroup.

Source application: Niles (1979), Lemma 7.6, printed pp.61-62,
the q-squared lower bound on the core omega in the original group.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace Representation.SL2
variable {F V : Type*} [Field F] [Finite F] [CharP F 2]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

theorem fixedCodim_top_lower
    (ρ : Representation (ZMod 2) SL(2,F) V) (hnt : ∃ g, ρ g ≠ 1)
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2^n) :
    2*n ≤ fixedCodim ρ ⊤ := by
  have hlarge : 3 < Nat.card F := by
    rw [hF]
    have hh := Nat.pow_le_pow_right (by decide : 0 < 2) (show 2 ≤ n by omega)
    norm_num at hh
    omega
  let : Group.IsPerfect SL(2,F) := GorensteinWalter.sl2_isPerfect_of_card_gt_three F hlarge
  let : Group.IsPerfect (⊤ : Subgroup SL(2,F)) := Group.IsPerfect.ofSurjective
    (f := (topEquiv (G := SL(2,F))).symm.toMonoidHom) topEquiv.symm.surjective
  have hne : ¬ (⊤ : Subgroup SL(2,F)) ≤ ρ.ker := by
    intro hh
    obtain ⟨g,hg⟩ := hnt
    exact hg (hh (mem_top g))
  have hquot := fixedQuotient_noncentral ρ ⊤ hne
  have hntQ : ∃ g, fixedQuotient ρ ⊤ g ≠ 1 := by
    by_contra! he
    exact hquot (fun g _ => he g)
  let e : (SL(2,F) ⧸ pCore 2 SL(2,F)) ≃* SL(2,F) :=
    (QuotientGroup.quotientMulEquivOfEq (Matrix.SL2.twoCore_eq_bot F)).trans
      QuotientGroup.quotientBot
  exact perfect_core_quotient_finrank_bound e (fixedQuotient ρ ⊤) hntQ (by omega) hF

variable {G : Type*} [Group G]
theorem normal_fixed_index_lower
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] [Finite U]
    (q : G →* SL(2,F)) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G))
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2^n) :
    Nat.card F ^ 2 ≤ (centralizer ((⊤ : Subgroup G) : Set G)).relIndex U := by
  let ρ := NormalElementaryQuotient.representation U q hq hker
  have hf := NormalElementaryQuotient.representation_injective U q hq hker
  have hnt : ∃ g, ρ g ≠ 1 := by
    let g : SL(2,F) := ⟨!![1,1;0,1],by simp [Matrix.det_fin_two]⟩
    have hg : g ≠ 1 := by
      intro he
      have hh := congrArg (fun a : SL(2,F) => a.val 0 1) he
      simp [g] at hh
    exact ⟨g,fun hh => hg (hf (hh.trans ρ.map_one.symm))⟩
  have hl := fixedCodim_top_lower (V := Additive U) ρ hnt hn hF
  rw [NormalElementaryQuotient.centralizer_index_eq_fixedCodim U q hq hker,
    map_top_of_surjective q hq,hF,←pow_mul]
  exact Nat.pow_le_pow_right (by decide) (by simpa only [Nat.mul_comm] using hl)
end Representation.SL2
