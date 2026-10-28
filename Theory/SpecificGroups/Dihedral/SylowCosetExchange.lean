module
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.Tactic.NormNum

/-!
# Exchanging Sylow-normalizer cosets in D₁₀

For the standard reflection Sylow, each rotation coset contains a
reflection and each reflection coset has the required involution directly.
Conjugating the marked Sylow gives the statement for every Sylow normalizer.

The DGS `CommutingNontrivial.NeighborExchange` application lifts this
exchange through the actual local two-core quotient. This retains the D₁₀
case of the source catalogue without assigning it a doubly transitive
neighbor action. Source: DGS, *Groups and Graphs* (1985), 8.6(b)--(c), p.139.
-/

@[expose] public noncomputable section
open Subgroup
namespace DihedralGroup
private theorem standard_five_exchange (g : DihedralGroup 5) :
    ∃ t : DihedralGroup 5, t * t = 1 ∧ t * g ∈
      normalizer (zpowers (sr 0 : DihedralGroup 5) : Set (DihedralGroup 5)) := by
  cases g with
  | r i =>
    refine ⟨sr (-i),sr_mul_self _,?_⟩
    simp only [sr_mul_r,neg_add_cancel]
    exact (zpowers (sr 0 : DihedralGroup 5)).le_normalizer (mem_zpowers _)
  | sr i => exact ⟨sr i,sr_mul_self _,by rw [sr_mul_self]; exact one_mem _⟩

/-- Every coset of a Sylow-two normalizer in D₁₀ contains an element of
order dividing two, giving an exchange with the base coset. -/
theorem five_sylow_coset_exchange (S : Sylow 2 (DihedralGroup 5)) (g : DihedralGroup 5) :
    ∃ t : DihedralGroup 5, t * t = 1 ∧ t * g ∈ normalizer (S : Set (DihedralGroup 5)) := by
  let T : Sylow 2 (DihedralGroup 5) := Sylow.ofCard (zpowers (sr 0 : DihedralGroup 5)) (by
    rw [Nat.card_zpowers,orderOf_sr,nat_card]
    rw [Nat.factorization_mul (by decide) (by decide),
      Nat.prime_two.factorization,Nat.prime_five.factorization]
    norm_num)
  obtain ⟨a,ha⟩ := MulAction.exists_smul_eq (DihedralGroup 5) S T
  let c := MulAut.conj a
  have hS : (S : Subgroup (DihedralGroup 5)).map c.toMonoidHom = zpowers (sr 0) := by
    change ((a • S : Sylow 2 (DihedralGroup 5)) : Subgroup (DihedralGroup 5)) = _
    rw [ha]
    rfl
  have hN : (normalizer (S : Set (DihedralGroup 5))).map c.toMonoidHom =
      normalizer (zpowers (sr 0 : DihedralGroup 5) : Set (DihedralGroup 5)) := by
    calc
      _ = normalizer ((S : Subgroup (DihedralGroup 5)).map c.toMonoidHom : Set (DihedralGroup 5)) :=
        map_equiv_normalizer_eq (S : Subgroup (DihedralGroup 5)) c
      _ = _ := by rw [hS]
  obtain ⟨t,ht,htg⟩ := standard_five_exchange (c g)
  refine ⟨c.symm t,by rw [←map_mul,ht,map_one],?_⟩
  rw [←hN] at htg
  obtain ⟨b,hb,he⟩ := htg
  change c b = t * c g at he
  have hb' : b = c.symm t * g := by
    apply c.injective
    simpa only [map_mul,MulEquiv.apply_symm_apply] using he
  exact hb' ▸ hb
end DihedralGroup

