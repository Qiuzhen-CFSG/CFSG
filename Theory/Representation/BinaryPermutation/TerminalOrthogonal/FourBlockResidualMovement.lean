module
public import Theory.Representation.BinaryPermutation.TerminalOrthogonal.FourBlockPoint
public import Theory.GroupTheory.Commutator.ResidualNormalGeneration
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.SylowNormalClosure
/-!
# Full Sylow movement of the even four-block residual

Every even permutation of four letters is a product of two odd involutions.
Pairing these decompositions in the two blocks expresses every member of
A₄ × A₄ as a product of involutions in the even block stabilizer. Each such
involution belongs to the normal closure of any Sylow two-subgroup.
Residual normal generation therefore gives [O²(P),S] = O²(P).

Only the four-letter decomposition uses finite computation; the eight-letter
embedding, normal closure and residual generation are structural.
Source: Aschbacher--Smith 12.6.31, printed p.836, the identity L₁=[L₁,T_L].
-/

public section
open Subgroup
open scoped commutatorElement
namespace BinaryPermutation.TerminalOrthogonal.FourBlockResidual
open Theory.SpecificGroups.SymmetricEight
private def pairPerm : (Equiv.Perm (Fin 4) × Equiv.Perm (Fin 4)) →* S8 :=
  (Equiv.permCongrHom (@finSumFinEquiv 4 4)).toMonoidHom.comp
    (Equiv.Perm.sumCongrHom (Fin 4) (Fin 4))
private theorem pair_mem_P (a b : Equiv.Perm (Fin 4))
    (he : Equiv.Perm.sign a * Equiv.Perm.sign b = 1) : pairPerm (a,b) ∈ P := by
  constructor
  · change Equiv.Perm.sign (pairPerm (a,b)) = 1
    change Equiv.Perm.sign ((@finSumFinEquiv 4 4).permCongr (Equiv.Perm.sumCongr a b)) = 1
    rw [Equiv.Perm.sign_permCongr,Equiv.Perm.sign_sumCongr]
    exact he
  · change ∀ i j : Fin 8, (pairPerm (a,b) i).val / 4 = (pairPerm (a,b) j).val / 4 ↔
      i.val / 4 = j.val / 4
    intro i j
    obtain ⟨i,rfl⟩ := (@finSumFinEquiv 4 4).surjective i
    obtain ⟨j,rfl⟩ := (@finSumFinEquiv 4 4).surjective j
    have hleft (x : Fin 4) :
        ((@finSumFinEquiv 4 4) (Sum.inl x) : Fin 8).val / 4 = 0 := by
      rw [finSumFinEquiv_apply_left]
      exact Nat.div_eq_of_lt x.isLt
    have hright (x : Fin 4) :
        ((@finSumFinEquiv 4 4) (Sum.inr x) : Fin 8).val / 4 = 1 := by
      rw [finSumFinEquiv_apply_right]
      simp only [Fin.val_natAdd]
      omega
    rcases i with i | i <;> rcases j with j | j <;>
      simp [pairPerm, Equiv.sumCongr_apply, hleft, hright]
private theorem even_pair_odd_involutions : ∀ a : Equiv.Perm (Fin 4),
    Equiv.Perm.sign a = 1 → ∃ b c : Equiv.Perm (Fin 4),
      b^2=1 ∧ c^2=1 ∧ Equiv.Perm.sign b = -1 ∧ Equiv.Perm.sign c = -1 ∧ b*c=a := by
  decide +kernel

private theorem residual_le_sylow_normalClosure (S : Sylow 2 P) :
    R.subgroupOf P ≤ normalClosure (S : Set P) := by
  let N := normalClosure (S : Set P)
  have hinv (x : P) (hx : x^2=1) : x ∈ N := by
    have hp : IsPGroup 2 (zpowers x) := IsPGroup.of_card_dvd_pow (n := 1) (by
      simpa only [Nat.card_zpowers,pow_one] using orderOf_dvd_of_pow_eq_one hx)
    exact hp.le_normalClosure_sylow S (mem_zpowers x)
  intro x hx
  obtain ⟨a,ha⟩ := productEquiv.surjective ⟨x,hx⟩
  obtain ⟨b₁,c₁,hb₁,hc₁,hsb₁,hsc₁,he₁⟩ := even_pair_odd_involutions a.1.val
    (Equiv.Perm.mem_alternatingGroup.mp a.1.property)
  obtain ⟨b₂,c₂,hb₂,hc₂,hsb₂,hsc₂,he₂⟩ := even_pair_odd_involutions a.2.val
    (Equiv.Perm.mem_alternatingGroup.mp a.2.property)
  let b : P := ⟨pairPerm (b₁,b₂),pair_mem_P _ _ (by rw [hsb₁,hsb₂]; decide)⟩
  let c : P := ⟨pairPerm (c₁,c₂),pair_mem_P _ _ (by rw [hsc₁,hsc₂]; decide)⟩
  have hb : b^2=1 := by
    apply Subtype.ext
    change (pairPerm (b₁,b₂))^2=1
    rw [←map_pow]
    have hh : (b₁,b₂)^2=(1 : Equiv.Perm (Fin 4) × Equiv.Perm (Fin 4)) :=
      Prod.ext hb₁ hb₂
    rw [hh,map_one]
  have hc : c^2=1 := by
    apply Subtype.ext
    change (pairPerm (c₁,c₂))^2=1
    rw [←map_pow]
    have hh : (c₁,c₂)^2=(1 : Equiv.Perm (Fin 4) × Equiv.Perm (Fin 4)) :=
      Prod.ext hc₁ hc₂
    rw [hh,map_one]
  have he : b*c=x := by
    apply Subtype.ext
    change pairPerm (b₁,b₂)*pairPerm (c₁,c₂) = x.val
    rw [←map_mul]
    change pairPerm (b₁*c₁,b₂*c₂)=x.val
    rw [he₁,he₂]
    exact congrArg Subtype.val ha
  exact he ▸ N.mul_mem (hinv b hb) (hinv c hc)

/-- Every Sylow two-subgroup moves the full intrinsic two-residual. -/
theorem full_sylow_commutator (S : Sylow 2 P) :
    ⁅pResidual 2 P,(S : Subgroup P)⁆ = pResidual 2 P := by
  apply (eq_commutator_of_normalClosure_contains (pResidual 2 P)
    (S : Subgroup P) (S : Subgroup P) (pResidual_sup_sylow_eq_top S)
    (isPPerfect_pResidual 2) S.isPGroup' (S : Subgroup P).le_normalizer ?_).symm
  intro x hx
  apply residual_le_sylow_normalClosure S
  exact (FourBlockPoint.intermediate_residual P R_le_P inf_le_right).le
    (mem_map_of_mem P.subtype hx)
end BinaryPermutation.TerminalOrthogonal.FourBlockResidual
