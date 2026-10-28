module

public import Theory.Representation.RankThreeThreeGroupWeightBase
public import Theory.Representation.AbelianWeightAutomizer
public import Theory.GroupTheory.PGroup.AbelianIndexThreeNormalizerOrbit


/-!
# Two-subgroups of nonabelian three-group normalizers in SL₃

Assume that the intersection of N(Q) with the centralizer of each abelian
index-three subgroup of Q has odd order. Then every two-subgroup of N(Q)
has order at most eight.

The faithful natural representation, extended to an algebraic closure, gives
an abelian index-three subgroup A. Its normalizer orbit has size at most four.
The stabilizer in the given two-subgroup acts on A through an automizer that
embeds in Sym(3). Its kernel lies in the stipulated odd intersection, hence
is trivial. Thus the stabilizer has order at most two, and orbit–stabilizer
gives the bound eight.

This is a conditional normalizer estimate for the solvable SL₃ reduction in
GLS3, Theorem 6.5.3(a–d), `refs/KGroup/GLS3/chapter6.tex`, used in
Aschbacher–Smith, Proposition 1.3.4, printed p.511 (PDF p.528 of
`refs/quasithin.pdf`). The weight-base and orbit inputs implement A.3.21(c).
The odd-intersection premise is retained explicitly for the assembly owner.
-/

public section

open Subgroup
open scoped TensorProduct

namespace Matrix.SL3.SplitMonomial

private theorem stabilizer_card_le_two
    {E G V : Type*} [Field E] [IsAlgClosed E] [Group G] [Finite G]
    [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    (rho : Representation E G V) (hrho : Function.Injective rho)
    (hdim : Module.finrank E V ≤ 3)
    (B Q P : Subgroup G) [IsMulCommutative B]
    (horder : (Nat.card B : E) ≠ 0)
    (hP : IsPGroup 2 P) (hPN : P ≤ normalizer (Q : Set G))
    (hodd : Odd (Nat.card ↥(centralizer (B : Set G) ⊓ normalizer (Q : Set G)))) :
    Nat.card ((normalizer (B : Set G)).subgroupOf P) ≤ 2 := by
  let N := normalizer (B : Set G)
  let S := N.subgroupOf P
  have hdis : Disjoint P (centralizer (B : Set G) ⊓ normalizer (Q : Set G)) := by
    apply disjoint_of_coprime_natCard
    obtain ⟨n, hn⟩ := hP.exists_card_eq
    rw [hn]
    exact (Nat.coprime_two_left.mpr hodd).pow_left n
  let i : S →* N := {
    toFun := fun x => ⟨x.val.val, x.property⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  let f : S →* B.normalizerMonoidHom.range :=
    B.normalizerMonoidHom.rangeRestrict.comp i
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply bot_unique
    intro x hx
    have hk : i x ∈ B.normalizerMonoidHom.ker := by
      exact congrArg Subtype.val (show f x = 1 from hx)
    rw [B.normalizerMonoidHom_ker] at hk
    have hxC : x.val.val ∈ centralizer (B : Set G) := hk
    have hx1 : x.val.val = 1 := mem_bot.mp
      (hdis.le_bot ⟨x.val.property, hxC, hPN x.val.property⟩)
    exact mem_bot.mpr (Subtype.ext (Subtype.ext hx1))
  obtain ⟨j, hj⟩ := Representation.automizer_embeds_perm_of_abelian
    rho B hrho horder 3 hdim
  have hd6 : Nat.card S ∣ 6 := by
    have hd := card_dvd_of_injective (j.comp f) (hj.comp hf)
    simpa [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial] using hd
  obtain ⟨n, hn⟩ := (hP.to_subgroup S).exists_card_eq
  have hcop : (Nat.card S).Coprime 3 := by
    rw [hn]
    exact (by decide : Nat.Coprime 2 3).pow_left n
  exact Nat.le_of_dvd (by decide : 0 < 2)
    (hcop.dvd_of_dvd_mul_right (show Nat.card S ∣ 2 * 3 from hd6))

/-- Odd centralizer intersections force two-subgroups of the normalizer of a
nonabelian three-subgroup of SL₃ to have order at most eight. -/
theorem two_subgroup_card_le_eight_of_odd_weight_kernels
    {F : Type*} [Field F] [Finite F]
    (p : ℕ) [Fact p.Prime] [CharP F p] (hp : 3 ≠ p)
    (Q : Subgroup (SpecialLinearGroup (Fin 3) F))
    (hQ : IsPGroup 3 Q) (hn : ¬ IsMulCommutative Q)
    (hkernel : ∀ A : Subgroup Q, IsMulCommutative A → A.index = 3 →
      Odd (Nat.card ↥(centralizer ((A.map Q.subtype : Subgroup
        (SpecialLinearGroup (Fin 3) F)) : Set (SpecialLinearGroup (Fin 3) F)) ⊓
        normalizer (Q : Set (SpecialLinearGroup (Fin 3) F)))))
    (P : Subgroup (SpecialLinearGroup (Fin 3) F)) (hP : IsPGroup 2 P)
    (hPN : P ≤ normalizer (Q : Set (SpecialLinearGroup (Fin 3) F))) :
    Nat.card P ≤ 8 := by
  let E := AlgebraicClosure F
  let rho := (Representation.specialLinearNatural (k := F) 3).extendScalars E
  have hrho : Function.Injective rho :=
    (Representation.extendScalars_faithful_iff E _).mp
      (Representation.specialLinearNatural_injective 3)
  have hdim : Module.finrank E (E ⊗[F] (Fin 3 → F)) = 3 := by
    rw [Module.finrank_baseChange, Module.finrank_pi, Fintype.card_fin]
  have h3 : (3 : F) ≠ 0 := by
    change (↑(3 : ℕ) : F) ≠ 0
    rw [ne_eq, CharP.cast_eq_zero_iff F p]
    intro hdiv
    exact hp ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_three).mp hdiv).symm
  have horderF : (Nat.card Q : F) ≠ 0 := by
    obtain ⟨n, hncard⟩ := hQ.exists_card_eq
    rw [hncard, Nat.cast_pow]
    exact pow_ne_zero n h3
  have horder : (Nat.card Q : E) ≠ 0 := by
    intro hz
    apply horderF
    apply (algebraMap F E).injective
    simpa using hz
  obtain ⟨A, _, hAc, hAi, _⟩ :=
    Representation.exists_normal_abelian_index_three_ambient_centralizer
      rho hrho hdim Q hQ hn horder
  let : IsMulCommutative A := hAc
  let B := A.map Q.subtype
  have horderA : (Nat.card A : E) ≠ 0 := by
    intro hz
    apply horder
    rw [← A.card_mul_index, Nat.cast_mul, hz, zero_mul]
  have horderB : (Nat.card B : E) ≠ 0 := by
    dsimp [B]
    rwa [card_map_of_injective Q.subtype_injective]
  let S := (normalizer (B : Set (SpecialLinearGroup (Fin 3) F))).subgroupOf P
  have hS : Nat.card S ≤ 2 :=
    stabilizer_card_le_two rho hrho hdim.le B Q P horderB hP hPN (hkernel A hAc hAi)
  have hiS : S.index ≤ 4 := by
    change (normalizer (B : Set (SpecialLinearGroup (Fin 3) F))).relIndex P ≤ 4
    exact (relIndex_le_of_le_right
      (H := normalizer (B : Set (SpecialLinearGroup (Fin 3) F))) hPN
      (by exact Subgroup.index_ne_zero_of_finite)).trans
      (normalizer_relIndex_le_four_of_abelian_index_three Q hQ hn A hAc hAi)
  calc
    Nat.card P = Nat.card S * S.index := S.card_mul_index.symm
    _ ≤ 2 * 4 := Nat.mul_le_mul hS hiS
    _ = 8 := rfl

end Matrix.SL3.SplitMonomial
