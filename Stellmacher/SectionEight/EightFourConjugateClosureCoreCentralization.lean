module
public import Stellmacher.SectionEight.EightFourSourceSevenCoreCentralization
public import Theory.GroupTheory.Commutator.ConjugateGeneratorProduct
/-!
# The conjugate closure reduction in Stellmacher (8.4)(7)

In the endpoint group, the normal two-subgroup `T` normalizes a subgroup
`Y`, which centralizes the conjugate factor `A.conjBy x`. A subgroup `D`
of `Y` commuting with `A` modulo the normal subgroup `Z` then centralizes
the two-core of the odd residual of `(A ⊔ A.conjBy x) ⊔ T`.
The local residual core containment and odd quotient are explicit inputs.

The conjugate-generator product identity puts `D` in `Y.conjBy x⁻¹ ⊔ Z`.
Its `T`-conjugate closure remains in this product and in `Y`, hence satisfies
both commutator bounds of the ambient source-(7) core-centralization lemma.
This construction needs no containment of `D` in the generated group.

Source: Stellmacher, Journal of Algebra 190 (1997), (8.4)(7), printed p.39;
this is the subgroup denoted `D*` and its three-subgroup reduction.
-/

namespace Stellmacher.SectionEight
open scoped commutatorElement
private theorem closure_le_normalized
    {G : Type*} [Group G] (D T K : Subgroup G) (hDK : D ≤ K)
    (hTK : T ≤ Subgroup.normalizer (K : Set G)) : Stellmacher.conjugateClosure D T ≤ K := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨t,d,rfl⟩
  exact (Subgroup.mem_normalizer_iff.mp (hTK t.property) (d : G)).mp (hDK d.property)

public theorem eight_four_conjugate_closure_core_centralization
    {G : Type*} [Group G] [Finite G]
    (D Y Z A T P : Subgroup G) [Z.Normal] [T.Normal] (x : G)
    (hgen : (A ⊔ A.conjBy x) ⊔ T = P) (hx : x ∈ A ⊔ A.conjBy x)
    (hT : IsPGroup 2 T) (hTY : T ≤ Subgroup.normalizer (Y : Set G))
    (hZT : ⁅Z,T⁆ = ⊥) (hYA : ⁅Y,A.conjBy x⁆ = ⊥)
    (hDY : D ≤ Y) (hDA : ⁅D,A⁆ ≤ Z)
    (hQT : (pCore 2 (twoResidualAmbient P)).map (twoResidualAmbient P).subtype ≤ T)
    (hodd : Odd (Nat.card ((twoResidualAmbient P) ⧸ pCore 2 (twoResidualAmbient P)))) :
    ⁅D,(pCore 2 (twoResidualAmbient P)).map (twoResidualAmbient P).subtype⁆ = ⊥ := by
  let M := Stellmacher.conjugateClosure D T
  have hMY : M ≤ Y := closure_le_normalized D T Y hDY hTY
  have hDM : D ≤ M := by
    intro d hd
    exact Subgroup.subset_closure ⟨1,⟨d,hd⟩,by simp⟩
  have hTM : T ≤ Subgroup.normalizer (M : Set G) := by
    change T ≤ Subgroup.normalizer (Stellmacher.conjugateClosure D T : Set G)
    rw [Stellmacher.conjugateClosure,Subgroup.le_normalizer_closure_iff]
    rintro t ht _ ⟨u,d,rfl⟩
    apply Subgroup.subset_closure
    refine ⟨⟨t*(u:G),T.mul_mem ht u.property⟩,d,?_⟩
    simp only [mul_inv_rev]
    group
  have hDAx : ⁅D,A.conjBy x⁆ = ⊥ :=
    le_bot_iff.mp ((Subgroup.commutator_mono hDY le_rfl).trans_eq hYA)
  have hprod := Subgroup.le_conjBy_inv_sup_of_commutator_conjugate_generators D Y A Z x hDY hDA hDAx hx
  have hTYprev : T ≤ Subgroup.normalizer (Y.conjBy x⁻¹ : Set G) := by
    have hh := Subgroup.map_mono (f := (MulAut.conj x⁻¹).toMonoidHom) hTY
    have hTmap : T.conjBy x⁻¹ = T := Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (Subgroup.le_normalizer_of_normal (show x⁻¹ ∈ (⊤ : Subgroup G) from trivial))
    have hnmap : (Subgroup.normalizer (Y : Set G)).conjBy x⁻¹ =
        Subgroup.normalizer (Y.conjBy x⁻¹ : Set G) :=
      Subgroup.map_equiv_normalizer_eq Y (MulAut.conj x⁻¹)
    change T.conjBy x⁻¹ ≤ (Subgroup.normalizer (Y : Set G)).conjBy x⁻¹ at hh
    rwa [hTmap,hnmap] at hh
  have hMprod : M ≤ Y.conjBy x⁻¹ ⊔ Z := closure_le_normalized D T _ hprod
    ((le_inf hTYprev Subgroup.le_normalizer_of_normal).trans
      (Subgroup.normalizer_inf_normalizer_le_normalizer_sup _ _))
  have hYprevA : ⁅Y.conjBy x⁻¹,A⁆ = ⊥ := by
    have hh := congrArg (Subgroup.map (MulAut.conj x⁻¹).toMonoidHom) hYA
    rw [Subgroup.map_commutator,Subgroup.map_bot] at hh
    change ⁅Y.conjBy x⁻¹,(A.conjBy x).conjBy x⁻¹⁆ = ⊥ at hh
    simpa only [Subgroup.conjBy_inv] using hh
  have hMA : ⁅M,A⁆ ≤ Z := by
    apply Subgroup.commutator_le.mpr
    intro m hm a ha
    obtain ⟨y,hy,z,hz,rfl⟩ := Subgroup.mem_sup_of_normal_right.mp (hMprod hm)
    have hyc : ⁅y,a⁆ = 1 := by
      have hh := Subgroup.commutator_mem_commutator hy ha
      rw [hYprevA] at hh
      exact hh
    have hzc : ⁅z,a⁆ ∈ Z := Subgroup.commutator_le_left Z A
      (Subgroup.commutator_mem_commutator hz ha)
    rw [commutatorElement_mul_left_eq_conj_mul,hyc,mul_one]
    exact (inferInstance : Z.Normal).conj_mem _ hzc y
  have hMAx : ⁅M,A.conjBy x⁆ = ⊥ :=
    le_bot_iff.mp ((Subgroup.commutator_mono hMY le_rfl).trans_eq hYA)
  have hMQ := eight_four_source_seven_core_centralization_in M Z A T P x
    ((le_sup_left.trans_eq hgen) hx) hgen hT hTM hZT hMA hMAx hQT hodd
  exact le_bot_iff.mp ((Subgroup.commutator_mono hDM le_rfl).trans_eq hMQ)
end Stellmacher.SectionEight
