module
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.FieldReduction
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.LargeFamily
public import GorensteinWalter.NormalPSL2SelfCentralizing
public import Theory.FieldTheory.FiniteAutomorphismOrder
public import Theory.SpecificGroups.PSL2.OddAutomorphismRank

/-!
# The actual semilinear models in the prime-square case

A self-centralizing normal PSL₂(p²) subgroup gives a faithful semilinear
embedding preserving its specified matrix realization. The field-automorphism
group has order two, so the literal linear kernel has index one or two.
In the first case the whole group is PSL₂ or PGL₂. In the second the field
projection is surjective; this asserts no involutory lift or complement.
All elementary actors of rank greater than one have rank two or three;
the maximal-overgroup reduction is specialized to precisely those actors.

The consumer is the conditional local-geometry assembly in `SquareGeometry`.
These reductions retain p=3 and p=5 and every subgroup containing the inner
PSL₂ layer, including mixed diagonal-field extensions.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
A.2.3(2) and E.1.14(6), printed pp.33 and 214. The source's remaining
local calculation cites Aschbacher (1982), Lemma 4.10.
-/

public section

namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry
open Subgroup GorensteinWalter Theory.GroupTheory
variable {F : Type*} [Field F] [Finite F]

/-- The actual field image has order one or two. -/
theorem linearKernel_index_eq_one_or_two {p : ℕ} (hp : p.Prime)
    (hF : Nat.card F = p ^ 2) (S : Subgroup (PGammaL2 F)) :
    (pGammaL2LinearKernel F S).index = 1 ∨
      (pGammaL2LinearKernel F S).index = 2 := by
  rw [pGammaL2LinearKernel_index_eq_card_range]
  apply (Nat.dvd_prime Nat.prime_two).mp
  have hd := (pGammaL2FieldProjection F S).range.card_subgroup_dvd_card
  simpa only [FiniteField.card_ringAut_of_card_prime_pow hp hF] using hd

/-- Index two means full field image, without asserting a splitting. -/
theorem fieldProjection_surjective_of_index_two {p : ℕ} (hp : p.Prime)
    (hF : Nat.card F = p ^ 2) (S : Subgroup (PGammaL2 F))
    (hindex : (pGammaL2LinearKernel F S).index = 2) :
    Function.Surjective (pGammaL2FieldProjection F S) := by
  let : Finite (F ≃+* F) := Finite.of_injective
    (fun a : F ≃+* F => (a : F → F)) DFunLike.coe_injective
  apply MonoidHom.range_eq_top.mp
  apply Subgroup.eq_top_of_card_eq
  rw [← pGammaL2LinearKernel_index_eq_card_range, hindex,
    FiniteField.card_ringAut_of_card_prime_pow hp hF]

/-- A trivial field image identifies the whole subgroup with PSL₂ or PGL₂. -/
theorem linear_model_of_kernel_index_one {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hF : Nat.card F = p ^ 2) (S : Subgroup (PGammaL2 F))
    (hS : pGammaL2PSLRange F ≤ S) (hindex : (pGammaL2LinearKernel F S).index = 1) :
    Nonempty (S ≃* PSL2 F) ∨ Nonempty (S ≃* PGL2 F) := by
  have hK : IsOddPrimePower (Nat.card F) := ⟨p, 2, hp, hodd, by decide, hF⟩
  have hm := pGammaL2_linear_kernel_model F hK S hS
  rw [Subgroup.index_eq_one.mp hindex] at hm
  exact hm.imp (fun h => ⟨Subgroup.topEquiv.symm.trans h.some⟩)
    (fun h => ⟨Subgroup.topEquiv.symm.trans h.some⟩)

/-- The field factor adds at most one to the dihedral two-rank. -/
theorem large_elementary_rank_eq_two_or_three {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hF : Nat.card F = p ^ 2) (S : Subgroup (PGammaL2 F)) [Finite S]
    (A : Subgroup S) (hA : IsElementaryAbelian 2 A) (hr : 1 < Group.rank A) :
    Group.rank A = 2 ∨ Group.rank A = 3 := by
  let : Finite (PGL2 F) := Finite.of_surjective
    Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  let : Finite (F ≃+* F) := Finite.of_injective
    (fun a : F ≃+* F => (a : F → F)) DFunLike.coe_injective
  let : Finite (PGammaL2 F) :=
    Finite.of_equiv (PGL2 F × (F ≃+* F)) SemidirectProduct.equivProd.symm
  let := hA
  have hK : IsOddPrimePower (Nat.card F) := ⟨p, 2, hp, hodd, by decide, hF⟩
  have hbound : Group.rank A ≤ 3 :=
    (A.rank_le_primeRank 2 (IsElementaryAbelian.isPGroup 2 A)).trans
      ((primeRank_le_of_injective 2 S.subtype S.subtype_injective).trans
        (Theory.PSL2.odd_pGammaL_two_rank F hK))
  omega

/-- In a concrete square-field model it is enough to handle rank-two and
rank-three families against maximal overgroups. The rank bound is proved from
the faithful semilinear action, not assumed of the source group. -/
theorem largeFamilyEscapeAt_of_rank_two_or_three_witnesses
    {F : Type*} [Field F] [Finite F] {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hF : Nat.card F = p ^ 2) (S : Subgroup (PGammaL2 F)) [Finite S]
    (T : Sylow 2 S)
    (hlocal : ∀ Ω : Set (Subgroup S), IsElementaryFamily Ω →
      (∀ A ∈ Ω, A ≤ (T : Subgroup S) → A ≠ ⊥ →
        Group.rank A = 2 ∨ Group.rank A = 3) →
      ∀ M : Subgroup S, IsCoatom M → (T : Subgroup S) ≤ M →
        normalizer (weakClosure (T : Subgroup S) Ω : Set S) ≤ M →
        ∃ A : Subgroup S, A ∈ Ω ∧ A ≤ (T : Subgroup S) ∧
          ∃ H : Subgroup S, IsEMemberAt 1 (T : Subgroup S) A H ∧ ¬ H ≤ M) :
    LargeFamilyEscapeAt T := by
  apply largeFamilyEscapeAt_of_maximal_escape T
  intro Ω hΩ hlarge M hM hTM hNM
  apply hlocal Ω hΩ _ M hM hTM hNM
  intro A hA hAT hne
  exact large_elementary_rank_eq_two_or_three hp hodd hF S A (hΩ.1 A hA)
    (hlarge A hA hAT hne)

/-- Realize the prescribed socle as exactly the canonical PSL₂ layer. -/
theorem exists_semilinear_model {G : Type*} [Group G] [Finite G]
    (L : Subgroup G) [L.Normal] {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hL : ClassicalGroup.IsPSL L 2 (p ^ 2))
    (hC : centralizer (L : Set G) = ⊥) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ 2 ∧
      ∃ (f : G →* PGammaL2 F), Function.Injective f ∧
        L.map f = pGammaL2PSLRange F ∧ pGammaL2PSLRange F ≤ f.range := by
  obtain ⟨F, _, _, hF, ⟨eL⟩⟩ := hL
  have hK : IsOddPrimePower (Nat.card F) := ⟨p, 2, hp, hodd, by decide, hF⟩
  obtain ⟨f, hf, hcore⟩ :=
    exists_normal_psl2_semilinear_embedding_of_centralizer_eq_bot L F hK eL hC
  have hmap : L.map f = pGammaL2PSLRange F := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      rw [hcore ⟨x, hx⟩]
      exact (mem_pGammaL2PSLRange_iff F _).mpr ⟨eL ⟨x, hx⟩, rfl⟩
    · intro y hy
      obtain ⟨z, rfl⟩ := (mem_pGammaL2PSLRange_iff F y).mp hy
      refine ⟨eL.symm z, (eL.symm z).property, ?_⟩
      rw [hcore, eL.apply_symm_apply]
  refine ⟨F, inferInstance, inferInstance, hF, f, hf, hmap, ?_⟩
  rw [← hmap]
  exact map_le_range (f := f) (H := L)
end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry
