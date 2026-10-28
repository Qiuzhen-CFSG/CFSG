module
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.FourGroup
public import Theory.GroupAction.IrreducibleBinaryQuotientAction
public import Theory.ElementaryAbelian.FixedOrderGeneration
public import CFSG.Quasithin.ChapterI.Section06To08.TIConjugates
public import CFSG.Quasithin.ChapterE.Section03.Offenders.Basic

/-!
# The irreducible TI branch of the first two weak closures

For an original nonquasisimple local component L acting irreducibly on an
elementary abelian TI subgroup U, choose an actual four-subgroup inside a
conjugate actor of order at least four. The original odd Frattini-plane
obstruction gives a nonidentity element trivial on L/O∞(L). Since O∞(L)
centralizes U, binary irreducibility makes that element fix U. The elementary
TI-pair theorem then makes the whole conjugate centralize U.

When |U| is at least eight, this applies to every whole-conjugate or
hyperplane generator of W₀(T,U) and W₁(T,U), proving w(T,U)>1. No faithful
four-group action or transvection marking is an extra premise. Original
13.1.4(5),13.1.10 and13.1.13 supply respectively radical centralization, the
irreducible module branch and TI. The reducible module branches remain
separate from this result.

Source: Aschbacher--Smith,13.1.14(1--2), printed pp.875--876, and I.6.2(1).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple
open Chapter1 ChapterI.Section06To08
variable {G : Type*} [Group G] [Finite G]

/-- Every sufficiently large original conjugate actor centralizes U in the
irreducible branch; its four-subgroup and kernel element are constructed. -/
theorem conjugate_actor_centralizes_of_irreducible
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {L U A : Subgroup G} (hL : L ∈ Chapter1.L G (T : Subgroup G))
    (hn : ¬ IsQuasisimple (XiQuotient L))
    [IsElementaryAbelian 2 U] (hTI : IsTISubgroup U)
    (hLU : L ≤ normalizer (U : Set G))
    (hRad : (solvableRadical L).map L.subtype ≤ centralizer (U : Set G))
    (hirr : ∀ D : Subgroup U,
      (∀ l : L, ∀ u ∈ D, U.normalizerMonoidHom (inclusion hLU l) u ∈ D) →
        D = ⊥ ∨ D = ⊤)
    (g : G) (hAg : A ≤ U.map (MulAut.conj g).toMonoidHom)
    (hAU : A ≤ normalizer (U : Set G))
    (hAL : A ≤ normalizer (L : Set G)) (hA : 4 ≤ Nat.card A) :
    A ≤ centralizer (U : Set G) := by
  let V := U.map (MulAut.conj g).toMonoidHom
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_le hAg
  by_contra hnon
  have hd : Disjoint V U := by
    rcases hTI.eq_or_disjoint_conjugate g with he | hd
    · apply (hnon ?_).elim
      rw [he] at hAg
      exact hAg.trans (le_centralizer_iff_isMulCommutative.mpr inferInstance)
    · exact hd
  obtain ⟨B,hBA,hB,hcard,_⟩ := IsElementaryAbelian.exists_two_power_subgroup_mem A
    (n := 2) (by decide) hA 1 A.one_mem
  let := hB
  have hBL := hBA.trans hAL
  have hBU := hBA.trans hAU
  let ρ := L.normalizerMonoidHom.comp (inclusion hBL)
  let σ := U.normalizerMonoidHom.comp (inclusion hBU)
  let τ := U.normalizerMonoidHom.comp (inclusion hLU)
  have hW : solvableRadical L ≤ τ.ker := by
    intro l hl
    apply MonoidHom.mem_ker.mpr
    apply MulEquiv.ext
    intro u
    apply Subtype.ext
    change (l : G) * (u : G) * (l : G)⁻¹ = (u : G)
    have hc := mem_centralizer_iff.mp (hRad (mem_map_of_mem L.subtype hl)) u u.property
    change (u : G) * (l : G) = (l : G) * (u : G) at hc
    rw [← hc,mul_inv_cancel_right]
  have he (b : B) (l : L) (u : U) : σ b (τ l u) = τ (ρ b l) (σ b u) := by
    apply Subtype.ext
    change (b : G) * ((l : G) * (u : G) * (l : G)⁻¹) * (b : G)⁻¹ =
      ((b : G) * (l : G) * (b : G)⁻¹) *
        ((b : G) * (u : G) * (b : G)⁻¹) *
          ((b : G) * (l : G) * (b : G)⁻¹)⁻¹
    group
  let q := (quotientAut (solvableRadical L)).comp ρ
  have hk : q.ker ≠ ⊥ := by
    intro hk
    exact normalizer_four_group_action_not_injective hG T hL hn
      (by simpa using hcard) hBL ((MonoidHom.ker_eq_bot_iff q).mp hk)
  obtain ⟨b,hb⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hk
  have hb1 : (b : B) ≠ 1 := fun he => hb (Subtype.ext he)
  have hb2 : (b : B) ^ 2 = 1 := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
    (IsElementaryAbelian.exponent_dvd_p 2 B) b
  have hfix : σ b = 1 := action_eq_one_of_quotient_eq_one_of_irreducible_binary
    (solvableRadical L) τ hW hirr ρ σ he b hb2 (MonoidHom.mem_ker.mp b.property)
  have hbC : ((b : B) : G) ∈ centralizer (U : Set G) := by
    apply mem_centralizer_iff.mpr
    intro u hu
    have hh := congrArg (fun f : MulAut U => ((f ⟨u,hu⟩ : U) : G)) hfix
    change ((b : B) : G) * u * ((b : B) : G)⁻¹ = u at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  have hC : V ⊓ centralizer (U : Set G) ≠ ⊥ := by
    intro hbot
    have hx : ((b : B) : G) ∈ V ⊓ centralizer (U : Set G) :=
      ⟨hAg (hBA (b : B).property),hbC⟩
    rw [hbot] at hx
    exact hb1 (Subtype.ext (mem_bot.mp hx))
  have hfull : U ⊓ normalizer (V : Set G) = U :=
    ti_pair_full_normalizer_of_centralizer_ne_bot U V hd.symm
      (hTI.map_equiv (MulAut.conj g)) hC
  have hc : U ≤ centralizer (V : Set G) :=
    ti_pair_commute_of_full_normalizer U V hd.symm hTI
      (hTI.map_equiv (MulAut.conj g))
      (card_map_of_injective (MulAut.conj g).injective).symm hfull
  exact hnon (hAg.trans (le_centralizer_iff.mp hc))

/-- The actual zero and first weak closures centralize the original
irreducible module, with the required actor sizes derived from their indices. -/
theorem weakClosure_centralizes_of_irreducible
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {L U : Subgroup G} (hL : L ∈ Chapter1.L G (T : Subgroup G))
    (hn : ¬ IsQuasisimple (XiQuotient L))
    [IsElementaryAbelian 2 U] (hTI : IsTISubgroup U)
    (hLU : L ≤ normalizer (U : Set G))
    (hRad : (solvableRadical L).map L.subtype ≤ centralizer (U : Set G))
    (hirr : ∀ D : Subgroup U,
      (∀ l : L, ∀ u ∈ D, U.normalizerMonoidHom (inclusion hLU l) u ∈ D) →
        D = ⊥ ∨ D = ⊤)
    (hTU : (T : Subgroup G) ≤ normalizer (U : Set G))
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hsize : 8 ≤ Nat.card U) (i : ℕ) (hi : i ≤ 1) :
    ChapterE.indexedWeakClosure U (T : Subgroup G) i ≤ centralizer (U : Set G) := by
  rw [ChapterE.weakClosure_eq_sSup_gamma]
  apply sSup_le
  rintro A ⟨⟨g,hAg,hindex⟩,hAT⟩
  apply conjugate_actor_centralizes_of_irreducible hG T hL hn hTI hLU hRad hirr g hAg
    (hAT.trans hTU) (hAT.trans hTL)
  have hc := relIndex_mul_relIndex (⊥ : Subgroup G) A
    (U.map (MulAut.conj g).toMonoidHom) bot_le hAg
  rw [relIndex_bot_left,relIndex_bot_left,hindex,
    card_map_of_injective (MulAut.conj g).injective] at hc
  interval_cases i <;> norm_num at hc ⊢ <;> omega

/-- The source weak-closure parameter is greater than one in the
irreducible TI-module branch. -/
theorem globalW_gt_one_of_irreducible
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {L U : Subgroup G} (hL : L ∈ Chapter1.L G (T : Subgroup G))
    (hn : ¬ IsQuasisimple (XiQuotient L))
    [IsElementaryAbelian 2 U] (hTI : IsTISubgroup U)
    (hLU : L ≤ normalizer (U : Set G))
    (hRad : (solvableRadical L).map L.subtype ≤ centralizer (U : Set G))
    (hirr : ∀ D : Subgroup U,
      (∀ l : L, ∀ u ∈ D, U.normalizerMonoidHom (inclusion hLU l) u ∈ D) →
        D = ⊥ ∨ D = ⊤)
    (hTU : (T : Subgroup G) ≤ normalizer (U : Set G))
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hsize : 8 ≤ Nat.card U) :
    1 < ChapterE.globalW U (T : Subgroup G) := by
  apply lt_of_not_ge
  intro h
  rcases Order.le_one_iff.mp h with hzero | hone
  · have he := ChapterE.globalW_attained (n := 0) hzero
    exact he (le_inf (ChapterE.indexedWeakClosure_le U (T : Subgroup G) 0)
      (weakClosure_centralizes_of_irreducible hG T hL hn hTI hLU hRad hirr hTU hTL hsize 0
        (by decide)))
  · have he := ChapterE.globalW_attained (n := 1) hone
    exact he (le_inf (ChapterE.indexedWeakClosure_le U (T : Subgroup G) 1)
      (weakClosure_centralizes_of_irreducible hG T hL hn hTI hLU hRad hirr hTU hTL hsize 1 le_rfl))

end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple
