module

public import CFSG.Quasithin.ChapterB.Section01.FittingStructure
public import Theory.GroupTheory.PrimeRankFixedJoin
public import Theory.GroupTheory.TwoPerfectSmallAction
public import Theory.ElementaryAbelian.Quotient

/-!
# Two-perfect normalizers of the B.1.9 factors

The independent cubic factors in B.1.9 generate an elementary abelian
three-group. Their number is therefore bounded by the ambient three-rank.
When that rank is at most two, a two-perfect subgroup fixes every actual
cubic factor under conjugation, and hence normalizes its symmetric factor.

Source: Aschbacher–Smith, proof of 13.7.14, printed p.943, applying B.1.9.
-/

public section

open Subgroup Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.FittingStructure
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)

theorem fittingMoved_elementary (hρ : Function.Injective ρ) (hlocal : LocalPlaneLaw ρ) :
    IsElementaryAbelian 3 (fittingMoved ρ) := by
  let : IsElementaryAbelian 3 ((i : Fin (cubicCount ρ)) → cubicFactor ρ i) := {
    toIsMulCommutative := ⟨⟨by
      intro x y
      funext i
      apply (cubicFactorModel ρ hlocal i).injective
      simp only [Pi.mul_apply, map_mul, mul_comm]⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by
      intro x
      funext i
      apply (cubicFactorModel ρ hlocal i).injective
      simp only [Pi.pow_apply, Pi.one_apply, map_pow, map_one]
      change Multiplicative.ofAdd (3 • (cubicFactorModel ρ hlocal i (x i)).toAdd) =
        Multiplicative.ofAdd 0
      congr 1
      rw [← Nat.cast_smul_eq_nsmul (ZMod 3), CharP.cast_eq_zero, zero_smul]) }
  exact IsElementaryAbelian.of_surjective (cubicProduct ρ hρ hlocal).toMonoidHom
    (cubicProduct ρ hρ hlocal).surjective

theorem cubicCount_le_primeRank (hρ : Function.Injective ρ) (hlocal : LocalPlaneLaw ρ) :
    cubicCount ρ ≤ primeRank 3 G := by
  let := fittingMoved_elementary ρ hρ hlocal
  exact IsElementaryAbelian.primeRank_ge_of_card (fittingMoved ρ)
    (fittingMoved_card ρ hρ hlocal)

omit [FiniteDimensional (ZMod 2) V] in
/-- Every actual cubic in B.1.9 is fixed by a two-perfect subgroup when
there are at most two such cubics. -/
theorem twoPerfect_normalizes_cubic_of_count_le_two
    (hc : cubicCount ρ ≤ 2) (K : Subgroup G) (hK : IsPPerfect 2 K)
    {X : Subgroup G} (hX : X ∈ minimalMovedFactors ρ) :
    K ≤ normalizer (X : Set G) := by
  let F := minimalMovedFactors ρ
  let : MulAction K F := {
    smul := fun k Y => ⟨Y.val.map (MulAut.conj (k : G)).toMonoidHom,
      minimalMovedFactors_map_conj ρ Y.property (k : G)⟩
    one_smul := fun Y => Subtype.ext (by
      change Y.val.map (MulAut.conj (1 : G)).toMonoidHom = Y.val
      rw [show (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G by
        ext x
        simp, map_id])
    mul_smul := fun k l Y => Subtype.ext (by
      change Y.val.map (MulAut.conj ((k : G) * (l : G))).toMonoidHom =
        (Y.val.map (MulAut.conj (l : G)).toMonoidHom).map
          (MulAut.conj (k : G)).toMonoidHom
      rw [map_map]
      congr 1
      ext x
      simp [mul_assoc]) }
  intro k hk
  apply mem_normalizer_iff_map_conj_eq.mpr
  exact congrArg Subtype.val
    (MulAction.fixed_of_twoPerfect_of_card_le_two hK hc (⟨k,hk⟩ : K) (⟨X,hX⟩ : F))

/-- The literal symmetric factor attached to any noncentral minimal offender
is normalized by each two-perfect subgroup of a group of three-rank at most two. -/
theorem twoPerfect_normalizes_planeGroup (hρ : Function.Injective ρ)
    (hlocal : LocalPlaneLaw ρ) (hrank : primeRank 3 G ≤ 2)
    (K : Subgroup G) (hK : IsPPerfect 2 K)
    {X : Subgroup G} (hX : X ∈ minimalMovedFactors ρ) :
    K ≤ normalizer (planeGroup ρ X : Set G) :=
  (twoPerfect_normalizes_cubic_of_count_le_two ρ
    ((cubicCount_le_primeRank ρ hρ hlocal).trans hrank) K hK hX).trans
      (normalizer_le_normalizer_planeGroup ρ X)

/-- In a two-group, a noncentral minimal offender is exactly the intersection
with its B.1.9 symmetric factor. -/
theorem planeGroup_inf_twoGroup (hρ : Function.Injective ρ)
    (hlocal : LocalPlaneLaw ρ) {B R : Subgroup G}
    (hB : IsMinimalBestOffender ρ B) (hn : ⁅fittingSubgroup G,B⁆ ≠ ⊥)
    (hR : IsPGroup 2 R) (hBR : B ≤ R) :
    planeGroup ρ ⁅fittingSubgroup G,B⁆ ⊓ R = B := by
  let N := planeGroup ρ ⁅fittingSubgroup G,B⁆
  have hBN : B ≤ N := offender_le_planeGroup ρ ⟨hB,hn,rfl⟩
  have hp : IsPGroup 2 (R.subgroupOf N) := hR.comap_subtype
  obtain ⟨S,hS⟩ := hp.exists_le_sylow
  have hc : Nat.card (N ⊓ R : Subgroup G) ≤ 2 := by
    have he : (R.subgroupOf N).map N.subtype = N ⊓ R := by
      rw [subgroupOf_map_subtype, inf_comm]
    rw [← he, card_map_of_injective N.subtype_injective]
    exact (card_le_of_le hS).trans
      (planeGroup_sylow_card ρ hρ hlocal ⟨B,hB,hn,rfl⟩ S).le
  obtain ⟨d⟩ := hlocal B hB hn
  exact (eq_of_le_of_card_ge (le_inf hBN hBR) (by rw [d.actor_card]; exact hc)).symm

/-- Source13.7.14's actual minimal offender is normalized by the original
two-perfect subgroup whenever it lies in a normalized two-group. -/
theorem twoPerfect_normalizes_minimal_offender (hρ : Function.Injective ρ)
    (hlocal : LocalPlaneLaw ρ) (hrank : primeRank 3 G ≤ 2)
    {K B R : Subgroup G} (hK : IsPPerfect 2 K)
    (hB : IsMinimalBestOffender ρ B) (hn : ⁅fittingSubgroup G,B⁆ ≠ ⊥)
    (hR : IsPGroup 2 R) (hBR : B ≤ R) (hKR : K ≤ normalizer (R : Set G)) :
    K ≤ normalizer (B : Set G) := by
  rw [← planeGroup_inf_twoGroup ρ hρ hlocal hB hn hR hBR]
  exact (le_inf (twoPerfect_normalizes_planeGroup ρ hρ hlocal hrank K hK
    ⟨B,hB,hn,rfl⟩) hKR).trans inf_normalizer_le_normalizer_inf

end CFSG.Quasithin.ChapterB.FittingStructure
