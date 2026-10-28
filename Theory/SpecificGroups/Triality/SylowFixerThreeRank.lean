module
public import Theory.SpecificGroups.Triality.SolvableFixedRank
public import Theory.SpecificGroups.Triality.EvenInvolutionGeometry.MixedFixers
public import Theory.SpecificGroups.Triality.OuterOddSubgroups.Coverage
public import Theory.SpecificGroups.Triality.OuterOddSubgroups.Coverage.RootGeometry.SimpleRecognition.ParabolicIntersections
public import Theory.GroupTheory.SylowNormalizerOvergroup

/-!
# The full highest-root centralizer in binary triality

The arms local factor centralizes the whole Sylow center. Borel--Tits
covers the centralizer of a nonidentity highest-root element. Sylow
normalizer alignment makes its join with the standard Borel proper.
The rank-two Tits system then forces this join to be the arms parabolic.
Inside that parabolic, the existing Borel scalar calculation removes the
complementary torus, identifying the full centralizer with the arms local
factor. Its actual PSL₂(q³) quotient and two-core bound cubic rank by one.

The inner-coefficient coverage and mixed-fixer calculation then apply to
the same original Sylow-fixing involution. All positive binary exponents,
including exponent one, use the genuine graph-field carrier.
Source: Aschbacher--Smith, proof of 12.6.26, printed p.832; F.1.12 and
16.1.6, with the intrinsic GLS3 normalizer cover and rank-two Tits system.
-/
public section
open Subgroup Theory.GroupTheory
namespace Triality.Standard
open Parabolics ConcreteBruhat RadicalCoordinates.Centers

/-- A nonidentity highest-root element has exactly the arms local centralizer. -/
theorem highestRoot_centralizer_eq_localFactor (n : ℕ) (hn : 0 < n)
    (r : BinaryCarrier n hn) (hr : r ∈ highestRoot (binaryParameters n hn)) (hne : r ≠ 1) :
    centralizer ({r} : Set (BinaryCarrier n hn)) = localFactor (binaryParameters n hn) .arms := by
  let P := binaryParameters n hn
  let C := centralizer ({r} : Set (Carrier P))
  have hL : localFactor P .arms ≤ C := by
    intro x hx
    apply mem_centralizer_singleton_iff.mpr
    have he := RadicalCoordinates.localFactor_arms_le_centralizer_center_unipotent P rfl hx
    rw [embedded_center_unipotent P rfl] at he
    exact (he r hr).symm
  let U := unipotentSylow P rfl
  have hUC : (U : Subgroup (Carrier P)) ≤ C :=
    (unipotentSylow_le_localFactor P rfl .arms).trans hL
  have hp : IsPGroup 2 (zpowers r) := by
    apply (U.isPGroup'.of_injective
      (inclusion ((zpowers_le.mpr (highestRoot_le_unipotent P rfl hr)) : zpowers r ≤ unipotent P)))
    exact inclusion_injective _
  obtain ⟨g,s,hg⟩ := TwoLocalCover.normalizer_cover n hn (zpowers r)
    (fun he => hne (zpowers_eq_bot.mp he)) hp
  have hCN : C ≤ normalizer (zpowers r : Set (Carrier P)) := by
    change centralizer ({r} : Set (Carrier P)) ≤ _
    rw [←centralizer_closure ({r} : Set (Carrier P)),←zpowers_eq_closure]
    exact Subgroup.centralizer_le_normalizer _
  have hsmall := U.normalizer_sup_lt_top_of_map_le U C (parabolic P s)
    (MulAut.conj g) hUC ((map_mono hCN).trans hg)
    (by rw [show (U : Set (Carrier P)) = (unipotent P : Set (Carrier P)) from rfl,
      normalizer_unipotent_eq_borel P rfl]; exact borel_le_parabolic P s)
    (lt_top_iff_ne_top.mpr (parabolic_ne_top_binary P rfl s))
  change normalizer (unipotent P : Set (Carrier P)) ⊔ C < ⊤ at hsmall
  rw [normalizer_unipotent_eq_borel P rfl] at hsmall
  have hPL : parabolic P .arms ≤ borel P ⊔ C := by
    rw [←localFactor_sup_borel_binary P rfl .arms]
    exact sup_le (hL.trans le_sup_right) le_sup_left
  have hnot : ¬ parabolic P .arms ≤ parabolic P .central := by
    intro h
    have ht : parabolic P .central = ⊤ := by
      rw [←parabolic_sup_binary P rfl,sup_eq_right.mpr h]
    exact parabolic_ne_top_binary P rfl .central ht
  have hB : borel P < borel P ⊔ C := lt_of_le_of_ne le_sup_left (by
    intro he
    exact hnot (hPL.trans (he ▸ borel_le_parabolic P .central)))
  obtain ⟨s,hs⟩ := OuterOdd.Coverage.RootGeometry.SimpleRecognition.eq_parabolic_of_borel_lt
    n hn (borel P ⊔ C) hB hsmall.ne_top
  have hCP : C ≤ parabolic P .arms := by
    cases s with
    | arms => exact hs ▸ le_sup_right
    | central => exact (hnot (hs ▸ hPL)).elim
  apply le_antisymm ?_ hL
  intro x hx
  let N := (localFactor P .arms).subgroupOf (parabolic P .arms)
  let B := (borel P).subgroupOf (parabolic P .arms)
  have htop : N ⊔ B = ⊤ := by
    rw [←subgroupOf_sup (localFactor_le_parabolic P .arms) (borel_le_parabolic P .arms),
      localFactor_sup_borel_binary P rfl .arms,subgroupOf_self]
  obtain ⟨l,hl,b,hb,he⟩ := mem_sup_of_normal_left.mp
    (htop.symm ▸ mem_top (⟨x,hCP hx⟩ : parabolic P .arms))
  have hex : l.val * b.val = x := congrArg Subtype.val he
  have hbC : b.val ∈ C := by
    have hh := C.mul_mem (C.inv_mem (hL hl)) hx
    change l.val⁻¹ * x ∈ C at hh
    rw [←hex,inv_mul_cancel_left] at hh
    exact hh
  rw [←hex]
  exact (localFactor P .arms).mul_mem hl
    (borel_highest_centralizer_le_localFactor P rfl r hr hne ⟨hb,hbC⟩)

/-- Every involutory Sylow fixer has actual fixed-group cubic rank at most one. -/
theorem sylow_fixer_fixed_threeRank_le_one (n : ℕ) (hn : 0 < n)
    [IsSimpleGroup (BinaryCarrier n hn)] [Group.IsPerfect (BinaryCarrier n hn)]
    (S : Sylow 2 (BinaryCarrier n hn)) (a : MulAut (BinaryCarrier n hn))
    (ha : orderOf a = 2) (hfix : ∀ x ∈ S, a x = x) : primeRank 3 a.fixedSubgroup ≤ 1 := by
  let P := binaryParameters n hn
  let U := unipotentSylow P rfl
  obtain ⟨_,e,_,he⟩ := Theory.GroupTheory.SolvableSylowControl.exists_aligned_equiv
    (MulEquiv.refl (BinaryCarrier n hn)) S U
  let b := MulAut.congr e a
  have hb : orderOf b = 2 := ((MulAut.congr e).orderOf_eq a).trans ha
  have hU : ∀ x ∈ U, b x = x := by
    intro x hx
    change x ∈ (U : Subgroup (Carrier P)) at hx
    rw [←he] at hx
    obtain ⟨y,hy,rfl⟩ := hx
    change e (a (e.symm (e y))) = e y
    rw [e.symm_apply_apply,hfix y hy]
  obtain ⟨x,hx⟩ := EvenInvolutionGeometry.inner_of_fixes_unipotent n hn b (k := 1)
    (by simpa only [pow_one,hb] using pow_orderOf_eq_one b)
    (OuterOdd.Coverage.binary_inner_coefficient n hn b) hU
  obtain ⟨r,hr,her,hrU,hrC⟩ := MulAut.inner_involution_fixing_sylow
    (binaryCarrier_center_eq_bot n hn) U b hb ⟨x,hx⟩ hU
  have hroot : r ∈ highestRoot P := by
    rw [←embedded_center_unipotent P rfl]
    exact ⟨⟨r,hrU⟩,mem_center_iff.mpr
      (fun y => Subtype.ext (hrC y y.property).eq.symm),rfl⟩
  have heC : b.fixedSubgroup = localFactor P .arms := by
    rw [her,MulAut.fixedSubgroup_conj]
    exact highestRoot_centralizer_eq_localFactor n hn r hroot (by intro he; simp [he] at hr)
  rw [primeRank_equiv 3 (MulAut.fixedSubgroupCongr e a),heC]
  exact localFactor_threeRank_le_one P rfl .arms
end Triality.Standard
