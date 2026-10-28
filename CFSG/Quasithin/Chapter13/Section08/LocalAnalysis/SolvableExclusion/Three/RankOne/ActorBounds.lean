module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Three.RankOne.Generation
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Three.RankOne.ContainedStructure
public import Theory.GroupAction.Extraspecial27ElementaryActor
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Faithful small odd-group actions bound the endpoint actors

The parabolic two-core has trivial centralizer of P* in H*, so every
conjugate-core actor acts faithfully on P*. For cyclic P* of order three,
its automorphism group has order two. For the contained branch, L₁*=Z(P*)
and normality and coprime orders make the parabolic core centralize it.
A faithful elementary two-group fixing the center of an extraspecial
group of order 27 has order at most two. Each nonidentity actor also
inverts the actual Frattini quotient.

These intrinsic automorphism bounds supply exactly the endpoint order
bound needed for the contradictions. The extraspecial inversion conclusion
is obtained directly from the proved involution theorem, with all of its
hypotheses established; no global D.2.17 reduction is required.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
13.8.13, printed p.951; compare D.2.17(4), printed p.192.
-/

@[expose] public section

open Subgroup
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Three.RankOne
variable {G : Type*} [Group G]

private theorem star_faithful_of_core_placement [Finite G] {p : ℕ}
    {H L₁ T M Vα B : Subgroup G} (d : ReducedOdd p H L₁ T M Vα)
    (h : H) (hB : B.map (MulAut.conj (h : G)).toMonoidHom ≤ (L₁ ⊔ T).pCoreIn 2) :
    Source.starImage H B ⊓ centralizer (Source.starImage H d.P : Set _) = ⊥ := by
  let := d.Pstar_normal
  let q := QuotientGroup.mk' (pCore 2 H)
  apply bot_unique
  rintro x ⟨⟨b, hb, rfl⟩, hcent⟩
  have hc : q h * q b * (q h)⁻¹ ∈
      Source.starImage H ((L₁ ⊔ T).pCoreIn 2) := by
    refine ⟨h * b * h⁻¹, hB (mem_map_of_mem _ hb), ?_⟩
    change q (h * b * h⁻¹) = _
    rw [map_mul, map_mul, map_inv]
  have hh := (inferInstance :
      (centralizer (Source.starImage H d.P : Set (Source.Hstar H))).Normal).conj_mem
      (q b) hcent (q h)
  have he : q h * q b * (q h)⁻¹ = 1 := by
    have hi := show q h * q b * (q h)⁻¹ ∈
      Source.starImage H ((L₁ ⊔ T).pCoreIn 2) ⊓
        centralizer (Source.starImage H d.P : Set (Source.Hstar H)) from ⟨hc, hh⟩
    rwa [parabolic_core_star_centralizer d, mem_bot] at hi
  exact mem_bot.mpr (mul_left_cancel ((mul_inv_eq_one.mp he).trans (mul_one (q h)).symm))

private theorem conjugation_injective_of_disjoint_centralizer
    (P A : Subgroup G) [P.Normal] (hf : A ⊓ centralizer (P : Set G) = ⊥) :
    Function.Injective ((MulAut.conjNormal : G →* MulAut P).comp A.subtype) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro a ha
  have hc : (a : G) ∈ centralizer (P : Set G) := by
    intro x hx
    have hh := congrArg Subtype.val (DFunLike.congr_fun ha (⟨x, hx⟩ : P))
    change (a : G) * x * (a : G)⁻¹ = x at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  apply Subtype.ext
  have hh : (a : G) ∈ A ⊓ centralizer (P : Set G) := ⟨a.property, hc⟩
  change (a : G) = 1
  simpa only [hf, mem_bot] using hh

private theorem contained_actor_centralizes_center [Finite G]
    {H L₁ T M Vα B : Subgroup G} (d : ReducedOdd 3 H L₁ T M Vα)
    (hlt : Source.starImage H L₁ < Source.starImage H d.P)
    (hne : Source.starImage H L₁ ≠ ⊥) (hTL : T ≤ normalizer (L₁ : Set G))
    (h : H) (hB : B.map (MulAut.conj (h : G)).toMonoidHom ≤ (L₁ ⊔ T).pCoreIn 2) :
    Source.starImage H B ≤ centralizer
      ((center (Source.starImage H d.P)).map (Source.starImage H d.P).subtype : Set _) := by
  let := d.Pstar_normal
  have hZ := contained_center d hlt hne hTL
  let : (Source.starImage H L₁).Normal := by
    rw [hZ]
    exact ConjAct.normal_of_characteristic_of_normal
  let Q := Source.starImage H ((L₁ ⊔ T).pCoreIn 2)
  have hcommQ : ⁅Source.starImage H L₁, Q⁆ ≤ Q :=
    (commutator_mono (starImage_mono H le_sup_left) le_rfl).trans
      (le_normalizer_iff_commutator_le_right.mp
        (starImage_normalizes H (le_normalizer_pCoreIn 2 (L₁ ⊔ T))))
  have hp : IsPGroup 3 (Source.starImage H L₁) :=
    (starImage_isPGroup H d.P d.P_isPGroup).to_le hlt.le
  have hd := hp.disjoint_of_coprime
    (starImage_isPGroup H ((L₁ ⊔ T).pCoreIn 2) (isPGroup_pCoreIn 2 _))
    (by decide : Nat.Coprime 3 2)
  have hcomm : ⁅Source.starImage H L₁, Q⁆ = ⊥ :=
    bot_unique ((le_inf (commutator_le_left _ _) hcommQ).trans hd.le_bot)
  have hQC := commutator_eq_bot_iff_le_centralizer.mp ((commutator_comm _ _).trans hcomm)
  rw [← hZ]
  let q := QuotientGroup.mk' (pCore 2 H)
  rintro _ ⟨b, hb, rfl⟩
  have hh : q h * q b * (q h)⁻¹ ∈ Q := by
    refine ⟨h * b * h⁻¹, hB (mem_map_of_mem _ hb), ?_⟩
    change q (h * b * h⁻¹) = _
    rw [map_mul, map_mul, map_inv]
  have hc := (inferInstance :
      (centralizer (Source.starImage H L₁ : Set (Source.Hstar H))).Normal).conj_mem
      _ (hQC hh) (q h)⁻¹
  simpa only [mul_assoc, inv_mul_cancel_left, inv_inv, inv_mul_cancel, mul_one] using hc

/-- Every elementary actor in a conjugate of the parabolic two-core has order
at most two in the contained branch. This proves the rank bound directly
from faithful center-fixing automorphisms of the actual extraspecial P*. -/
theorem contained_actor_card_le_two [Finite G]
    {H L₁ T M Vα B : Subgroup G} [IsElementaryAbelian 2 B]
    (d : ReducedOdd 3 H L₁ T M Vα)
    (hlt : Source.starImage H L₁ < Source.starImage H d.P)
    (hne : Source.starImage H L₁ ≠ ⊥) (hTL : T ≤ normalizer (L₁ : Set G))
    (hBH : B ≤ H) (h : H)
    (hB : B.map (MulAut.conj (h : G)).toMonoidHom ≤ (L₁ ⊔ T).pCoreIn 2) :
    Nat.card (Source.starImage H B) ≤ 2 := by
  let := d.Pstar_normal
  let := (contained_extraspecial d hlt hne hTL).1
  let : IsElementaryAbelian 2 (Source.starImage H B) :=
    CriticalGeometry.starImage_isElementaryAbelian H B hBH
  let act := (MulAut.conjNormal : Source.Hstar H →* MulAut (Source.starImage H d.P)).comp
    (Source.starImage H B).subtype
  have hi : Function.Injective act := conjugation_injective_of_disjoint_centralizer _ _
    (star_faithful_of_core_placement d h hB)
  have hcenter := contained_actor_centralizes_center d hlt hne hTL h hB
  apply MulAut.elementary_two_center_preserving_card_le_two
    (by simpa using (contained_extraspecial d hlt hne hTL).2.1) act hi
  intro b z hz
  have hc := mem_centralizer_iff.mp (hcenter b.property) (z : Source.Hstar H)
    (mem_map_of_mem _ hz)
  apply Subtype.ext
  change (b : Source.Hstar H) * (z : Source.Hstar H) * (b : Source.Hstar H)⁻¹ = z
  rw [← hc, mul_inv_cancel_right]

/-- Each nonidentity star actor in this branch inverts the actual Frattini quotient.
The extraspecial involution theorem supplies the D.2.17(4) conclusion directly. -/
theorem contained_actor_inverts_frattini [Finite G]
    {H L₁ T M Vα B : Subgroup G} [IsElementaryAbelian 2 B]
    (d : ReducedOdd 3 H L₁ T M Vα)
    (hlt : Source.starImage H L₁ < Source.starImage H d.P)
    (hne : Source.starImage H L₁ ≠ ⊥) (hTL : T ≤ normalizer (L₁ : Set G))
    (hBH : B ≤ H) (h : H)
    (hB : B.map (MulAut.conj (h : G)).toMonoidHom ≤ (L₁ ⊔ T).pCoreIn 2) :
    let _ := d.Pstar_normal
    ∀ b : Source.starImage H B, b ≠ 1 → ∀ x : Source.starImage H d.P,
      QuotientGroup.mk' (frattini (Source.starImage H d.P)) (MulAut.conjNormal (b : Source.Hstar H) x) =
        (QuotientGroup.mk' (frattini (Source.starImage H d.P)) x)⁻¹ := by
  dsimp only
  let := d.Pstar_normal
  let := (contained_extraspecial d hlt hne hTL).1
  let : IsElementaryAbelian 2 (Source.starImage H B) :=
    CriticalGeometry.starImage_isElementaryAbelian H B hBH
  let act := (MulAut.conjNormal : Source.Hstar H →* MulAut (Source.starImage H d.P)).comp
    (Source.starImage H B).subtype
  have hi : Function.Injective act := conjugation_injective_of_disjoint_centralizer _ _
    (star_faithful_of_core_placement d h hB)
  have hcenter := contained_actor_centralizes_center d hlt hne hTL h hB
  intro b hb
  apply (IsExtraspecial.exponent_and_frattini_inversion_of_card27
    (by simpa using (contained_extraspecial d hlt hne hTL).2.1) (act b) ?_ ?_ ?_).2
  · intro x
    have hh : b ^ 2 = 1 := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 _) b
    have hh' := congrArg act hh
    rw [map_pow, map_one, pow_two] at hh'
    exact DFunLike.congr_fun hh' x
  · exact fun he => hb (hi (he.trans act.map_one.symm))
  · intro z hz
    have hc := mem_centralizer_iff.mp (hcenter b.property) (z : Source.Hstar H)
      (mem_map_of_mem _ hz)
    apply Subtype.ext
    change (b : Source.Hstar H) * (z : Source.Hstar H) * (b : Source.Hstar H)⁻¹ = z
    rw [← hc, mul_inv_cancel_right]

/-- An actor placed in the parabolic core embeds in Aut(C₃), of order two.
This gives the cyclic branch's required star-image bound directly. -/
theorem cyclic_actor_card_le_two [Finite G]
    {H L₁ T M Vα B : Subgroup G} (d : ReducedOdd 3 H L₁ T M Vα)
    (hP : Nat.card (Source.starImage H d.P) = 3)
    (h : H) (hB : B.map (MulAut.conj (h : G)).toMonoidHom ≤ (L₁ ⊔ T).pCoreIn 2) :
    Nat.card (Source.starImage H B) ≤ 2 := by
  let := d.Pstar_normal
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let : IsCyclic (Source.starImage H d.P) := isCyclic_of_prime_card hP
  let act := (MulAut.conjNormal : Source.Hstar H →* MulAut (Source.starImage H d.P)).comp
    (Source.starImage H B).subtype
  have hi : Function.Injective act := conjugation_injective_of_disjoint_centralizer _ _
    (star_faithful_of_core_placement d h hB)
  have hc : Nat.card (MulAut (Source.starImage H d.P)) = 2 := by
    rw [IsCyclic.card_mulAut, hP, Nat.totient_prime Nat.prime_three]
  simpa only [hc] using Nat.card_le_card_of_injective act hi

end CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Three.RankOne
end
