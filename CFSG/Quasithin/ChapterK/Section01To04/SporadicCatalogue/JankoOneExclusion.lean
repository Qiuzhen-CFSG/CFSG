module

public import Theory.Representation.BinaryPrimeDisplacement.Quotient
public import CFSG.Quasithin.ChapterK.Section01To04.SporadicCatalogue.Source
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.OuterModels.AlternatingSporadic.JankoOne
public import Theory.SpecificGroups.Janko1.Model.Certification
public import Theory.Representation.BinaryIrreducibleCentralizer
public import Theory.GroupAction.PerfectCentralQuotient
public import Theory.GroupAction.InnerInvolutionGeometry


/-!
# The J₁ cubic exclusion, retaining all central covers

Every involution in an ambient faithful binary action that is irreducible on
its perfect normal subgroup with central quotient J₁ moves at least nine
dimensions. Indeed the induced quotient automorphism is nontrivial by Schur's
lemma and faithful descent through the center. Every automorphism of J₁ is
inner, and its involutions fuse to the standard generator a. The standard
commutator [a,b] has order 19. Lift the conjugator and b to the perfect normal
subgroup: the resulting ambient commutator has an image of order 19 and hence
moves at least ord₁₉(2) = 18 dimensions. Commutator subadditivity gives the nine
bound on the original involution.

Every elementary abelian two-subgroup embeds in Aut(J₁), whose order has
2-part eight. A cubic actor of ratio at most two therefore moves at most six
dimensions, contradicting the nine bound for any of its involutions. This
proves the exclusion in every dimension and, in particular, in degree at most
18. The central kernel is retained throughout; no multiplier or module table
is assumed, and the independent three-conjugate geometry is not required.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, K.4,
printed p.457 (PDF p.468), citing GM02, Theorem 6.6 and Table 6.7. This is a
direct proof of its J₁ exclusion using G.7.1(1) and the checked intrinsic model
and automorphism results. The ATLAS matrix provenance is recorded in
`Theory.SpecificGroups.Janko1.Model.Basic` and the imported outer certificate.
-/

public section

open Subgroup Representation.BinaryOffender Theory.GroupTheory
open scoped ENNReal
namespace CFSG.Quasithin.ChapterK.SporadicCatalogue
namespace JankoOneExclusion

private theorem conjugation_injective : Function.Injective (MulAut.conj :
    Janko1.Model →* MulAut Janko1.Model) :=
  MulAut.conj_injective_of_center_eq_bot Subgroup.center_eq_bot_of_simple_perfect

private theorem automorphism_card : Nat.card (MulAut Janko1.Model) = 175560 := by
  let e := MulEquiv.ofBijective (MulAut.conj : Janko1.Model →* MulAut Janko1.Model)
    ⟨conjugation_injective, Janko1.OuterCertificate.aut_inner⟩
  exact (Nat.card_congr e.toEquiv).symm.trans Janko1.card_model

private theorem orderOf_two_nineteen : orderOf (2 : ZMod 19) = 18 := by
  apply (orderOf_eq_iff (by decide : 0 < 18)).mpr
  constructor
  · decide
  · intro m hm hpos
    interval_cases m <;> norm_num at * <;> decide

private theorem standard_commutator_order :
    orderOf (Janko1.a * Janko1.b * Janko1.a⁻¹ * Janko1.b⁻¹) = 19 := by
  have ha : Janko1.a⁻¹ = Janko1.a :=
    inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using Janko1.a_pow_two)
  have hb : Janko1.b⁻¹ = Janko1.b ^ 2 := by
    apply inv_eq_of_mul_eq_one_right
    exact (pow_succ' Janko1.b 2).symm.trans Janko1.b_pow_three
  simpa only [ha, hb] using Janko1.orderOf_abab_sq

variable {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (L : Subgroup G) [L.Normal] [Group.IsPerfect L]
    (hf : Function.Injective ρ) (hi : Representation.IsIrreducible (ρ.comp L.subtype))
    (e : L ⧸ center L ≃* Janko1.Model)

private def quotientAction : G →* MulAut Janko1.Model :=
  (MulAut.centralQuotientAction e).comp MulAut.conjNormal

omit [Finite G] [Group.IsPerfect L] in
private theorem quotientAction_subtype (x : L) :
    quotientAction L e (x : G) = MulAut.conj (e (QuotientGroup.mk' (center L) x)) := by
  change MulAut.centralQuotientAction e (MulAut.conjNormal (x : G)) = _
  rw [MulAut.conjNormal_val, MulAut.centralQuotientAction_conj]

include hf hi e

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
private theorem eq_one_of_quotientAction_eq_one {t : G} (ht : t ^ 2 = 1)
    (he : quotientAction L e t = 1) : t = 1 := by
  let := hi
  have hc : (MulAut.conjNormal t : MulAut L) = 1 :=
    MulAut.centralQuotientAction_injective e (he.trans (map_one _).symm)
  apply Representation.BinaryIrreducibleCentralizer.centralizing_square_one_eq_one ρ L hf ht
  apply mem_centralizer_iff.mpr
  intro x hx
  have h := congrArg (fun α : MulAut L => ((α ⟨x, hx⟩ : L) : G)) hc
  change t * x * t⁻¹ = x at h
  exact (mul_inv_eq_iff_eq_mul.mp h).symm

omit [FiniteDimensional (ZMod 2) V] in
private theorem elementary_rank_le_three (A : Subgroup G) (hA : IsElementaryAbelian 2 A) :
    rank A ≤ 3 := by
  let := hA
  let f := (quotientAction L e).comp A.subtype
  have hinj : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply le_bot_iff.mp
    intro t ht
    apply Subtype.ext
    apply eq_one_of_quotientAction_eq_one ρ L hf hi e
      (elemPow_eq_one_of_isElementaryAbelian (t : G) t.property)
    exact ht
  have hd := Subgroup.card_dvd_of_injective f hinj
  rw [automorphism_card] at hd
  obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_card_eq
  have hn3 : n ≤ 3 := by
    by_contra! hn3
    have h16 : 16 ∣ 175560 :=
      (show 16 ∣ 2 ^ n from pow_dvd_pow 2 (by omega : 4 ≤ n)).trans (hn ▸ hd)
    norm_num at h16
  simpa only [rank, hn, Nat.log_pow (by decide : 1 < 2)] using hn3

private theorem involution_displacement_ge_nine (t : G) (ht : t ≠ 1)
    (ht2 : t ^ 2 = 1) : 9 ≤ fixedCodim ρ (zpowers t) := by
  let f := quotientAction L e
  have hft : f t ≠ 1 := fun h => ht (eq_one_of_quotientAction_eq_one ρ L hf hi e ht2 h)
  obtain ⟨s, hs⟩ := Janko1.OuterCertificate.aut_inner (f t)
  have hs1 : s ≠ 1 := fun h => hft (by rw [← hs, h, map_one])
  have hs2 : s ^ 2 = 1 := conjugation_injective (by
    rw [map_pow, hs, ← map_pow, ht2, map_one, map_one])
  obtain ⟨k, hk⟩ := Janko1.involution_fusion s (orderOf_eq_prime hs2 hs1)
  let π : L →* Janko1.Model := e.toMonoidHom.comp (QuotientGroup.mk' (center L))
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  obtain ⟨l, hl⟩ := hπ k
  obtain ⟨x, hx⟩ := hπ Janko1.b
  have hfl : f (l : G) = MulAut.conj k := (quotientAction_subtype L e l).trans (congrArg MulAut.conj hl)
  have hfx : f (x : G) = MulAut.conj Janko1.b := (quotientAction_subtype L e x).trans (congrArg MulAut.conj hx)
  let t' : G := (l : G) * t * (l : G)⁻¹
  have hft' : f t' = MulAut.conj Janko1.a := by
    change f ((l : G) * t * (l : G)⁻¹) = _
    rw [map_mul, map_mul, map_inv, hfl, ← hs, ← map_inv, ← map_mul, ← map_mul, hk]
  have hcomm : orderOf (f (t' * x * t'⁻¹ * (x : G)⁻¹)) = 19 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hft', hfx,
      ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
    rw [orderOf_injective _ conjugation_injective]
    exact standard_commutator_order
  have hd := prime_order_image_le_fixedCodim ρ hf f (by decide : Nat.Prime 19)
    (by decide) _ hcomm
  rw [orderOf_two_nineteen] at hd
  have hb := fixedCodim_commutator_le_twice ρ t' (x : G)
  have he : fixedCodim ρ (zpowers t') = fixedCodim ρ (zpowers t) :=
    fixedCodim_zpowers_conj ρ t l
  rw [he] at hb
  omega

end JankoOneExclusion

universe u v

/-- J₁ is excluded by the cubic source hypotheses for every central cover and
ambient action. Every involution moves at least nine dimensions, whereas an
actor of ratio at most two has rank at most three and moves at most six. -/
theorem sourceExclusion_j1 : SourceExclusion.{u,v} .j1 := by
  intro G V _ _ _ _ _ ρ h he
  obtain ⟨e⟩ := he
  let L := generalizedFitting G
  let := h.quasisimple
  obtain ⟨A, hA, _, hr⟩ := (cubicRatio_le_nat_iff ρ 2).mp h.cubic_le_two
  have hAr := JankoOneExclusion.elementary_rank_le_three ρ L h.faithful h.irreducible e A hA.2
  obtain ⟨t, htA, ht⟩ := A.bot_or_exists_ne_one.resolve_left hA.1
  let := hA.2
  have hd := JankoOneExclusion.involution_displacement_ge_nine ρ L h.faithful h.irreducible e
    t ht (elemPow_eq_one_of_isElementaryAbelian t htA)
  have hfix := Submodule.finrank_mono (fixedSpace_antitone ρ (zpowers_le.mpr htA))
  have h₁ := fixedCodim_add_finrank ρ (zpowers t)
  have h₂ := fixedCodim_add_finrank ρ A
  omega

/-- The requested degree-eighteen window, as a consequence of the stronger
cover-preserving local-action exclusion. -/
theorem boundedSourceExclusion_j1 : BoundedSourceExclusion.{u,v} .j1 18 := by
  intro G V _ _ _ _ _ ρ h he _
  exact sourceExclusion_j1 ρ h he

end CFSG.Quasithin.ChapterK.SporadicCatalogue
