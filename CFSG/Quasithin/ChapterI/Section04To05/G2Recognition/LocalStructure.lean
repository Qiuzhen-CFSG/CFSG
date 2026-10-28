module
public import CFSG.Quasithin.Chapter14.Section04.DimensionFour.Configuration
public import Theory.GroupTheory.GeneralizedFitting.ElementaryEightAction
public import Theory.SpecificGroups.PSL3Two.Parabolics.LinearModel
public import Theory.SpecificGroups.SL2.ThreeResidualCore
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.ElementaryAbelian.Injective

/-!
# Local consequences of the genuine G₂(3) recognition configuration

The two normal SL₂(3) factors give a product of order 288, equal to O²(H),
and |H| = 576. Their intersection defines an actual ambient involution
whose centralizer is H. Independently, F*(M) is O₂(M), and conjugation
identifies the literal quotient M/F*(M) with the full automorphism group
of the elementary eight. Its nonidentity points have M-centralizers of
order 192. In particular neither H nor M contains the other.

These are consequences of (G1)–(G2), not a recognition theorem: the
ambient amalgam/fusion argument and identification with the octonion
model remain with `qt-i45-g2-recognition`. The Chapter 14 final assembly
owner is `qt-d-14414-g2-source`, including its consolidated local-data work.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, §I.4,
printed p.417, preceding Lemma I.4.5; cited recognition source:
M. Aschbacher, *Finite groups of G₂(3)-type*, J. Algebra 257 (2002), 197–214.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
open Chapter14.Section04.DimensionFour
variable {G : Type*} [Group G] [Finite G] (c : G2ThreeConfiguration G)
attribute [local instance] G2ThreeConfiguration.H₁_normal G2ThreeConfiguration.H₂_normal
  G2ThreeConfiguration.V_normal

private instance parameters_elementary : IsElementaryAbelian 2 (Multiplicative (Fin 3 → ZMod 2)) where
  is_comm := ⟨mul_comm⟩
  exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by
    intro x
    rw [pow_two]
    change (fun i => x.toAdd i + x.toAdd i) = (fun _ => 0)
    exact funext (fun i => (by decide : ∀ a : ZMod 2, a + a = 0) (x.toAdd i)))

omit [Finite G] in
theorem V_elementary : IsElementaryAbelian 2 c.V :=
  IsElementaryAbelian.of_injective c.V_model.some.toMonoidHom c.V_model.some.injective
attribute [local instance] V_elementary

omit [Finite G] in
theorem V_card : Nat.card c.V = 8 := by
  rw [Nat.card_congr c.V_model.some.toEquiv]
  change Nat.card (Fin 3 → ZMod 2) = 8
  simp

omit [Finite G] in
theorem quotient_card : Nat.card (c.M ⧸ c.V) = 168 :=
  (Nat.card_congr c.quotient_model.some.toEquiv).trans Matrix.PSL3Two.card_PSL

omit [Finite G] in
theorem M_card : Nat.card c.M = 1344 :=
  GeneralizedFittingEight.card_group c.V (V_card c) (quotient_card c)

theorem V_eq_pCore : c.V = pCore 2 c.M :=
  (GeneralizedFittingEight.pCore_eq c.V c.fitting).symm

theorem V_centralizer : centralizer (c.V : Set c.M) = c.V :=
  GeneralizedFittingEight.centralizer_eq c.V c.fitting

noncomputable def quotientConjugationEquiv : (c.M ⧸ c.V) ≃* MulAut c.V :=
  GeneralizedFittingEight.quotientConjugationEquiv c.V c.fitting (V_card c) (quotient_card c)

theorem quotientConjugationEquiv_mk (m : c.M) (v : c.V) :
    (quotientConjugationEquiv c (QuotientGroup.mk' c.V m) v : c.M) =
      m * (v : c.M) * m⁻¹ := rfl

theorem seed_nonidentity_conjugate (x y : c.V) (hx : x ≠ 1) (hy : y ≠ 1) :
    ∃ m : c.M, m * (x : c.M) * m⁻¹ = (y : c.M) :=
  GeneralizedFittingEight.nonidentity_conjugate c.V c.fitting (V_card c) (quotient_card c) x y hx hy

theorem seed_point_centralizer_card (x : c.V) (hx : x ≠ 1) :
    Nat.card (centralizer ({(x : c.M)} : Set c.M)) = 192 :=
  GeneralizedFittingEight.point_centralizer_card c.V c.fitting (V_card c) (quotient_card c) x hx

omit [Finite G] in
theorem intersection_card : Nat.card (c.H₁ ⊓ c.H₂ : Subgroup c.H) = 2 := by
  rw [Nat.card_congr c.intersection_model.some.toEquiv]
  change Nat.card (ZMod 2) = 2
  simp

theorem product_card : Nat.card (c.H₁ ⊔ c.H₂ : Subgroup c.H) = 288 := by
  have hl := (Nat.card_congr c.H₁_model.some.toEquiv).trans
    GLS3.Chapter5.SchurPresentation.sl23_card_eq
  have hr := (Nat.card_congr c.H₂_model.some.toEquiv).trans
    GLS3.Chapter5.SchurPresentation.sl23_card_eq
  have hc := card_mul_eq_card_inf_mul_card_sup_of_normalizes c.H₁ c.H₂
    (show c.H₂ ≤ normalizer (c.H₁ : Set c.H) from le_normalizer_of_normal)
  rw [hl,hr,intersection_card c] at hc
  omega

theorem H_card : Nat.card c.H = 576 := by
  have hc := (c.H₁ ⊔ c.H₂).card_mul_index
  rw [product_card c, c.index] at hc
  exact hc.symm

omit [Finite G] in
theorem H_residual : pResidual 2 c.H = c.H₁ ⊔ c.H₂ := by
  apply le_antisymm
  · apply sInf_le
    refine ⟨inferInstance, IsPGroup.of_card (n := 1) ?_⟩
    exact c.index
  · apply sup_le
    · exact le_pResidual_of_isPPerfect c.H₁
        (GLS3.Chapter5.SchurPresentation.sl23_twoPerfect.of_surjective
          c.H₁_model.some.symm.toMonoidHom c.H₁_model.some.symm.surjective)
    · exact le_pResidual_of_isPPerfect c.H₂
        (GLS3.Chapter5.SchurPresentation.sl23_twoPerfect.of_surjective
          c.H₂_model.some.symm.toMonoidHom c.H₂_model.some.symm.surjective)

theorem not_M_le_H : ¬ c.M ≤ c.H := by
  intro h
  have hd := card_dvd_of_le h
  rw [M_card c, H_card c] at hd
  norm_num at hd

theorem not_H_le_M : ¬ c.H ≤ c.M := by
  intro h
  have hd := card_dvd_of_le h
  rw [M_card c, H_card c] at hd
  norm_num at hd

include c in
theorem ambient_order_divisible : 4032 ∣ Nat.card G := by
  have hd := Nat.lcm_dvd c.H.card_subgroup_dvd_card c.M.card_subgroup_dvd_card
  simpa only [H_card c, M_card c, show Nat.lcm 576 1344 = 4032 from rfl] using hd

theorem exists_involution_centralizer :
    ∃ z : G, orderOf z = 2 ∧ c.H = centralizer ({z} : Set G) := by
  let Z : Subgroup G := (c.H₁ ⊓ c.H₂).map c.H.subtype
  have hZ : Nat.card Z = 2 :=
    (card_map_of_injective c.H.subtype_injective).trans (intersection_card c)
  obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' (G := Z) 2 (by rw [hZ])
  have hzG : orderOf (z : G) = 2 := by
    exact (orderOf_injective Z.subtype Z.subtype_injective z).trans hz
  have hgen : zpowers (z : G) = Z := by
    apply eq_of_le_of_card_ge (zpowers_le.mpr z.property)
    rw [Nat.card_zpowers, hzG, hZ]
  refine ⟨z,hzG,?_⟩
  rw [c.centralizer]
  change centralizer (Z : Set G) = _
  calc
    centralizer (Z : Set G) = centralizer (zpowers (z : G) : Set G) :=
      congrArg (fun A : Subgroup G => centralizer (A : Set G)) hgen.symm
    _ = centralizer ({(z : G)} : Set G) := by
      rw [zpowers_eq_closure, centralizer_closure]

end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
