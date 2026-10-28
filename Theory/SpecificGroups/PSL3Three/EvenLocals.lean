module

public import Theory.SpecificGroups.PSL3Three.Cardinality
public import Theory.SpecificGroups.GL2.SemidihedralSylow
public import Theory.SpecificGroups.SL3.InvolutionConjugacy
public import Theory.SpecificGroups.GL2.ThreeCharacteristicTwo
public import Theory.GroupTheory.SylowContainingTwoLocal
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Theory.GroupTheory.SemidihedralNormalElementary
public import Theory.Quasithin.EvenCharacteristic

/-!
# Sylow-containing two-locals of SL₃(3)

The determinant-corrected block embedding sends a semidihedral subgroup of
GL₂(3), of order sixteen, into SL₃(3). Since |SL₃(3)| = 5616 = 16 · 351,
this is a Sylow two-subgroup. Sylow conjugacy gives its presentation for
any Sylow two-subgroup T.

Every maximal two-local containing T is the normalizer of a nontrivial
normal elementary subgroup of T. The SD16 presentation forces that subgroup
to be the central involution line, so the local is an involution centralizer.
The actual block-centralizer isomorphism with GL₂(3) then transports the
proved self-centralization of its two-core. The GL₂(3) calculation uses
solvability and trivial odd core, as proved in `GL2.ThreeCharacteristicTwo`.

This supplies condition E for the PSL₃(3) alternative of Aschbacher–Smith,
Theorem 0.1.2(4), printed p.4, repeated as Theorem 0.1.1(4) on p.482.
The semidihedral matrix construction comes from Alperin–Brauer–Gorenstein
II.2 Lemma 1, article p.17. No classification of maximal subgroups is used.
-/

namespace Matrix.PSL3Three
open Subgroup

/-- Every Sylow two-subgroup of SL₃(3) has the full SD16 presentation. -/
public theorem sylowTwo_generators_SL (T : Sylow 2 SL) :
    ∃ a b : T, orderOf a = 8 ∧ orderOf b = 2 ∧
      b * a * b⁻¹ = a ^ 3 ∧ closure ({a, b} : Set T) = ⊤ := by
  obtain ⟨P, n, _, hp, a, b, ha, hb, hc, hg, -, -⟩ :=
    GeneralLinearGroup.exists_semidihedral_sylow (ZMod 3) (by norm_num)
  have hPcard : Nat.card P = 16 := by
    rw [P.card_eq_multiplicity, Matrix.card_GL_field]
    norm_num [Fin.prod_univ_two]
    decide +kernel
  have hn4 : n = 4 := by
    have h : 2 ^ n = 2 ^ 4 := hp.symm.trans hPcard
    exact Nat.pow_right_injective (by decide : 2 ≤ 2) h
  subst n
  norm_num at ha hc
  let f : GL (Fin 2) (ZMod 3) →* SL := SL3.blockEmbedding (ZMod 3)
  have hf : Function.Injective f := SL3.blockEmbedding_injective (ZMod 3)
  let S := (P : Subgroup _).map f
  let eS : P ≃* S := Subgroup.equivMapOfInjective _ f hf
  have hS : Nat.card S = 16 := (Nat.card_congr eS.toEquiv).symm.trans hPcard
  let U : Sylow 2 SL := Sylow.ofCard S (by rw [hS, card_SL]; decide +kernel)
  let e : P ≃* T := eS.trans (U.equiv T)
  refine ⟨e a, e b, ?_, ?_, ?_, ?_⟩
  · exact (e.orderOf_eq a).trans ha
  · exact (e.orderOf_eq b).trans hb
  · rw [← map_inv, ← map_mul, ← map_mul, hc, map_pow]
  · have hh := congrArg (Subgroup.map e.toMonoidHom) hg
    rw [MonoidHom.map_closure, Set.image_insert_eq, Set.image_singleton,
      Subgroup.map_top_of_surjective e.toMonoidHom e.surjective] at hh
    convert hh using 1
    rfl

/-- Every maximal two-local containing a Sylow subgroup is an actual involution centralizer. -/
public theorem maximalTwoLocal_eq_involutionCentralizer_SL
    (T : Sylow 2 SL) {M : Subgroup SL}
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup SL) ≤ M) :
    ∃ z : SL, orderOf z = 2 ∧ M = centralizer ({z} : Set SL) := by
  obtain ⟨a, b, ha, hb, hc, hg⟩ := sylowTwo_generators_SL T
  obtain ⟨R, hR, hn, he, hMR⟩ :=
    Theory.GroupTheory.exists_normal_elementary_normalizer_of_sylow_le T hM hTM
  let : R.Normal := hn
  let : IsElementaryAbelian 2 R := he
  rw [Semidihedral.normal_elementary_eq_of_order_sixteen a b ha hb hc hg R hR,
    MonoidHom.map_zpowers] at hMR
  have hz : orderOf (((a ^ 4 : T) : SL)) = 2 := by
    rw [Subgroup.orderOf_coe, orderOf_pow, ha]
    norm_num
  refine ⟨((a ^ 4 : T) : SL), hz, ?_⟩
  change M = normalizer (zpowers (((a ^ 4 : T) : SL)) : Set SL) at hMR
  rwa [normalizer_zpowers_eq_centralizer_of_order_two _ hz] at hMR

/-- Each involution centralizer in SL₃(3) has self-centralizing two-core. -/
public theorem involutionCentralizer_twoCore_selfCentralizing_SL
    (z : SL) (hz : orderOf z = 2) :
    let C := centralizer ({z} : Set SL)
    centralizer (pCore 2 C : Set C) ≤ pCore 2 C := by
  exact (Theory.Quasithin.centralizer_pCore_le_iff 2
    (SL3.involutionCentralizerEquiv (ZMod 3) z hz (by decide))).mpr
    GeneralLinearGroup.three_centralizer_twoCore_le

end Matrix.PSL3Three
