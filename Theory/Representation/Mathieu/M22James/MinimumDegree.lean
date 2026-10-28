module

public import Theory.Representation.Mathieu.M22James
public import Theory.Representation.BinaryCoprimeDegree
public import Theory.Representation.BinaryPrimeDegree
public import Theory.Representation.NormalInvariants
import Theory.Mathieu.M22.Properties.ThreeRank
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreNormalizer.LinearNormalizer.CoreRecognition.ProjectiveAction
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreNormalizer.LinearNormalizer.CoreRecognition.PermutationComparison
public import Theory.GroupTheory.PGroup.PrimeCubeCenter
import Mathlib.Tactic.FinCases

/-!
# James minimum degree for the binary triple cover of M₂₂

The concrete projective action supplies an explicit order-nine elementary subgroup
of M₂₂. Its preimage in the genuine matrix triple cover is checked to be
noncommutative of order 27, hence extraspecial. James's binary degree argument
then gives divisibility by six; the order-eleven divisor of the carrier order
excludes degree ten.

Source: James, *The modular characters of the Mathieu groups*, Lemma 8.3,
J. Algebra 27 (1973), pp. 57–111; quasithin reference H.12.1, pp. 393–394.
-/

namespace Sporadic.Mathieu.M22TripleCover
open Sporadic.Mathieu
open Subgroup
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
noncomputable section
set_option maxRecDepth 100000

private def jamesEvalWord {G : Type*} [Group G] (u v : G) (w : List (Fin 4)) : G :=
  (w.map ![u, v, u⁻¹, v⁻¹]).prod
private def jamesXWord : List (Fin 4) := [2,2,2,1,2,2,2,1,0,0,1,2,2,2,2,1,0,0]
private def jamesYWord : List (Fin 4) := [1,0,1,0,0,0,0,1,2,1,2,2,2,1,2,2,2,1,2,2]
private def jamesXPerm : Equiv.Perm (Fin 22) where
  toFun := ![4, 21, 8, 16, 17, 5, 7, 12, 18, 10, 19, 11, 6, 1, 14, 15, 20, 0, 2, 9, 3, 13]
  invFun := ![17, 13, 18, 20, 0, 5, 12, 6, 2, 19, 9, 11, 7, 21, 14, 15, 3, 4, 8, 10, 16, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
private def jamesYPerm : Equiv.Perm (Fin 22) where
  toFun := ![20, 13, 8, 7, 3, 5, 0, 4, 18, 9, 10, 15, 17, 21, 11, 14, 12, 16, 2, 19, 6, 1]
  invFun := ![6, 21, 18, 4, 7, 5, 20, 3, 2, 9, 10, 14, 16, 1, 15, 11, 17, 12, 8, 19, 0, 13]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem jamesXPerm_eq_word : jamesXPerm = jamesEvalWord corePermA corePermB jamesXWord := by
  ext i
  fin_cases i <;> decide +kernel
private theorem jamesYPerm_eq_word : jamesYPerm = jamesEvalWord corePermA corePermB jamesYWord := by
  ext i
  fin_cases i <;> decide +kernel
private theorem jamesEvalWord_mem {G : Type*} [Group G] (H : Subgroup G)
    {u v : G} (hu : u ∈ H) (hv : v ∈ H) (w : List (Fin 4)) : jamesEvalWord u v w ∈ H := by
  induction w with
  | nil => exact H.one_mem
  | cons i w ih =>
    apply H.mul_mem _ ih
    fin_cases i
    · exact hu
    · exact hv
    · exact H.inv_mem hu
    · exact H.inv_mem hv
private theorem jamesXPerm_mem : jamesXPerm ∈ M22 := by
  rw [jamesXPerm_eq_word]
  exact jamesEvalWord_mem M22 corePermA_mem_M22 corePermB_mem_M22 jamesXWord
private theorem jamesYPerm_mem : jamesYPerm ∈ M22 := by
  rw [jamesYPerm_eq_word]
  exact jamesEvalWord_mem M22 corePermA_mem_M22 corePermB_mem_M22 jamesYWord
private def jamesRankX : M22 := ⟨jamesXPerm, jamesXPerm_mem⟩
private def jamesRankY : M22 := ⟨jamesYPerm, jamesYPerm_mem⟩
private theorem jamesRankX_order : orderOf jamesRankX = 3 := by
  apply orderOf_eq_prime
  · apply Subtype.ext
    decide +kernel
  · intro h
    have hne : (jamesRankX : Equiv.Perm (Fin 22)) ≠ 1 := by decide +kernel
    exact hne (congrArg Subtype.val h)
private theorem jamesRankY_order : orderOf jamesRankY = 3 := by
  apply orderOf_eq_prime
  · apply Subtype.ext
    decide +kernel
  · intro h
    have hne : (jamesRankY : Equiv.Perm (Fin 22)) ≠ 1 := by decide +kernel
    exact hne (congrArg Subtype.val h)
private theorem jamesRankX_commute_rankY : Commute jamesRankX jamesRankY := by
  apply Subtype.ext
  decide +kernel
private theorem jamesRankY_not_mem : jamesRankY ∉ zpowers jamesRankX := by
  rw [mem_zpowers_iff_mem_range_orderOf, jamesRankX_order]
  intro h
  obtain ⟨i, hi, he⟩ := Finset.mem_image.mp h
  have hh : ∀ i : Fin 3,
      (jamesRankY : Equiv.Perm (Fin 22)) ≠ (jamesRankX : Equiv.Perm (Fin 22)) ^ i.val := by
    decide +kernel
  exact hh ⟨i, Finset.mem_range.mp hi⟩ (congrArg Subtype.val he).symm
private def jamesE : Subgroup M22 := zpowers jamesRankX ⊔ zpowers jamesRankY
private theorem jamesE_properties : IsElementaryAbelian 3 jamesE ∧ Nat.card jamesE = 3 ^ 2 := by
  let : IsElementaryAbelian 3 (zpowers jamesRankX) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one (jamesRankX_order ▸ pow_orderOf_eq_one jamesRankX)
  have hc : Nat.card (zpowers jamesRankX) = 3 ^ 1 := by
    rw [Nat.card_zpowers, jamesRankX_order]; norm_num
  have hfix : zpowers jamesRankX ≤ centralizer ({jamesRankY} : Set M22) := by
    apply zpowers_le.mpr
    exact mem_centralizer_singleton_iff.mpr jamesRankX_commute_rankY.eq
  exact IsElementaryAbelian.fixed_join_card (zpowers jamesRankX) jamesRankY jamesRankY_order
    ((zpowers jamesRankX).disjoint_zpowers_of_prime_order_not_mem jamesRankY jamesRankY_order jamesRankY_not_mem)
    hfix hc
private instance jamesE_elementary : IsElementaryAbelian 3 jamesE := jamesE_properties.1
private theorem jamesE_card : Nat.card jamesE = 3 ^ 2 := jamesE_properties.2

private def jamesXCore : M22TripleCover := jamesEvalWord coreGeneratorA coreGeneratorB jamesXWord
private def jamesYCore : M22TripleCover := jamesEvalWord coreGeneratorA coreGeneratorB jamesYWord
private theorem jamesXCore_image : corePermutationAction jamesXCore = jamesXPerm := by
  rw [jamesXCore, jamesEvalWord, MonoidHom.map_list_prod]
  rw [List.map_map]
  have hv : (corePermutationAction ∘ (fun i : Fin 4 => ![coreGeneratorA, coreGeneratorB,
      coreGeneratorA⁻¹, coreGeneratorB⁻¹] i)) =
      (fun i : Fin 4 => ![corePermA, corePermB, corePermA⁻¹, corePermB⁻¹] i) := by
    funext i
    fin_cases i <;> simp [corePermutationAction_coreGeneratorA, corePermutationAction_coreGeneratorB]
  rw [hv]
  exact jamesXPerm_eq_word.symm
private theorem jamesYCore_image : corePermutationAction jamesYCore = jamesYPerm := by
  rw [jamesYCore, jamesEvalWord, MonoidHom.map_list_prod]
  rw [List.map_map]
  have hv : (corePermutationAction ∘ (fun i : Fin 4 => ![coreGeneratorA, coreGeneratorB,
      coreGeneratorA⁻¹, coreGeneratorB⁻¹] i)) =
      (fun i : Fin 4 => ![corePermA, corePermB, corePermA⁻¹, corePermB⁻¹] i) := by
    funext i
    fin_cases i <;> simp [corePermutationAction_coreGeneratorA, corePermutationAction_coreGeneratorB]
  rw [hv]
  exact jamesYPerm_eq_word.symm

private theorem jamesCore_noncomm : jamesXCore * jamesYCore ≠ jamesYCore * jamesXCore := by
  decide +kernel


private noncomputable def jamesQuotientMap : M22TripleCover →* M22 :=
  centralQuotientEquiv.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center M22TripleCover))
private theorem jamesQuotientMap_surjective : Function.Surjective jamesQuotientMap := by
  intro y
  obtain ⟨z, rfl⟩ := centralQuotientEquiv.surjective y
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (Subgroup.center M22TripleCover) z
  exact ⟨x, by
    change centralQuotientEquiv (QuotientGroup.mk' (Subgroup.center M22TripleCover) x) =
      centralQuotientEquiv z
    rw [hx]⟩
private theorem jamesQuotientMap_ker : jamesQuotientMap.ker = Subgroup.center M22TripleCover := by
  apply le_antisymm
  · intro x hx
    apply (QuotientGroup.eq_one_iff _).mp
    apply centralQuotientEquiv.injective
    simpa [jamesQuotientMap] using (MonoidHom.mem_ker.mp hx)
  · intro x hx
    apply MonoidHom.mem_ker.mpr
    change centralQuotientEquiv (QuotientGroup.mk' (Subgroup.center M22TripleCover) x) = 1
    rw [← centralQuotientEquiv.map_one]
    have hq : QuotientGroup.mk' (Subgroup.center M22TripleCover) (x : M22TripleCover) = 1 :=
      (QuotientGroup.eq_one_iff (x : M22TripleCover)).mpr hx
    rw [hq]
private def jamesP : Subgroup M22TripleCover := jamesE.comap jamesQuotientMap
private theorem james_card_comap_mul
    {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hsurj : Function.Surjective f) (K : Subgroup H) :
    Nat.card (K.comap f) = Nat.card K * Nat.card f.ker := by
  classical
  let s : H → G := fun h => Classical.choose (hsurj h)
  have hs (h : H) : f (s h) = h := Classical.choose_spec (hsurj h)
  let e : ↥K × ↥f.ker ≃ ↥(K.comap f) :=
    { toFun := fun x => ⟨s x.1.1 * x.2.1, by
        rw [Subgroup.mem_comap, map_mul, hs, MonoidHom.mem_ker.mp x.2.2, mul_one]
        exact x.1.2⟩
      invFun := fun y => ⟨⟨f y.1, (Subgroup.mem_comap.mp y.2)⟩,
        ⟨(s (f y.1))⁻¹ * y.1, by
          rw [MonoidHom.mem_ker, map_mul, map_inv, hs, inv_mul_cancel]⟩⟩
      left_inv := by
        intro x
        apply Prod.ext
        · apply Subtype.ext
          change f (s x.1.1 * x.2.1) = x.1.1
          rw [map_mul, hs, MonoidHom.mem_ker.mp x.2.2, mul_one]
        · apply Subtype.ext
          have hk : f (s x.1.1 * x.2.1) = x.1.1 := by
            rw [map_mul, hs, MonoidHom.mem_ker.mp x.2.2, mul_one]
          calc
            (s (f (s x.1.1 * x.2.1)))⁻¹ * (s x.1.1 * x.2.1)
                = (s x.1.1)⁻¹ * (s x.1.1 * x.2.1) := by rw [hk]
            _ = x.2.1 := by simp
      right_inv := by
        intro y
        apply Subtype.ext
        calc
          s (f y.1) * ((s (f y.1))⁻¹ * y.1) = y.1 := by simp }
  rw [← Nat.card_congr e]
  rw [Nat.card_prod]

private theorem jamesP_card : Nat.card jamesP = 27 := by
  change Nat.card (jamesE.comap jamesQuotientMap) = 27
  rw [james_card_comap_mul jamesQuotientMap jamesQuotientMap_surjective jamesE]
  rw [jamesE_card, jamesQuotientMap_ker, M22TripleCover.center_card]
  norm_num
private theorem jamesCentralQuotient_action (x : M22TripleCover) :
    centralQuotientEquiv (QuotientGroup.mk' (Subgroup.center M22TripleCover) x) =
      ⟨corePermutationAction x, by
        rw [← corePermutationAction_range_eq_M22]
        exact ⟨x, rfl⟩⟩ := by rfl
private theorem jamesXQuotient_image : jamesQuotientMap jamesXCore = jamesRankX := by
  apply Subtype.ext
  rw [jamesQuotientMap]
  simp only [MonoidHom.comp_apply]
  change ((centralQuotientEquiv.toMonoidHom
      (QuotientGroup.mk' (Subgroup.center M22TripleCover) jamesXCore) : M22) : Equiv.Perm (Fin 22)) =
      (jamesRankX : Equiv.Perm (Fin 22))
  rw [show centralQuotientEquiv.toMonoidHom
      (QuotientGroup.mk' (Subgroup.center M22TripleCover) jamesXCore) =
      centralQuotientEquiv (QuotientGroup.mk' (Subgroup.center M22TripleCover) jamesXCore) from rfl]
  simp only [jamesCentralQuotient_action, jamesXCore_image]
  rfl
private theorem jamesYQuotient_image : jamesQuotientMap jamesYCore = jamesRankY := by
  apply Subtype.ext
  rw [jamesQuotientMap]
  simp only [MonoidHom.comp_apply]
  change ((centralQuotientEquiv.toMonoidHom
      (QuotientGroup.mk' (Subgroup.center M22TripleCover) jamesYCore) : M22) : Equiv.Perm (Fin 22)) =
      (jamesRankY : Equiv.Perm (Fin 22))
  rw [show centralQuotientEquiv.toMonoidHom
      (QuotientGroup.mk' (Subgroup.center M22TripleCover) jamesYCore) =
      centralQuotientEquiv (QuotientGroup.mk' (Subgroup.center M22TripleCover) jamesYCore) from rfl]
  simp only [jamesCentralQuotient_action, jamesYCore_image]
  rfl
private theorem jamesX_mem_P : jamesXCore ∈ jamesP := by
  change jamesQuotientMap jamesXCore ∈ jamesE
  rw [jamesXQuotient_image]
  exact Subgroup.mem_sup_left (Subgroup.mem_zpowers jamesRankX)
private theorem jamesY_mem_P : jamesYCore ∈ jamesP := by
  change jamesQuotientMap jamesYCore ∈ jamesE
  rw [jamesYQuotient_image]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers jamesRankY)
private theorem jamesP_noncomm : ¬ IsMulCommutative jamesP := by
  intro h
  have he := (@IsMulCommutative.is_comm _ _ h).comm
    (⟨jamesXCore, jamesX_mem_P⟩ : jamesP)
    (⟨jamesYCore, jamesY_mem_P⟩ : jamesP)
  have he' := congrArg jamesP.subtype he
  apply jamesCore_noncomm
  change jamesXCore * jamesYCore = jamesYCore * jamesXCore at he'
  exact he' 


private theorem jamesCenterL_le_P : Subgroup.center M22TripleCover ≤ jamesP := by
  intro x hx
  change jamesQuotientMap x ∈ jamesE
  have hker : x ∈ jamesQuotientMap.ker := by
    rw [jamesQuotientMap_ker]
    exact hx
  have hq : jamesQuotientMap x = 1 := MonoidHom.mem_ker.mp hker
  rw [hq]
  exact jamesE.one_mem
private def jamesZP : Subgroup jamesP :=
  (Subgroup.center M22TripleCover).subgroupOf jamesP
private theorem jamesZP_card : Nat.card jamesZP = 3 := by
  rw [show Nat.card jamesZP = Nat.card (Subgroup.center M22TripleCover) by
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe jamesCenterL_le_P).toEquiv]
  exact M22TripleCover.center_card
private theorem jamesZP_le_center : jamesZP ≤ Subgroup.center jamesP := by
  intro x hx
  change (x : M22TripleCover) ∈ Subgroup.center M22TripleCover at hx
  apply Subgroup.mem_center_iff.mpr
  intro y
  apply Subtype.ext
  exact (Subgroup.mem_center_iff.mp hx) y.1
private theorem jamesCenterP_card : Nat.card (Subgroup.center jamesP) = 3 := by
  exact Subgroup.card_center_eq_prime_of_card_eq_prime_cube jamesP_card jamesP_noncomm
private theorem jamesZP_eq_center : jamesZP = Subgroup.center jamesP := by
  apply Subgroup.eq_of_le_of_card_ge jamesZP_le_center
  rw [jamesCenterP_card, jamesZP_card]
private def jamesRestrict : jamesP →* jamesE where
  toFun x := ⟨jamesQuotientMap x, by
    simpa only [jamesP, Subgroup.mem_comap] using x.property⟩
  map_one' := by ext; simp
  map_mul' x y := by ext; simp
private theorem jamesRestrict_surjective : Function.Surjective jamesRestrict := by
  intro e
  obtain ⟨x, hx⟩ := jamesQuotientMap_surjective e
  exact ⟨⟨x, by rw [jamesP, Subgroup.mem_comap, hx]; exact e.2⟩, Subtype.ext hx⟩
private theorem jamesRestrict_ker : jamesRestrict.ker = jamesZP := by
  ext x
  change jamesRestrict x = 1 ↔ x ∈ jamesZP
  let hxE : jamesQuotientMap (x : M22TripleCover) ∈ jamesE := by
    simpa only [jamesP, Subgroup.mem_comap] using x.property
  have happ : jamesRestrict x = (⟨jamesQuotientMap (x : M22TripleCover), hxE⟩ : jamesE) := rfl
  rw [happ, Subtype.ext_iff]
  change jamesQuotientMap (x : M22TripleCover) = 1 ↔
    (x : M22TripleCover) ∈ Subgroup.center M22TripleCover
  rw [← MonoidHom.mem_ker, jamesQuotientMap_ker]
private instance jamesZP_normal : jamesZP.Normal := by
  rw [jamesZP_eq_center]
  infer_instance
private def jamesQuotientLift : jamesP ⧸ jamesZP →* jamesE :=
  QuotientGroup.lift jamesZP jamesRestrict (by
    exact le_of_eq jamesRestrict_ker.symm)
private theorem jamesQuotientLift_surjective : Function.Surjective jamesQuotientLift := by
  intro e
  obtain ⟨x, hx⟩ := jamesRestrict_surjective e
  refine ⟨QuotientGroup.mk' jamesZP x, ?_⟩
  exact (QuotientGroup.lift_mk' _ _ _).trans hx
private noncomputable def jamesQuotientEquivZ : jamesP ⧸ jamesZP ≃* jamesE :=
  MulEquiv.ofBijective jamesQuotientLift (by
    refine ⟨?_, jamesQuotientLift_surjective⟩
    intro a b hab
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective jamesZP a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective jamesZP b
    have hxy : jamesRestrict x = jamesRestrict y := by
      have hN : jamesZP ≤ jamesRestrict.ker := le_of_eq jamesRestrict_ker.symm
      rw [← QuotientGroup.lift_mk' jamesZP hN, ← QuotientGroup.lift_mk' jamesZP hN]
      exact hab
    have hker : jamesRestrict (x * y⁻¹) = 1 := by
      rw [map_mul, map_inv, hxy, mul_inv_cancel]
    have hz : x * y⁻¹ ∈ jamesZP := by
      rw [← jamesRestrict_ker]
      exact MonoidHom.mem_ker.mpr hker
    have hq : QuotientGroup.mk' jamesZP (x * y⁻¹) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hz
    rw [map_mul, map_inv] at hq
    exact mul_inv_eq_one.mp hq)
private theorem jamesP_quotient_elementary_Z :
    IsElementaryAbelian 3 (jamesP ⧸ jamesZP) := by
  let e := jamesQuotientEquivZ
  have hcomm : ∀ a b : jamesE, a * b = b * a :=
    (@IsElementaryAbelian.toIsMulCommutative 3 jamesE _ jamesE_elementary).is_comm.comm
  refine { toIsMulCommutative := ⟨⟨?_⟩⟩, exponent_dvd_p := ?_ }
  · intro x y
    apply e.injective
    calc
      e (x * y) = e x * e y := map_mul e x y
      _ = e y * e x := hcomm (e x) (e y)
      _ = e (y * x) := (map_mul e y x).symm
  · rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    intro x
    apply e.injective
    simpa only [map_pow, map_one] using
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 3 jamesE) (e x))
private theorem jamesP_quotient_elementary :
    IsElementaryAbelian 3 (jamesP ⧸ Subgroup.center jamesP) := by
  let e := QuotientGroup.quotientMulEquivOfEq jamesZP_eq_center.symm
  have he := jamesP_quotient_elementary_Z
  have hcomm : ∀ a b : jamesP ⧸ jamesZP, a * b = b * a :=
    (@IsElementaryAbelian.toIsMulCommutative 3 _ _ he).is_comm.comm
  refine { toIsMulCommutative := ⟨⟨?_⟩⟩, exponent_dvd_p := ?_ }
  · intro x y
    apply e.injective
    calc
      e (x * y) = e x * e y := map_mul e x y
      _ = e y * e x := hcomm (e x) (e y)
      _ = e (y * x) := (map_mul e y x).symm
  · rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    intro x
    apply e.injective
    simpa only [map_pow, map_one] using
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 3 (jamesP ⧸ jamesZP)) (e x))
private theorem jamesX_not_center :
    (⟨jamesXCore, jamesX_mem_P⟩ : jamesP) ∉ Subgroup.center jamesP := by
  intro hx
  have he := (Subgroup.mem_center_iff.mp hx) (⟨jamesYCore, jamesY_mem_P⟩ : jamesP)
  have he' := congrArg jamesP.subtype he
  apply jamesCore_noncomm
  change jamesYCore * jamesXCore = jamesXCore * jamesYCore at he'
  exact he'.symm
private theorem jamesP_quotient_nontrivial :
    Nontrivial (jamesP ⧸ Subgroup.center jamesP) := by
  apply Finite.one_lt_card_iff_nontrivial.mp
  have hmul := (Subgroup.center jamesP).card_mul_index
  rw [jamesCenterP_card, jamesP_card] at hmul
  have hi : (Subgroup.center jamesP).index = 9 := by omega
  rw [← Subgroup.index_eq_card]
  rw [hi]
  norm_num
private instance jamesP_extraspecial : IsExtraspecial 3 jamesP where
  center_order_p := jamesCenterP_card
  quotient_elementary_abelian := jamesP_quotient_elementary
  quotient_nontrivial := jamesP_quotient_nontrivial

public theorem faithful_irreducible_finrank_ge_twelve
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) M22TripleCover W)
    (hfaith : Function.Injective ρ) [Representation.IsIrreducible ρ] :
    12 ≤ Module.finrank (ZMod 2) W := by
  let : FiniteDimensional (ZMod 2) W :=
    Representation.finiteDimensional_of_irreducible_finite_group ρ inferInstance
  have hfixL : Representation.invariants (ρ.comp (Subgroup.center M22TripleCover).subtype) = ⊥ := by
    by_contra hne
    have hker := Representation.le_ker_of_normal_invariants_ne_bot ρ
      (Subgroup.center M22TripleCover) hne
    have hbot : Subgroup.center M22TripleCover = ⊥ := by
      apply bot_unique
      simpa only [(MonoidHom.ker_eq_bot_iff _).mpr hfaith] using hker
    have hc := M22TripleCover.center_card
    rw [hbot] at hc
    norm_num at hc
  have hfixP : Representation.invariants
      ((ρ.comp jamesP.subtype).comp (Subgroup.center jamesP).subtype) = ⊥ := by
    apply le_antisymm
    · intro v hv
      have hvL : v ∈ Representation.invariants
          (ρ.comp (Subgroup.center M22TripleCover).subtype) := by
        rw [Representation.mem_invariants]
        intro z
        let pz : jamesP := ⟨z, jamesCenterL_le_P z.property⟩
        have hpz : pz ∈ Subgroup.center jamesP := by
          rw [← jamesZP_eq_center]
          exact z.property
        have hv' := (Representation.mem_invariants
          ((ρ.comp jamesP.subtype).comp (Subgroup.center jamesP).subtype) v).mp hv
          ⟨pz, hpz⟩
        exact hv'
      rw [hfixL, Submodule.mem_bot] at hvL
      exact hvL
    · exact bot_le
  have h6 : 6 ∣ Module.finrank (ZMod 2) W := by
    exact Representation.BinaryCoprimeDegree.six_dvd_finrank_of_extraspecial_twentySeven
      (ρ.comp jamesP.subtype) jamesP_card hfixP
  have h10 : 10 ≤ Module.finrank (ZMod 2) W := by
    have h := Representation.BinaryPrimeDegree.orderOf_le_finrank ρ hfaith
      (by decide : Nat.Prime 11) (by decide : 11 ≠ 2)
      (by rw [M22TripleCover.card]; norm_num)
    simpa only [Representation.BinaryPrimeDegree.orderOf_two_mod_eleven] using h
  omega

end
end Sporadic.Mathieu.M22TripleCover
