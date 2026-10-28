module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.FourThreeBranch.NaturalSelection.Structure.CubicParity
public import Theory.SpecificGroups.Alternating.FourPairCore
public import Theory.SpecificGroups.SymmetricTwoResidual
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# The even four-plus-three residual in the rank-four branch

The literal partition stabilizer inside A₇ has embedded two-residual A₄ × A₃,
which is also the existing cubic closure. Its intrinsic two-core quotient is
C₃ × C₃. Each even partition actor induces one common scalar on that quotient.
These facts retain the actual residual and its intrinsic core, so the source
fixing/inverting actor can be compared after transport through the local marking.

Source: Aschbacher–Smith, Lemma 14.7.50, printed p.1064, refs/quasithin.pdf.
-/

public noncomputable section
open Equiv Subgroup
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource.FourExclusion.Model
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.FourThreeBranch.NaturalSelection

/-- The literal even subgroup of the four-plus-three partition stabilizer. -/
@[expose] def P : Subgroup S7 := fourThreeStabilizer ⊓ alternatingGroup (Fin 7)
/-- The intrinsic two-residual embedded in the seven-point permutation group. -/
@[expose] def R : Subgroup S7 := (pResidual 2 P).map P.subtype
private def A : Subgroup FourThree :=
  (alternatingGroup (Fin 4)).prod (alternatingGroup (Fin 3))

private theorem sign_of_cube {n : ℕ} (g : Perm (Fin n)) (h : g ^ 3 = 1) :
    g.sign = 1 := by
  have hs : g.sign ^ 3 = 1 := by rw [← map_pow, h, map_one]
  rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, Int.units_sq, one_mul] at hs
  exact hs

private theorem theta_eq : fourThreeTheta = A.map fourThreeHom := by
  apply le_antisymm
  · apply (closure_le _).mpr
    rintro x ⟨⟨c, rfl⟩, hc⟩
    refine mem_map.mpr ⟨c, ?_, rfl⟩
    have h3 : c ^ 3 = 1 := fourThreeHom_injective (by
      rw [map_pow, map_one]
      simpa only [hc] using pow_orderOf_eq_one (fourThreeHom c))
    exact ⟨sign_of_cube c.1 (congrArg Prod.fst h3),
      sign_of_cube c.2 (congrArg Prod.snd h3)⟩
  · have hf (f : Perm (Fin 4) →* S7) (hi : Function.Injective f)
        (hp : f.range ≤ fourThreeStabilizer) :
        (alternatingGroup (Fin 4)).map f ≤ fourThreeTheta := by
      rw [← Perm.closure_three_cycles_eq_alternating, MonoidHom.map_closure, closure_le]
      rintro _ ⟨a, ha, rfl⟩
      exact subset_closure ⟨hp ⟨a,rfl⟩,(orderOf_injective f hi a).trans ha.orderOf⟩
    have hg (f : Perm (Fin 3) →* S7) (hi : Function.Injective f)
        (hp : f.range ≤ fourThreeStabilizer) :
        (alternatingGroup (Fin 3)).map f ≤ fourThreeTheta := by
      rw [← Perm.closure_three_cycles_eq_alternating, MonoidHom.map_closure, closure_le]
      rintro _ ⟨a, ha, rfl⟩
      exact subset_closure ⟨hp ⟨a,rfl⟩,(orderOf_injective f hi a).trans ha.orderOf⟩
    have h4 := hf (fourThreeHom.comp (MonoidHom.inl _ _))
      (fourThreeHom_injective.comp (fun _ _ h => congrArg Prod.fst h))
      (by rintro _ ⟨x,rfl⟩; exact ⟨(x,1),rfl⟩)
    have h3 := hg (fourThreeHom.comp (MonoidHom.inr _ _))
      (fourThreeHom_injective.comp (fun _ _ h => congrArg Prod.snd h))
      (by rintro _ ⟨x,rfl⟩; exact ⟨(1,x),rfl⟩)
    rintro _ ⟨⟨a,b⟩,⟨ha,hb⟩,rfl⟩
    have hh := fourThreeTheta.mul_mem (h4 ⟨a,ha,rfl⟩) (h3 ⟨b,hb,rfl⟩)
    simpa only [MonoidHom.comp_apply, MonoidHom.inl_apply, MonoidHom.inr_apply,
      ← map_mul, Prod.mk_mul_mk, mul_one, one_mul] using hh

/-- The two-residual of the even partition stabilizer is the literal cubic closure. -/
theorem residual_eq_theta : R = fourThreeTheta := by
  apply le_antisymm
  · rw [theta_eq]
    let c : P →* FourThree := fourThreeEquiv.symm.toMonoidHom.comp (inclusion inf_le_left)
    rintro _ ⟨x,hx,rfl⟩
    refine ⟨c x,?_,?_⟩
    · constructor
      · have h := map_pResidual_le 2 ((MonoidHom.fst _ _).comp c) ⟨x,hx,rfl⟩
        rwa [Perm.twoResidual_eq_alternating] at h
      · have h := map_pResidual_le 2 ((MonoidHom.snd _ _).comp c) ⟨x,hx,rfl⟩
        rwa [Perm.twoResidual_eq_alternating] at h
    · exact congrArg Subtype.val (fourThreeEquiv.apply_symm_apply (inclusion inf_le_left x))
  · apply (closure_le _).mpr
    intro c hc
    have hp : c ∈ P := ⟨hc.1,sign_of_cube c (hc.2 ▸ pow_orderOf_eq_one c)⟩
    refine ⟨⟨c,hp⟩,mem_pResidual_of_orderOf_coprime ?_,rfl⟩
    rw [← orderOf_coe,hc.2]
    decide

/-- Both block alternating subgroups give the entire literal residual. -/
theorem residual_eq_product : R =
    ((alternatingGroup (Fin 4)).prod (alternatingGroup (Fin 3))).map fourThreeHom :=
  residual_eq_theta.trans theta_eq

private def residualEquiv : R ≃* alternatingGroup (Fin 4) × alternatingGroup (Fin 3) :=
  (MulEquiv.subgroupCongr (residual_eq_theta.trans theta_eq)).trans
    ((A.equivMapOfInjective fourThreeHom fourThreeHom_injective).symm.trans
      (prodEquiv _ _))

private theorem card_alt_three : Nat.card (alternatingGroup (Fin 3)) = 3 := by
  rw [nat_card_alternatingGroup,Nat.card_fin]
  rfl

private theorem three_core : pCore 2 (alternatingGroup (Fin 3)) = ⊥ := by
  have h3 : IsPGroup 3 (alternatingGroup (Fin 3)) :=
    IsPGroup.of_card (n := 1) (by simpa using card_alt_three)
  exact le_bot_iff.mp ((le_inf le_rfl le_top).trans
    (pCore_isPGroup.disjoint_of_coprime (h3.to_subgroup ⊤)
      (by decide : Nat.Coprime 2 3)).le_bot)

private theorem four_quotient_card :
    Nat.card (alternatingGroup (Fin 4) ⧸ pCore 2 (alternatingGroup (Fin 4))) = 3 := by
  have hc := (pCore 2 (alternatingGroup (Fin 4))).card_mul_index
  have hk : Nat.card (pCore 2 (alternatingGroup (Fin 4))) = 4 := by
    rw [AlternatingFourPair.twoCore_eq_kleinFour,
      alternatingGroup.kleinFour_card_of_card_eq_four (by norm_num)]
  rw [hk,nat_card_alternatingGroup,Nat.card_fin] at hc
  change 4 * Nat.card (alternatingGroup (Fin 4) ⧸ pCore 2 (alternatingGroup (Fin 4))) = 12 at hc
  omega

private theorem quotient_model : Nonempty (R ⧸ pCore 2 R ≃*
    Multiplicative (ZMod 3) × Multiplicative (ZMod 3)) := by
  let e := QuotientGroup.congr _ _ residualEquiv (pCore_map_iso 2 residualEquiv)
  let f := QuotientGroup.quotientMulEquivOfEq (pCore_prod 2 (G := alternatingGroup (Fin 4))
    (A := alternatingGroup (Fin 3)))
  let q := QuotientGroup.prodMulEquiv (pCore 2 (alternatingGroup (Fin 4)))
    (pCore 2 (alternatingGroup (Fin 3)))
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let a := mulEquivOfPrimeCardEq four_quotient_card
    (show Nat.card (Multiplicative (ZMod 3)) = 3 by simp [Nat.card_eq_fintype_card])
  let b := (QuotientGroup.quotientMulEquivOfEq three_core).trans QuotientGroup.quotientBot
  let c := mulEquivOfPrimeCardEq card_alt_three
    (show Nat.card (Multiplicative (ZMod 3)) = 3 by simp [Nat.card_eq_fintype_card])
  exact ⟨((e.trans f).trans q).trans (MulEquiv.prodCongr a (b.trans c))⟩

/-- The intrinsic quotient of the literal residual, with both cubic factors. -/
def quotientEquiv : R ⧸ pCore 2 R ≃* Multiplicative (ZMod 3) × Multiplicative (ZMod 3) :=
  Classical.choice quotient_model

/-- The residual has intrinsic two-core quotient of order nine. -/
theorem quotient_card : Nat.card (R ⧸ pCore 2 R) = 9 := by
  rw [Nat.card_congr quotientEquiv.toEquiv]
  simp [Nat.card_eq_fintype_card]

/-- Every element of the intrinsic residual quotient has cube one. -/
theorem quotient_cube (x : R ⧸ pCore 2 R) : x ^ 3 = 1 := by
  apply quotientEquiv.injective
  rw [map_pow,map_one]
  have h (y : Multiplicative (ZMod 3)) : y ^ 3 = 1 := by
    simpa only [Nat.card_eq_fintype_card,Fintype.card_multiplicative,ZMod.card]
      using pow_card_eq_one' (x := y)
  exact Prod.ext (h _) (h _)

/-- Every even partition actor acts by one common scalar on the residual quotient. -/
theorem scalar_quotient (t : P) (τ : R →* R)
    (ha : ∀ x : R, (τ x).val = t.val * x.val * t.val⁻¹) :
    (∀ x, QuotientGroup.mk' (pCore 2 R) (τ x) = QuotientGroup.mk' (pCore 2 R) x) ∨
    (∀ x, QuotientGroup.mk' (pCore 2 R) (τ x) = (QuotientGroup.mk' (pCore 2 R) x)⁻¹) := by
  apply CubicParity.even_scalar_quotient quotientEquiv R.subtype
    (by rw [R.ker_subtype]; exact IsPGroup.of_subsingleton 2 _) _ τ t.val t.property.1 t.property.2 ha
  rw [range_subtype,residual_eq_theta]
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource.FourExclusion.Model
