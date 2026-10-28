module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.CartanGeometry.Torus
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.TwoLocalCover.Geometry
public import Theory.SpecificGroups.PSL3.LinearThreeLocalCores
public import Theory.Representation.SpecialLinearThreeTransitivity
public import BenderSuzuki.External.Huppert.II.theorem_6_14
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Basic
public import Mathlib.Algebra.CharP.CharAndCard

/-!
# The original Cartan fixes only the central kernel

The source Cartan has odd order (q−1)² and embeds through the original
component quotient. A nonzero fixed natural vector would put it in a pointwise
vector stabilizer. For both SL₃ and Sp₄ that stabilizer has two-core quotient
SL₂(q), so the odd Cartan would embed in SL₂(q). Its order cannot divide
q(q²−1) when q is even and greater than two.

Transport through the literal projection V → V/C_V(L) proves the ambient
fixed-space bound without splitting or discarding the central kernel. Comparing
Sylow orders excludes a G₂ marking under either actual block hypothesis, so
the result applies to any coordinates supplied by the source.

Source: Aschbacher–Smith, combined manuscript, 1 March 2004, the Cartan in
Chapter 11's setup and its use in 11.1.5, printed pp.759,765–766. The model
Sylow APIs retain their existing ATLAS attribution.
-/

open Subgroup Theory.GroupTheory Matrix
open scoped MatrixGroups
@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointCohomology.PointGeometry

private theorem injective_of_odd_two_kernel {A B : Type*} [Group A] [Finite A] [Group B]
    (f : A →* B) (ho : Odd (Nat.card A)) (hk : IsPGroup 2 f.ker) :
    Function.Injective f := by
  apply f.ker_eq_bot_iff.mp
  have hc : Odd (Nat.card f.ker) := Odd.of_dvd_nat ho f.ker.card_subgroup_dvd_card
  obtain ⟨n, hn⟩ := hk.exists_card_eq
  have hn0 : n = 0 := by
    by_contra h
    exact hc.not_two_dvd_nat (hn ▸ dvd_pow_self 2 h)
  apply Subgroup.eq_bot_of_card_eq
  exact hn.trans (by rw [hn0]; rfl)

private theorem torus_order_not_dvd_sl2 {q : ℕ} (hq : 2 < q) (ho : Odd (q-1)) :
    ¬ (q-1)^2 ∣ q * (q^2-1) := by
  intro hd
  have hpos : 0 < q - 1 := by omega
  have he : q * (q^2-1) = (q-1) * (q*(q+1)) := by
    have h : q - 1 + 1 = q := by omega
    have h2 : q ^ 2 - 1 + 1 = q ^ 2 := Nat.sub_add_cancel (by nlinarith)
    nlinarith
  rw [he, pow_two] at hd
  have hd' : q-1 ∣ q*(q+1) := (Nat.mul_dvd_mul_iff_left hpos).mp hd
  have hcop : Nat.Coprime (q-1) q := by
    exact (Nat.coprime_self_sub_left (show 1 ≤ q by omega)).mpr (Nat.coprime_one_left _)
  have hh : q-1 ∣ q+1 := hcop.dvd_of_dvd_mul_left hd'
  have htwo : q-1 ∣ 2 := by
    have he : q+1 = (q-1)+2 := by omega
    rw [he] at hh
    exact (Nat.dvd_add_right (dvd_refl (q-1))).mp hh
  have hle := Nat.le_of_dvd (by decide : 0 < 2) htwo
  obtain ⟨k, hk⟩ := ho
  omega

private theorem not_injective_sl2 {F A : Type*} [Field F] [Finite F] [Group A] [Finite A]
    (hF : 2 < Nat.card F) (ho : Odd (Nat.card F - 1))
    (hc : Nat.card A = (Nat.card F - 1)^2) (f : A →* SL(2,F)) :
    ¬ Function.Injective f := by
  intro hi
  have hd := Subgroup.card_dvd_of_injective f hi
  rw [hc, BenderSuzuki.External.huppert614_card_specialLinearGroup] at hd
  exact torus_order_not_dvd_sl2 hF ho hd

private theorem odd_embedding_core_quotient {A B : Type*} [Group A] [Finite A] [Group B]
    (f : A →* B) (hi : Function.Injective f) (ho : Odd (Nat.card A)) :
    Function.Injective ((QuotientGroup.mk' (pCore 2 B)).comp f) := by
  apply injective_of_odd_two_kernel _ ho
  change IsPGroup 2 ((QuotientGroup.mk' (pCore 2 B)).ker.comap f)
  rw [QuotientGroup.ker_mk']
  exact pCore_isPGroup.comap_of_injective f hi

namespace LinearModel
open Matrix.PSL3.LinearThree
private theorem sl3_fixed_eq_zero {F A : Type*} [Field F] [Finite F] [CharP F 2]
    [Group A] [Finite A] (hF : 2 < Nat.card F) (ho : Odd (Nat.card F - 1))
    (hc : Nat.card A = (Nat.card F - 1)^2) (f : A →* SL(3,F))
    (hi : Function.Injective f) (v : Fin 3 → F)
    (hv : ∀ a, (f a).val *ᵥ v = v) : v = 0 := by
  by_contra hn
  have he0 : (![1,0,0] : Fin 3 → F) ≠ 0 := by
    intro h
    have := congrFun h 0
    simp at this
  obtain ⟨g,hg⟩ := Matrix.SpecialLinearGroup.exists_mulVec_eq_three v ![1,0,0] hn he0
  let j := (MulAut.conj g).toMonoidHom.comp f
  have hj (a : A) : j a ∈ pointLocalSL F := by
    have hh : (j a) • (![1,0,0] : Fin 3 → F) = ![1,0,0] := by
      change (g * f a * g⁻¹) • (![1,0,0] : Fin 3 → F) = _
      change g • v = ![1,0,0] at hg
      rw [← hg, mul_smul, mul_smul, inv_smul_smul]
      change g • ((f a).val *ᵥ v) = g • v
      rw [hv]
    apply (mem_pointLocalSL_iff F _).mpr
    change (j a).val *ᵥ ![1,0,0] = ![1,0,0] at hh
    have h0 := congrFun hh 0
    have h1 := congrFun hh 1
    have h2 := congrFun hh 2
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using And.intro h0 (And.intro h1 h2)
  let k := j.codRestrict (pointLocalSL F) hj
  have hk : Function.Injective k := by
    intro a b h
    exact hi ((MulAut.conj g).injective (congrArg Subtype.val h))
  have hodd : Odd (Nat.card A) := hc ▸ ho.pow
  let r := (pointLocalSLCoreQuotientEquiv F).toMonoidHom.comp
    ((QuotientGroup.mk' (pCore 2 (pointLocalSL F))).comp k)
  exact not_injective_sl2 hF ho hc r
    ((pointLocalSLCoreQuotientEquiv F).injective.comp (odd_embedding_core_quotient k hk hodd))
end LinearModel

namespace SymplecticModel
open Theory.SpecificGroups.SymplecticFour
private theorem sp4_fixed_eq_zero {F A : Type*} [Field F] [Finite F] [CharP F 2]
    [Group A] [Finite A] (hF : 2 < Nat.card F) (ho : Odd (Nat.card F - 1))
    (hc : Nat.card A = (Nat.card F - 1)^2) (f : A →* Sp F)
    (hi : Function.Injective f) (v : Vector F)
    (hv : ∀ a, (f a) • v = v) : v = 0 := by
  by_contra hn
  have he0 : e (F := F) 0 ≠ 0 := by
    intro h
    have := congrFun h (.inl 0)
    simp [Theory.SpecificGroups.SymplecticFour.e] at this
  obtain ⟨g,hg⟩ := TwoLocalCover.nonzero_vector_transitive hn he0
  let j := (MulAut.conj g).toMonoidHom.comp f
  have hj (a : A) : j a ∈ pointLocal := by
    apply (mem_pointLocal_iff_fixed _).mpr
    change (g * f a * g⁻¹) • e (F := F) 0 = _
    rw [← hg, mul_smul, mul_smul, inv_smul_smul, hv]
  let k := j.codRestrict (pointLocal (F := F)) hj
  have hk : Function.Injective k := by
    intro a b h
    exact hi ((MulAut.conj g).injective (congrArg Subtype.val h))
  have hodd : Odd (Nat.card A) := hc ▸ ho.pow
  let r := (pointQuotient (F := F)).comp k
  have hr : IsPGroup 2 r.ker := by
    change IsPGroup 2 ((pointQuotient (F := F)).ker.comap k)
    rw [pointQuotient_ker]
    exact (IsElementaryAbelian.isPGroup 2 (pointRadical (F := F))).comap_of_injective k hk
  exact not_injective_sl2 hF ho hc r (injective_of_odd_two_kernel r hodd hr)
end SymplecticModel

open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
open scoped MatrixGroups

private theorem sylow_card_congr {A B : Type*} [Group A] [Group B]
    [Finite A] [Finite B] (e : A ≃* B) (P : Sylow 2 A) (Q : Sylow 2 B) :
    Nat.card P = Nat.card Q := by
  let R := P.mapSurjective (f := e.toMonoidHom) e.surjective
  exact (Nat.card_congr ((P : Subgroup A).equivMapOfInjective e.toMonoidHom e.injective).toEquiv).trans
    (Nat.card_congr (Sylow.equiv R Q).toEquiv)

private theorem g2_not_sl3 {F K : Type*} [Field F] [Finite F] [CharP F 2]
    [Field K] [Finite K] [CharP K 2] {n : ℕ} (hn : 0 < n)
    (hF : Nat.card F = 2^n) (hK : Nat.card K = 2^n)
    (e : Atlas.G2.Model F ≃* SL(3,K)) : False := by
  have hc := sylow_card_congr e Atlas.G2.LieParabolicSetup.sylow
    (Matrix.PSL3.CartanActions.BorelQuotient.unipotentSLSylow K hn hK)
  change Nat.card (Atlas.G2.unipotent (K := F)) =
    Nat.card (Matrix.PSL3.LinearThree.unipotentSL K) at hc
  rw [Atlas.G2.card_unipotent, Matrix.PSL3.LinearThree.card_unipotentSL, hF, hK,
    ← pow_mul, ← pow_mul] at hc
  have he := (Nat.pow_right_injective (by decide : 1 < 2)) hc
  omega

private theorem g2_not_sp4_four {F K : Type*} [Field F] [Finite F] [CharP F 2]
    [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hF : Nat.card F = 2^n) (hK : Nat.card K = 4)
    (e : Atlas.G2.Model F ≃* Matrix.symplecticGroup (Fin 2) K) : False := by
  have hk : Nat.card K = 2^2 := by omega
  have hc := sylow_card_congr e Atlas.G2.LieParabolicSetup.sylow
    (Theory.SpecificGroups.SymplecticFour.unipotentSylow hk (by decide))
  change Nat.card (Atlas.G2.unipotent (K := F)) =
    Nat.card (Theory.SpecificGroups.SymplecticFour.unipotent (F := K)) at hc
  rw [Atlas.G2.card_unipotent, Theory.SpecificGroups.SymplecticFour.card_unipotent,
    hF, hk, ← pow_mul, ← pow_mul] at hc
  have he := (Nat.pow_right_injective (by decide : 1 < 2)) hc
  omega

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

/-- Neither actual block quotient can carry a G₂ marking of the same source field. -/
theorem no_g2_block_marking
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier)))
    (hb : CFSG.Quasithin.ChapterC.IsSL3EvenBlock L S.field.degree ∨
      CFSG.Quasithin.ChapterC.IsSp4FourBlock L) : False := by
  rcases hb with hb | hb
  · obtain ⟨_, _, F, inst, fin, hF, hmodel⟩ := hb
    let : Field F := inst
    let : Finite F := fin
    let : Fintype F := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := S.field.degree)
      (by simpa only [Nat.card_eq_fintype_card] using hF)
    exact g2_not_sl3 S.field.degree_pos S.field.card_eq hF
      (m.groupEquiv.symm.trans hmodel.quotient_iso.some)
  · obtain ⟨_, F, inst, fin, hF, ρ, ⟨model⟩, _⟩ := hb
    let : Field F := inst
    let : Finite F := fin
    let : Fintype F := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2)
      (by simpa only [Nat.card_eq_fintype_card, show (2:ℕ)^2 = 4 from rfl] using hF)
    exact g2_not_sp4_four S.field.card_eq hF
      (m.groupEquiv.symm.trans model.quotientIso)

private def cartanModelMap {F : BinaryField} (c : Coordinates D F)
    {X : Subgroup G} (hX : IsCartan T L X) : X →* c.ModelGroup :=
  c.quotientMap.comp (inclusion (hX.1.trans inf_le_left))

private theorem cartanModelMap_injective {F : BinaryField} (c : Coordinates D F)
    {X : Subgroup G} (hX : IsCartan T L X) :
    Function.Injective (cartanModelMap D c hX) := by
  apply injective_of_odd_two_kernel _ hX.odd
  have he : (cartanModelMap D c hX).ker =
      (pCore 2 L).comap (inclusion (hX.1.trans inf_le_left)) := by
    ext x
    change c.groupEquiv (QuotientGroup.mk' (pCore 2 L)
      (inclusion (hX.1.trans inf_le_left) x)) = 1 ↔ _
    rw [map_eq_one_iff _ c.groupEquiv.injective]
    exact QuotientGroup.eq_one_iff _
  rw [he]
  exact pCore_isPGroup.comap_of_injective _ (inclusion_injective _)

private theorem cartan_projection_fixed {F : BinaryField} (c : Coordinates D F)
    {X : Subgroup G} (hX : IsCartan T L X) (v : V)
    (hv : (v : G) ∈ centralizer (X : Set G)) (x : X) :
    c.modelAction (cartanModelMap D c hX x) (c.projection v).toAdd =
      (c.projection v).toAdd := by
  let l : L := inclusion (hX.1.trans inf_le_left) x
  have he : V.normalizerMonoidHom (inclusion D.normalizes l) v = v := by
    apply Subtype.ext
    change (x : G) * (v : G) * (x : G)⁻¹ = v
    rw [hv x x.property, mul_inv_cancel_right]
  exact (c.projection_component_conjugation l v).symm.trans
    (congrArg (fun w : V => (c.projection w).toAdd) he)

private theorem field_large : 2 < Nat.card S.field.Carrier := by
  rw [S.field.card_eq]
  exact lt_of_le_of_lt (by decide : 2 ≤ 2^1)
    ((Nat.pow_lt_pow_right (by decide : 1 < 2)) S.nonbinary)

private theorem field_predecessor_odd : Odd (Nat.card S.field.Carrier - 1) := by
  rw [S.field.card_eq]
  exact Nat.Even.sub_odd (Nat.one_le_pow _ _ (by decide))
    (even_two.pow_of_ne_zero (Nat.ne_of_gt S.field.degree_pos)) odd_one

/-- The original SL₃ quotient has no nonzero Cartan-fixed vector. -/
theorem sl3_cartan_fixed_le
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    {X : Subgroup G} (hX : IsCartan T L X) :
    V ⊓ centralizer (X : Set G) ≤ centralizer (L : Set G) := by
  rintro v ⟨hv,hc⟩
  let w : V := ⟨v,hv⟩
  let c := Coordinates.sl3 m
  apply (c.projection_eq_one_iff w).mp
  apply Multiplicative.toAdd.injective
  exact LinearModel.sl3_fixed_eq_zero (field_large D S) (field_predecessor_odd D S)
    (by rw [c.cartan_card hX, S.field.card_eq]) (cartanModelMap D c hX)
    (cartanModelMap_injective D c hX) _ (cartan_projection_fixed D c hX w hc)

/-- The Cartan fixes only the original central kernel, also for nonsplit Sp₄ covers. -/
theorem sp4_cartan_fixed_le
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))
    {X : Subgroup G} (hX : IsCartan T L X) :
    V ⊓ centralizer (X : Set G) ≤ centralizer (L : Set G) := by
  rintro v ⟨hv,hc⟩
  let w : V := ⟨v,hv⟩
  let c := Coordinates.sp4 m
  apply (c.projection_eq_one_iff w).mp
  apply Multiplicative.toAdd.injective
  exact SymplecticModel.sp4_fixed_eq_zero (field_large D S) (field_predecessor_odd D S)
    (by rw [c.cartan_card hX, S.field.card_eq]) (cartanModelMap D c hX)
    (cartanModelMap_injective D c hX) _ (cartan_projection_fixed D c hX w hc)

/-- Every source Cartan has the required fixed-space bound in the two block rows. -/
theorem block_cartan_fixed_le
    (c : Coordinates D S.field)
    (hb : CFSG.Quasithin.ChapterC.IsSL3EvenBlock L S.field.degree ∨
      CFSG.Quasithin.ChapterC.IsSp4FourBlock L)
    {X : Subgroup G} (hX : IsCartan T L X) :
    V ⊓ centralizer (X : Set G) ≤ centralizer (L : Set G) := by
  cases c with
  | sl3 m => exact sl3_cartan_fixed_le D S m hX
  | sp4 m => exact sp4_cartan_fixed_le D S m hX
  | g2 m => exact (no_g2_block_marking D S m hb).elim


end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointCohomology.PointGeometry
