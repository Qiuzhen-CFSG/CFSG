module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryCartan
public import Theory.SpecificGroups.PSL3.UniversalProjection
public import Theory.SpecificGroups.SL3.CenterProjectiveComparison
public import Theory.SpecificGroups.PSU3.UniversalCover.EvenKernelBound.TwoPrimary
public import CFSG.Quasithin.ChapterI.Section01.LieMultipliers.PSL2
public import CFSG.Quasithin.ChapterI.Section01.LieMultipliers.Suzuki
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.Even
public import Theory.GroupTheory.CoveringKernelCard
public import Theory.GroupTheory.SylowCoprimeEquivalence
public import Theory.GroupTheory.CharacteristicNormalizerRestriction
public import Theory.GroupTheory.GeneralizedFitting.ComponentLocalClosure.Sylow

open Subgroup Theory.GroupTheory PerfectCentralCovering
open scoped MatrixGroups
/-!
# Lifting the classical component Sylow into the original core

The nonexceptional multiplier calculations give odd center in each surviving
Bender or classical component, with the original field parameters. The literal
map K → K/Z(K) is therefore injective on the original component Sylow.
Centralization by the projected moving sixteen lifts along the marked inner
action, so that Sylow centralizes both the paired plane and its supplement.
It consequently lies in Q=C_T(W). Component-orbit Sylow conjugacy then makes
Q Sylow in KQ, including when Q permutes components.

The actual chosen-module application and characteristic-normalizer control
are in NonFFSourceDoubledBinaryCoverPlacement. Exceptional Lie rows and the
local C(G,Q) containment argument remain with qt-d-1222-nonff-doubled.
Source: Aschbacher–Smith, proof of 7.7.6, printed p.706, refs/quasithin.pdf;
the multiplier inputs are I.1.3, printed p.407.
-/
public noncomputable section
namespace CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryCoverPlacement
universe u v w
private theorem odd_center_of_cover {K : Type u} {S : Type v} {C : Type w}
    [Group K] [Finite K] [IsQuasisimple K]
    [Group S] [Finite S] [IsQuasisimple S]
    [Group C] [Finite C] [IsQuasisimple C]
    (e : K ⧸ center K ≃* S) (c : Covering C S)
    (hc : Covering.IsUniversal.{v,w,u} c) (ho : Odd (Nat.card c.toMonoidHom.ker)) :
    Odd (Nat.card (center K)) := by
  let f : Covering K S := (centralQuotientCover e).toCovering
  have hd := kernel_card_dvd_of_surjective_factor c.toMonoidHom f.toMonoidHom
    (hc.lift f).toMonoidHom (hc.lift f).surjective
    (congrArg Covering.toMonoidHom (hc.lift_fac f))
  have hh := Odd.of_dvd_nat ho hd
  change Odd (Nat.card (centralQuotientCover e).toMonoidHom.ker) at hh
  simpa only [centralQuotientCover_ker] using hh

/-- The original central quotient in each surviving classical or Bender row
has odd covering kernel, at its original field parameter. -/
theorem linearTwo_odd_center {K : Type*} [Group K] [Finite K] [IsQuasisimple K]
    {n : ℕ} (hn : 4 ≤ n) (hm : ClassicalGroup.IsPSL (K ⧸ center K) 2 (2^n)) :
    Odd (Nat.card (center K)) := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  have hbig : 8 ≤ Nat.card F := by
    rw [hF]
    exact (by decide : 8 ≤ 2^4).trans (Nat.pow_le_pow_right (by decide) hn)
  let : Fact (3 < Nat.card F) := ⟨by omega⟩
  have heven : Even (Nat.card F) := by
    rw [hF]
    exact even_iff_two_dvd.mpr (dvd_pow_self 2 (by omega))
  apply odd_center_of_cover e (Covering.id : Covering PSL(2,F) PSL(2,F))
    (GorensteinWalter.PSL2Cover.identity_isUniversal_of_even F heven hbig)
  simp only [Covering.id_toMonoidHom,MonoidHom.ker_id,card_bot]
  decide

theorem linearThree_odd_center {K : Type*} [Group K] [Finite K] [IsQuasisimple K]
    {n : ℕ} (hn : 4 ≤ n) (hm : ClassicalGroup.IsPSL (K ⧸ center K) 3 (2^n)) :
    Odd (Nat.card (center K)) := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  have hbig : 16 ≤ Nat.card F := by
    rw [hF]
    exact Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hn
  apply odd_center_of_cover e (Matrix.PSL3.projectionCovering F)
    (Matrix.PSL3.UniversalProjection.projection_isUniversal (by omega) (by omega))
  change Odd (Nat.card (Matrix.PSL3.projection F).ker)
  rw [Matrix.PSL3.projection_ker]
  exact Matrix.SL3.odd_card_center F

theorem unitary_odd_center {K : Type*} [Group K] [Finite K] [IsQuasisimple K]
    {n : ℕ} (hn : 2 ≤ n) (hm : ClassicalGroup.IsPSU (K ⧸ center K) 3 (2^n)) :
    Odd (Nat.card (center K)) := by
  obtain ⟨F,_,_,J,hF,hconj,⟨e⟩⟩ := hm
  apply Nat.not_even_iff_odd.mp
  rw [even_iff_two_dvd]
  simpa only [centralQuotientCover_ker] using
    BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover.EvenKernelBound.not_two_dvd_cover_kernel
      J hn hF hconj (centralQuotientCover e)

theorem symplectic_odd_center {K : Type*} [Group K] [Finite K] [IsQuasisimple K]
    {n : ℕ} (hn : 2 ≤ n) (hm : ClassicalGroup.IsPSp (K ⧸ center K) 2 (2^n)) :
    Odd (Nat.card (center K)) := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  let e' := e.trans Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.symm
  have hz := center_eq_bot_of_centralQuotientEquiv
    (Theory.SpecificGroups.SymplecticFour.CentralCovers.Even.universalProjection_ker_eq_bot_of_card_pow
      hF (by omega)) e'
  rw [hz,card_bot]
  decide

theorem suzuki_odd_center {K : Type*} [Group K] [Finite K] [IsQuasisimple K]
    {m : ℕ} (hm : 2 ≤ m)
    (he : Nonempty ((K ⧸ center K) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)) :
    Odd (Nat.card (center K)) := by
  let : Fact (0 < m) := ⟨by omega⟩
  apply odd_center_of_cover he.some (Covering.id : Covering
    (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m))
    (ChapterI.LieMultipliers.Suzuki.ordinary_identity_isUniversal m hm)
  simp only [Covering.id_toMonoidHom,MonoidHom.ker_id,card_bot]
  decide
end CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryCoverPlacement

namespace CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryCoverPlacement
private theorem inner_conj {K : Type*} [Group K] (k : K) :
    innerEquivCentralQuotient ((MulAut.conj : K →* MulAut K).rangeRestrict k) =
      (QuotientGroup.mk' (center K)) k := by
  change QuotientGroup.quotientMulEquivOfEq DoubleCoverCentralizer.conj_kernel
    ((QuotientGroup.quotientKerEquivRange (MulAut.conj : K →* MulAut K)).symm
      (MulAut.conj.rangeRestrict k)) = _
  have he : (QuotientGroup.quotientKerEquivRange (MulAut.conj : K →* MulAut K)).symm
      (MulAut.conj.rangeRestrict k) = QuotientGroup.mk k := by
    apply (QuotientGroup.quotientKerEquivRange (MulAut.conj : K →* MulAut K)).injective
    rw [MulEquiv.apply_symm_apply]
    rfl
  rw [he]
  rfl

/-- Centralization lifts on the original component Sylow through the literal
inner-action map, because the central quotient has odd kernel. -/
theorem centralizes_original_sylow
    {G : Type*} [Group G] [Finite G] (K A : Subgroup G)
    (ho : Odd (Nat.card (center K))) (hAN : A ≤ normalizer (K : Set G))
    (j : A →* K ⧸ center K)
    (hact : ∀ a : A, (innerEquivCentralQuotient.symm (j a) : MulAut K) =
      K.normalizerMonoidHom (inclusion hAN a))
    (P : Sylow 2 K)
    (hc : let Q := P.mapSurjective (QuotientGroup.mk'_surjective (center K))
      j.range ≤ (center Q).map (Q : Subgroup _).subtype) :
    (P : Subgroup K).map K.subtype ≤ centralizer (A : Set G) := by
  let q := QuotientGroup.mk' (center K)
  let Q := P.mapSurjective (QuotientGroup.mk'_surjective (center K))
  have hinj : Function.Injective (q.comp (P : Subgroup K).subtype) :=
    injective_comp_subtype_of_coprime_ker q
      (by simpa only [q,QuotientGroup.ker_mk'] using ho.coprime_two_left)
      (P : Subgroup K) P.isPGroup'
  rintro _ ⟨p,hp,rfl⟩ a ha
  let a₀ : A := ⟨a,ha⟩
  obtain ⟨z,hz,hzj⟩ := hc (show j a₀ ∈ j.range from ⟨a₀,rfl⟩)
  obtain ⟨k,hk,hkz⟩ := z.property
  have hkq : q k = j a₀ := hkz.trans hzj
  have hkp : p * k = k * p := by
    have hh := congrArg Subtype.val (mem_center_iff.mp hz
      (⟨q p,mem_map_of_mem q hp⟩ : Q))
    change q p * (z : K ⧸ center K) = (z : K ⧸ center K) * q p at hh
    rw [←hkz,←map_mul,←map_mul] at hh
    exact congrArg Subtype.val (hinj (a₁ := ⟨p*k,P.mul_mem hp hk⟩)
      (a₂ := ⟨k*p,P.mul_mem hk hp⟩) hh)
  have he : (innerEquivCentralQuotient.symm (q k) : MulAut K) = MulAut.conj k := by
    rw [←inner_conj k, MulEquiv.symm_apply_apply]
    rfl
  have hf : K.normalizerMonoidHom (inclusion hAN a₀) p = p := by
    rw [←hact a₀,←hkq,he]
    change k*p*k⁻¹ = p
    rw [←hkp,mul_inv_cancel_right]
  have hh := congrArg Subtype.val hf
  change a * (p : G) * a⁻¹ = (p : G) at hh
  exact mul_inv_eq_iff_eq_mul.mp hh

/-- Once the original orbit is the paired plane times its moving sixteen,
the original component Sylow is contained in the original core C_T(W). -/
theorem original_sylow_le_core
    {G : Type*} [Group G] [Finite G] (K A U W T Q : Subgroup G)
    (hW : U ⊔ A = W) (hQ : T ⊓ centralizer (W : Set G) = Q)
    (hKC : K ≤ centralizer (U : Set G)) (P : Sylow 2 K)
    (hPT : (P : Subgroup K).map K.subtype ≤ T)
    (hPC : (P : Subgroup K).map K.subtype ≤ centralizer (A : Set G)) :
    (P : Subgroup K).map K.subtype ≤ Q := by
  rw [←hQ,←hW]
  refine le_inf hPT (le_centralizer_iff.mpr (sup_le ?_ (le_centralizer_iff.mp hPC)))
  exact le_centralizer_iff.mp ((map_subtype_le _).trans hKC)

/-- A full original component Sylow in Q makes Q Sylow in the component join,
even when Q permutes the components. -/
theorem core_sylow_join
    {G : Type*} [Group G] [Finite G] (H K Q : Subgroup G)
    (hK : IsComponentIn K H) (hQH : Q ≤ H) (hp : IsPGroup 2 Q)
    (P : Sylow 2 K) (hPQ : (P : Subgroup K).map K.subtype ≤ Q) :
    ∃ S : Sylow 2 (K ⊔ Q : Subgroup G),
      (S : Subgroup _).map (K ⊔ Q).subtype = Q := by
  let K₀ := K.subgroupOf H
  let Q₀ := Q.subgroupOf H
  let e : K ≃* K₀ := (subgroupOfEquivOfLe hK.1).symm
  let P₀ := P.mapSurjective (f := e.toMonoidHom) e.surjective
  have hP₀ : (P₀ : Subgroup K₀).map K₀.subtype ≤ Q₀ := by
    rintro _ ⟨x,⟨y,hy,rfl⟩,rfl⟩
    exact hPQ (mem_map_of_mem K.subtype hy)
  obtain ⟨S,hS⟩ := hK.2.exists_sylow_local_orbit_le (E := K₀) (D := Q₀) (T := Q₀)
    le_rfl inf_le_right le_rfl P₀ hP₀
  obtain ⟨R,hR⟩ := exists_sylow_join_eq_intersection (componentOrbit K₀ Q₀) Q₀ Q₀
    hp.comap_subtype le_rfl (le_normalizer_componentOrbit K₀ Q₀) S hS
  let f : (componentOrbit K₀ Q₀ ⊔ Q₀ : Subgroup H) ≃* (K ⊔ Q : Subgroup G) :=
    (MulEquiv.subgroupCongr (componentOrbit_sup K₀ Q₀)).trans
      ((MulEquiv.subgroupCongr (subgroupOf_sup hK.1 hQH).symm).trans
        (subgroupOfEquivOfLe (sup_le hK.1 hQH)))
  refine ⟨R.mapSurjective (f := f.toMonoidHom) f.surjective,?_⟩
  change ((R : Subgroup (componentOrbit K₀ Q₀ ⊔ Q₀ : Subgroup H)).map f.toMonoidHom).map
    (K ⊔ Q).subtype = Q
  rw [hR]
  ext x
  constructor
  · rintro ⟨a,⟨b,hb,rfl⟩,rfl⟩
    exact hb
  · intro hx
    exact ⟨⟨x,mem_sup_right hx⟩,⟨⟨⟨x,hQH hx⟩,mem_sup_right hx⟩,hx,rfl⟩,rfl⟩
end CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryCoverPlacement
