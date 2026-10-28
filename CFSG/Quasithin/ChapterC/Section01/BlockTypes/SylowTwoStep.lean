module
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.OddFixedPoints
public import Theory.GroupAction.CubicNormalizerClassTwo
public import Theory.SpecificGroups.SL2.SylowConsequences
public import Theory.GroupTheory.PGroup.OmegaCenterIn
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents
/-!
# Central elementary commutators in a natural-block Sylow subgroup

The defining-characteristic Sylow of the SL₂ quotient is abelian, so the
Sylow commutator lies in the two-core. When the core equals the elementary
U-module and a cubic torus acts on a centerless block, odd fixed-point
control and Neumann's theorem make that commutator central and involutory.
This is the weaker Sylow geometry needed for the second-block recovery;
no special-group or split affine recognition is assumed.
Source: Aschbacher--Smith 10.2.3(4), printed p.747.
-/
public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC
variable {L : Type*} [Group L] [Finite L]
open scoped MatrixGroups

theorem IsL2EvenBlock.sylow_commutator_le_core {n : ℕ} (hL : IsL2EvenBlock L n)
    (P : Sylow 2 L) : ⁅(P : Subgroup L),(P : Subgroup L)⁆ ≤ pCore 2 L := by
  obtain ⟨_,_,F,_,_,hF,_,ρ,⟨m⟩,hρ⟩ := hL
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let q : L →* SL(2,F) := m.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := m.quotientIso.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker=pCore 2 L := by
    ext x
    exact m.quotientIso.map_eq_one_iff.trans (QuotientGroup.eq_one_iff _)
  let Q := P.mapSurjective hq
  let e := Matrix.SpecialLinearGroup.sylowEquivAdditive F 2 Q
  have hcomm : IsMulCommutative Q := IsMulCommutative.of_comm (fun x y => by
    apply e.symm.injective
    simp only [map_mul,mul_comm])
  have hbot : ⁅(P : Subgroup L).map q,(P : Subgroup L).map q⁆=⊥ := by
    exact commutator_self_eq_bot_iff.mpr hcomm
  rw [←hk]
  apply (Subgroup.map_eq_bot_iff _).mp
  rw [map_commutator]
  exact hbot

theorem IsL2EvenBlock.sylow_commutator_le_omegaCenterIn {n : ℕ}
    (hL : IsL2EvenBlock L n) (hcore : pCore 2 L = blockU L)
    (hz : center L = ⊥) (P : Sylow 2 L) (D : Subgroup L)
    (hD : Nat.card D=3) (hn : D ≤ normalizer (P : Set L)) :
    ⁅(P : Subgroup L),(P : Subgroup L)⁆ ≤ omegaCenterIn (P : Subgroup L) := by
  have hodd : Odd (Nat.card D) := hD ▸ (by decide : Odd 3)
  have hne : D ≠ ⊥ := by intro h; simp [h] at hD
  have hfixed : (P : Subgroup L) ⊓ centralizer (D : Set L)=⊥ :=
    bot_unique ((hL.sylow_odd_fixed_le_center hcore P D hodd hne).trans hz.le)
  have hc := commutator_le_center_of_cubic_normalizer (P : Subgroup L) D hD hn hfixed
  have hU := hL.sylow_commutator_le_core P
  let : IsElementaryAbelian 2 (blockU L) := hL.2.1.elementary
  have hmap : (commutator P).map (P : Subgroup L).subtype = ⁅(P : Subgroup L),(P : Subgroup L)⁆ := by
    rw [_root_.commutator_def,map_commutator,←MonoidHom.range_eq_map,range_subtype]
  intro x hx
  obtain ⟨y,hy,rfl⟩ := hmap.symm ▸ hx
  refine (mem_omegaCenterIn_iff _ _).mpr ⟨y.property,?_,?_⟩
  · intro z hz
    exact congrArg (P : Subgroup L).subtype (mem_center_iff.mp (hc hy) ⟨z,hz⟩)
  · exact elemPow_eq_one_of_isElementaryAbelian (y:L) (hcore ▸ hU (hmap ▸ mem_map_of_mem _ hy))

/-- The same Sylow geometry with the literal ambient Sylow and cubic subgroup. -/
theorem IsL2EvenBlock.ambient_sylow_commutator_le_omegaCenterIn
    {G : Type*} [Group G] [Finite G] (K P D : Subgroup G) {n : ℕ}
    (hK : IsL2EvenBlock K n) (hcore : pCore 2 K = blockU K) (hz : center K = ⊥)
    (hP : Chapter1.IsSylowIn 2 P K) (hDK : D ≤ K) (hD : Nat.card D=3)
    (hn : D ≤ normalizer (P : Set G)) : ⁅P,P⁆ ≤ omegaCenterIn P := by
  obtain ⟨Q,hQ⟩ := hP
  have hD' : Nat.card (D.subgroupOf K)=3 :=
    (Nat.card_congr (subgroupOfEquivOfLe hDK).toEquiv).trans hD
  have hn' : D.subgroupOf K ≤ normalizer (Q : Set K) := by
    apply le_normalizer_iff_commutator_le_right.mpr
    apply (map_le_map_iff_of_injective K.subtype_injective).mp
    rw [map_commutator,map_subgroupOf_eq_of_le hDK,hQ]
    exact le_normalizer_iff_commutator_le_right.mp hn
  have hh := hK.sylow_commutator_le_omegaCenterIn hcore hz Q (D.subgroupOf K) hD' hn'
  have hmap : (⁅(Q : Subgroup K),(Q : Subgroup K)⁆).map K.subtype=⁅P,P⁆ := by
    rw [map_commutator,hQ]
  intro x hx
  obtain ⟨y,hy,rfl⟩ := hmap.symm ▸ hx
  obtain ⟨hyQ,hyc,hy2⟩ := (mem_omegaCenterIn_iff _ _).mp (hh hy)
  refine (mem_omegaCenterIn_iff _ _).mpr ⟨hQ ▸ mem_map_of_mem K.subtype hyQ,?_,?_⟩
  · intro z hz
    obtain ⟨w,hw,rfl⟩ := hQ.symm ▸ hz
    exact congrArg K.subtype (hyc w hw)
  · exact congrArg K.subtype hy2
end CFSG.Quasithin.ChapterC
