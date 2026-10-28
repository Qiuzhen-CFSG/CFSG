module
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.SylowTwoStep
public import Theory.SpecificGroups.SL2.SylowPointFixer

/-!
# Sylow squares in a centerless natural block

The square of a Sylow element lies in the elementary natural two-core.
If its quotient image is nonidentity, the square is fixed by that image,
hence by the entire SL₂ Sylow because their natural fixed lines agree.
If the image is identity, elementary abelianness makes the square trivial.
Thus all Sylow squares are central, and the commutator subgroup consists
of central involutions. This holds over every even field without a cubic
torus or a splitting assumption.

Source: Aschbacher–Smith 10.2.3(4), printed p.747, the common Sylow step.
-/

public section
open Subgroup Theory.GroupTheory Matrix
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.ChapterC
variable {L : Type*} [Group L] [Finite L]

/-- Every Sylow square is central in a centerless block with full natural core. -/
theorem IsL2EvenBlock.sylow_square_mem_center {n : ℕ} (hL : IsL2EvenBlock L n)
    (hcore : pCore 2 L = blockU L) (hz : center L = ⊥)
    (P : Sylow 2 L) (x : P) : x ^ 2 ∈ center P := by
  have helem : IsElementaryAbelian 2 (blockU L) := hL.2.1.elementary
  let := helem
  obtain ⟨_,_,F,_,_,hF,_,ρ,⟨m⟩,hρ⟩ := hL
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let q : L →* SL(2,F) := m.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := m.quotientIso.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 L := by
    ext y
    exact m.quotientIso.map_eq_one_iff.trans (QuotientGroup.eq_one_iff _)
  let Q := P.mapSurjective hq
  have hQtwo (y : Q) : y ^ 2 = 1 := by
    let a := Matrix.SpecialLinearGroup.sylowEquivAdditive F 2 Q
    apply a.symm.injective
    rw [map_pow,map_one]
    apply Multiplicative.toAdd.injective
    change (2 : ℕ) • (a.symm y).toAdd = 0
    rw [two_nsmul]
    exact CharTwo.add_self_eq_zero _
  have hxcore : (x : L) ^ 2 ∈ pCore 2 L := by
    rw [←hk,MonoidHom.mem_ker,map_pow]
    exact congrArg Subtype.val (hQtwo ⟨q x,mem_map_of_mem q x.property⟩)
  by_cases hqx : q x = 1
  · have hxU : (x : L) ∈ blockU L := hcore ▸ (hk ▸ hqx)
    have hs : x ^ 2 = 1 := Subtype.ext (elemPow_eq_one_of_isElementaryAbelian _ hxU)
    rw [hs]
    exact one_mem _
  let u : blockU L := ⟨(x : L) ^ 2,hcore ▸ hxcore⟩
  let v := m.moduleIso (QuotientGroup.mk' (blockFixed L) u)
  have hinj : Function.Injective (QuotientGroup.mk' (blockFixed L)) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rw [QuotientGroup.ker_mk']
    change (center L).subgroupOf (blockU L) = ⊥
    rw [hz,bot_subgroupOf]
  have hv : q x • v.toAdd = v.toAdd := by
    have he := congrArg Multiplicative.toAdd (m.intertwining x u)
    have hconj : blockConjugate L x u = u := by
      apply Subtype.ext
      change (x : L) * (x : L)^2 * (x : L)⁻¹ = (x : L)^2
      group
    rw [hconj,hρ] at he
    exact he.symm
  have hfix := Matrix.SpecialLinearGroup.sylow_fixed_of_nonidentity_fixed Q (q x)
    (mem_map_of_mem q x.property) hqx v.toAdd hv
  apply mem_center_iff.mpr
  intro y
  have he := congrArg Multiplicative.toAdd (m.intertwining y u)
  rw [hρ] at he
  have hvy : (q y).val *ᵥ v.toAdd = v.toAdd := hfix (q y) (mem_map_of_mem q y.property)
  have hcu : blockConjugate L y u = u := hinj (m.moduleIso.injective
    (Multiplicative.toAdd.injective (he.trans hvy)))
  apply Subtype.ext
  have hh := congrArg Subtype.val hcu
  change (y : L) * (x : L)^2 * (y : L)⁻¹ = (x : L)^2 at hh
  exact mul_inv_eq_iff_eq_mul.mp hh

/-- Central involutory Sylow commutators, over an arbitrary even field. -/
theorem IsL2EvenBlock.sylow_commutator_le_omegaCenterIn_of_center_eq_bot {n : ℕ} (hL : IsL2EvenBlock L n)
    (hcore : pCore 2 L = blockU L) (hz : center L = ⊥) (P : Sylow 2 L) :
    ⁅(P : Subgroup L),(P : Subgroup L)⁆ ≤ omegaCenterIn (P : Subgroup L) := by
  have hpow (x : P ⧸ center P) : x ^ 2 = 1 := by
    obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective (center P) x
    rw [←map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr (hL.sylow_square_mem_center hcore hz P y)
  have hq : IsMulCommutative (P ⧸ center P) := IsMulCommutative.of_comm (fun x y =>
    (Commute.of_orderOf_dvd_two (fun z => orderOf_dvd_of_pow_eq_one (hpow z)) x y).eq)
  have hc : commutator P ≤ center P :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mp hq
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

/-- The same bound on the literal Sylow subgroup in its ambient group. -/
theorem IsL2EvenBlock.ambient_sylow_commutator_le_omegaCenterIn_of_center_eq_bot {G : Type*} [Group G] [Finite G]
    (K P : Subgroup G) {n : ℕ} (hK : IsL2EvenBlock K n)
    (hcore : pCore 2 K = blockU K) (hz : center K = ⊥)
    (hP : Chapter1.IsSylowIn 2 P K) : ⁅P,P⁆ ≤ omegaCenterIn P := by
  obtain ⟨Q,hQ⟩ := hP
  have hh := hK.sylow_commutator_le_omegaCenterIn_of_center_eq_bot hcore hz Q
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
