module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.BinaryInspection.Kernel
public import Theory.SpecificGroups.Triality.ParabolicGeometry
public import Theory.SpecificGroups.Triality.LeviIdentification
public import Theory.SpecificGroups.Triality.RadicalCoordinates.Centers
public import BenderSuzuki.External.Huppert.II.theorem_6_14

/-!
# Excluding the genuine binary triality component

The residual condition in 15.3.43(a) makes the order of every three-subgroup
of M ∩ I divide three. The supplied central Sylow involution gives a direct
centralizer obstruction to the triality alternative in the binary paragraph.

The component is centerless by the existing binary kernel calculation.
Its representative for the inner involution has square one and centralizes
the component Sylow subgroup, so it lies in that Sylow's center. Sylow
conjugacy on the genuine descended carrier puts this representative in the
highest-root subgroup. The actual arms Levi, isomorphic to PSL₂(8), centralizes
that root subgroup. It therefore centralizes the original source involution
and embeds in M ∩ I. Its order 504 has a factor nine, contradicting the source
residual index three.

Only a Levi containment is asserted: no full parabolic or local subgroup is
identified with its prime-to-two residual. This route uses the supplied
source involution to avoid an automorphism-extension or maximal-parabolic
classification. It needs no independent simplicity theorem for the model.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
15.3.43(a) and the n = 1 paragraph, printed pp.1139--1140;
1.1.5(3)(a), pp.501--502; A.2.3--4, p.33; and the triality root structure
in F.1.12(I)(4), pp.263--264 (`refs/quasithin.pdf`).
-/

public section

open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels.BinaryInspection.ExceptionalInspection

variable {G : Type*} [Group G] [Finite G]
variable {Yplus S M I L V₁ V₂ : Subgroup G}
variable (c : ReducedConfiguration Yplus S M I L V₁ V₂)

include c in
/-- The source index bounds orders of three-subgroups, including cyclic ones. -/
private theorem three_subgroup_card_dvd_three (A : Subgroup G)
    (hA : IsPGroup 3 A) (hAM : A ≤ M ⊓ I) : Nat.card A ∣ 3 := by
  have hAY : A ≤ Yplus := by
    intro x hx
    obtain ⟨n, hn⟩ := hA (⟨x, hx⟩ : A)
    rw [c.residual]
    exact mem_map.mpr ⟨⟨x, hAM hx⟩,
      mem_primePowerGenerated_of_pow (Subtype.ext (congrArg (fun a : A => (a : G)) hn)), rfl⟩
  have hd : Nat.card A ∣ Nat.card Yplus :=
    card_dvd_of_injective (inclusion hAY) (inclusion_injective hAY)
  obtain ⟨k, hk⟩ := (pCore_isPGroup (p := 2) (G := Yplus)).exists_card_eq
  have hc : Nat.card Yplus = 2 ^ k * 3 := by
    rw [← (pCore 2 Yplus).card_mul_index, hk, c.index]
  rw [hc] at hd
  obtain ⟨j, hj⟩ := hA.exists_card_eq
  have hcop : Nat.Coprime (Nat.card A) (2 ^ k) := by
    rw [hj]
    exact ((by decide : Nat.Coprime 3 2).pow_left j).pow_right k
  exact hcop.dvd_mul_left.mp hd

include c in
private theorem no_nine_divisor {K : Type*} [Group K] [Finite K]
    (f : K →* G) (hf : Function.Injective f) (hM : f.range ≤ M ⊓ I)
    (h9 : 9 ∣ Nat.card K) : False := by
  let P : Sylow 3 K := default
  have hd : 9 ∣ Nat.card P := P.pow_dvd_card_of_pow_dvd_card (n := 2) h9
  have hc := three_subgroup_card_dvd_three c ((P : Subgroup K).map f)
    (P.isPGroup'.map f) ((map_le_range _ _).trans hM)
  rw [Subgroup.card_map_of_injective hf] at hc
  exact (by decide : ¬ 9 ∣ 3) (hd.trans hc)

private theorem mem_sylow_of_square_of_centralizes {K : Type*} [Group K]
    (T : Sylow 2 K) (l : K) (hl : l ^ 2 = 1)
    (hc : l ∈ centralizer (T : Set K)) : l ∈ T := by
  have hcyc : IsPGroup 2 (zpowers l) := by
    apply IsPGroup.of_card_dvd_pow (n := 1)
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_dvd_of_pow_eq_one hl
  have hn : zpowers l ≤ normalizer (T : Set K) :=
    (zpowers_le.mpr hc).trans (Subgroup.centralizer_le_normalizer _)
  have he := T.is_maximal' (T.isPGroup'.to_sup_of_normal_left' hcyc hn) le_sup_left
  exact he.le (Subgroup.mem_sup_right (mem_zpowers l))

omit [Finite G] in
include c in
private theorem inner_representative (hZ : center L = ⊥) {z : G}
    (hz : SourceInvolution S M z) (hi : ActsInner L z)
    (T : Sylow 2 L) (hT : (T : Subgroup L).map L.subtype = S ⊓ L) :
    ∃ l : L, l ∈ T ∧ l ∈ centralizer (T : Set L) ∧
      ∀ x : L, z * (x : G) * z⁻¹ = (l : G) * (x : G) * (l : G)⁻¹ := by
  obtain ⟨l, hl⟩ := hi
  have hSI : S ≤ I := (sylow_le_local c).trans inf_le_right
  let zn : normalizer (L : Set G) := ⟨z, c.normalizes (hSI hz.mem)⟩
  have he : L.normalizerMonoidHom zn = MulAut.conj l := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    exact hl x
  have hzn : zn ^ 2 = 1 := by
    apply Subtype.ext
    exact hz.order ▸ pow_orderOf_eq_one z
  have hp : MulAut.conj (l ^ 2) = 1 := by
    rw [map_pow, ← he, ← map_pow, hzn, map_one]
  have hc : l ^ 2 ∈ center L := by
    apply mem_center_iff.mpr
    intro x
    have hh := DFunLike.congr_fun hp x
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  have hl2 : l ^ 2 = 1 := hZ.le hc
  have hcl : l ∈ centralizer (T : Set L) := by
    intro x hx
    have hxs : (x : G) ∈ S := (hT.le (mem_map_of_mem L.subtype hx)).1
    have hh := hl x
    have hzx : z * (x : G) * z⁻¹ = (x : G) := by
      rw [← hz.central x hxs, mul_inv_cancel_right]
    rw [hzx] at hh
    exact Subtype.ext (mul_inv_eq_iff_eq_mul.mp hh.symm).symm
  exact ⟨l, mem_sylow_of_square_of_centralizes T l hl2 hcl, hcl, hl⟩

open Triality.Standard Triality.Standard.Parabolics
open Triality.Standard.RadicalCoordinates.Centers

include c in
/-- The genuine arms Levi embeds in the source local group through the
centralizer of the supplied involution. -/
private theorem source_arms_embedding (hZ : center L = ⊥) {z : G}
    (hz : SourceInvolution S M z) (hi : ActsInner L z)
    (P : Parameters) (hp : P.prime = 2) (e : L ≃* Carrier P) :
    ∃ f : levi P .arms →* G, Function.Injective f ∧ f.range ≤ M ⊓ I := by
  obtain ⟨T, hT⟩ := component_sylow c
  obtain ⟨l, hlT, hlC, hl⟩ := inner_representative c hZ hz hi T hT
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Carrier P)
    (T.mapSurjective (f := e.toMonoidHom) e.surjective) (unipotentSylow P hp)
  let e' := e.trans (MulAut.conj g)
  have hTU : (T : Subgroup L).map e'.toMonoidHom = unipotent P := by
    change (T : Subgroup L).map ((MulAut.conj g).toMonoidHom.comp e.toMonoidHom) = _
    rw [← map_map]
    exact congrArg Sylow.toSubgroup hg
  have hlu : e' l ∈ unipotent P := hTU ▸ mem_map_of_mem e'.toMonoidHom hlT
  have hlcenter : (⟨e' l, hlu⟩ : unipotent P) ∈ center (unipotent P) := by
    apply mem_center_iff.mpr
    intro x
    obtain ⟨y, hy, he⟩ := hTU.ge x.property
    apply Subtype.ext
    change (x : Carrier P) * e' l = e' l * x
    rw [← he]
    exact (e'.map_mul y l).symm.trans ((congrArg e' (hlC y hy)).trans (e'.map_mul l y))
  have hlroot : e' l ∈ highestRoot P := by
    rw [← embedded_center_unipotent P hp]
    exact mem_map_of_mem (unipotent P).subtype hlcenter
  let f : levi P .arms →* G := L.subtype.comp
    (e'.symm.toMonoidHom.comp (levi P .arms).subtype)
  refine ⟨f, L.subtype_injective.comp (e'.symm.injective.comp (levi P .arms).subtype_injective), ?_⟩
  rintro _ ⟨x, rfl⟩
  refine ⟨hz.centralizer_le ?_, c.component_le (e'.symm x).property⟩
  apply mem_centralizer_singleton_iff.mpr
  have hcx : l * e'.symm x = e'.symm x * l := by
    apply e'.injective
    simpa only [map_mul, e'.apply_symm_apply] using
      levi_le_centralizer_highestRoot P hp x.property (e' l) hlroot
  symm
  apply mul_inv_eq_iff_eq_mul.mp
  change z * ((e'.symm x : L) : G) * z⁻¹ = _
  rw [hl, ← Subgroup.coe_mul, hcx, Subgroup.coe_mul, mul_inv_cancel_right]
  rfl

private theorem arms_card (P : Parameters) (hp : P.prime = 2) (hq : P.q = 2) :
    Nat.card (levi P .arms) = 504 := by
  let : CharP (ExtensionField P) 2 := hp ▸ inferInstanceAs (CharP (ExtensionField P) P.prime)
  rw [Nat.card_congr (leviArmsEquivPSL2 P hp).toEquiv,
    ← Nat.card_congr (Theory.PSL2.sl2QuotientEquiv (ExtensionField P)).toEquiv,
    BenderSuzuki.External.huppert614_card_specialLinearGroup,
    card_extensionField, hq]
  norm_num

include c in
/-- The binary triality alternative is incompatible with the reduced source
configuration and the specified inner involution. -/
theorem not_triality {z : G} (hz : SourceInvolution S M z) (hs : IsSimpleGroup L)
    (hi : ActsInner L z) (iso : IsTrialityGroupAt 2 L) : False := by
  have hm : Model L z 1 := .simple hs (.rankTwo (.triality (by decide) (by simpa using iso))) hi
  have hZ := binary_center_eq_bot c hm
  obtain ⟨P, hq, ⟨e⟩⟩ := iso
  have hp : P.prime = 2 := by
    apply (Nat.prime_dvd_prime_iff_eq P.prime_prime Nat.prime_two).mp
    rw [← hq]
    exact dvd_pow_self P.prime (Nat.ne_of_gt P.exponent_pos)
  obtain ⟨f, hf, hM⟩ := source_arms_embedding c hZ hz hi P hp e
  exact no_nine_divisor c f hf hM (by rw [arms_card P hp hq]; decide)

end CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels.BinaryInspection.ExceptionalInspection
