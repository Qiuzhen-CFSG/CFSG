module
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.BenderPlacement.SmallAutomizer
public import Theory.SpecificGroups.Alternating.FiveBorelCentralFactor
-- Internal constructor extension: retain the chosen prime in the original
-- inverted-line construction without reopening the general witness API.
import all CFSG.Quasithin.ChapterE.Section02.Witnesses.Involution.Basic

/-!
# Odd-prime inversion in the original small-automizer source

A specified odd-prime element inverted by the order-two image of V gives
a dihedral source pair with that same prime. Lift the pair through the
actual maximal core and apply the original small quaternion-core theorem.
The lifted pair has order 192, forcing the chosen odd prime to be three.
This supplies the source restriction used to exclude model involutions
that invert a five-element (in particular the binary symplectic row).

Source: Aschbacher–Smith E.2.17, the odd-rotation claim on printed p.230.
This module is an internal extension of the inverted-line constructor in
Involution.Basic; the public conclusions retain the original quotient map.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.Witnesses.Involution
variable {H D : Type*} [Group H] [Finite H] [Group D] [Finite D]

theorem exists_pair_of_inverted_prime (T : Sylow 2 H) (M V : Subgroup H)
    [IsElementaryAbelian 2 V] (hVT : V ≤ T)
    (hcore : V ≤ (pCore 2 M).map M.subtype) (hcard : Nat.card V = 2)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (v r : H)
    (hv : v ∈ V) (hv1 : v ≠ 1) (hr : orderOf r = p) (hi : v*r*v⁻¹=r⁻¹) :
    ∃ w : QuotientLift.Pair T M V, ∃ a : ℕ, 0 < a ∧
      Nonempty ((w.subgroup ⧸ (M.subgroupOf w.subgroup).normalCore) ≃* DihedralGroup (p^a)) := by
  let : Fact p.Prime := ⟨hp⟩
  have hrM := rotation_not_mem_of_inverter_in_core M v r hp2 (hcore hv) hr hi
  have hd : Disjoint (zpowers r) M := (M.disjoint_zpowers_of_prime_order_not_mem r hr hrM).symm
  have hsign : ∀ w∈V,w*r*w⁻¹=r ∨ w*r*w⁻¹=r⁻¹ := by
    intro w hw
    by_cases h : w=1
    · left; simp only [h,one_mul,inv_one,mul_one]
    · have he : w=v := by
        obtain ⟨x,hx,hu⟩ := (Nat.card_eq_two_iff' (1:V)).mp hcard
        exact congrArg Subtype.val ((hu ⟨w,hw⟩ (fun he => h (congrArg Subtype.val he))).trans
          (hu ⟨v,hv⟩ (fun he => hv1 (congrArg Subtype.val he))).symm)
      exact Or.inr (he ▸ hi)
  obtain ⟨w⟩ := witness_of_inverted_line M V (hcore.trans (map_subtype_le _)) r v 1 hv
    (by decide) (by simpa only [pow_one] using hr) (hr ▸ hp.odd_of_ne_two hp2)
    (fun h => hp.ne_one (hr.symm.trans (h ▸ orderOf_one))) hi hsign hd
  have hTS : (T : Subgroup H).subgroupOf w.subgroup = w.sylow := by
    apply w.sylow.is_maximal' T.isPGroup'.comap_subtype
    intro x hx
    have hV : (x:H) ∈ (w.sylow : Subgroup w.subgroup).map w.subgroup.subtype :=
      mem_map_of_mem w.subgroup.subtype hx
    rw [w.sylow_eq] at hV
    exact hVT hV
  have hmap : (w.sylow : Subgroup w.subgroup).map w.subgroup.subtype =
      (T : Subgroup H) ⊓ w.subgroup := by
    rw [←hTS,subgroupOf_map_subtype]
  have htwo : IsPGroup 2 (M.subgroupOf w.subgroup).normalCore := by
    rw [w.maximal_eq]
    exact ((IsElementaryAbelian.isPGroup 2 V).comap_subtype).to_le (normalCore_le _)
  have hclosed : ∃ S : Sylow 2 (M.subgroupOf w.subgroup).normalCore,
      (S : Subgroup (M.subgroupOf w.subgroup).normalCore).Normal := by
    refine ⟨(htwo.to_subgroup ⊤).toSylow (by simp),?_⟩
    exact inferInstanceAs (⊤ : Subgroup (M.subgroupOf w.subgroup).normalCore).Normal
  exact ⟨⟨w.subgroup,w.le,w.conjugator,w.generate,w.sylow,hmap,hclosed⟩,
    w.exponent,w.positive,w.dihedral⟩

theorem source_prime_inverter_eq_three
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (V : Subgroup H) [IsElementaryAbelian 2 V] (hVT : V ≤ T)
    (hvn : (V.subgroupOf (T : Subgroup H)).Normal)
    (hcore : V ≤ (ChapterB.minimalParabolicMax T hP).pCoreIn 2)
    (hout : ¬ V ≤ ChapterB.minimalParabolicCore T hP)
    (hfit : generalizedFitting H = pCore 2 H) (hV : Nat.card V = 16)
    (U : Subgroup H) (hTU : (T : Subgroup H) ≤ U) (hU : U ≤ normalizer (V : Set H))
    (f : U →* D) (hf : Function.Surjective f)
    (hk : f.ker = (centralizer (V : Set H)).subgroupOf U)
    (hD : Nat.card D ≤ 4)
    (hratio : 1 < cubicRatio (DihedralCubic.representation U V hU f hf hk))
    (hcard : Nat.card (V.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) = 2)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (v r : H ⧸ ChapterB.minimalParabolicCore T hP)
    (hv : v ∈ V.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP)))
    (hv1 : v ≠ 1) (hr : orderOf r = p) (hi : v*r*v⁻¹=r⁻¹) : p = 3 := by
  let J := ChapterB.minimalParabolicCore T hP
  let M := ChapterB.minimalParabolicMax T hP
  let q := QuotientGroup.mk' J
  let S := T.mapSurjective (QuotientGroup.mk'_surjective J)
  let W := V.map q
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map q
  have hWcore : W ≤ (pCore 2 (M.map q)).map (M.map q).subtype :=
    (map_mono hcore).trans (Theory.SpecificGroups.Alternating.FiveBorelCentralFactor.core_image_le q M)
  obtain ⟨w,a,ha,⟨e⟩⟩ := exists_pair_of_inverted_prime S (M.map q) W
    (map_mono hVT) hWcore hcard hp hp2 v r hv hv1 hr hi
  obtain ⟨w',_,_,_,e',_⟩ := QuotientLift.lift_pair T hP V hVT hvn hcore w
  let b : BenderPlacement.OriginalWitness T M V 1 :=
    ⟨w',1,by decide,one_dvd _,.dihedral rfl p a hp hp2 ha (e'.trans e)⟩
  have hTV := (normal_subgroupOf_iff_le_normalizer hVT).mp hvn
  have hNV := ChapterE.minimalParabolic_normalizer_le T hP V
    (IsElementaryAbelian.isPGroup 2 V) hTV hout
  obtain ⟨⟨d⟩,_,_,⟨e6⟩,_⟩ := b.small_quaternion_core hVT hTV hcore hNV hfit hV hTU hU
    f hf hk hD hratio
  have hpc : Nat.card (pCore 2 w'.subgroup) = 32 := by
    have hh := d.card
    change Nat.card ((pCore 2 w'.subgroup).map w'.subgroup.subtype) = 32 at hh
    rwa [card_map_of_injective w'.subgroup.subtype_injective] at hh
  have hidx : (pCore 2 w'.subgroup).index = 6 := by
    change Nat.card (w'.subgroup ⧸ pCore 2 w'.subgroup) = 6
    rw [Nat.card_congr e6.toEquiv,DihedralGroup.nat_card]
  have hI : Nat.card w'.subgroup = 192 := by
    have hh := (pCore 2 w'.subgroup).card_mul_index
    rw [hpc,hidx] at hh
    omega
  have hdvd : p ∣ 192 := by
    have hc : Nat.card (w'.subgroup ⧸ (M.subgroupOf w'.subgroup).normalCore) = 2*p^a := by
      rw [Nat.card_congr (e'.trans e).toEquiv,DihedralGroup.nat_card]
    have hq := (M.subgroupOf w'.subgroup).normalCore.index_dvd_card
    change Nat.card (w'.subgroup ⧸ (M.subgroupOf w'.subgroup).normalCore) ∣ _ at hq
    rw [hc,hI] at hq
    exact (dvd_mul_of_dvd_right (dvd_pow_self p (Nat.ne_of_gt ha)) 2).trans hq
  change p ∣ 2^6*3 at hdvd
  rcases hp.dvd_mul.mp hdvd with h2 | h3
  · have he : p = 2 := (Nat.dvd_prime Nat.prime_two).mp (hp.dvd_of_dvd_pow h2) |>.resolve_left hp.ne_one
    exact (hp2 he).elim
  · exact ((Nat.dvd_prime Nat.prime_three).mp h3).resolve_left hp.ne_one

end CFSG.Quasithin.ChapterE.Witnesses.Involution
