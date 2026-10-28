module

public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.GraphField.ModelData
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.GraphField.NormalizerModels.Marking
public import Theory.SpecificGroups.PSL3Four.CentralCover.InnerFamilyNormalizer.DoubleCover

/-!
# The actual normalizer in the center-C₂ graph-field case

The marked four intersects L in its central involution. An element of L
normalizes this four exactly when its displacement under r lies in Z(L),
equivalently when its projective image is graph-field fixed. Decomposing
L⟨r,z⟩ into component and actor factors identifies its entire four-normalizer
with the preimage of the projective fixed subgroup extended by r.

Sylow theory constructs an actual two-subgroup containing the marked four
inside this normalizer. The whole normalizer preserves the residual, since
C_L(E) = C_L(r) and the two-residual is characteristic. Every such
two-subgroup fixes z. The intrinsic
central displacement is related explicitly to conjugation of r below.
The quaternion quotient, centralizer equality and nontrivial displacement
calculation remain to be supplied before the requested normalizer and
cyclic-four action witnesses are assembled.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
16.4.9(2), printed p.1191, using I.2.2(3), pp.409–410.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter16.Intersections.GraphField.NormalizerModels.DoubleCoverConstruction
open Matrix.PSL3Four
open Matrix.PSL3Four.ExtendedCentralizer.ProjectiveFixer
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {z g r : G} {L R : Subgroup G}

theorem four_inter_component (h : IntersectionSetup T z L g R)
    (hr : r ∈ R) (hr2 : orderOf r = 2) (hout : r ∉ centralizer (L : Set G) ⊔ L)
    (hZ : (center L).map L.subtype = zpowers z) :
    L ⊓ fourGroup r z = zpowers z := by
  classical
  have hzL : zpowers z ≤ L := hZ ▸ map_subtype_le (center L)
  have hzN : zpowers z ≤ normalizer (zpowers r : Set G) := by
    apply zpowers_le.mpr
    apply centralizer_le_normalizer
    intro y hy
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hy
    have hc : Commute z r := (mem_centralizer_singleton_iff.mp
      (h.sylow_centralizes (h.le_sylow hr))).symm
    exact (hc.zpow_right n).eq.symm
  apply le_antisymm
  · intro x hx
    have he := hx.2
    change x ∈ (↑(zpowers r ⊔ zpowers z) : Set G) at he
    rw [coe_mul_of_right_le_normalizer_left _ _ hzN] at he
    obtain ⟨y, hy, w, hw, rfl⟩ := he
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp (mem_zpowers_iff_mem_range_orderOf.mp hy)
    have hn2 : n < 2 := by simpa only [Finset.mem_range, hr2] using hn
    rcases (show n = 0 ∨ n = 1 by omega) with rfl | rfl
    · simpa using hw
    · exfalso
      apply hout
      apply mem_sup_right
      have hm := L.mul_mem hx.1 (L.inv_mem (hzL hw))
      simpa only [pow_one, mul_inv_cancel_right] using hm
  · exact le_inf hzL le_sup_right

theorem normalizer_four_iff_central_displacement (h : IntersectionSetup T z L g R)
    (hr : r ∈ R) (hr2 : orderOf r = 2) (hout : r ∉ centralizer (L : Set G) ⊔ L)
    (hZ : (center L).map L.subtype = zpowers z)
    (hn : r ∈ normalizer (L : Set G)) (x : L) :
    (x : G) ∈ normalizer (fourGroup r z : Set G) ↔
      L.normalizerMonoidHom ⟨r, hn⟩ x * x⁻¹ ∈ center L := by
  let a := L.normalizerMonoidHom ⟨r, hn⟩
  have hrE : r ∈ fourGroup r z := mem_sup_left (mem_zpowers r)
  have hxz : MulAut.conj (x : G) z = z := by
    change (x : G) * z * (x : G)⁻¹ = z
    rw [mem_centralizer_singleton_iff.mp (h.component.1 x.property), mul_inv_cancel_right]
  constructor
  · intro hx
    have he : (x : G) * r * (x : G)⁻¹ * r⁻¹ ∈ fourGroup r z :=
      (fourGroup r z).mul_mem ((mem_normalizer_iff.mp hx r).mp hrE)
        ((fourGroup r z).inv_mem hrE)
    have hd : ((a x * x⁻¹ : L) : G) ∈ fourGroup r z := by
      have hi := (fourGroup r z).inv_mem he
      change r * (x : G) * r⁻¹ * (x : G)⁻¹ ∈ fourGroup r z
      convert hi using 1
      group
    have hz : ((a x * x⁻¹ : L) : G) ∈ zpowers z :=
      (four_inter_component h hr hr2 hout hZ).le ⟨(a x * x⁻¹).property, hd⟩
    rw [← hZ] at hz
    obtain ⟨y, hy, heq⟩ := hz
    exact (Subtype.ext heq : y = a x * x⁻¹) ▸ hy
  · intro hd
    have hz : ((a x * x⁻¹ : L) : G) ∈ zpowers z := by
      rw [← hZ]
      exact mem_map_of_mem L.subtype hd
    have he : MulAut.conj (x : G) r ∈ fourGroup r z := by
      have hh := (fourGroup r z).mul_mem
        ((fourGroup r z).inv_mem (mem_sup_right hz)) hrE
      change (x : G) * r * (x : G)⁻¹ ∈ fourGroup r z
      convert hh using 1
      change _ = (r * (x : G) * r⁻¹ * (x : G)⁻¹)⁻¹ * r
      group
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply eq_of_le_of_card_ge
    · change (zpowers r ⊔ zpowers z).map (MulAut.conj (x : G)).toMonoidHom ≤ _
      rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
      exact sup_le (zpowers_le.mpr he) (by simpa only [MulEquiv.coe_toMonoidHom, hxz] using
        (show zpowers z ≤ fourGroup r z from le_sup_right))
    · rw [card_map_of_injective (MulAut.conj (x : G)).injective]

/-- Normalizing the marked four is exactly being fixed after projectivization. -/
theorem component_normalizer_eq_preimage (h : IntersectionSetup T z L g R)
    (hr : r ∈ R) (hr2 : orderOf r = 2) (hout : r ∉ centralizer (L : Set G) ⊔ L)
    (hZ : (center L).map L.subtype = zpowers z) (d : MarkedCover L r) :
    (normalizer (fourGroup r z : Set G)).subgroupOf L =
      graphField.fixedSubgroup.comap d.cover.toMonoidHom := by
  ext x
  rw [mem_subgroupOf, normalizer_four_iff_central_displacement h hr hr2 hout hZ d.actor_mem,
    ← d.kernel_center, mem_comap, MulAut.mem_fixedSubgroup, MonoidHom.mem_ker]
  change d.cover.toMonoidHom (L.normalizerMonoidHom ⟨r, d.actor_mem⟩ x * x⁻¹) = 1 ↔
    graphField (d.cover.toMonoidHom x) = d.cover.toMonoidHom x
  rw [map_mul, map_inv, mul_inv_eq_one, d.compatible]

/-- The actual local normalizer is the preimage of the projective fixed group,
extended by the given involution. -/
theorem normalizer_eq_preimage_sup (h : IntersectionSetup T z L g R)
    (hr : r ∈ R) (hr2 : orderOf r = 2) (hout : r ∉ centralizer (L : Set G) ⊔ L)
    (hZ : (center L).map L.subtype = zpowers z) (d : MarkedCover L r) :
    (L ⊔ fourGroup r z) ⊓ normalizer (fourGroup r z : Set G) =
      (graphField.fixedSubgroup.comap d.cover.toMonoidHom).map L.subtype ⊔ zpowers r := by
  have hzL : zpowers z ≤ L := hZ ▸ map_subtype_le (center L)
  have hprod : L ⊔ fourGroup r z = L ⊔ zpowers r := by
    change L ⊔ (zpowers r ⊔ zpowers z) = _
    rw [← sup_assoc, sup_eq_left.mpr (hzL.trans le_sup_left)]
  have hrN : zpowers r ≤ normalizer (fourGroup r z : Set G) :=
    le_sup_left.trans (fourGroup r z).le_normalizer
  have hD := component_normalizer_eq_preimage h hr hr2 hout hZ d
  rw [← hD, subgroupOf_map_subtype, hprod, inf_comm (normalizer (fourGroup r z : Set G)) L]
  apply le_antisymm
  · intro x hx
    have hxprod : x ∈ (↑(L ⊔ zpowers r) : Set G) := hx.1
    rw [coe_mul_of_right_le_normalizer_left _ _ (zpowers_le.mpr d.actor_mem)] at hxprod
    obtain ⟨l, hl, u, hu, rfl⟩ := hxprod
    have hln : l ∈ normalizer (fourGroup r z : Set G) := by
      have hh := (normalizer (fourGroup r z : Set G)).mul_mem hx.2
        ((normalizer (fourGroup r z : Set G)).inv_mem (hrN hu))
      simpa only [mul_inv_cancel_right] using hh
    exact (L ⊓ normalizer (fourGroup r z : Set G) ⊔ zpowers r).mul_mem
      (mem_sup_left ⟨hl, hln⟩) (mem_sup_right hu)
  · exact sup_le (le_inf (inf_le_left.trans le_sup_left) inf_le_right)
      (le_inf le_sup_right hrN)

/-- The centralizer of E inside L is the centralizer of the actor r inside L. -/
theorem component_centralizer_four (h : IntersectionSetup T z L g R) :
    L ⊓ centralizer (fourGroup r z : Set G) = L ⊓ centralizer ({r} : Set G) := by
  apply le_antisymm
  · rintro x ⟨hxL, hxE⟩
    exact ⟨hxL, mem_centralizer_singleton_iff.mpr
      (hxE r (mem_sup_left (mem_zpowers r))).symm⟩
  · rintro x ⟨hxL, hxr⟩
    refine ⟨hxL, ?_⟩
    have hf : fourGroup r z ≤ centralizer ({x} : Set G) := by
      apply sup_le <;> apply zpowers_le.mpr <;> apply mem_centralizer_singleton_iff.mpr
      · exact (mem_centralizer_singleton_iff.mp hxr).symm
      · exact (mem_centralizer_singleton_iff.mp (h.component.1 hxL)).symm
    intro y hy
    exact mem_centralizer_singleton_iff.mp (hf hy)

/-- The whole actual local four-normalizer preserves the embedded two-residual. -/
theorem normalizer_normalizes_residual (h : IntersectionSetup T z L g R) (hr : r ∈ R) :
    (L ⊔ fourGroup r z) ⊓ normalizer (fourGroup r z : Set G) ≤
      normalizer (residual L r : Set G) := by
  have hprod : L ⊔ fourGroup r z ≤ normalizer (L : Set G) := by
    apply sup_le L.le_normalizer
    apply sup_le
    · exact zpowers_le.mpr (h.sylow_normalizes (h.le_sylow hr))
    · exact zpowers_le.mpr ((centralizer_le_normalizer _) (central_involution_mem_centralizer h))
  have hc : (L ⊔ fourGroup r z) ⊓ normalizer (fourGroup r z : Set G) ≤
      normalizer ((L ⊓ centralizer (fourGroup r z : Set G) : Subgroup G) : Set G) :=
    (le_inf (inf_le_left.trans hprod)
      (inf_le_right.trans (normalizer_le_normalizer_centralizer (fourGroup r z)))).trans
      inf_normalizer_le_normalizer_inf
  rw [component_centralizer_four h] at hc
  exact hc.trans (normalizer_le_normalizer_characteristic_image
    (L ⊓ centralizer ({r} : Set G)) (pResidual 2 (L ⊓ centralizer ({r} : Set G) : Subgroup G)))

/-- Sylow theory already constructs a genuine two-subgroup containing E inside
its local normalizer. The quaternion quotient and cover action remain separate. -/
theorem exists_two_subgroup (h : IntersectionSetup T z L g R)
    (hr : r ∈ R) (hr2 : orderOf r = 2) (hout : r ∉ centralizer (L : Set G) ⊔ L) :
    ∃ Q : Subgroup G, IsPGroup 2 Q ∧ fourGroup r z ≤ Q ∧
      Q ≤ L ⊔ fourGroup r z ∧ Q ≤ normalizer (fourGroup r z : Set G) ∧
      Q ≤ normalizer (residual L r : Set G) ∧ Q ≤ centralizer ({z} : Set G) ∧
      SylowIn Q ((L ⊔ fourGroup r z) ⊓ normalizer (fourGroup r z : Set G)) := by
  let N := (L ⊔ fourGroup r z) ⊓ normalizer (fourGroup r z : Set G)
  have hEN : fourGroup r z ≤ N := le_inf le_sup_right (fourGroup r z).le_normalizer
  let := (fourGroup_elementary_card h hr hr2 hout).1
  have hp : IsPGroup 2 ((fourGroup r z).subgroupOf N) :=
    (IsElementaryAbelian.isPGroup 2 (fourGroup r z)).of_equiv (subgroupOfEquivOfLe hEN).symm
  obtain ⟨S, hS⟩ := hp.exists_le_sylow
  have hQN : (S : Subgroup N).map N.subtype ≤ N := map_subtype_le _
  refine ⟨(S : Subgroup N).map N.subtype, S.isPGroup'.map _, ?_,
    hQN.trans inf_le_left, hQN.trans inf_le_right,
    hQN.trans (normalizer_normalizes_residual h hr), hQN.trans (inf_le_left.trans (product_le_centralizer_z h hr)), ⟨S, rfl⟩⟩
  rw [← map_subgroupOf_eq_of_le hEN]
  exact map_mono hS

/-- The source hypotheses identify the actual local normalizer through the
constructed marked cover, without an assumed normalizer or quaternion subgroup. -/
theorem source_normalizer_eq_preimage_sup {𝒦 : GroupClass}
    (hG : Hypothesis1611 𝒦 G) (h : IntersectionSetup T z L g R)
    (hr : r ∈ R) (hr2 : orderOf r = 2) (hout : r ∉ centralizer (L : Set G) ⊔ L)
    (hTC : commutingSylow T L = zpowers z) (hcore : pCore 2 L ≠ ⊥)
    (d : MarkedCover L r) :
    (L ⊔ fourGroup r z) ⊓ normalizer (fourGroup r z : Set G) =
      (graphField.fixedSubgroup.comap d.cover.toMonoidHom).map L.subtype ⊔ zpowers r := by
  have hcenter := hG.evenType.component_center_eq_twoCore h.involution h.component
  exact normalizer_eq_preimage_sup h hr hr2 hout
    (center_eq_zpowers_of_nontrivial_core h hTC hcenter hcore) d

omit [Finite G] in
/-- The intrinsic displacement computes conjugation of the actual ambient actor. -/
theorem displacement_conjugates_actor (d : MarkedCover L r)
    (x : InnerFamilyNormalizer.DoubleCover.fixedPreimage d.cover) :
    MulAut.conj ((x : L) : G) r =
      (((InnerFamilyNormalizer.DoubleCover.displacement d.cover
        (L.normalizerMonoidHom ⟨r, d.actor_mem⟩) d.compatible x : center L) : L) : G)⁻¹ * r := by
  change ((x : L) : G) * r * ((x : L) : G)⁻¹ =
    (r * ((x : L) : G) * r⁻¹ * ((x : L) : G)⁻¹)⁻¹ * r
  group

end CFSG.Quasithin.Chapter16.Intersections.GraphField.NormalizerModels.DoubleCoverConstruction
