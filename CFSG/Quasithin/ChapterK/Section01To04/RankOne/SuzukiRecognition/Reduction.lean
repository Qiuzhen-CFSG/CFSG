module

public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.Covers
public import CFSG.Quasithin.ChapterB.Section01.QuasisimpleSections.Group
public import Theory.SpecificGroups.Suzuki.CyclicOuter
public import Theory.SpecificGroups.Suzuki.SubgroupParameters
public import Theory.Representation.Quotient
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Theory.Representation.BinaryOffender.TwoFCardBound

/-!
# The source degree window for Suzuki recognition

The covering equivalence kills the center of the layer through its literal
central projection. Self-centralization of F* and oddness of the Suzuki outer
group put every elementary binary actor of G in L. Transport that actor to
the concrete matrix group without changing its fixed space or cubic action.
The squared-offender cardinality bound and |Sz(q)| < q^5 then give dim V < 10r,
where q = 2^r and r = 2m+1.

This is the numerical reduction used in Guralnick–Malle, *Classification of
2F-modules, II*, Lemmas 2.1 and 8.3. It does not identify the representation;
the small-degree Suzuki classification remains a separate proof obligation.
Source application: Aschbacher–Smith, K.3.5–K.3.6, printed p.457.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterK.RankOne
open BenderSuzuki.MatrixGroups Subgroup Representation Representation.BinaryOffender
open Theory.GroupTheory
variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

namespace SourceHypotheses
variable (h : SourceHypotheses ρ L) {m : ℕ} (hm : 1 ≤ m)
  (e : (L ⧸ center L) ≃* SuzukiMatrixGroup m)

/-- The layer representation on the literal Suzuki matrix carrier. -/
noncomputable def suzukiRepresentation : Representation (ZMod 2) (SuzukiMatrixGroup m) V :=
  (ρ.comp L.subtype).comp (h.suzukiEquiv hm e).symm.toMonoidHom

@[simp] theorem suzukiRepresentation_apply (g : L) (v : V) :
    h.suzukiRepresentation hm e (h.suzukiEquiv hm e g) v = ρ (g : G) v := by
  change ρ ((h.suzukiEquiv hm e).symm (h.suzukiEquiv hm e g) : G) v = _
  rw [MulEquiv.symm_apply_apply]

theorem suzukiRepresentation_faithful : Function.Injective (h.suzukiRepresentation hm e) :=
  h.faithful.comp (L.subtype_injective.comp (h.suzukiEquiv hm e).symm.injective)

theorem suzukiRepresentation_irreducible : IsIrreducible (h.suzukiRepresentation hm e) :=
  (irreducible_comp_surjective_iff (h.suzukiEquiv hm e).symm.toMonoidHom
    (h.suzukiEquiv hm e).symm.surjective (ρ.comp L.subtype)).mpr h.irreducible

include h hm e

private theorem suzuki_center_eq_bot : center L = ⊥ := by
  apply bot_unique
  intro x hx
  have hxq : (QuotientGroup.mk x : L ⧸ center L) = 1 :=
    (QuotientGroup.eq_one_iff x).mpr hx
  have he : h.suzukiEquiv hm e x = 1 := by rw [h.suzukiEquiv_apply hm e, hxq, map_one]
  exact mem_bot.mpr ((h.suzukiEquiv hm e).injective (he.trans (map_one _).symm))

private theorem suzuki_centralizer_eq_bot_of_quotient : centralizer (L : Set G) = ⊥ := by
  have hCL : centralizer (L : Set G) ≤ L := by
    rw [← h.fitting]
    exact ChapterB.QuasisimpleSections.centralizer_generalizedFitting_le
  apply bot_unique
  intro g hg
  have hgZ : (⟨g, hCL hg⟩ : L) ∈ center L := by
    rw [mem_center_iff]
    intro x
    exact Subtype.ext (hg x x.property)
  rw [h.suzuki_center_eq_bot hm e] at hgZ
  exact congrArg Subtype.val (mem_bot.mp hgZ)

/-- Odd index follows from the cover identification before module recognition. -/
theorem suzuki_odd_index_of_quotient : Odd L.index := by
  let : L.Normal := h.layer_normal
  have houter : Odd (Nat.card (MulAut.Outer L)) := by
    rw [Nat.card_congr (MulAut.outerCongr (h.suzukiEquiv hm e)).toEquiv]
    exact suzuki_odd_outer_index m hm
  exact houter.of_dvd_nat (card_dvd_of_injective (MulAut.outerAction L)
    (MulAut.outerAction_injective L (h.suzuki_centralizer_eq_bot_of_quotient hm e)))

/-- Every elementary binary actor of the original group lies in the layer. -/
theorem suzuki_elementary_le_layer_of_quotient {A : Subgroup G}
    (hA : IsElementaryTwo A) : A ≤ L := by
  let : L.Normal := h.layer_normal
  let : IsElementaryAbelian 2 A := hA.2
  have hodd : Odd (Nat.card (G ⧸ L)) := h.suzuki_odd_index_of_quotient hm e
  intro a ha
  apply (QuotientGroup.eq_one_iff a).mp
  apply orderOf_eq_one_iff.mp
  apply Nat.eq_one_of_dvd_coprimes hodd.coprime_two_left
  · apply orderOf_dvd_iff_pow_eq_one.mpr
    change (QuotientGroup.mk' L a) ^ 2 = 1
    rw [← map_pow, elemPow_eq_one_of_isElementaryAbelian a ha, map_one]
  · exact orderOf_dvd_natCard _

/-- The small cubic actor survives both restriction to L and its exact marking. -/
theorem suzukiRepresentation_smallCubic : cubicRatio (h.suzukiRepresentation hm e) ≤ 2 := by
  obtain ⟨A, hA, hc, hd⟩ := (cubicRatio_le_nat_iff ρ 2).mp h.smallCubic
  have hAL := h.suzuki_elementary_le_layer_of_quotient hm e hA
  let B := A.subgroupOf L
  let f := h.suzukiEquiv hm e
  have hBmap : B.map L.subtype = A := map_subgroupOf_eq_of_le hAL
  let : IsElementaryAbelian 2 A := hA.2
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.subgroupOf hAL
  have hBne : B ≠ ⊥ := by
    intro hb
    exact hA.1 (by rw [← hBmap, hb, Subgroup.map_bot])
  have hCne : B.map f.toMonoidHom ≠ ⊥ := by
    intro hc
    apply hBne
    apply Subgroup.map_injective (f := f.toMonoidHom) f.injective
    simpa using hc
  apply (cubicRatio_le_nat_iff (h.suzukiRepresentation hm e) 2).mpr
  refine ⟨B.map f.toMonoidHom, ⟨hCne, IsElementaryAbelian.map _⟩, ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ _ ⟨c, hcB, rfl⟩ v
    simpa only [displacement, LinearMap.sub_apply, LinearMap.id_apply,
      f, MulEquiv.coe_toMonoidHom, suzukiRepresentation_apply] using hc a ha b hb c hcB v
  · have hfix : fixedSpace (ρ.comp L.subtype) B = fixedSpace ρ A := by
      rw [fixedSpace_comp_map, hBmap]
    have hcodim : fixedCodim (ρ.comp L.subtype) B = fixedCodim ρ A := by
      unfold fixedCodim
      rw [hfix]
    have hdim := fixedCodim_map_equivariant (ρ.comp L.subtype)
      (h.suzukiRepresentation hm e) f.toMonoidHom (LinearEquiv.refl (ZMod 2) V)
      (fun g v => (h.suzukiRepresentation_apply hm e g v).symm) B
    rw [← hdim, hcodim, rank_map_injective f.toMonoidHom f.injective]
    have hrank : rank B = rank A := by
      rw [← hBmap, rank_map_injective L.subtype L.subtype_injective]
    rwa [hrank]

/-- The exact squared group-order bound required in the Suzuki GM04 argument. -/
theorem suzuki_card_le_group_sq : Nat.card V ≤ Nat.card (SuzukiMatrixGroup m) ^ 2 := by
  let : IsIrreducible (h.suzukiRepresentation hm e) := h.suzukiRepresentation_irreducible hm e
  exact TwoFCardBound.card_le_group_sq_of_cubic (h.suzukiRepresentation hm e)
    (h.suzukiRepresentation_faithful hm e) (h.suzukiRepresentation_smallCubic hm e)

/-- The squared Suzuki order is strictly below q^10. -/
theorem suzuki_finrank_lt_ten_mul : Module.finrank (ZMod 2) V < 10 * (2 * m + 1) := by
  have hb := h.suzuki_card_le_group_sq hm e
  have hq : 1 < (2 : ℕ) ^ (2 * m + 1) := one_lt_pow₀ (by decide) (by omega)
  have horder : Nat.card (SuzukiMatrixGroup m) < ((2 : ℕ) ^ (2 * m + 1)) ^ 5 := by
    rw [suzukiMatrixGroup_card m (by omega)]
    have hsub : 2 ^ (2 * m + 1) - 1 + 1 = (2 : ℕ) ^ (2 * m + 1) := by omega
    let q := (2 : ℕ) ^ (2 * m + 1)
    change (q ^ 2 + 1) * q ^ 2 * (q - 1) < q ^ 5
    have hid : (q ^ 2 + 1) * (q - 1) + q ^ 2 + 1 = q ^ 3 + q := by
      calc
        _ = (q ^ 2 + 1) * (q - 1 + 1) := by ring
        _ = q ^ 3 + q := by rw [hsub]; ring
    have hqq : q < q ^ 2 + 1 := by nlinarith only [Nat.le_mul_self q]
    have hcub : (q ^ 2 + 1) * (q - 1) < q ^ 3 := by omega
    calc
      (q ^ 2 + 1) * q ^ 2 * (q - 1) = ((q ^ 2 + 1) * (q - 1)) * q ^ 2 := by ring
      _ < q ^ 3 * q ^ 2 := Nat.mul_lt_mul_of_pos_right hcub (pow_pos (by omega) 2)
      _ = q ^ 5 := by ring
  have hsq := Nat.pow_lt_pow_left horder (by decide : 2 ≠ 0)
  have hsmall := hb.trans_lt hsq
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V), Nat.card_zmod,
    ← pow_mul, ← pow_mul] at hsmall
  have he := (Nat.pow_lt_pow_iff_right (by decide : 1 < (2 : ℕ))).mp hsmall
  omega

end SourceHypotheses
end CFSG.Quasithin.ChapterK.RankOne
