module

public import Stellmacher.Recognition.NormalEightSeparatedClosureEightData
public import Stellmacher.Recognition.NormalEightSeparatedClosureEightLocal
public import Theory.SpecificGroups.CyclicTwoDihedralFourAlignment
public import Theory.SpecificGroups.CyclicTwoDihedralFourExtension
public import Theory.SpecificGroups.AffineEight.SimpleSylowExclusion

/-!
# Excluding an order-eight closure

Once the involution centralizer in the Sylow subgroup is identified with
C₂ × D₈, the closure determines its elementary-eight coordinates. The
involution is a nonsquare: the unique nonidentity square of a normal C₂ × D₈
subgroup is central in the whole group. Coordinate alignment and the proved
normalizer equality then identify the Sylow subgroup with the affine group of
the cyclic group of order eight. Transfer excludes this Sylow group in a
nonsolvable simple group.

The local C₂ × D₈ identification is supplied by `centralizer_model`; the
final theorem discharges this premise using the local setup and the
order-two central omega hypothesis.
Source: Janko–Thompson, Math. Z. 113 (1970), Lemma 3.1, printed p.388;
refs/original/n-group-global/odd-core-rank-two-source/janko-thompson-1970-gdz.pdf.
The affine Sylow exclusion replaces the source's appeal to Fong.
-/

namespace Stellmacher.Recognition.NormalEightSeparatedClosureEight
open Subgroup NormalEightSeparatedCentralizers
private abbrev Model := Multiplicative (ZMod 2) × DihedralGroup 4

private theorem model_square_unique : ∀ a b : Model,
    a ^ 2 ≠ 1 → b ^ 2 ≠ 1 → a ^ 2 = b ^ 2 := by decide

/-- A noncentral element cannot be a square in a normal C₂ × D₈ subgroup. -/
private theorem nonsquare_of_noncentral
    {P : Type*} [Group P] (C : Subgroup P) [C.Normal]
    (e : C ≃* Model) (i : C) (hi : (i : P) ∉ center P) :
    ∀ x : C, x ^ 2 ≠ i := by
  intro x hx
  have hi1 : i ≠ 1 := fun h => hi (by simpa only [h, coe_one] using (one_mem (center P)))
  have hsquare (y : C) (hy : y ^ 2 ≠ 1) : y ^ 2 = i := by
    apply e.injective
    rw [← hx, map_pow, map_pow]
    apply model_square_unique
    · intro h
      exact hy (e.injective (by simpa only [map_pow, map_one] using h))
    · intro h
      apply hi1
      apply e.injective
      simpa only [← hx, map_pow, map_one] using h
  apply hi
  apply mem_center_iff.mpr
  intro g
  let α : MulAut C := C.normalizerMonoidHom
    ⟨g, by rw [C.normalizer_eq_top]; trivial⟩
  have hα : (α x) ^ 2 ≠ 1 := by
    rw [← map_pow, hx]
    exact fun h => hi1 (α.injective (h.trans α.map_one.symm))
  have he : α i = i := by
    calc
      α i = α (x ^ 2) := congrArg α hx.symm
      _ = (α x) ^ 2 := map_pow α x 2
      _ = i := hsquare _ hα
  have he' : g * (i : P) * g⁻¹ = (i : P) := congrArg Subtype.val he
  exact mul_inv_eq_iff_eq_mul.mp he'

/-- The local C₂ × D₈ identification suffices for the order-eight contradiction. -/
public theorem false_of_closure_eight_of_centralizer_equiv
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G)
    (S : Sylow 2 G) (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W]
    (hW : Nat.card W = 4) (z : S) (hzW : z ∈ W) (hzC : z ∈ center S)
    (hz : orderOf z = 2) (i : S) (hiW : i ∈ W) (hi : orderOf i = 2)
    (hiC : i ∉ center S)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (d : CentralizerSetup S W i) (hc : Nat.card d.closure = 8)
    (e : centralizer ({i} : Set S) ≃* (Multiplicative (ZMod 2) × DihedralGroup 4)) :
    False := by
  let C := centralizer ({i} : Set S)
  have hindex : C.index = 2 :=
    centralizer_involution_index S W hW z hzW hzC hz i hiW hi hiC
  let : C.Normal := C.normal_of_index_eq_two hindex
  let iC : C := ⟨i, mem_centralizer_singleton_iff.mpr rfl⟩
  have hiCC : iC ∈ center C := by
    apply mem_center_iff.mpr
    intro x
    exact Subtype.ext (mem_centralizer_singleton_iff.mp x.property)
  let E := closureInSylow d
  have hEC : E ≤ C := closureInSylow_le_centralizer d
  let EC := E.subgroupOf C
  let : IsElementaryAbelian 2 E := closureInSylow_elementary d
  let : IsElementaryAbelian 2 EC := IsElementaryAbelian.subgroupOf hEC
  let E₀ := EC.map e.toMonoidHom
  have hE₀ : IsElementaryAbelian 2 E₀ := IsElementaryAbelian.map _
  have hcard : Nat.card E₀ = 8 := by
    rw [card_map_of_injective e.injective,
      Nat.card_congr (subgroupOfEquivOfLe hEC).toEquiv, card_closureInSylow, hc]
  have hens : ∀ x : Model, x ^ 2 ≠ e iC := by
    intro x hx
    apply nonsquare_of_noncentral C e iC hiC (e.symm x)
    apply e.injective
    simpa only [map_pow, e.apply_symm_apply] using hx
  obtain ⟨u, huc, huE⟩ := CyclicTwoDihedralFour.exists_alignment E₀ hE₀ hcard
    (e iC) (centerCongr e ⟨iC, hiCC⟩).property hens
  let k : Model ≃* C := u.trans e.symm
  have hkc : k (Multiplicative.ofAdd 1, 1) = iC := by
    change e.symm (u (Multiplicative.ofAdd 1, 1)) = iC
    rw [huc, e.symm_apply_apply]
  have hkE : (centralizer ({(1, DihedralGroup.sr 0)} : Set Model)).map
      k.toMonoidHom = EC := by
    change (centralizer ({(1, DihedralGroup.sr 0)} : Set Model)).map
      (e.symm.toMonoidHom.comp u.toMonoidHom) = EC
    rw [← map_map, huE]
    change (EC.map e.toMonoidHom).map e.symm.toMonoidHom = EC
    rw [map_map]
    have hid : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id C := by
      apply MonoidHom.ext
      intro x
      exact e.symm_apply_apply x
    rw [hid, map_id]
  let j : Model →* S := C.subtype.comp k.toMonoidHom
  have hj : Function.Injective j := C.subtype_injective.comp k.injective
  have hrange : j.range = C := by
    apply le_antisymm
    · rintro x ⟨y, rfl⟩
      exact (k y).property
    · intro x hx
      exact ⟨k.symm ⟨x, hx⟩, congrArg Subtype.val (k.apply_symm_apply ⟨x, hx⟩)⟩
  have hjc : j (Multiplicative.ofAdd 1, 1) = i := congrArg Subtype.val hkc
  have hjE : (centralizer ({(1, DihedralGroup.sr 0)} : Set Model)).map j = E := by
    change (centralizer ({(1, DihedralGroup.sr 0)} : Set Model)).map
      (C.subtype.comp k.toMonoidHom) = E
    rw [← map_map, hkE, map_subgroupOf_eq_of_le hEC]
  obtain ⟨f, _⟩ := CyclicTwoDihedralFour.exists_mulEquiv_affineEight j hj
    (hrange ▸ hindex) (by rw [hjc, hrange]) (by
      rw [hjE, hrange]
      exact normalizer_closureInSylow_eq S W hW z hzW hzC hz i hiW hi hiC hno d hc)
  exact AffineEight.false_of_simple_sylow hns S f

/-- Conditional assembly from the local group identification. -/
public theorem closure_card_ne_eight_of_centralizer_equiv
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G)
    (S : Sylow 2 G) (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W]
    (hW : Nat.card W = 4) (z : S) (hzW : z ∈ W) (hzC : z ∈ center S)
    (hz : orderOf z = 2) (i : S) (hiW : i ∈ W) (hi : orderOf i = 2)
    (hiC : i ∉ center S)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (d : CentralizerSetup S W i)
    (hmodel : Nat.card d.closure = 8 → Nonempty
      (centralizer ({i} : Set S) ≃* (Multiplicative (ZMod 2) × DihedralGroup 4))) :
    Nat.card d.closure ≠ 8 := by
  intro hc
  obtain ⟨e⟩ := hmodel hc
  exact false_of_closure_eight_of_centralizer_equiv
    hns S W hW z hzW hzC hz i hiW hi hiC hno d hc e

/-- The normal closure in an involution-centralizer supplement cannot have
order eight. The local group identification is derived from the setup. -/
public theorem closure_card_ne_eight
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G)
    (S : Sylow 2 G) (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W]
    (hW : Nat.card W = 4)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (z : S) (hzW : z ∈ W) (hzC : z ∈ center S) (hz : orderOf z = 2)
    (i : S) (hiW : i ∈ W) (hi : orderOf i = 2) (hiC : i ∉ center S)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (d : CentralizerSetup S W i) : Nat.card d.closure ≠ 8 := by
  apply closure_card_ne_eight_of_centralizer_equiv
    hns S W hW z hzW hzC hz i hiW hi hiC hno d
  exact centralizer_model hN S W hW hZ z hzW hzC hz i hiW hi hiC hno d

end Stellmacher.Recognition.NormalEightSeparatedClosureEight
