module

public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OutsideStructure.Statements
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OutsideStructure.LocalControl
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OutsideStructure.LocalBranches.Geometry
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OutsideStructure.LocalBranches.SecondAction
public import Theory.GroupTheory.PResidual.OddCoreSupplement
public import Theory.GroupTheory.PResidual.SylowSupplement

/-!
# The second-choice span and residual intersection

The actual cubic coordinate action gives V₂ ≤ ⟨Z^{Y₊}⟩: the commutator
of that span with Y₊ is nontrivial, and the cubic orbit of any nonzero
vector spans V₂. We reuse the established residual-centralizer image.

The two-core of Y lies in S and acts trivially on V. Since Y/O₂(Y) is a
three-group, C_Y(V₁) = Y₊ O₂(Y). Its image has order three in the order-nine
image of Y, so this subgroup has index three in Y. An outside overgroup I
contains it but cannot contain Y; hence Y ∩ I = Y₊ O₂(Y). Taking the
two-residual gives Y₊ = O²(Y ∩ I). These two results discharge the span and
intersection premises in the centralizer and normalizer conclusions.

Only the earlier 15.3.7 image, span and three-group quotient outputs are
inputs. In particular the argument applies to both alternatives of 15.3.7,
and never identifies the full action kernel with O₂(Y) in the extraspecial
alternative.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 15.3.11(2)–(4),
printed pp.1123–1124, with the setup of 15.3.7 and 15.3.10 on pp.1122–1123.
-/

public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter15.Section03.OutsideStructure.LocalBranches
open RankTwo RankTwo.FullActionCoordinates

local instance : MulDistribMulAction OrthogonalPlaneActor OrthogonalPlaneVector :=
  FourGroupMatrixCoordinates.naturalAction
local instance : MulDistribMulAction OrthogonalActor OrthogonalVector := orthogonalAction

private theorem cubic_plane_orbit : ∀ (w v : OrthogonalPlaneVector),
    w ≠ 1 → v = 1 ∨ v = w ∨ v = cubicMatrix • w ∨ v = w * (cubicMatrix • w) := by
  decide +kernel

private theorem cubic_orbit_spans (j : OrthogonalPlaneIndex) (w v : OrthogonalVector)
    (hw : w ∈ orthogonalCoordinatePlane j) (hne : w ≠ 1)
    (hv : v ∈ orthogonalCoordinatePlane j) :
    v = 1 ∨ v = w ∨ v = coordinateCubic j • w ∨ v = w * (coordinateCubic j • w) := by
  have hne' : w j ≠ 1 := by
    intro he
    apply hne
    funext k
    by_cases hk : k = j
    · simpa [hk] using he
    · exact hw k hk
  have hs (k : OrthogonalPlaneIndex) :
      (coordinateCubic j • w) k = (if k = j then cubicMatrix else 1) • w k := by
    change (if k = j then cubicMatrix else 1) • w ((1 : OrthogonalPlaneIndex)⁻¹ * k) = _
    rw [inv_one, one_mul]
  rcases cubic_plane_orbit (w j) (v j) hne' with h | h | h | h
  · left
    funext k
    by_cases hk : k = j
    · simpa [hk] using h
    · exact hv k hk
  · right; left
    funext k
    by_cases hk : k = j
    · simpa [hk] using h
    · rw [hv k hk, hw k hk]
  · right; right; left
    funext k
    rw [hs]
    by_cases hk : k = j
    · simpa [hk] using h
    · simp only [if_neg hk, one_smul, hv k hk, hw k hk]
  · right; right; right
    funext k
    change v k = w k * (coordinateCubic j • w) k
    rw [hs]
    by_cases hk : k = j
    · simpa [hk] using h
    · simp only [if_neg hk, one_smul, hv k hk, hw k hk, mul_one]

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem plane_mem_iff {M V : Subgroup G} (a : NaturalOrthogonalAction M V)
    (j : OrthogonalPlaneIndex) (v : V) :
    (v : G) ∈ a.plane j ↔ a.coordinates v ∈ orthogonalCoordinatePlane j := by
  constructor
  · rintro ⟨w, hw, he⟩
    exact (Subtype.ext he : w = v) ▸ hw
  · intro hv
    exact ⟨v, hv, rfl⟩

omit [Finite G] in
private theorem plane_le_of_cubic_orbit {M V X W : Subgroup G}
    (a : NaturalOrthogonalAction M V) (j : OrthogonalPlaneIndex)
    (hc : coordinateCubic j ∈ a.image X)
    (hn : X ≤ normalizer (W : Set G))
    {w : G} (hwP : w ∈ a.plane j) (hwW : w ∈ W) (hw : w ≠ 1) :
    a.plane j ≤ W := by
  obtain ⟨m, hmX, hm⟩ := hc
  let w₀ : V := ⟨w, a.plane_le j hwP⟩
  let u : V := V.normalizerMonoidHom ⟨m, a.normalizes m.property⟩ w₀
  have huW : (u : G) ∈ W := le_normalizer_iff.mp hn m hmX w hwW
  have hu : a.coordinates u = coordinateCubic j • a.coordinates w₀ := by
    rw [a.compatible, hm]
  have hw₀ : a.coordinates w₀ ≠ 1 := by
    intro he
    have hh := a.coordinates.injective (he.trans (map_one _).symm)
    exact hw (congrArg Subtype.val hh)
  intro v hv
  let v₀ : V := ⟨v, a.plane_le j hv⟩
  change (v₀ : G) ∈ W
  rcases cubic_orbit_spans j (a.coordinates w₀) (a.coordinates v₀)
      ((plane_mem_iff a j w₀).mp hwP) hw₀ ((plane_mem_iff a j v₀).mp hv) with h | h | h | h
  · have he := a.coordinates.injective (h.trans (map_one _).symm)
    exact (congrArg Subtype.val he).symm ▸ W.one_mem
  · have he := a.coordinates.injective h
    exact (congrArg Subtype.val he).symm ▸ hwW
  · have he := a.coordinates.injective (h.trans hu.symm)
    exact (congrArg Subtype.val he).symm ▸ huW
  · have he : a.coordinates v₀ = a.coordinates (w₀ * u) := by
      rw [map_mul, hu]
      exact h
    have he' := congrArg Subtype.val (a.coordinates.injective he)
    exact he'.symm ▸ W.mul_mem hwW huW

/-- The cubic action on the second plane puts it in the actual conjugate span
of Z under Y₊. Noncentrality supplies a nonzero vector in the plane, whose
cubic orbit spans that plane. -/
theorem second_choice_plane_le_span (d : CharacteristicTwo.LocalData G)
    (hsecond : SecondChoice d)
    (h7image : d.action.image d.Y = twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (h7span : localSpan d.Z d.Y = d.V) :
    d.V₂ ≤ localSpan d.Z d.Yplus := by
  let W := localSpan d.Z d.Yplus
  have hWV : W ≤ d.V := by
    rw [← h7span]
    exact conjugateSpanBy_mono le_rfl (choice_le d.M d.Y d.S d.V₁ d.Yplus d.choice)
  have hn : d.Yplus ≤ normalizer (W : Set G) := le_normalizer_conjugateSpanBy _ _
  have hCW : ⁅W, d.Yplus⁆ ≤ W := le_normalizer_iff_commutator_le_left.mp hn
  have hCP : ⁅W, d.Yplus⁆ ≤ d.V₂ := by
    rw [← (second_choice_commutator d hsecond h7image).1]
    exact commutator_mono hWV le_rfl
  have hne : ⁅W, d.Yplus⁆ ≠ ⊥ := by
    intro he
    exact second_choice_noncentral_ui d d.Yplus hsecond h7image h7span
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp he))
  obtain ⟨⟨w, hw⟩, hwne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hc : coordinateCubic (Multiplicative.ofAdd (1 : ZMod 2)) ∈ d.action.image d.Yplus := by
    rw [hsecond.2]
    change _ ∈ d.action.image (RankTwo.centralizingFactor d.Y d.V₁)
    rw [RankTwo.residualY_centralizingFactor_image_eq_coordinateCubic d.action h7image
      (show (1 : OrthogonalPlaneIndex) ≠ Multiplicative.ofAdd (1 : ZMod 2) by decide)]
    exact mem_zpowers _
  exact plane_le_of_cubic_orbit d.action _ hc hn (hCP hw) (hCW hw) (fun he => hwne (Subtype.ext he))

private theorem residual_eq (H : Subgroup G) :
    twoResidualAmbient H = (pResidual 2 H).map H.subtype := by
  unfold twoResidualAmbient twoResidualSubgroup pResidual
  congr 1
  apply congrArg sInf
  ext N
  constructor
  · rintro ⟨hN, n, hn⟩
    exact ⟨hN, IsPGroup.of_card hn⟩
  · rintro ⟨hN, hp⟩
    exact ⟨hN, IsPGroup.iff_card.mp hp⟩

/-- Normality of Y in M places its two-core in T; the plane action then
places it in S. No conclusion of 15.3.11 is used. -/
theorem y_core_le_s (d : CharacteristicTwo.LocalData G) : d.Y.pCoreIn 2 ≤ d.S := by
  have hQM : d.Y.pCoreIn 2 ≤ d.M.pCoreIn 2 := le_pCoreIn_of_normalizes
    (isPGroup_pCoreIn 2 d.Y)
    ((pCoreIn_le 2 d.Y).trans (Chapter14.SourcePreliminaries.sourceResidual_le _ _))
    ((m_normalizes_y d).trans (normalizer_le_normalizer_characteristic_image d.Y (pCore 2 d.Y)))
  have hQT : d.Y.pCoreIn 2 ≤ (d.T : Subgroup G) := by
    have hh := hQM.trans (pCoreIn_le_sylow d.M (d.T.subtype d.sylow_le))
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le d.sylow_le] using hh
  exact le_inf hQT ((pCoreIn_le 2 d.Y).trans (y_normalizes_plane d 1))

omit [Finite G] in
private theorem core_le_actor_ker (d : CharacteristicTwo.LocalData G)
    (h7image : d.action.image d.Y = twoResidualAmbient (⊤ : Subgroup OrthogonalActor)) :
    pCore 2 d.Y ≤ (d.action.actor.comp
      (inclusion (Chapter14.SourcePreliminaries.sourceResidual_le d.M d.Mc))).ker := by
  let f := d.action.actor.comp
    (inclusion (Chapter14.SourcePreliminaries.sourceResidual_le d.M d.Mc))
  have hr : Nat.card f.range = 9 := by
    rw [natural_restricted_actor_range, h7image, orthogonal_twoResidual_card]
  have hp := (pCore_isPGroup (p := 2) (G := d.Y)).map f
  have hd : Nat.card ((pCore 2 d.Y).map f) ∣ 9 := hr ▸ card_dvd_of_le (map_le_range _ _)
  have hb : (pCore 2 d.Y).map f = ⊥ := by
    apply card_eq_one.mp
    rcases hp.card_eq_or_dvd with he | he
    · exact he
    · have : 2 ∣ 9 := he.trans hd
      norm_num at this
  exact (Subgroup.map_eq_bot_iff _).mp hb

/-- The odd quotient makes the two-core a supplement to the residual of
C_Y(V₁). The full order-nine image ensures that the two-core centralizes V. -/
theorem second_choice_core_supplement (d : CharacteristicTwo.LocalData G)
    (hsecond : SecondChoice d)
    (h7image : d.action.image d.Y = twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (hodd : IsPGroup 3 (d.Y ⧸ pCore 2 d.Y)) :
    d.Yplus ⊔ d.Y.pCoreIn 2 = d.Y ⊓ centralizer (d.V₁ : Set G) := by
  let C := d.Y ⊓ centralizer (d.V₁ : Set G)
  have hCY : C ≤ d.Y := inf_le_left
  have hQC : pCore 2 d.Y ≤ C.subgroupOf d.Y := by
    have hk := core_le_actor_ker d h7image
    rw [natural_restricted_actor_ker] at hk
    intro y hy
    exact ⟨y.property, centralizer_le (d.action.plane_le 1) (hk hy)⟩
  have hcop : Nat.Coprime 2 (Nat.card (d.Y ⧸ pCore 2 d.Y)) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hodd
    rw [hn]
    exact (by decide : Nat.Coprime 2 3).pow_right n
  have hh := congrArg (Subgroup.map d.Y.subtype)
    (residual_sup_eq_of_quotient_coprime 2 (pCore 2 d.Y) (C.subgroupOf d.Y) hQC hcop)
  rw [Subgroup.map_sup, map_embedded_pResidual, map_subgroupOf_eq_of_le hCY] at hh
  rw [hsecond.2, residual_eq]
  exact hh

/-- The index-three calculation in the proof of 15.3.11(3). The supplement
contains the action kernel and has the proved cubic image of order three. -/
theorem second_choice_supplement_index (d : CharacteristicTwo.LocalData G)
    (hsecond : SecondChoice d)
    (h7image : d.action.image d.Y = twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (hodd : IsPGroup 3 (d.Y ⧸ pCore 2 d.Y)) :
    (d.Yplus ⊔ d.Y.pCoreIn 2).relIndex d.Y = 3 := by
  let J := d.Yplus ⊔ d.Y.pCoreIn 2
  have hJY : J ≤ d.Y := sup_le (choice_le d.M d.Y d.S d.V₁ d.Yplus d.choice) (pCoreIn_le 2 d.Y)
  let f := d.action.actor.comp
    (inclusion (Chapter14.SourcePreliminaries.sourceResidual_le d.M d.Mc))
  have hr : Nat.card f.range = 9 := by
    rw [natural_restricted_actor_range, h7image, orthogonal_twoResidual_card]
  have hkJ : f.ker ≤ J.subgroupOf d.Y := by
    rw [natural_restricted_actor_ker]
    intro y hy
    change (y : G) ∈ J
    rw [show J = d.Y ⊓ centralizer (d.V₁ : Set G) from second_choice_core_supplement d hsecond h7image hodd]
    exact ⟨y.property, centralizer_le (d.action.plane_le 1) hy⟩
  have hmap : (J.subgroupOf d.Y).map f = d.action.image d.Yplus := by
    have hsub : J.subgroupOf d.Y = d.Yplus.subgroupOf d.Y ⊔ pCore 2 d.Y := by
      apply map_injective d.Y.subtype_injective
      rw [map_subgroupOf_eq_of_le hJY, Subgroup.map_sup,
        map_subgroupOf_eq_of_le (choice_le d.M d.Y d.S d.V₁ d.Yplus d.choice)]
      rfl
    rw [hsub, Subgroup.map_sup, (Subgroup.map_eq_bot_iff _).mpr (core_le_actor_ker d h7image), sup_bot_eq]
    change (d.Yplus.subgroupOf d.Y).map (d.action.actor.comp _) = _
    rw [← map_map]
    congr 1
    ext m
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hm
      exact ⟨⟨m, choice_le d.M d.Y d.S d.V₁ d.Yplus d.choice hm⟩, hm, rfl⟩
  have hc : Nat.card ((J.subgroupOf d.Y).map f) = 3 := by
    rw [hmap, hsecond.2]
    exact (residualY_fullActionCoordinateFacts d.action h7image).image_card 1
  have hi := relIndex_map_map f (J.subgroupOf d.Y) ⊤
  rw [← MonoidHom.range_eq_map, sup_eq_left.mpr hkJ, top_sup_eq, relIndex_top_right] at hi
  have hle : (J.subgroupOf d.Y).map f ≤ f.range := map_le_range _ _
  have hh := (((J.subgroupOf d.Y).map f).subgroupOf f.range).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv, hc] at hh
  change 3 * ((J.subgroupOf d.Y).map f).relIndex f.range = Nat.card f.range at hh
  rw [hr, hi] at hh
  change (J.subgroupOf d.Y).index = 3
  omega


/-- An outside overgroup contains the supplement but cannot contain Y.
Its intersection with Y is therefore exactly the index-three supplement. -/
theorem second_choice_intersection_eq_supplement (d : CharacteristicTwo.LocalData G)
    (I : Subgroup G) (hI : I ∈ d.Hplus) (hsecond : SecondChoice d)
    (h7image : d.action.image d.Y = twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (hodd : IsPGroup 3 (d.Y ⧸ pCore 2 d.Y)) :
    d.Y ⊓ I = d.Yplus ⊔ d.Y.pCoreIn 2 := by
  let J := d.Yplus ⊔ d.Y.pCoreIn 2
  have hJY : J ≤ d.Y := sup_le
    (choice_le d.M d.Y d.S d.V₁ d.Yplus d.choice) (pCoreIn_le 2 d.Y)
  have hJI : J ≤ I := sup_le (le_sup_left.trans hI.1.2)
    ((y_core_le_s d).trans (le_sup_right.trans hI.1.2))
  have hle : J ≤ d.Y ⊓ I := le_inf hJY hJI
  have hm := relIndex_mul_relIndex J (d.Y ⊓ I) d.Y hle inf_le_left
  rw [second_choice_supplement_index d hsecond h7image hodd] at hm
  have hp : (J.relIndex (d.Y ⊓ I) * (d.Y ⊓ I).relIndex d.Y).Prime := hm ▸ Nat.prime_three
  rcases Nat.prime_mul_iff.mp hp with h | h
  · exact False.elim (y_not_le_outside_of_second_choice d I hI hsecond
      ((relIndex_eq_one.mp h.2).trans inf_le_right))
  · exact le_antisymm (relIndex_eq_one.mp h.2) hle

/-- The residual equality of 15.3.11(3): adjoining the normalizing two-core
to the two-perfect group Y₊ does not change its two-residual. -/
theorem second_choice_intersection_residual (d : CharacteristicTwo.LocalData G)
    (I : Subgroup G) (hI : I ∈ d.Hplus) (hsecond : SecondChoice d)
    (h7image : d.action.image d.Y = twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (hodd : IsPGroup 3 (d.Y ⧸ pCore 2 d.Y)) :
    d.Yplus = twoResidualAmbient (d.Y ⊓ I) := by
  have hp : IsPPerfect 2 d.Yplus := by
    rw [hsecond.2]
    exact centralizingFactor_isPPerfect d.Y d.V₁
  rw [second_choice_intersection_eq_supplement d I hI hsecond h7image hodd, residual_eq,
    embedded_pResidual_join_pGroup _ _ hp (isPGroup_pCoreIn 2 d.Y)
      (((pCoreIn_le 2 d.Y).trans le_sup_left).trans (ys_normalizes_yplus d))]

/-- Clause (2) in the second choice, using the proved plane containment
and its ambient normalizer control. -/
theorem second_choice_centralizer_le (d : CharacteristicTwo.LocalData G)
    (I : Subgroup G) (hI : I ∈ d.Hplus) (hsecond : SecondChoice d)
    (h7image : d.action.image d.Y = twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (h7span : localSpan d.Z d.Y = d.V) :
    I ⊓ centralizer (d.UI I : Set G) ≤ d.MI I := by
  exact centralizer_localSpan_le_intersection d.Z d.Yplus I d.M d.V₂
    (le_sup_left.trans hI.1.2) (second_choice_plane_le_span d hsecond h7image h7span)
    (second_choice_normalizers d hsecond h7image).2.1

/-- Clause (4) in the second choice. Relative normality of Y in M and the
proved residual equality supply normalization by M ∩ I. -/
theorem second_choice_normalizer_eq (d : CharacteristicTwo.LocalData G)
    (I : Subgroup G) (hI : I ∈ d.Hplus) (hsecond : SecondChoice d)
    (h7image : d.action.image d.Y = twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (hodd : IsPGroup 3 (d.Y ⧸ pCore 2 d.Y)) :
    I ⊓ normalizer (d.Yplus : Set G) = d.MI I := by
  exact normalizer_in_eq_of_intersection_residual d.Yplus d.Y d.M I
    (m_normalizes_y d) (second_choice_intersection_residual d I hI hsecond h7image hodd)
    (second_choice_normalizers d hsecond h7image).2.2

end CFSG.Quasithin.Chapter15.Section03.OutsideStructure.LocalBranches
end
