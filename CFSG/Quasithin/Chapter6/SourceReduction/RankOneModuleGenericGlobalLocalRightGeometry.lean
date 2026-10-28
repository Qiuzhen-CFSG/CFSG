module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalLocalCharacteristic
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalLocalCartan
public import Theory.GroupTheory.Hall.TwoClosedNormal

/-!
# Cartan geometry from the source family of right factors

The source selects either a C-component or the C-component of one of two
rank-one parabolics. This module proves the common argument once that
family is constructed. Its invariance under the residual Sylow normalizer
makes both odd Cartans fix every member. The two-closed residual overlap
identifies its two-core with T ∩ K and hence S ∩ R with T ∩ R. Hall
restriction to the marked Borel then gives the literal product with B ∩ R.
Generation with T supplies escape from N_G(L).

`RightGeometry` is an explicit intermediate construction contract, not a
proof of source selection. Its Bender and diagram constructors remain
separate obligations. In particular the actual quotient by O₂(R), and
S-normalization in the non-PSL₃(4) branch, must be proved by those producers.
The Chapter 12 extension applies the common argument to the actual
`rankOne_global_preparation_of_rightFactor` consumer.

Source: Aschbacher--Smith, 5.1.10--11, the selection preceding 5.2.1,
and 5.2.4, printed pp.634--635,646,649--650 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G] [Finite G]

/-- The component/parabolic family before either odd Cartan is chosen.
The quotients and Borel overlaps are literal ambient subgroups. -/
structure RightGeometry (T : Sylow 2 G) (L H : Subgroup G)
    (ℛ : Set (Subgroup G)) : Prop where
  nonempty : ℛ.Nonempty
  small : ℛ.ncard ≤ 2
  two_closed : normalizer (L : Set G) ⊓ residual H ≤
    normalizer (((T : Subgroup G) ⊓ residual H : Subgroup G) : Set G)
  invariant : ∀ g : G, g ∈ normalizer (residual H : Set G) →
    g ∈ normalizer (((T : Subgroup G) ⊓ residual H : Subgroup G) : Set G) →
    ∀ R ∈ ℛ, R.map (MulAut.conj g).toMonoidHom ∈ ℛ
  le_residual : ∀ R ∈ ℛ, R ≤ residual H
  generates : ∀ R ∈ ℛ, R ⊔ (T : Subgroup G) = H
  sylow : ∀ R ∈ ℛ, ∃ P : Sylow 2 R,
    (P : Subgroup R).map R.subtype = (T : Subgroup G) ⊓ R
  quotient : ∀ R ∈ ℛ, ChapterF.Source.IsRankOneModel (R ⧸ pCore 2 R)
  S_normalizes : ∀ R ∈ ℛ, sourceS L H ≤ normalizer (R : Set G)
  overlap : ∀ R ∈ ℛ, ChapterF.Source.borel R (T : Subgroup G) =
    normalizer (L : Set G) ⊓ R

private theorem odd_normalizes_of_small_family {A R : Subgroup G}
    {ℛ : Set (Subgroup G)} (ho : Odd (Nat.card A)) (hc : ℛ.ncard ≤ 2)
    (hR : R ∈ ℛ)
    (hi : ∀ a : A, ∀ Q ∈ ℛ, Q.map (MulAut.conj (a : G)).toMonoidHom ∈ ℛ) :
    A ≤ normalizer (R : Set G) := by
  let : MulAction A (Subgroup G) :=
    MulAction.compHom (Subgroup G) ((MulAut.conj : G →* MulAut G).comp A.subtype)
  have hsub : MulAction.orbit A R ⊆ ℛ := by
    rintro Q ⟨a, rfl⟩
    exact hi a R hR
  have hb : (MulAction.stabilizer A R).index ≤ 2 := by
    rw [MulAction.index_stabilizer]
    exact (Set.ncard_le_ncard hsub).trans hc
  have hod : Odd (MulAction.stabilizer A R).index :=
    ho.of_dvd_nat (MulAction.stabilizer A R).index_dvd_card
  have he : (MulAction.stabilizer A R).index = 1 := by
    have hp := (MulAction.stabilizer A R).index_ne_zero_of_finite
    have hn := hod.not_two_dvd_nat
    omega
  have ht := Subgroup.index_eq_one.mp he
  intro a ha
  apply mem_normalizer_iff_map_conj_eq.mpr
  exact show (⟨a, ha⟩ : A) ∈ MulAction.stabilizer A R from ht ▸ mem_top _

variable {T : Sylow 2 G} {L H : Subgroup G} {ℛ : Set (Subgroup G)}

/-- The source two-closed residual overlap has exactly the prescribed Sylow as its core. -/
theorem RightGeometry.residual_core (d : RightGeometry T L H ℛ)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hTH : (T : Subgroup G) ≤ H) :
    (normalizer (L : Set G) ⊓ residual H : Subgroup G).pCoreIn 2 =
      (T : Subgroup G) ⊓ residual H := by
  have hTKM : (T : Subgroup G) ⊓ residual H ≤ normalizer (L : Set G) ⊓ residual H :=
    le_inf (inf_le_left.trans hTL) inf_le_right
  obtain ⟨P, hP⟩ := exists_sylow_component (hTH.trans (le_normalizer_residual H))
  obtain ⟨Q,hQ⟩ := P.exists_map_subtype_eq_of_le
    (show normalizer (L : Set G) ⊓ residual H ≤ residual H from inf_le_right)
    (hP ▸ hTKM)
  exact le_antisymm ((pCoreIn_le_sylow _ Q).trans_eq (hQ.trans hP))
    (le_pCoreIn_of_normalizes (T.isPGroup'.to_le inf_le_left) hTKM d.two_closed)

/-- Characteristic control in the overlap proves the original 5.1.11(1) intersection. -/
theorem RightGeometry.sourceS_intersection_residual (d : RightGeometry T L H ℛ)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hTH : (T : Subgroup G) ≤ H) :
    sourceS L H ⊓ residual H = (T : Subgroup G) ⊓ residual H := by
  have hnorm : intersection L H ≤
      normalizer ((normalizer (L : Set G) ⊓ residual H : Subgroup G) : Set G) :=
    (le_inf (inf_le_left.trans (normalizer (L : Set G)).le_normalizer)
      (inf_le_right.trans (le_normalizer_residual H))).trans inf_normalizer_le_normalizer_inf
  have hnorm' := hnorm.trans (normalizer_le_normalizer_characteristic_image
    (normalizer (L : Set G) ⊓ residual H) (pCore 2 (normalizer (L : Set G) ⊓ residual H : Subgroup G)))
  change intersection L H ≤
    normalizer ((normalizer (L : Set G) ⊓ residual H : Subgroup G).pCoreIn 2 : Set G) at hnorm'
  rw [d.residual_core hTL hTH] at hnorm'
  have hle : (T : Subgroup G) ⊓ residual H ≤ sourceS L H :=
    le_pCoreIn_of_normalizes (T.isPGroup'.to_le inf_le_left)
      (le_inf (inf_le_left.trans hTL) (inf_le_left.trans hTH)) hnorm'
  exact le_antisymm (inf_le_inf_right _ (sourceS_le_sylow hTL hTH)) (le_inf hle inf_le_right)

/-- Restrict the residual intersection to the selected source factor. -/
theorem RightGeometry.sourceS_intersection (d : RightGeometry T L H ℛ)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hTH : (T : Subgroup G) ≤ H) {R : Subgroup G} (hR : R ∈ ℛ) :
    sourceS L H ⊓ R = (T : Subgroup G) ⊓ R := by
  calc
    sourceS L H ⊓ R = (sourceS L H ⊓ residual H) ⊓ R := by
      rw [inf_assoc, inf_eq_right.mpr (d.le_residual R hR)]
    _ = ((T : Subgroup G) ⊓ residual H) ⊓ R := by rw [d.sourceS_intersection_residual hTL hTH]
    _ = (T : Subgroup G) ⊓ R := by rw [inf_assoc, inf_eq_right.mpr (d.le_residual R hR)]

/-- The odd Hall subgroup lies in O²(H), since its image in the two-quotient is trivial. -/
theorem right_cartan_le_residual {A B : Subgroup G} (c : CartanPair T L H A B) :
    B ≤ residual H := by
  have ho : Odd (Nat.card B) := by
    rw [← Nat.card_congr (subgroupOfEquivOfLe c.right_le).toEquiv]
    exact OddHall.odd_hall_odd c.right_hall
  have hBH := c.right_le.trans inf_le_right
  have ho' : Odd (Nat.card (B.subgroupOf H)) := by
    rwa [Nat.card_congr (subgroupOfEquivOfLe hBH).toEquiv]
  have hh := OddHall.odd_subgroup_le (pResidual 2 H) (B.subgroupOf H)
    (isPGroup_quotient_pResidual 2) ho'
  have hm := map_mono (f := H.subtype) hh
  rwa [map_subgroupOf_eq_of_le hBH] at hm

/-- An odd Cartan cannot interchange the at most two source factors.
Characteristic control of T ∩ K puts the left Cartan in the family stabilizer. -/
theorem RightGeometry.cartans_normalize {A B : Subgroup G}
    (d : RightGeometry T L H ℛ) (c : CartanPair T L H A B)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hTH : (T : Subgroup G) ≤ H)
    (hN : localBorel T L ≤ normalizer (residual H : Set G))
    {R : Subgroup G} (hR : R ∈ ℛ) :
    A ≤ normalizer (R : Set G) ∧ B ≤ normalizer (R : Set G) := by
  have hAM : A ≤ normalizer (L : Set G) := (c.left_le.trans inf_le_left).trans L.le_normalizer
  have hAK : A ≤ normalizer (residual H : Set G) := c.left_le.trans hN
  have hAMK := (le_inf (hAM.trans (normalizer (L : Set G)).le_normalizer) hAK).trans
    inf_normalizer_le_normalizer_inf
  have hATK := hAMK.trans (normalizer_le_normalizer_characteristic_image
    (normalizer (L : Set G) ⊓ residual H) (pCore 2 (normalizer (L : Set G) ⊓ residual H : Subgroup G)))
  change A ≤
    normalizer ((normalizer (L : Set G) ⊓ residual H : Subgroup G).pCoreIn 2 : Set G) at hATK
  rw [d.residual_core hTL hTH] at hATK
  have hBTK := (le_inf (c.right_le.trans inf_le_left) (right_cartan_le_residual c)).trans d.two_closed
  constructor
  · refine odd_normalizes_of_small_family (ℛ := ℛ) ?_ d.small hR ?_
    · rw [← Nat.card_congr (subgroupOfEquivOfLe c.left_le).toEquiv]
      exact OddHall.odd_hall_odd c.left_hall
    · intro a Q hQ
      exact d.invariant a (hAK a.property) (hATK a.property) Q hQ
  · refine odd_normalizes_of_small_family (ℛ := ℛ) ?_ d.small hR ?_
    · rw [← Nat.card_congr (subgroupOfEquivOfLe c.right_le).toEquiv]
      exact OddHall.odd_hall_odd c.right_hall
    · intro b Q hQ
      exact d.invariant b ((c.right_le.trans inf_le_right).trans (le_normalizer_residual H) b.property)
        (hBTK b.property) Q hQ

/-- Hall restriction computes the literal Borel product; generation proves escape.
This consumes a constructed source family, whose model fields remain explicit. -/
theorem RightGeometry.rightFactor {A B R : Subgroup G}
    (d : RightGeometry T L H ℛ) (c : CartanPair T L H A B)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hN : localBorel T L ≤ normalizer (residual H : Set G)) (hR : R ∈ ℛ) :
    RightFactor T L H A B R := by
  obtain ⟨hAN,hBN⟩ := d.cartans_normalize c hTL hH.1.1.2 hN hR
  have hSR := d.sourceS_intersection hTL hH.1.1.2 hR
  have hb : ChapterF.Source.borel R (sourceS L H) = normalizer (L : Set G) ⊓ R := by
    unfold ChapterF.Source.borel
    rw [hSR]
    exact d.overlap R hR
  refine ⟨d.le_residual R hR, ?_, ?_, d.quotient R hR, d.S_normalizes R hR, hAN, ?_⟩
  · intro hRM
    exact hH.1.2 ((d.generates R hR) ▸ sup_le hRM hTL)
  · rw [hSR]
    exact d.sylow R hR
  · let U := normalizer (L : Set G) ⊓ R
    have hRU : R ≤ H := (d.le_residual R hR).trans (map_subtype_le _)
    have hU : U ≤ intersection L H := le_inf inf_le_left (inf_le_right.trans hRU)
    have hBU : B ≤ normalizer (U : Set G) :=
      (le_inf ((c.right_le.trans inf_le_left).trans (normalizer (L : Set G)).le_normalizer)
        hBN).trans inf_normalizer_le_normalizer_inf
    have hh := OddHall.hall_restrict_of_normalizes c.right_hall c.right_le hU hBU
    obtain ⟨P,hP⟩ := d.sylow R hR
    obtain ⟨Q,hQ⟩ := P.exists_map_subtype_eq_of_le (show U ≤ R from inf_le_right)
      (hP ▸ le_inf (inf_le_left.trans hTL) inf_le_right)
    have he := congrArg (Subgroup.map U.subtype) (OddHall.sylow_complement_of_hall Q hh).sup_eq_top
    have hi : B ⊓ U = B ⊓ R := by
      dsimp [U]
      rw [← inf_assoc, inf_eq_left.mpr (c.right_le.trans inf_le_left)]
    rw [Subgroup.map_sup, hQ, hP, subgroupOf_map_subtype, hi,
      ← MonoidHom.range_eq_map, range_subtype] at he
    rw [hb, hSR]
    exact he.symm

/-- Any source family supplies the right factor for every compatible Cartan pair. -/
theorem RightGeometry.exists_rightFactor {A B : Subgroup G}
    (d : RightGeometry T L H ℛ) (c : CartanPair T L H A B)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hN : localBorel T L ≤ normalizer (residual H : Set G)) :
    ∃ R : Subgroup G, RightFactor T L H A B R := by
  obtain ⟨R,hR⟩ := d.nonempty
  exact ⟨R,d.rightFactor c hTL hH hN hR⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
