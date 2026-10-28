module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.LocalGeometry.SecondCentralizer.Recognition.Contracts
public import CFSG.Quasithin.ChapterI.Section04To05.Dihedral.BSWSetup
public import CFSG.Quasithin.ChapterI.Section04To05.Dihedral.SmallBranch
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Recognition of the transfer kernel as A₄ or A₅

The embedded C₂ × S₄ contains an ambient Sylow two-subgroup because both
Sylow orders are sixteen. Its index is therefore odd. In a proposed normal
index-four transfer kernel, the embedded A₄ likewise has odd index.
Consequently every kernel involution conjugates into that A₄, whose explicit
cubic action fuses all three involutions.

The seed's centralizer containment and the exact local intersection identify
the literal involution centralizer with the embedded Klein four-group. The
checked dihedral-centralizer/BSW argument now recognizes the kernel as A₄
or A₅. No simplicity, ambient order, or classification alternative is assumed.

Source: Aschbacher, “A 2-local characterization of M12”, Illinois J. Math.
47 (2003), 31–47, Lemma 4.2.
-/

@[expose] public section
namespace CFSG.Quasithin.Extraspecial32.DegreeTwelve.SecondCentralizer
open Subgroup Equiv Equiv.Perm
variable {G : Type*} [Group G] [Finite G] {z t : G}

omit [Finite G] in
theorem LocalSeed.range_card (s : LocalSeed z t) : Nat.card s.embed.range = 48 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective s.injective).toEquiv]
  norm_num [Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]

theorem LocalSeed.exists_sylow_le_range (s : LocalSeed z t) :
    ∃ T : Sylow 2 (Centralizer t), (T : Subgroup (Centralizer t)) ≤ s.embed.range := by
  let S : Sylow 2 (Model 4) := Sylow.nonempty.some
  have hS : Nat.card S = 16 := by
    rw [Sylow.card_eq_multiplicity]
    have hc : Nat.card (Model 4) = 48 := by
      norm_num [Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
    rw [hc, show 48 = 2 ^ 4 * 3 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Nat.factorization_pow]
    norm_num [Nat.prime_two.factorization, Nat.prime_three.factorization]
  obtain ⟨T, hT⟩ := (S.isPGroup'.map s.embed).exists_le_sylow
  have he : (S : Subgroup (Model 4)).map s.embed = (T : Subgroup (Centralizer t)) :=
    Subgroup.eq_of_le_of_card_ge hT (by rw [Subgroup.card_map_of_injective s.injective,
      hS, s.sylow_card T])
  exact ⟨T, he ▸ Subgroup.map_le_range _ _⟩

theorem LocalSeed.range_index_odd (s : LocalSeed z t) : Odd s.embed.range.index := by
  obtain ⟨T, hT⟩ := s.exists_sylow_le_range
  exact Nat.not_even_iff_odd.mp (fun he =>
    T.not_dvd_index ((even_iff_two_dvd.mp he).trans (index_dvd_of_le hT)))

private theorem conjugate_into_of_odd_index {H : Type*} [Group H] [Finite H]
    (L : Subgroup H) (hL : Odd L.index) (a : H) (ha : orderOf a = 2) :
    ∃ k : H, k * a * k⁻¹ ∈ L := by
  let Q : Sylow 2 L := Sylow.nonempty.some
  let R : Subgroup H := (Q : Subgroup L).map L.subtype
  have hpR : IsPGroup 2 R := Q.isPGroup'.map L.subtype
  have hR : ¬ 2 ∣ R.index := by
    rw [show R.index = (Q : Subgroup L).index * L.index from index_map_subtype _]
    exact Nat.prime_two.not_dvd_mul Q.not_dvd_index hL.not_two_dvd_nat
  let T : Sylow 2 H := hpR.toSylow hR
  have hp : IsPGroup 2 (zpowers a) := IsPGroup.of_card (n := 1)
    (by rw [Nat.card_zpowers, ha, pow_one])
  obtain ⟨U, hU⟩ := hp.exists_le_sylow
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq H U T
  refine ⟨k, (map_subtype_le (Q : Subgroup L)) ?_⟩
  change k * a * k⁻¹ ∈ (T : Subgroup H)
  rw [← hk]
  exact ⟨a, hU (mem_zpowers a), rfl⟩

theorem LocalSeed.involution_conjugate_into_range (s : LocalSeed z t)
    (a : Centralizer t) (ha : orderOf a = 2) :
    ∃ x : Model 4, IsConj a (s.embed x) := by
  obtain ⟨k, hk⟩ := conjugate_into_of_odd_index s.embed.range s.range_index_odd a ha
  obtain ⟨x, hx⟩ := hk
  exact ⟨x, isConj_iff.mpr ⟨k, hx.symm⟩⟩

namespace TransferKernel
variable {s : LocalSeed z t} (d : TransferKernel s)

def evenMap : A4 →* d.K :=
  (s.embed.comp evenEmbed).codRestrict d.K (fun a =>
    (d.local_mem (evenEmbed a)).mpr ⟨rfl, mem_alternatingGroup.mp a.property⟩)

omit [Finite G] in
theorem evenMap_injective : Function.Injective d.evenMap := by
  intro a b h
  exact evenEmbed_injective (s.injective (congrArg Subtype.val h))

omit [Finite G] in
theorem evenMap_range_card : Nat.card d.evenMap.range = 12 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective d.evenMap_injective).toEquiv]
  exact alternatingGroup.card_of_card_eq_four (by simp)

theorem evenMap_range_index_odd : Odd d.evenMap.range.index := by
  let T : Sylow 2 (Centralizer t) := Sylow.nonempty.some
  have hT := (T : Subgroup (Centralizer t)).card_mul_index
  rw [s.sylow_card T] at hT
  have hA := d.evenMap.range.card_mul_index
  rw [d.evenMap_range_card] at hA
  have hK := d.K.card_mul_index
  rw [d.index] at hK
  have he : 3 * d.evenMap.range.index = (T : Subgroup (Centralizer t)).index := by
    nlinarith
  apply Nat.not_even_iff_odd.mp
  intro hh
  apply T.not_dvd_index
  rw [← he]
  exact (even_iff_two_dvd.mp hh).mul_left 3

theorem involutions_conjugate (a : d.K) (ha : orderOf a = 2) :
    IsConj a (d.evenMap evenInvolution) := by
  obtain ⟨k, hk⟩ := conjugate_into_of_odd_index d.evenMap.range d.evenMap_range_index_odd a ha
  obtain ⟨b, hb⟩ := hk
  have hab : IsConj a (d.evenMap b) := isConj_iff.mpr ⟨k, hb.symm⟩
  have hb2 : orderOf b = 2 :=
    (orderOf_injective d.evenMap d.evenMap_injective b).symm.trans
      ((conjugate_order hab).symm.trans ha)
  obtain ⟨j, hj⟩ := even_cubic_fusion b hb2
  exact hab.trans (d.evenMap.map_isConj (isConj_iff.mpr ⟨evenCycle ^ j.val, hj⟩))

def centralizerMap : centralizer ({evenInvolution} : Set A4) →*
    centralizer ({d.evenMap evenInvolution} : Set d.K) where
  toFun a := ⟨d.evenMap a, mem_centralizer_singleton_iff.mpr (by
    simpa only [map_mul] using congrArg d.evenMap (mem_centralizer_singleton_iff.mp a.property))⟩
  map_one' := Subtype.ext d.evenMap.map_one
  map_mul' a b := Subtype.ext (d.evenMap.map_mul a b)

omit [Finite G] in
theorem centralizerMap_bijective : Function.Bijective d.centralizerMap := by
  refine ⟨fun a b h => Subtype.ext (d.evenMap_injective (congrArg Subtype.val h)), ?_⟩
  intro x
  have hxC : ((x : d.K) : Centralizer t) ∈
      centralizer ({s.embed (evenEmbed evenInvolution)} : Set (Centralizer t)) := by
    apply mem_centralizer_singleton_iff.mpr
    exact congrArg Subtype.val (mem_centralizer_singleton_iff.mp x.property)
  obtain ⟨m, hm⟩ := s.centralizer_le _ evenEmbed_first hxC
  have hmK : s.embed m ∈ d.K := hm.symm ▸ (x : d.K).property
  have hmark := (d.local_mem m).mp hmK
  let a : A4 := ⟨m.2, mem_alternatingGroup.mpr hmark.2⟩
  have hea : evenEmbed a = m := Prod.ext hmark.1.symm rfl
  have he : d.evenMap a = (x : d.K) := Subtype.ext (by
    change s.embed (evenEmbed a) = _
    rw [hea, hm])
  have haC : a ∈ centralizer ({evenInvolution} : Set A4) := by
    apply mem_centralizer_singleton_iff.mpr
    apply d.evenMap_injective
    rw [map_mul, map_mul, he]
    exact mem_centralizer_singleton_iff.mp x.property
  exact ⟨⟨a, haC⟩, Subtype.ext he⟩

omit [Finite G] in
theorem centralizer_equiv : Nonempty
    (centralizer ({d.evenMap evenInvolution} : Set d.K) ≃* DihedralGroup 2) := by
  obtain ⟨e⟩ := even_centralizer_equiv
  exact ⟨(MulEquiv.ofBijective d.centralizerMap d.centralizerMap_bijective).symm.trans e⟩

/-- The source four-group, with its original inclusion in the local A₄. -/
def fourGroup : Subgroup d.K := (alternatingGroup.kleinFour (Fin 4)).map d.evenMap

omit [Finite G] in
theorem centralizer_eq_fourGroup :
    centralizer ({d.evenMap evenInvolution} : Set d.K) = d.fourGroup := by
  ext x
  constructor
  · intro hx
    obtain ⟨a, ha⟩ := d.centralizerMap_bijective.2 ⟨x, hx⟩
    exact mem_map.mpr ⟨a, even_centralizer ▸ a.property, congrArg Subtype.val ha⟩
  · rintro ⟨a, ha, rfl⟩
    rw [← even_centralizer] at ha
    exact (d.centralizerMap ⟨a, ha⟩).property

omit [Finite G] in
theorem fourGroup_isKleinFour : IsKleinFour d.fourGroup := by
  let e := (alternatingGroup.kleinFour (Fin 4)).equivMapOfInjective
    d.evenMap d.evenMap_injective
  exact ⟨(Nat.card_congr e.toEquiv).symm.trans
      (alternatingGroup.kleinFour_card_of_card_eq_four (by simp)),
    (Monoid.exponent_eq_of_mulEquiv e).symm.trans
      (alternatingGroup.exponent_kleinFour_of_card_eq_four (by simp))⟩

/-- The literal centralizer and fused involutions satisfy the checked BSW input. -/
def involutionCentralizerData : DihedralInvolutionCentralizerHypotheses d.K 2 := by
  have hi : orderOf (d.evenMap evenInvolution) = 2 :=
    (orderOf_injective d.evenMap d.evenMap_injective _).trans evenInvolution_order
  exact
    { two_le := le_rfl
      z := d.evenMap evenInvolution
      involution := ⟨fun he => by simp [he] at hi, hi ▸ pow_orderOf_eq_one _⟩
      involutions_conjugate := fun u hu =>
        isConj_iff.mp (d.involutions_conjugate u (orderOf_eq_prime hu.2 hu.1))
      centralizer_equiv := d.centralizer_equiv }

theorem fourGroup_isSylow : ∃ S : Sylow 2 d.K, (S : Subgroup d.K) = d.fourGroup := by
  obtain ⟨S, hS⟩ := d.involutionCentralizerData.centralizer_isSylow
  exact ⟨S, hS.trans d.centralizer_eq_fourGroup⟩

theorem alternating_four_or_five :
    Nonempty (d.K ≃* alternatingGroup (Fin 4)) ∨
    Nonempty (d.K ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨b, _, _, hb⟩ := d.involutionCentralizerData.exists_brauerSuzukiWallHypotheses
  exact alternating_four_or_five_of_bsw_card_two b (by simpa using hb)
end TransferKernel

end CFSG.Quasithin.Extraspecial32.DegreeTwelve.SecondCentralizer
end
