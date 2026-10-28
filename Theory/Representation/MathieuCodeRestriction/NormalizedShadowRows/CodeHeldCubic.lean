module
public import Theory.SpecificGroups.Held.CubicCentralizers.Terminal
public import Theory.SpecificGroups.Held.TwoLocalCandidates.ThreeCoreBounds
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue
public import Theory.SpecificGroups.Held.TwoPartDivisibility
public import Theory.GroupTheory.FourGroupNormalizerIndex
public import Theory.GroupTheory.SylowContainingTwoLocal
public import Theory.Quasithin.EvenCharacteristic
public import Theory.GroupTheory.CoprimeSubgroupCentralizer
public import Theory.GroupTheory.PCoreFrattiniTransport
public import Theory.GroupTheory.PrimeOrderLift

/-!
# A controlled cubic cannot occur in a Held covering section

The native cubic fusion and centralizing-seven witnesses imply that every
cubic centralizer in Held has order divisible by seven. The full-Sylow
maximal two-local catalogue shows that no such two-local has both five and
seven in its order. Thus a Sylow-normalized subgroup with a factor five,
whose normalizer contains a cubic centralizer, has trivial two-core.

If its two-core quotient has center of order three, this is impossible:
the Sylow centralizes that center with index at most two, forcing 960 to
divide a cubic centralizer order, contrary to the native Held calculation.
Coprime centralizer lifting carries the obstruction through an arbitrary
surjection with two-group kernel, retaining the full smaller core quotient.

Source application: Aschbacher--Smith 8.2.2(1), printed p.715. Native
facts retain the ATLAS HeG1 and GLS3 Table 5.3p attribution in their imports.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace MathieuCode.NormalizedShadowRows
open Held.LocalPairs.PairCoverage Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner

theorem held_cubic_centralizer_seven (x : Held.He) (hx : orderOf x = 3) :
    7 ∣ Nat.card (centralizer ({x} : Set Held.He)) := by
  have seed (u : Held.He) (hs : ∃ y : Held.He, orderOf y = 7 ∧ Commute y u)
      (hc : IsConj u x) : 7 ∣ Nat.card (centralizer ({x} : Set Held.He)) := by
    obtain ⟨y,hy,hcY⟩ := hs
    obtain ⟨g,hg⟩ := isConj_iff.mp hc
    let e := MulAut.conj g
    have he : e u = x := hg
    have hm : e y ∈ centralizer ({x} : Set Held.He) := by
      rw [mem_centralizer_singleton_iff,←he]
      simpa only [map_mul] using congrArg e hcY.eq
    have hd := orderOf_dvd_natCard (⟨e y,hm⟩ : centralizer ({x} : Set Held.He))
    rwa [←orderOf_coe,e.orderOf_eq,hy] at hd
  rcases Held.CubicCentralizers.cubic_fusion x hx with h | h
  · exact seed _ Held.CubicCentralizers.exists_seven_centralizing_x h
  · exact seed _ Held.CubicCentralizers.exists_seven_centralizing_z h

private theorem max34_seven_free (i : Bool) : ¬ 7 ∣ Nat.card (localOvergroup i) := by
  let f := SixPoint.quotientAction i
  have hk : ¬ 7 ∣ Nat.card f.ker := fun h =>
    (by decide : ¬ 7 ∣ 3) (h.trans (Held.TwoLocalCandidates.ThreeCoreBounds.quotientAction_kernel_card_dvd_three i))
  have hi : ¬ 7 ∣ Nat.card f.range := by
    intro h
    have hh := h.trans f.range.card_subgroup_dvd_card
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm] at hh
  have hquot : ¬ 7 ∣ Nat.card (LocalQuotient i) := by
    rw [←f.ker.card_mul_index,index_ker]
    exact fun h => ((by decide : Nat.Prime 7).dvd_mul.mp h).elim hk hi
  obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := localOvergroup i)).exists_card_eq
  rw [←(pCore 2 (localOvergroup i)).card_mul_index,index_eq_card,hn]
  intro h
  rcases (by decide : Nat.Prime 7).dvd_mul.mp h with h | h
  · exact (by decide : ¬ 7 ∣ 2) ((by decide : Nat.Prime 7).dvd_of_dvd_pow h)
  · exact hquot h

theorem held_twoLocal_not_five_and_seven (S : Sylow 2 Held.He) (M : Subgroup Held.He)
    (hM : IsTwoLocal M) (hSM : (S : Subgroup Held.He) ≤ M)
    (h5 : 5 ∣ Nat.card M) (h7 : 7 ∣ Nat.card M) : False := by
  obtain ⟨T,hcatalogue⟩ := Held.TwoLocalCandidates.MaximalNormalizerCatalogue.exists_sylow_catalogue
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq Held.He S T
  let a := MulAut.conj g
  have hT : (T : Subgroup Held.He) ≤ M.map a.toMonoidHom := by
    have hh := map_mono (f := a.toMonoidHom) hSM
    change ((g • S : Sylow 2 Held.He) : Subgroup Held.He) ≤ _ at hh
    rwa [hg] at hh
  obtain ⟨N,hMN,hN⟩ := Finite.exists_le_maximal (Theory.Quasithin.isTwoLocal_map a hM)
  obtain ⟨R,hR,hRn,hRe,hNR⟩ := exists_normal_elementary_normalizer_of_sylow_le T hN (hT.trans hMN)
  obtain ⟨i,k,hk⟩ := hcatalogue R hR hRn hRe (hNR ▸ hN)
  have hd (p : ℕ) (hp : p ∣ Nat.card M) : p ∣ Nat.card (Held.TwoLocalCandidates.subgroup i) := by
    have hdN : p ∣ Nat.card N :=
      (by rwa [card_map_of_injective a.injective] : p ∣ Nat.card (M.map a.toMonoidHom)).trans
        (card_dvd_of_le hMN)
    rwa [hNR,hk,card_map_of_injective (MulAut.conj k).injective] at hdN
  fin_cases i
  · exact max34_seven_free false (hd 7 h7)
  · exact max34_seven_free true (hd 7 h7)
  · have hh := hd 5 h5
    change 5 ∣ Nat.card Held.TwoLocalCandidates.max5 at hh
    rw [Held.InvolutionFixedData.TwoB.max5_card] at hh
    norm_num at hh

theorem held_not_normalized_cubic_center (S : Sylow 2 Held.He) (B : Subgroup Held.He)
    (hn : (S : Subgroup Held.He) ≤ normalizer (B : Set Held.He))
    (h5 : 5 ∣ Nat.card B) (hZ : Nat.card (center B) = 3) : False := by
  let Z := (center B).map B.subtype
  have hZc : Nat.card Z = 3 := (card_map_of_injective B.subtype_injective).trans hZ
  have hSN : (S : Subgroup Held.He) ≤ normalizer (Z : Set Held.He) :=
    hn.trans (normalizer_le_normalizer_characteristic_image B (center B))
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' 3 (show 3 ∣ Nat.card Z by rw [hZc])
  have hxo : orderOf (x : Held.He) = 3 := (orderOf_coe x).trans hx
  have hx1 : (x : Held.He) ≠ 1 := by intro hh; simp only [hh,orderOf_one] at hxo; omega
  let C := centralizer ({(x : Held.He)} : Set Held.He)
  have hBC : B ≤ C := by
    obtain ⟨z,hz,hzx⟩ := x.property
    intro b hb
    rw [mem_centralizer_singleton_iff,←hzx]
    exact congrArg Subtype.val ((mem_center_iff.mp hz) ⟨b,hb⟩)
  have h3 : 3 ∣ Nat.card B := by
    rw [←hZ]
    exact card_subgroup_dvd_card _
  have h15 : 15 ∣ Nat.card C :=
    ((by decide : Nat.Coprime 3 5).mul_dvd_of_dvd_of_dvd h3 h5).trans (card_dvd_of_le hBC)
  have hi : C.relIndex (S : Subgroup Held.He) ≤ 2 := by
    have hh := centralizer_relIndex_le_card_sub_one (S : Subgroup Held.He) Z hSN x x.property hx1
    simpa only [hZc] using hh
  have hi0 : 0 < C.relIndex (S : Subgroup Held.He) := Nat.pos_of_ne_zero index_ne_zero_of_finite
  have hS := S.pow_dvd_card_of_pow_dvd_card (n := 10) Held.two_pow_ten_dvd_card
  have hcard := (C.subgroupOf S).card_mul_index
  change Nat.card (C.subgroupOf S) * C.relIndex S = Nat.card S at hcard
  have h512 : 512 ∣ Nat.card (C.subgroupOf S) := by
    have he : C.relIndex S = 1 ∨ C.relIndex S = 2 := by omega
    rcases he with he | he
    · rw [he,mul_one] at hcard
      exact (by decide : 512 ∣ 2^10).trans (hcard.symm ▸ hS)
    · rw [he] at hcard
      apply Nat.dvd_of_mul_dvd_mul_right (k := 2) (by decide)
      change 1024 ∣ Nat.card (C.subgroupOf S) * 2
      rw [hcard]
      exact hS
  let j : C.subgroupOf S →* C := {
    toFun y := ⟨y.val.val,y.property⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hj : Function.Injective j := fun a b he => Subtype.ext (Subtype.ext (congrArg (fun c : C => (c : Held.He)) he))
  have h64 : 64 ∣ Nat.card C :=
    ((by decide : 64 ∣ 512).trans h512).trans (Subgroup.card_dvd_of_injective j hj)
  exact Held.CubicCentralizers.not_960_dvd_centralizer x hxo
    ((by decide : Nat.Coprime 64 15).mul_dvd_of_dvd_of_dvd h64 h15)

theorem held_controlled_cubic_obstruction (S : Sylow 2 Held.He) (B : Subgroup Held.He)
    (hn : (S : Subgroup Held.He) ≤ normalizer (B : Set Held.He))
    (h5 : 5 ∣ Nat.card B) (hZ : Nat.card (center (B ⧸ pCore 2 B)) = 3)
    (x : Held.He) (hx : orderOf x = 3)
    (hC : centralizer ({x} : Set Held.He) ≤ normalizer (B : Set Held.He)) : False := by
  by_cases hb : pCore 2 B = ⊥
  · let e : (B ⧸ pCore 2 B) ≃* B :=
      (QuotientGroup.quotientMulEquivOfEq hb).trans QuotientGroup.quotientBot
    exact held_not_normalized_cubic_center S B hn h5
      ((Nat.card_congr (centerCongr e).toEquiv).symm.trans hZ)
  · let U := (pCore 2 B).map B.subtype
    have hU : U ≠ ⊥ := fun he => hb ((map_eq_bot_iff_of_injective _ B.subtype_injective).mp he)
    have hloc : IsTwoLocal (normalizer (U : Set Held.He)) :=
      ⟨U,hU,pCore_isPGroup.map B.subtype,rfl⟩
    have hnorm := normalizer_le_normalizer_characteristic_image B (pCore 2 B)
    exact held_twoLocal_not_five_and_seven S (normalizer (U : Set Held.He)) hloc
      (hn.trans hnorm) (h5.trans (card_dvd_of_le (B.le_normalizer.trans hnorm)))
      ((held_cubic_centralizer_seven x hx).trans (card_dvd_of_le (hC.trans hnorm)))

theorem controlled_cubic_cover_not_held
    {G : Type*} [Group G] [Finite G]
    (q : G →* Held.He) (hq : Function.Surjective q) (hk : IsPGroup 2 q.ker)
    (S : Sylow 2 G) (B : Subgroup G)
    (hn : (S : Subgroup G) ≤ normalizer (B : Set G))
    (h5 : 5 ∣ Nat.card (B ⧸ pCore 2 B))
    (hZ : Nat.card (center (B ⧸ pCore 2 B)) = 3)
    (x : G) (hx : orderOf x = 3)
    (hC : centralizer ({x} : Set G) ≤ normalizer (B : Set G)) : False := by
  let A := B.map q
  have hbk : IsPGroup 2 (q.subgroupMap B).ker := by
    rw [ker_subgroupMap]
    exact hk.comap_subtype
  let e := (q.subgroupMap B).pCoreQuotientEquiv (q.subgroupMap_surjective B) hbk
  have h5A : 5 ∣ Nat.card A := by
    rw [Nat.card_congr e.toEquiv] at h5
    exact h5.trans (card_quotient_dvd_card _)
  have hZA : Nat.card (center (A ⧸ pCore 2 A)) = 3 :=
    (Nat.card_congr (centerCongr e).toEquiv).symm.trans hZ
  have hp : IsPGroup 3 (zpowers x) := IsPGroup.of_card (n := 1)
    (by rw [Nat.card_zpowers,hx]; norm_num)
  have hcop : Nat.Coprime 3 (Nat.card q.ker) := by
    obtain ⟨n,hn⟩ := hk.exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  have hmap := map_centralizer_eq_of_isPGroup_of_surjective_coprime 3 (zpowers x) hp q hq hcop
  rw [MonoidHom.map_zpowers] at hmap
  simp only [zpowers_eq_closure,centralizer_closure] at hmap
  apply held_controlled_cubic_obstruction (S.mapSurjective hq) A
    ((map_mono hn).trans (B.le_normalizer_map q)) h5A hZA (q x)
    ((q.orderOf_map_eq_of_coprime_of_isPGroup_ker hk x (by rw [hx]; decide)).trans hx)
  rw [←hmap]
  exact (map_mono hC).trans (B.le_normalizer_map q)

end MathieuCode.NormalizedShadowRows
