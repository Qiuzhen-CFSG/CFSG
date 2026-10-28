module
public import CFSG.Quasithin.Chapter6.SourceReduction.LocalCentralization.FourCubic
public import CFSG.Quasithin.Chapter6.SourceReduction.LocalCentralization.SixThompson
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Odd.SevenThompsonNormalizer

/-!
# The escaping cubic does not normalize the six-space Thompson subgroup

Both original Hall products pass to the full seven-letter action. The
cyclic odd Cartan image containing the escaping cubic has order three,
so the actual right Hall and cubic form an elementary nine-group permuting
with the full Sylow image. The six-space Thompson image is the three-pair
group. Its cubic normalizer obstruction therefore applies, and mapping
normalizers transports the contradiction to the original J(T).

Source: Aschbacher–Smith 5.1.13, p.637, using B.3.2(4), pp.83–84.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
private theorem odd_cyclic_seven_card_three (R : Subgroup (Equiv.Perm (Fin 7)))
    [IsCyclic R] (ho : Odd (Nat.card R)) (h3 : 3 ∣ Nat.card R) : Nat.card R = 3 := by
  have hRA : R ≤ alternatingGroup (Fin 7) := by
    intro r hr
    apply Equiv.Perm.mem_alternatingGroup.mpr
    rcases Int.units_eq_one_or (Equiv.Perm.sign r) with he | he
    · exact he
    have hp : Equiv.Perm.sign r ^ Nat.card R = 1 := by
      rw [←map_pow]
      have hh := congrArg Subtype.val (pow_card_eq_one' (x := (⟨r,hr⟩ : R)))
      change r ^ Nat.card R = 1 at hh
      rw [hh,map_one]
    rw [he,ho.neg_one_pow] at hp
    exact (by decide : (-1 : ℤˣ) ≠ 1) hp |>.elim
  let e := subgroupOfEquivOfLe hRA
  let : IsCyclic (R.subgroupOf (alternatingGroup (Fin 7))) :=
    isCyclic_of_injective e.toMonoidHom e.injective
  have hc := Nat.card_congr e.toEquiv
  exact hc.symm.trans (Representation.BinaryAlternatingSevenControl.Cartan.odd_cyclic_card_three
    (R.subgroupOf (alternatingGroup (Fin 7))) (hc.symm ▸ ho) (hc.symm ▸ h3))

/-- Both original Hall identities control the full seven-letter Sylow image. -/
theorem LocalA7Configuration.seven_hall_plane_permutes
    {T : Sylow 2 G} {L W H A B Y X D K : Subgroup G} {n : ℕ}
    (a : LocalA7Configuration T L H X K)
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (d : LocalCartanWitness T H A Y X D)
    (q : (K ⊔ (T : Subgroup G) : Subgroup G) →* Equiv.Perm (Fin 7))
    (hcore : q.ker = pCore 2 (K ⊔ (T : Subgroup G) : Subgroup G)) :
    let M := K ⊔ (T : Subgroup G)
    let E := ((B ⊔ D).subgroupOf M).map q
    let P := ((T : Subgroup G).subgroupOf M).map q
    IsElementaryAbelian 3 E ∧ Nat.card E = 9 ∧
      Nat.card ((D.subgroupOf M).map q) = 3 ∧
      (E : Set (Equiv.Perm (Fin 7))) * (P : Set _) = (P : Set _) * (E : Set _) := by
  let M := K ⊔ (T : Subgroup G)
  let P := T.subtype (show (T : Subgroup G) ≤ M from le_sup_right)
  obtain ⟨he,hcard,hle,_⟩ := d.hall_cubic_plane h hH hgen c
  have hEM : B ⊔ D ≤ M := hle.trans (a.contains.trans le_sup_left)
  let E := (B ⊔ D).subgroupOf M
  have hEc : Nat.card E = 9 := (Nat.card_congr (subgroupOfEquivOfLe hEM).toEquiv).trans hcard
  have hdis : Disjoint E q.ker :=
    (IsPGroup.of_card (p := 3) (n := 2) hEc).disjoint_of_coprime
      (hcore.symm ▸ pCore_isPGroup) (by decide)
  have hqi : Function.Injective (q.subgroupMap E) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply _root_.eq_bot_iff.mpr
    intro x hx
    apply Subtype.ext
    exact mem_bot.mp (hdis.le_bot ⟨x.property,congrArg Subtype.val (show q.subgroupMap E x = 1 from hx)⟩)
  have hEq : Nat.card (E.map q) = 9 :=
    (Nat.card_congr (MulEquiv.ofBijective (q.subgroupMap E)
      ⟨hqi,q.subgroupMap_surjective E⟩).toEquiv).symm.trans hEc
  have hDM : D ≤ M := le_sup_right.trans hEM
  have hDqcard : Nat.card ((D.subgroupOf M).map q) = 3 := by
    have hi : Function.Injective (q.subgroupMap (D.subgroupOf M)) := by
      intro x y hxy
      have hxy' : q x.val = q y.val :=
        congrArg (fun z : (D.subgroupOf M).map q => (z : Equiv.Perm (Fin 7))) hxy
      have hh : (⟨x.val,(show D ≤ B ⊔ D from le_sup_right) x.property⟩ : E) =
          ⟨y.val,(show D ≤ B ⊔ D from le_sup_right) y.property⟩ := hqi (Subtype.ext hxy')
      exact Subtype.ext (congrArg (fun z : E => (z : M)) hh)
    exact (Nat.card_congr (MulEquiv.ofBijective (q.subgroupMap (D.subgroupOf M))
      ⟨hi,q.subgroupMap_surjective _⟩).toEquiv).symm.trans
        ((Nat.card_congr (subgroupOfEquivOfLe hDM).toEquiv).trans d.cubic_card)
  let : IsCyclic A := (c.left_cyclic_and_card h.sylow_normalizes h.linear).1
  let j : A.subgroupOf M →* A := {
    toFun x := ⟨x.val,x.property⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hji : Function.Injective j := by
    intro x y hh
    exact Subtype.ext (Subtype.ext (congrArg (fun a : A => (a : G)) hh))
  let : IsCyclic (A.subgroupOf M) := isCyclic_of_injective j hji
  let : IsCyclic ((A.subgroupOf M).map q) :=
    isCyclic_of_surjective (q.subgroupMap _) (q.subgroupMap_surjective _)
  have hAo : Odd (Nat.card A) := by
    rw [←Nat.card_congr (subgroupOfEquivOfLe c.left_le).toEquiv]
    exact OddHall.odd_hall_odd c.left_hall
  have hAqo : Odd (Nat.card ((A.subgroupOf M).map q)) :=
    (hAo.of_dvd_nat (card_dvd_of_injective j hji)).of_dvd_nat (card_map_dvd _ q)
  have hDAq : (D.subgroupOf M).map q ≤ (A.subgroupOf M).map q :=
    map_mono (comap_mono (d.cubic_le.trans inf_le_left))
  have hAqcard := odd_cyclic_seven_card_three
    ((A.subgroupOf M).map q) hAqo (hDqcard ▸ card_dvd_of_le hDAq)
  have hDAqe : (D.subgroupOf M).map q = (A.subgroupOf M).map q :=
    eq_of_le_of_card_ge hDAq (by rw [hDqcard,hAqcard])
  have hDperm := c.image_intersection_permutes_sylow h.sylow_normalizes
    (show (T : Subgroup G) ≤ M from le_sup_right) q
  rw [←hDAqe] at hDperm
  change ((D.subgroupOf M).map q : Set (Equiv.Perm (Fin 7))) * ((P : Subgroup M).map q : Set _) =
    ((P : Subgroup M).map q : Set _) * ((D.subgroupOf M).map q : Set _) at hDperm
  have hBM : B ≤ M := le_sup_left.trans hEM
  have hBperm := map_subgroupOf_permutes hBM (show (T : Subgroup G) ≤ M from le_sup_right) q
    (c.right_permutes_sylow h.sylow_normalizes hH.1.1.2)
  change ((B.subgroupOf M).map q : Set (Equiv.Perm (Fin 7))) * ((P : Subgroup M).map q : Set _) =
    ((P : Subgroup M).map q : Set _) * ((B.subgroupOf M).map q : Set _) at hBperm
  have hBD : (B.subgroupOf M).map q ≤ normalizer ((D.subgroupOf M).map q : Set _) := by
    have hb : B ≤ normalizer (D : Set G) :=
      c.right_normalizes_left.trans (normalizer_le_normalizer_of_le_cyclic D A (d.cubic_le.trans inf_le_left))
    have hb' : B.subgroupOf M ≤ normalizer (D.subgroupOf M : Set M) := by
      intro b hbmem
      exact mem_normalizer_iff.mpr (fun x => mem_normalizer_iff.mp (hb hbmem) x.val)
    exact (map_mono hb').trans ((D.subgroupOf M).le_normalizer_map q)
  have hperm : (E.map q : Set (Equiv.Perm (Fin 7))) * ((P : Subgroup M).map q : Set _) =
      ((P : Subgroup M).map q : Set _) * (E.map q : Set _) := by
    have heq : E.map q = (B.subgroupOf M).map q ⊔ (D.subgroupOf M).map q := by
      rw [←Subgroup.map_sup,←subgroupOf_sup hBM hDM]
    rw [heq,coe_mul_of_left_le_normalizer_right _ _ hBD]
    rw [mul_assoc,hDperm,←mul_assoc,hBperm,mul_assoc]
  let := he
  let : IsElementaryAbelian 3 E := IsElementaryAbelian.subgroupOf hEM
  exact ⟨IsElementaryAbelian.of_surjective (q.subgroupMap E) (q.subgroupMap_surjective E),
    hEq,hDqcard,hperm⟩
/-- In the actual six-space alternative the escaping cubic cannot normalize
J(T). Both original Hall conditions control the full Sylow image. -/
theorem LocalA7Configuration.six_cubic_not_normalizes_thompson
    {T : Sylow 2 G} {L W H A B Y X D K : Subgroup G} {n : ℕ}
    (a : LocalA7Configuration T L H X K)
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (d : LocalCartanWitness T H A Y X D)
    (hc : Nat.card (localOmegaModule T K) = 64) :
    ¬ D ≤ normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) := by
  let M := K ⊔ (T : Subgroup G)
  let P := T.subtype (show (T : Subgroup G) ≤ M from le_sup_right)
  let J := (elementaryAbelianMaxJ (T : Subgroup G)).subgroupOf M
  obtain ⟨q,hq,hker,hcore,hK,⟨g,hg⟩,hcard⟩ := a.six_thompson_image h hH d hc
  obtain ⟨he,hE,hD,hperm⟩ := a.seven_hall_plane_permutes h hH hgen c d q hcore
  let E := ((B ⊔ D).subgroupOf M).map q
  let C := (D.subgroupOf M).map q
  let := he
  have hPmap : (P : Subgroup M).map M.subtype = (T : Subgroup G) :=
    map_subgroupOf_eq_of_le le_sup_right
  have hJM : elementaryAbelianMaxJ (T : Subgroup G) ≤ M :=
    (show elementaryAbelianMaxJ (T : Subgroup G) ≤ (T : Subgroup G) from
      sSup_le fun _ hE => hE.1).trans le_sup_right
  have hJ : elementaryAbelianMaxJ (P : Subgroup M) = J := by
    apply map_injective M.subtype_injective
    rw [←elementaryAbelianMaxJ_map_injective M.subtype M.subtype_injective,hPmap,
      map_subgroupOf_eq_of_le hJM]
  have hPJ : (P : Subgroup M).map q ≤ normalizer (J.map q : Set (Equiv.Perm (Fin 7))) := by
    rw [←hJ]
    exact (map_mono ((P : Subgroup M).le_normalizer.trans (normalizer_le_normalizer_elementaryAbelianMaxJ _))).trans
      ((elementaryAbelianMaxJ (P : Subgroup M)).le_normalizer_map q)
  have hn := ChapterB.Offenders.SevenNormalizer.plane_cubic_not_normalizes
    (P.mapSurjective hq) E C (J.map q) hE hD
    (map_mono (comap_mono (show D ≤ B ⊔ D from le_sup_right))) hperm g hg hPJ
  intro hd
  apply hn
  have hdM : D.subgroupOf M ≤ normalizer (J : Set M) := by
    intro x hx
    apply mem_normalizer_iff.mpr
    intro j
    exact mem_normalizer_iff.mp (hd hx) j.val
  exact (map_mono hdM).trans (J.le_normalizer_map q)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
