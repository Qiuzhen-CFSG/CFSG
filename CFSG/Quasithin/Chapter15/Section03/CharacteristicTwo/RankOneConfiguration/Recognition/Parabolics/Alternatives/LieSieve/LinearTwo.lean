module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Parabolics.Alternatives.LieSieve.SolvableLift
public import Theory.SpecificGroups.SL2.SylowUniqueMaximal
public import Theory.SpecificGroups.SL2.EvenBorelResidual
public import Theory.SpecificGroups.LinearSylowNormalizers.Triangular
public import Theory.GroupTheory.RelativeNormalizerTransport

/-!
# The marked linear-two alternative

Conjugate the supplied model so that the actual component Sylow intersection
is the upper root group. Every proper overgroup of this root group lies in
its Borel. That Borel is S-invariant because it is the Sylow normalizer;
it contains Y₊*, so it is also Y₊*-invariant. Solvable-invariant control
applied to its preimage inside the component gives the reverse containment.

The residual identity forces the component intersection to have order
divisible by three. A Borel in odd field degree has order prime to three,
so the given field degree is even and, being positive, greater than one.
Finally the canonical SL₂–PSL₂ equivalence transports the same marking.
No pushing-up result or later exclusion 15.3.30–31 is used.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.28(1), printed p.1131 (PDF p.1148).
-/

@[expose] public section
open Subgroup Matrix.SpecialLinearGroup
open scoped Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Parabolics.LieSieve
variable {G : Type*} [Group G] [Finite G]
variable {d : LocalData G} {I : Subgroup G} {c : ComponentWitness d I}

/-- Construct the actual Borel identification for the given linear-two field. -/
theorem linearTwo_marking (a : Input d I c) (F : ClassificationField)
    (e : d.starImage I c.L ≃* Matrix.SpecialLinearGroup (Fin 2) F.Carrier) :
    Nonempty (LinearTwo.BorelIdentification d I c F.degree F.Carrier) := by
  let L := d.starImage I c.L
  let S := d.starImage I d.S
  let P := d.starImage I (d.M ⊓ c.L)
  let J := P.subgroupOf L
  have hPL : P ≤ L := a.componentIntersectionStar_lt.le
  have hSM : S ≤ d.starImage I (d.MI I) :=
    map_mono (comap_mono (le_inf (inf_le_left.trans d.sylow_le) a.sylow_le))
  obtain ⟨Q, hQ⟩ := a.exists_componentSylow
  let Qe := Q.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq
    (Matrix.SpecialLinearGroup (Fin 2) F.Carrier) Qe (upperUnipotentSylow F.Carrier 2)
  let f : L ≃* Matrix.SpecialLinearGroup (Fin 2) F.Carrier := e.trans (MulAut.conj g)
  have hSf : (S.subgroupOf L).map f.toMonoidHom = upperUnipotent F.Carrier := by
    rw [← hQ]
    change (Q : Subgroup L).map ((MulAut.conj g).toMonoidHom.comp e.toMonoidHom) = _
    rw [← map_map]
    exact congrArg Sylow.toSubgroup hg
  have hJne : J.map f.toMonoidHom ≠ ⊤ := by
    intro ht
    have hJ : J = ⊤ := map_injective f.injective
      (ht.trans (map_top_of_surjective f.toMonoidHom f.surjective).symm)
    exact a.componentIntersectionStar_lt.not_ge (subgroupOf_eq_top.mp hJ)
  have hSJ : S.subgroupOf L ≤ J := by
    intro x hx
    change (x : d.Star I) ∈ P
    rw [show P = L ⊓ d.starImage I (d.MI I) from a.intersectionStar_eq_inf]
    exact ⟨x.property, hSM hx⟩
  have hJBorel : J.map f.toMonoidHom ≤ rankOneBorel F.Carrier :=
    overgroup_le_rankOneBorel (hSf ▸ map_mono hSJ) hJne
  let B₀ := (rankOneBorel F.Carrier).map f.symm.toMonoidHom
  let B := B₀.map L.subtype
  have hJB : J ≤ B₀ := by
    have h := map_le_iff_le_comap.mp hJBorel
    rwa [comap_equiv_eq_map_symm'] at h
  have hPB : P ≤ B := by
    rw [← map_subgroupOf_eq_of_le hPL]
    exact map_mono hJB
  have hBsolv : Group.IsSolvable B := by
    let : Group.IsSolvable (rankOneBorel F.Carrier) :=
      Theory.SpecificGroups.LinearSylowNormalizers.isSolvable_sylow_normalizer 2 F.Carrier
        (by decide) (upperUnipotentSylow F.Carrier 2)
    let : Group.IsSolvable B₀ :=
      Group.isSolvable_of_surjective (f.symm.toMonoidHom.subgroupMap_surjective _)
    exact Group.isSolvable_of_surjective (L.subtype.subgroupMap_surjective _)
  have hSB : S ≤ normalizer (B : Set (d.Star I)) := by
    let := a.componentStar_normal
    apply le_trans (le_inf le_rfl (show S ≤ normalizer (L : Set (d.Star I)) from
      le_normalizer_of_normal))
    exact normalizes_pullback_of_stabilizer_invariant f _ _ hSf (by
      intro β hβ
      change (normalizer (upperUnipotent F.Carrier : Set _)).map β.toMonoidHom = _
      rw [map_equiv_normalizer_eq, hβ])
  have hYB : d.starImage I d.Yplus ≤ B :=
    (map_mono (comap_mono (le_inf (a.yplus_le_intersection.trans inf_le_left)
      a.contains))).trans hPB
  have hYSB : d.starImage I (d.Yplus ⊔ d.S) ≤ normalizer (B : Set (d.Star I)) := by
    change ((d.Yplus ⊔ d.S).subgroupOf I).map (d.starMap I) ≤ _
    rw [subgroupOf_sup (a.yplus_le_intersection.trans inf_le_right) a.sylow_le,
      Subgroup.map_sup]
    exact sup_le (hYB.trans B.le_normalizer) hSB
  have hBP : B ≤ P := a.solvable_star_subgroup_le_intersection B (map_subtype_le _) hBsolv hYSB
  have hJ : J = B₀ := by
    apply map_injective L.subtype_injective
    exact (map_subgroupOf_eq_of_le hPL).trans (le_antisymm hPB hBP)
  have hmark : J.map f.toMonoidHom = rankOneBorel F.Carrier := by
    rw [hJ]
    change ((rankOneBorel F.Carrier).map f.symm.toMonoidHom).map f.toMonoidHom = _
    rw [map_map]
    have hid : f.toMonoidHom.comp f.symm.toMonoidHom = MonoidHom.id _ := by
      apply MonoidHom.ext
      intro x
      exact f.apply_symm_apply x
    rw [hid, Subgroup.map_id]
  have hc : Nat.card P = Nat.card (rankOneBorel F.Carrier) :=
    (Nat.card_congr (subgroupOfEquivOfLe hPL).toEquiv).symm.trans
      (Nat.card_congr ((f.subgroupMap J).trans (MulEquiv.subgroupCongr hmark)).toEquiv)
  have heven : Even F.degree := by
    by_contra hn
    have hp := Matrix.ProjectiveSpecialLinearGroup.EvenBorelResidual.borel_threePrime_of_odd
      F.Carrier F.card_eq (Nat.not_even_iff_odd.mp hn)
    have heq := Nat.card_congr
      (Matrix.ProjectiveSpecialLinearGroup.EvenBorelResidual.rankOneBorelEquiv F.Carrier).toEquiv
    have hd := a.componentIntersectionStar_three_dvd
    rw [hc, heq] at hd
    exact Nat.prime_three.coprime_iff_not_dvd.mp hp hd
  refine ⟨{
    parameter_gt_one := ?_
    parameter_even := heven
    field_card := F.card_eq
    projective := f.trans (Theory.PSL2.sl2QuotientEquiv F.Carrier)
    borel := ?_ }⟩
  · have hn := F.degree_pos
    obtain ⟨k, hk⟩ := heven
    omega
  · change J.map ((Theory.PSL2.quotientMap F.Carrier).comp f.toMonoidHom) = _
    rw [← map_map, hmark]
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Parabolics.LieSieve
