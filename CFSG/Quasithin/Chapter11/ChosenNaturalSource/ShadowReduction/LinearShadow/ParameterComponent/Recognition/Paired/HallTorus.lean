module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Recognition.Paired.TorusDivisor


/-!
# The literal paired Hall factor is the full split torus

The component overlap maps, through the original H/O₂(H) projection, onto
the normalizer of its prescribed Sylow subgroup in the actual PSL₂ model.
The binary Borel then maps onto the field-unit group with a two-group
kernel. Restricting this composite to the original odd Hall factor is
bijective: the kernel meets it trivially, and its image is Hall in an odd
group. Thus A intersect K is cyclic of order 2^f - 1, including all prime
powers, for the independent model exponent f.

SplitTorsion uses this on the same Hall subgroup and exchange element as
the original Cartan-plane construction. The field exponent is never
identified with generationParameter H without proof. Rank-one recognition,
the fixed-point construction, and the doubled-parameter exclusion remain
with the parameter-component owner. Genuine preceding source discharge
remains with qt-d-1222-shadow-linear-geometry.
Source: Aschbacher--Smith 11.3.5(2), printed pp.771--772, using E.2.2.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent
namespace Paired

private theorem hall_two_kernel_bijective {X Y : Type*} [Group X] [Finite X]
    [Group Y] [Finite Y] (A : Subgroup X)
    (hA : IsHallSubgroup OddHall.oddPrimes A)
    (f : X →* Y) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    (ho : Odd (Nat.card Y)) : Function.Bijective (f.comp A.subtype) := by
  have hodd := OddHall.odd_hall_odd hA
  have hd : Disjoint A f.ker := by
    obtain ⟨r,hr⟩ := hk.exists_card_eq
    apply disjoint_of_coprime_natCard
    rw [hr]
    exact (Nat.coprime_two_right.mpr hodd).pow_right r
  have hinj : Function.Injective (f.comp A.subtype) := by
    apply (f.comp A.subtype).ker_eq_bot_iff.mp
    apply le_bot_iff.mp
    intro a ha
    exact Subtype.ext (disjoint_def.mp hd a.property ha)
  have hmap : IsHallSubgroup OddHall.oddPrimes (A.map f) :=
    ⟨fun p hp => hA.p_in_pi_of_p_dvd_card p (hp.trans (A.card_map_dvd f)),
      fun p hp => hA.p_in_pi_of_p_dvd_index p (hp.trans (index_map_dvd (H := A) hf))⟩
  have htop : IsHallSubgroup OddHall.oddPrimes (⊤ : Subgroup Y) := by
    refine ⟨?_,?_⟩
    · intro p hp he
      have hp2 : p.val = 2 := he
      have hh : 2 ∣ Nat.card Y := by simpa [hp2] using hp
      exact ho.not_two_dvd_nat hh
    · intro p hp
      exact (p.property.not_dvd_one (by simpa using hp)).elim
  have he := hmap.eq_of_le htop le_top
  refine ⟨hinj,?_⟩
  intro y
  have hy : y ∈ A.map f := he ▸ mem_top y
  obtain ⟨x,hx,hxy⟩ := hy
  exact ⟨⟨x,hx⟩,hxy⟩

private theorem linear_normalizer_torus {X : Type*} [Group X] [Finite X]
    (P : Sylow 2 X) {f : ℕ} (hm : ClassicalGroup.IsPSL X 2 (2 ^ f)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ f ∧
      ∃ φ : normalizer (P : Set X) →* Fˣ,
        Function.Surjective φ ∧ IsPGroup 2 φ.ker := by
  obtain ⟨F,hF,hfin,hcard,⟨e⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
  have he : (normalizer (P : Set X)).map e.toMonoidHom = normalizer (Q : Set PSL(2,F)) := by
    change (normalizer ((P : Subgroup X) : Set X)).map e.toMonoidHom = _
    rw [map_normalizer_eq_of_bijective (P : Subgroup X) e.bijective]
    rfl
  let d := ((e.subgroupMap (normalizer (P : Set X))).trans (MulEquiv.subgroupCongr he)).trans
    (Matrix.ProjectiveSpecialLinearGroup.EvenBorelResidual.sylowNormalizerEquiv F Q)
  let a := Matrix.ProjectiveSpecialLinearGroup.EvenBorelResidual.quotientTorusEquiv F hcard
  let φ := a.toMonoidHom.comp ((QuotientGroup.mk' _).comp d.toMonoidHom)
  refine ⟨F,hF,hfin,hcard,φ,a.surjective.comp ((QuotientGroup.mk'_surjective _).comp d.surjective),?_⟩
  have heker : φ.ker = (pCore 2 _).comap d.toMonoidHom := by
    ext x
    change a (QuotientGroup.mk' _ (d x)) = 1 ↔ d x ∈ pCore 2 _
    rw [← map_one a, a.injective.eq_iff]
    exact QuotientGroup.eq_one_iff (d x)
  rw [heker]
  exact pCore_isPGroup.comap_of_injective d.toMonoidHom d.injective

end Paired

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient} {H K : Subgroup G}

private theorem overlap_eq_maximal (h : Hypothesis1131At D S U₁ H)
    (hP : ChapterB.IsMinimalParabolicOver (T.subtype h.outside.1.1.2) ⊤) :
    (normalizer (L : Set G)).subgroupOf H =
      ChapterB.minimalParabolicMax (T.subtype h.outside.1.1.2) hP := by
  let B := H ⊓ normalizer (L : Set G)
  have hi := Chapter3.HStar.unique_maximal T D.sylow_normalizes_component h.outside
  have hBne : B.subgroupOf H ≠ ⊤ := by
    intro he
    have hm := congrArg (map H.subtype) he
    rw [map_subgroupOf_eq_of_le inf_le_left, ← MonoidHom.range_eq_map,range_subtype] at hm
    exact hi.2.1.lt.ne hm
  have hcoat : IsCoatom (B.subgroupOf H) := by
    refine ⟨hBne,?_⟩
    intro Y hY
    have hy : B < Y.map H.subtype := by
      rw [←map_subgroupOf_eq_of_le (show B ≤ H from inf_le_left)]
      exact (map_lt_map_iff_of_injective H.subtype_injective).mpr hY
    have he := (hi.2.1.eq_or_eq hy.le (map_subtype_le Y)).resolve_left hy.ne'
    apply map_injective H.subtype_injective
    rw [he,←MonoidHom.range_eq_map,range_subtype]
  have hle : B.subgroupOf H ≤ ChapterB.minimalParabolicMax (T.subtype h.outside.1.1.2) hP := by
    apply hP.1.le_maximal
      ⟨(ChapterB.minimalParabolicMax_spec _ hP).2,
        (ChapterB.minimalParabolicMax_spec _ hP).1.covBy_top⟩
    · intro x hx
      exact ⟨x.property,D.sylow_normalizes_component hx⟩
    · exact hcoat.lt_top
  have he := (hcoat.le_iff.mp hle).resolve_left (ChapterB.minimalParabolicMax_spec _ hP).1.ne_top
  simpa only [B,inf_subgroupOf_left] using he.symm


/-- The actual component overlap maps onto its model's split torus with
only a two-group kernel. -/
theorem ComponentSeed.paired_overlap_torus_projection (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary)
    (hn : ¬ (K.subgroupOf H).Normal)
    {f : ℕ} (hf : 0 < f)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ f)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ f ∧
      ∃ φ : ((H ⊓ normalizer (L : Set G)) ⊓ K : Subgroup G) →* Fˣ,
        Function.Surjective φ ∧ IsPGroup 2 φ.ker := by
  let P := T.subtype h.outside.1.1.2
  let J := K.subgroupOf H
  have hP := outside_minimalParabolic h (weakClosure_not_le_core_of_counterexample h pr hc)
  have hsolv := counterexample_not_solvable h pr hc hs
  have hgen := ComponentSeed.intrinsic_supplement s h.outside.1.1.2
  let R := ChapterB.minimalParabolicCore P hP
  let q := QuotientGroup.mk' R
  have hq := QuotientGroup.mk'_surjective R
  have hcore : R = pCore 2 H :=
    (ChapterB.minimalParabolic_nonsolvable_core_eq_radical P hP hsolv).trans
      (s.paired_radical_eq_twoCore h pr hc hs hn)
  let e := ComponentSeed.quotientImageEquivOfCore s R hcore
  have hi := ChapterE.Structure.source_component_simple_image P hP hsolv J s.component.2 hgen
  let : IsSimpleGroup (J.map q) := hi.1
  let M := (normalizer (L : Set G)).subgroupOf H
  have hM := overlap_eq_maximal h hP
  have hMstar : M.map q = ChapterB.minimalParabolicMax (P.mapSurjective hq)
      (ChapterE.Structure.source_star_minimal_core_free P hP).1 := by
    rw [show M = ChapterB.minimalParabolicMax P hP from hM]
    exact ChapterB.minimalParabolicMax_map_core P hP q hq (by rw [QuotientGroup.ker_mk'])
  have hkM : q.ker ≤ M := by
    rw [QuotientGroup.ker_mk',hcore]
    exact (pCore_isPGroup.le_sylow_of_normal P).trans
      (fun x hx => D.sylow_normalizes_component hx)
  have hmj : (M ⊓ J).map q = M.map q ⊓ J.map q := by
    rw [inf_comm M J,map_inf_of_ker_le q J M hkM,inf_comm]
  have heven : 2 ∣ Nat.card (J.map q) := by
    by_contra hne
    have ho : Odd (Nat.card (J.map q)) := Nat.not_even_iff_odd.mp (by
      simpa only [even_iff_two_dvd] using hne)
    let := hi.2.1.2
    exact Group.IsPerfect.not_isSolvable (J.map q) (odd_order_theorem _ ho)
  have hb := ChapterE.Witnesses.PairedBender.component_borel_intersection
    (P.mapSurjective hq) (ChapterE.Structure.source_star_minimal_core_free P hP).1
    (J.map q) hi.2.1 heven
    (ChapterE.Structure.generating_component_orbit_eq_residual
      (ChapterE.Structure.source_star_sqtk ChapterA.Section02.theoremA_knownSimple
        (outside_sqtk h) P hP hsolv).stronglyQuasithin
      (P.mapSurjective hq) hi.2.1 hi.2.2.2)
    (.linear f hf (hm.of_mulEquiv e.symm))
  obtain ⟨Q,hQ⟩ := (P.mapSurjective hq).exists_subgroupOf_eq_of_subnormal (J.map q) hi.2.1.1
  rw [←hMstar,←hQ] at hb
  change (M.map q).subgroupOf (J.map q) = normalizer (Q : Set (J.map q)) at hb
  let d : (M ⊓ J).map q ≃* normalizer (Q : Set (J.map q)) :=
    (MulEquiv.subgroupCongr hmj).trans
      ((subgroupOfEquivOfLe (show M.map q ⊓ J.map q ≤ J.map q from inf_le_right)).symm.trans
        (MulEquiv.subgroupCongr (by simpa only [inf_subgroupOf_right] using hb)))
  let g := d.toMonoidHom.comp (q.subgroupMap (M ⊓ J))
  have hg : Function.Surjective g := d.surjective.comp (q.subgroupMap_surjective (M ⊓ J))
  have hgker : IsPGroup 2 g.ker := by
    have he : g.ker = R.comap (M ⊓ J : Subgroup H).subtype := by
      ext x
      change d ((q.subgroupMap (M ⊓ J)) x) = 1 ↔ x.val ∈ R
      rw [← map_one d, d.injective.eq_iff]
      change (q.subgroupMap (M ⊓ J)) x = 1 ↔ x.val ∈ R
      rw [Subtype.ext_iff]
      exact QuotientGroup.eq_one_iff x.val
    rw [he,hcore]
    exact pCore_isPGroup.comap_subtype
  obtain ⟨F,hF,hfin,hcard,φ,hφ,hφker⟩ := Paired.linear_normalizer_torus Q (hm.of_mulEquiv e.symm)
  have he : (M ⊓ J).map H.subtype = (H ⊓ normalizer (L : Set G)) ⊓ K := by
    rw [Subgroup.map_inf _ _ _ H.subtype_injective,
      show J.map H.subtype = K from map_subgroupOf_eq_of_le s.component.1]
    congr 1
    exact (subgroupOf_map_subtype (normalizer (L : Set G)) H).trans (inf_comm _ _)
  let b := ((M ⊓ J).equivMapOfInjective H.subtype H.subtype_injective).trans
    (MulEquiv.subgroupCongr he)
  let ψ := (φ.comp g).comp b.symm.toMonoidHom
  refine ⟨F,hF,hfin,hcard,ψ,hφ.comp (hg.comp b.symm.surjective),?_⟩
  change IsPGroup 2 ((φ.ker.comap g).comap b.symm.toMonoidHom)
  exact (hφker.comap_of_ker_isPGroup g hgker).comap_of_injective b.symm.toMonoidHom b.symm.injective

/-- Every actual odd Hall factor is the entire split torus of the model,
including its higher prime powers. -/
theorem ComponentSeed.paired_hall_factor_cyclic_card (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary)
    (hn : ¬ (K.subgroupOf H).Normal)
    {f : ℕ} (hf : 0 < f)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ f))
    (A : Subgroup G) (hA : A ≤ H ⊓ normalizer (L : Set G))
    (hHall : IsHallSubgroup OddHall.oddPrimes
      (A.subgroupOf (H ⊓ normalizer (L : Set G)))) :
    IsCyclic (A ⊓ K : Subgroup G) ∧ Nat.card (A ⊓ K : Subgroup G) = 2 ^ f - 1 := by
  obtain ⟨F,hF,hfin,hcard,φ,hφ,hφker⟩ :=
    s.paired_overlap_torus_projection h pr hc hs hn hf hm
  have ho : Odd (Nat.card Fˣ) := by
    rw [Nat.card_units,hcard]
    have htwo : Even (2 ^ f) := even_iff_two_dvd.mpr (dvd_pow_self 2 hf.ne')
    exact Nat.Even.sub_odd (Nat.one_le_pow _ _ (by decide)) htwo (by decide)
  let B := ((H ⊓ normalizer (L : Set G)) ⊓ K : Subgroup G)
  let C := (A ⊓ K).subgroupOf B
  have hC := s.paired_hall_factor h pr hc hs hn A hA hHall
  let e := (subgroupOfEquivOfLe (show A ⊓ K ≤ B from
    le_inf (inf_le_left.trans hA) inf_le_right)).symm.trans
      (MulEquiv.ofBijective (φ.comp C.subtype) (Paired.hall_two_kernel_bijective C hC φ hφ hφker ho))
  exact ⟨isCyclic_of_injective e.toMonoidHom e.injective,
    (Nat.card_congr e.toEquiv).trans (by rw [Nat.card_units,hcard])⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent
