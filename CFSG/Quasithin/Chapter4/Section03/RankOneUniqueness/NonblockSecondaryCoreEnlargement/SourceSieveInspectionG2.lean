module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryCoreEnlargement.SourceSieveInspectionRankTwo
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.CyclicOuter
public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.NormalizerCover
public import Theory.AtlasPort.LinearGroups.G2.PerfectLocalPrimes

/-!
# Excluding the remaining binary G₂ rows on the source action

The cyclic outer group puts the moved core image inside the inner component.
The proved whole-radical generation identity then puts the radical there too.
Its nontrivial two-group normalizer is conjugate into a root parabolic, so an
original torus prime divides the quadratic torus factor. The two commuting
rank-one factors give prime rank at least two in the component, contradicting
the source rank-one restriction. The prior cubic argument rules out even
source degree. All transports retain the literal action and central cover.

Source: Aschbacher--Smith 4.3.12--16, printed pp.617--618, and A.3.12,
printed pp.47--48. No full-Sylow normalization of the secondary is assumed.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable {c : SourceConfiguration T L} {n : ℕ}

private theorem moved_le_inner_of_cyclic_outer {A : Type*} [Group A]
    [IsCyclic (MulAut.Outer A)] (Q Y : Subgroup (MulAut A)) (hm : ⁅Q,Y⁆=Q) :
    Q ≤ MulAut.innerSubgroup A := by
  let q := QuotientGroup.mk' (MulAut.innerSubgroup A)
  have hh : Q.map q=⊥ := by
    rw [←hm,map_commutator]
    apply bot_unique
    exact (commutator_mono le_top le_top).trans
      (commutator_self_eq_bot_iff.mpr (inferInstance : IsMulCommutative (⊤ : Subgroup (MulAut.Outer A)))).le
  intro a ha
  exact (QuotientGroup.eq_one_iff _).mp ((Subgroup.map_eq_bot_iff _).mp hh ha)

/-- Core movement and generation put the whole radical image inside the
actual G₂ inner component, retaining its possible central cover. -/
theorem SecondaryActionData.g2_radical_le_inner (s : SecondaryActionData c n)
    (hg : SecondaryActionData.ActionGeneration s) {f : ℕ} (hf : 2≤f)
    (hm : ClassificationModels.IsG2At (SecondaryActionData.componentImage s) (2^f)) :
    SecondaryActionData.radicalImage s ≤ SecondaryActionData.componentImage s := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let := s.quasisimple
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  have hq : 2<Nat.card F := by
    have hh := Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) hf
    omega
  let := Atlas.G2.LieAutomorphismExtensions.outer_isCyclic (F:=F) hq
  let a := (SecondaryActionData.sieveCentralQuotientEquiv s).trans e
  let k := MulAut.centralQuotientAction a
  have hi : SecondaryActionData.coreImage s ≤ SecondaryActionData.componentImage s := by
    rw [SecondaryActionData.componentImage_eq_inner]
    have hmoved : ⁅(SecondaryActionData.coreImage s).map k,
        (SecondaryActionData.torusImage s).map k⁆ = (SecondaryActionData.coreImage s).map k := by
      rw [←map_commutator,SecondaryActionData.coreImage_moved]
    have hh := moved_le_inner_of_cyclic_outer _ _ hmoved
    intro x hx
    obtain ⟨y,hy⟩ := hh (mem_map_of_mem k hx)
    obtain ⟨z,hz⟩ := (MulAut.centralQuotientAction_inner_iff a x).mp ⟨y,hy.symm⟩
    exact ⟨z,hz.symm⟩
  rw [←hg]
  apply sup_le hi
  rw [SecondaryActionData.componentImage_eq_inner]
  exact (Subgroup.commutator_mono le_top
    (by rw [←SecondaryActionData.componentImage_eq_inner]
        exact SecondaryActionData.secondaryImage_le_componentImage s)).trans
    (Subgroup.commutator_le_right _ _)


/-- Proper parabolic inspection excludes every larger binary G₂ row. -/
theorem SecondaryActionData.not_g2_inner (s : SecondaryActionData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hn : 1<n) (hg : SecondaryActionData.ActionGeneration s)
    {f : ℕ} (hf : 2≤f)
    (hm : ClassificationModels.IsG2At (SecondaryActionData.componentImage s) (2^f)) : False := by
  have hnodd := SecondaryActionData.g2_inner_source_degree_odd s D h hf hm
  have hRI := SecondaryActionData.g2_radical_le_inner s hg hf hm
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let := s.normal
  let := s.quasisimple
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  have hq : 2<Nat.card F := by
    have hh := Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) hf
    omega
  have hXI := SecondaryActionData.secondaryImage_le_componentImage s
  let I := SecondaryActionData.componentImage s
  let X := SecondaryActionData.secondaryImage s
  let R := SecondaryActionData.radicalImage s
  let b := subgroupOfEquivOfLe hXI
  let r := subgroupOfEquivOfLe hRI
  let B := (X.subgroupOf I).map e.toMonoidHom
  let W := (R.subgroupOf I).map e.toMonoidHom
  let b' := b.symm.trans ((X.subgroupOf I).equivMapOfInjective e.toMonoidHom e.injective)
  let r' := r.symm.trans ((R.subgroupOf I).equivMapOfInjective e.toMonoidHom e.injective)
  have hW : W≠⊥ := by
    intro hh
    have hcard : Nat.card R=1 := (Nat.card_congr r'.toEquiv).trans (by change Nat.card W=1; rw [hh]; simp)
    exact s.radical_action (R.eq_bot_of_card_eq hcard)
  have hpW : IsPGroup 2 W :=
    ((SourceImages.radical_geometry c s.component s.radical_normalizer).1).of_equiv r'
  let : Group.IsPerfect X := SourceImages.secondary_perfect c s.component
    (s.secondary_le.trans (map_subtype_le _))
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective
    (f:=b'.toMonoidHom) b'.surjective
  have hBW : B ≤ normalizer (W : Set (Atlas.G2.Model F)) := by
    apply le_trans (map_mono ?_) ((R.subgroupOf I).le_normalizer_map e.toMonoidHom)
    intro x hx y
    exact (SourceImages.radical_geometry c s.component s.radical_normalizer).2.2.2.1 hx y.val
  obtain ⟨g,hgl⟩ := Atlas.G2.EvenLocal.NormalizerCover.normalizer_conjugate_le_parabolic W hW hpW
  let j := (MulAut.conj g).toMonoidHom.comp B.subtype
  have hj : Function.Injective j := (MulAut.conj g).injective.comp B.subtype_injective
  have hjN : j.range ≤ (normalizer (W : Set _)).map (MulAut.conj g).toMonoidHom := by
    rintro _ ⟨x,rfl⟩
    exact mem_map_of_mem _ (hBW x.property)
  have htwo : 4≤2^n := Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) (by omega : 2≤n)
  obtain ⟨p,hp,hd⟩ := Nat.exists_prime_and_dvd (by omega : 2^n-1≠1)
  let : Fact p.Prime := ⟨hp⟩
  have ho := Nat.BinarySignedTorus.odd_of_dvd_sub (by omega : 0<n) hd
  have hp3 : p≠3 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hnodd)
      ((Nat.BinaryTorusParity.three_dvd_sub_one_iff n).mp hd)
  have hdB : p∣Nat.card B := by
    rw [←Nat.card_congr b'.toEquiv]
    have hmodel : ClassicalGroup.IsPSL (X ⧸ pCore 2 X) 2 (2^n) :=
      SourceImages.secondaryImage_model c s.component s.secondary_le s.secondary_model
    obtain ⟨K,_,_,hK,⟨a⟩⟩ := hmodel
    have hc := card_quotient_dvd_card (pCore 2 X)
    let : Fintype K := Fintype.ofFinite K
    let : CharP K 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hK
    rw [Nat.card_congr (a.trans (Theory.PSL2.sl2QuotientEquiv K).symm).toEquiv,
      BenderSuzuki.External.huppert614_card_specialLinearGroup,hK] at hc
    apply dvd_trans _ hc
    apply dvd_mul_of_dvd_right
    exact hd.trans (by simpa only [pow_one] using
      Nat.pow_sub_one_dvd_pow_sub_one (2^n) (by decide : 1∣2))
  have hquad := Atlas.G2.PerfectSubgroups.prime_dvd_quadratic_of_perfect_local hq j hj
    (hgl.imp hjN.trans hjN.trans) hp ho hdB
  obtain ⟨E,hE,hcardE⟩ := Atlas.G2.NoncubicFieldActors.exists_elementary_quadratic hquad
  have hrI : 2≤primeRank p I := by
    rw [primeRank_congr p e]
    by_contra hh
    have hb := (primeRank_le_iff_elementary_card_le (Atlas.G2.Model F)).mp
      (by omega : primeRank p (Atlas.G2.Model F)≤1) E hE
    rw [hcardE,pow_one] at hb
    have := hp.two_le
    nlinarith
  have hr : primeRank p s.component=primeRank p I := by
    rw [←primeRank_quotient_eq_of_isTwoGroup p ho _ pCore_isPGroup]
    let a := SecondaryActionData.sieveCentralQuotientEquiv s
    rw [←primeRank_congr p a]
    apply primeRank_eq_of_surjective_of_coprime p (QuotientGroup.mk' _)
      (QuotientGroup.mk'_surjective _)
    rw [QuotientGroup.ker_mk']
    exact SecondaryActionData.componentQuotient_center_coprime s D h hp hp3
  have hu := SecondaryActionData.noncubic_prime_rank_one s D h hn hp ho hd hp3
  omega
/-- Only larger binary PSL₃ and degree-five J₄ survive the proper-parabolic
G₂ inspection. These are actual inner-component equivalences. -/
theorem SecondaryActionData.inspection_remaining_rows_after_g2
    (s : SecondaryActionData c n) (hn : 1<n)
    (hg : SecondaryActionData.ActionGeneration s)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L) :
    (∃ f : ℕ, 2≤f ∧ ClassicalGroup.IsPSL (SecondaryActionData.componentImage s) 3 (2^f)) ∨
      (n=5 ∧ Nonempty (SecondaryActionData.componentImage s ≃* Janko4.Model)) := by
  rcases SecondaryActionData.inspection_remaining_rows_after_rank_two s hn hg D h with
    hh | ⟨_,f,hf,hm⟩ | hh
  · exact Or.inl hh
  · exact (SecondaryActionData.not_g2_inner s D h hn hg hf hm).elim
  · exact Or.inr hh

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
