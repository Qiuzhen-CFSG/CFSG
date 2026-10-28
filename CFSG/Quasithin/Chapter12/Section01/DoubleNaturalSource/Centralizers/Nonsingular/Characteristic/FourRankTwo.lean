module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Nonsingular.Characteristic.ModelReduction
public import Theory.SpecificGroups.PSL3Two.ClassicalSectionObstructions

/-!
# Excluding the degree-four rank-two component rows

The actual local image has a perfect L₃(2) two-core quotient and normalizes
its nontrivial moving two-subgroup. The genuine two-local covers place it
in a parabolic. Its image in the rank-one Levi has solvable kernel, which
is impossible because binary SL₂ has elementary Sylow two-subgroups while
L₃(2) has elements of order four. This treats the linear, symplectic, G₂,
triality and Ree rows. The Tits embedding gives the same Ree obstruction;
the two small derived rows have insufficient two-rank.

`FourModels` applies this to the original nonsingular centralizer, with no
additional Sylow or model premise. The remaining component rows and the
normal and parabolic branches stay with qt-d-double-natural-centralizers.
Source: Aschbacher--Smith, 12.1.1 and A.2.3, printed pp.788 and32--33.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Nonsingular

private theorem solvable_ker_of_injective {X Y : Type*} [Group X] [Group Y]
    (f : X →* Y) (hf : Function.Injective f) : Group.IsSolvable f.ker := by
  rw [(MonoidHom.ker_eq_bot_iff f).mpr hf]
  infer_instance

private theorem no_twoCore_section {X Y F : Type*} [Group X] [Finite X] [Group.IsPerfect X]
    [Group Y] [Finite Y] [Field F] [Finite F] [CharP F 2]
    (e : (X ⧸ pCore 2 X) ≃* Matrix.PSL3Two.PSL)
    (f : X →* Y) (hf : Function.Injective f)
    (a : (Y ⧸ pCore 2 Y) ≃* SL(2,F)) : False := by
  let r := a.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 Y))
  let : Group.IsSolvable f.ker := solvable_ker_of_injective f hf
  let : Group.IsSolvable r.ker := by
    rw [show r.ker = pCore 2 Y from by
      rw [MonoidHom.ker_comp_of_injective _ _ a.injective,QuotientGroup.ker_mk']]
    let : Group.IsNilpotent (pCore 2 Y) := pCore_isPGroup.isNilpotent
    infer_instance
  exact Matrix.PSL3Two.no_solvable_kernel_rankOne_local e f r

private theorem no_linear_parabolic {X F : Type*} [Group X] [Finite X] [Group.IsPerfect X]
    [Field F] [Finite F] [CharP F 2]
    (e : (X ⧸ pCore 2 X) ≃* Matrix.PSL3Two.PSL) (hF : 4 ≤ Nat.card F)
    (f : X →* PSL(3,F)) (hf : Function.Injective f)
    (hp : f.range ≤ Matrix.PSL3.LinearThree.pointParabolic F ∨
      f.range ≤ Matrix.PSL3.LinearThree.lineParabolic F) : False := by
  let : Group.IsPerfect f.range := Group.IsPerfect.range f
  rcases hp with hp | hp
  · have hl : f.range ≤ Matrix.PSL3.LinearThree.pointLocal F := by
      rw [←Matrix.PSL3.LinearThree.PerfectSubgroups.pointParabolic_residual F hF]
      exact le_map_solvableResidual_of_isPerfect _ _ hp
    let j := f.codRestrict _ (fun x => hl ⟨x,rfl⟩)
    exact no_twoCore_section e j (fun x y h => hf (congrArg Subtype.val h))
      (Matrix.PSL3.LinearThree.pointLocalCoreQuotientEquiv F)
  · have hl : f.range ≤ Matrix.PSL3.LinearThree.lineLocal F := by
      rw [←Matrix.PSL3.LinearThree.PerfectSubgroups.lineParabolic_residual F hF]
      exact le_map_solvableResidual_of_isPerfect _ _ hp
    let j := f.codRestrict _ (fun x => hl ⟨x,rfl⟩)
    exact no_twoCore_section e j (fun x y h => hf (congrArg Subtype.val h))
      (Matrix.PSL3.LinearThree.lineLocalCoreQuotientEquiv F)

private theorem no_triality_parabolic {X : Type*} [Group X] [Finite X] [Group.IsPerfect X]
    (e : (X ⧸ pCore 2 X) ≃* Matrix.PSL3Two.PSL)
    (P : Triality.Standard.Parameters) (hp : P.prime = 2) (a : Triality.Standard.Parabolics.Node)
    (f : X →* Triality.Standard.Parabolics.parabolic P a) (hf : Function.Injective f) : False := by
  let N := (Triality.Standard.Parabolics.localFactor P a).subgroupOf
    (Triality.Standard.Parabolics.parabolic P a)
  let := Triality.Standard.Parabolics.parabolic_quotient_isCyclic P hp a
  have hc : commutator (Triality.Standard.Parabolics.parabolic P a) ≤ N :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le (N := N)).mp inferInstance
  let : Group.IsPerfect f.range := Group.IsPerfect.range f
  have hl : f.range ≤ N := by
    rw [←commutator_eq_self (H := f.range)]
    exact (commutator_mono le_top le_top).trans hc
  let k := f.codRestrict N (fun x => hl ⟨x,rfl⟩)
  let d := subgroupOfEquivOfLe (Triality.Standard.Parabolics.localFactor_le_parabolic P a)
  let j := d.toMonoidHom.comp k
  have hj : Function.Injective j := d.injective.comp
    (fun x y h => hf (congrArg Subtype.val h))
  cases a with
  | arms =>
    let : CharP (Triality.Standard.ExtensionField P) 2 :=
      hp ▸ inferInstanceAs (CharP (Triality.Standard.ExtensionField P) P.prime)
    exact no_twoCore_section e j hj
      ((Triality.Standard.Parabolics.localFactorArmsQuotientEquivPSL2 P hp).trans
        (Theory.PSL2.sl2QuotientEquiv _).symm)
  | central =>
    let : CharP (GaloisField P.prime P.exponent) 2 :=
      hp ▸ inferInstanceAs (CharP (GaloisField P.prime P.exponent) P.prime)
    exact no_twoCore_section e j hj
      ((Triality.Standard.Parabolics.localFactorCentralQuotientEquivPSL2 P hp).trans
        (Theory.PSL2.sl2QuotientEquiv _).symm)

private theorem no_ree_linear_parabolic {X : Type*} [Group X] [Finite X] [Group.IsPerfect X]
    (e : (X ⧸ pCore 2 X) ≃* Matrix.PSL3Two.PSL) {m : ℕ} (hm : 1 ≤ m)
    (f : X →* ReeF4.ConverseParabolics.parabolic m .linear) (hf : Function.Injective f) : False := by
  let r := ReeF4.ConverseParabolics.linearProjection hm
  let g := r.comp f
  let j := (MonoidHom.fst _ _).comp g
  have hs : ∀ x, (g x).2 = 1 := by
    intro x
    apply Abelianization.commutator_subset_ker ((MonoidHom.snd _ _).comp g)
    rw [Group.IsPerfect.commutator_eq_top]
    trivial
  have hk : j.ker = g.ker := by
    ext x
    change (g x).1 = 1 ↔ g x = 1
    exact ⟨fun hx => Prod.ext hx (hs x),fun hx => congrArg Prod.fst hx⟩
  let : Group.IsSolvable f.ker := solvable_ker_of_injective f hf
  let : Group.IsNilpotent r.ker :=
    (ReeF4.ConverseParabolics.linearProjection_ker_isPGroup hm).isNilpotent
  let : Group.IsSolvable j.ker := by
    rw [hk,show g.ker = r.ker.comap f from rfl]
    exact isSolvable_comap_of_solvable_ker f r.ker
  exact Matrix.SpecialLinearGroup.no_binaryLinearTwo_of_solvable_kernel e j

private theorem three_dvd_of_section {X : Type*} [Group X] [Finite X]
    (e : (X ⧸ pCore 2 X) ≃* Matrix.PSL3Two.PSL) : 3 ∣ Nat.card X := by
  apply dvd_trans _ (card_quotient_dvd_card (pCore 2 X))
  rw [Nat.card_congr (e.trans Matrix.PSL3Two.equiv.symm).toEquiv,Matrix.PSL3Two.card_SL]
  decide

private theorem no_ree_twoLocal {X : Type*} [Group X] [Finite X] [Group.IsPerfect X]
    (e : (X ⧸ pCore 2 X) ≃* Matrix.PSL3Two.PSL) {m : ℕ} (hm : 1 ≤ m)
    (f : X →* ReeF4.Model m) (hf : Function.Injective f)
    (R : Subgroup (ReeF4.Model m)) (hR : R ≠ ⊥) (hp : IsPGroup 2 R)
    (hn : f.range ≤ normalizer (R : Set (ReeF4.Model m))) : False := by
  obtain ⟨g,s,hg⟩ := ReeF4.ConverseParabolics.normalizer_cover hm R hR hp
  let j := (MulAut.conj g).toMonoidHom.comp f
  have hj : j.range ≤ ReeF4.ConverseParabolics.parabolic m s := by
    rw [MonoidHom.range_comp]
    exact (map_mono hn).trans hg
  let k := j.codRestrict _ (fun x => hj ⟨x,rfl⟩)
  have hk : Function.Injective k := fun x y h =>
    hf ((MulAut.conj g).injective (congrArg Subtype.val h))
  cases s with
  | linear => exact no_ree_linear_parabolic e hm k hk
  | suzuki =>
    exact ReeF4.ConverseParabolics.suzuki_parabolic_three_free hm
      ((three_dvd_of_section e).trans (card_dvd_of_injective k hk))

private theorem transport_three_local
    {A Y : Type*} [Group A] [Group Y] [Finite A] [Finite Y]
    (P R : Subgroup A) [Group.IsPerfect P]
    (eP : (P ⧸ pCore 2 P) ≃* Matrix.PSL3Two.PSL)
    (hR : R ≠ ⊥) (hp : IsPGroup 2 R) (hn : P ≤ normalizer (R : Set A))
    (e : A ≃* Y) :
    ∃ B W : Subgroup Y, Group.IsPerfect B ∧
      Nonempty ((B ⧸ pCore 2 B) ≃* Matrix.PSL3Two.PSL) ∧
      W ≠ ⊥ ∧ IsPGroup 2 W ∧ B ≤ normalizer (W : Set Y) := by
  let a := P.equivMapOfInjective e.toMonoidHom e.injective
  refine ⟨P.map e.toMonoidHom,R.map e.toMonoidHom,
    Group.IsPerfect.ofSurjective (f := a.toMonoidHom) a.surjective,
    ⟨(QuotientGroup.congr _ _ a.symm (pCore_map_iso 2 a.symm)).trans eP⟩,?_,hp.map _,?_⟩
  · exact fun he => hR ((map_eq_bot_iff_of_injective R e.injective).mp he)
  · exact (map_mono hn).trans (R.le_normalizer_map e.toMonoidHom)

private theorem rankTwo_three_local_false
    {A : Type*} [Group A] [Finite A]
    (P R : Subgroup A) [Group.IsPerfect P]
    (eP : (P ⧸ pCore 2 P) ≃* Matrix.PSL3Two.PSL)
    (hR : R ≠ ⊥) (hp : IsPGroup 2 R) (hn : P ≤ normalizer (R : Set A))
    (h2 : 6 ≤ primeRank 2 A) {n : ℕ}
    (hm : CFSG.Quasithin.ChapterA.Section02.IsTheoremCRankTwoModel A n) : False := by
  cases hm with
  | linear hn' hm =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    by_cases hn1 : n = 1
    · have hu : primeRank 2 A ≤ 5 := primeRank_le_of_prime_pow_not_dvd (by
        rw [Nat.card_congr e.toEquiv,Matrix.PSL3.LinearThree.card_projective,hF,hn1]
        decide)
      omega
    let : Fintype F := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using hF)
    obtain ⟨B,W,hperf,⟨eB⟩,hW,hp,hn⟩ := transport_three_local P R eP hR hp hn e
    let := hperf
    obtain ⟨g,point,hg⟩ := CFSG.Quasithin.MainConverse.LinearThreeGeometry.twoLocal_conjugate_le F
      (by omega) hF (normalizer (W : Set _)) ⟨W,hW,hp,rfl⟩
    let j := (MulAut.conj g).toMonoidHom.comp B.subtype
    have hj : j.range ≤ (normalizer (W : Set _)).map (MulAut.conj g).toMonoidHom := by
      rintro _ ⟨b,rfl⟩
      exact mem_map_of_mem _ (hn b.property)
    apply no_linear_parabolic eB (by
      rw [hF]
      exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 2 ≤ n)) j
      ((MulAut.conj g).injective.comp B.subtype_injective)
    cases point with
    | false => exact .inr (hj.trans hg)
    | true => exact .inl (hj.trans hg)
  | symplectic hn' hm =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
    let a := e.trans (Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv (F := F)).symm
    obtain ⟨B,W,hperf,⟨eB⟩,hW,hp,hn⟩ := transport_three_local P R eP hR hp hn a
    let := hperf
    obtain ⟨g,hg⟩ := Theory.SpecificGroups.SymplecticFour.twoLocal_parabolic_cover_of_charTwo
      (normalizer (W : Set _)) ⟨W,hW,hp,rfl⟩
    let j := (MulAut.conj g).toMonoidHom.comp B.subtype
    have hi : Function.Injective j := (MulAut.conj g).injective.comp B.subtype_injective
    let : Group.IsSolvable j.ker := solvable_ker_of_injective j hi
    have hj : j.range ≤ (normalizer (W : Set _)).map (MulAut.conj g).toMonoidHom := by
      rintro _ ⟨b,rfl⟩
      exact mem_map_of_mem _ (hn b.property)
    exact Theory.SpecificGroups.SymplecticFour.no_linearThree_section_in_parabolic
      eB j (hg.imp hj.trans hj.trans)
  | g2 hn' hm =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    let : Fintype F := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using hF)
    obtain ⟨B,W,hperf,⟨eB⟩,hW,hp,hn⟩ := transport_three_local P R eP hR hp hn e
    let := hperf
    obtain ⟨g,hg⟩ := Atlas.G2.EvenLocal.NormalizerCover.normalizer_conjugate_le_parabolic W hW hp
    let j := (MulAut.conj g).toMonoidHom.comp B.subtype
    have hi : Function.Injective j := (MulAut.conj g).injective.comp B.subtype_injective
    let : Group.IsSolvable j.ker := solvable_ker_of_injective j hi
    have hj : j.range ≤ (normalizer (W : Set _)).map (MulAut.conj g).toMonoidHom := by
      rintro _ ⟨b,rfl⟩
      exact mem_map_of_mem _ (hn b.property)
    have hq : 2 < Nat.card F := by
      rw [hF]
      have hh := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hn'
      norm_num at hh
      omega
    exact Atlas.G2.no_linearThree_section_in_parabolic eB hq j (hg.imp hj.trans hj.trans)
  | triality hn' hm =>
    have hnpos : 0 < n := by omega
    obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff A n hnpos).mp hm
    obtain ⟨B,W,hperf,⟨eB⟩,hW,hp,hn⟩ := transport_three_local P R eP hR hp hn e
    let := hperf
    obtain ⟨g,a,hg⟩ := Triality.Standard.TwoLocalCover.normalizer_cover n hnpos W hW hp
    let Q := Triality.Standard.Parabolics.parabolic (Triality.Standard.binaryParameters n hnpos) a
    let j := (MulAut.conj g).toMonoidHom.comp B.subtype
    let f : B →* Q := j.codRestrict Q (fun b => hg (mem_map_of_mem _ (hn b.property)))
    exact no_triality_parabolic eB (Triality.Standard.binaryParameters n hnpos) rfl a f
      (fun x y h => B.subtype_injective ((MulAut.conj g).injective (congrArg Subtype.val h)))
  | ree_f4 m hm _ he =>
    obtain ⟨B,W,hperf,⟨eB⟩,hW,hp,hn⟩ := transport_three_local P R eP hR hp hn he.some
    let := hperf
    exact no_ree_twoLocal eB hm B.subtype B.subtype_injective W hW hp
      (by simpa only [B.range_subtype] using hn)
  | symplectic_derived _ he =>
    rw [primeRank_equiv 2 (he.some.trans
      Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix),
      (GLS3.Chapter5.PRank.alternating_hasPRank_two 6).primeRank_eq Nat.prime_two] at h2
    norm_num at h2
  | g2_derived _ he =>
    have hu : primeRank 2 A ≤ 5 := primeRank_le_of_prime_pow_not_dvd (by
      rw [Nat.card_congr he.some.toEquiv,Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp)]
      decide)
    omega
  | tits _ he =>
    obtain ⟨B,W,hperf,⟨eB⟩,hW,hp,hn⟩ := transport_three_local P R eP hR hp hn he.some
    let := hperf
    obtain ⟨f,hf⟩ := ReeF4.Subfield.exists_tits_embedding 1
    let j := f.comp B.subtype
    have hW' : W.map f ≠ ⊥ := fun hh => hW ((map_eq_bot_iff_of_injective W hf).mp hh)
    have hj : j.range ≤ normalizer (W.map f : Set (ReeF4.Model 1)) := by
      rw [MonoidHom.range_comp,B.range_subtype]
      exact (map_mono hn).trans (W.le_normalizer_map f)
    exact no_ree_twoLocal eB (by decide) j (hf.comp B.subtype_injective) (W.map f) hW' (hp.map f) hj

/-- The actual local L₃(2) quotient excludes every rank-two component model in degree four. -/
theorem four_component_not_rankTwo
    {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (h : CFSG.Quasithin.Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : CFSG.Quasithin.Chapter12.Section02.ChosenModule T L V)
    (B : DoubledBranch T L V 4) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G), B.AdaptedPoint S w →
      ∀ K : Subgroup G, IsComponentIn K (B.pointCentralizer w) →
        ∀ f, ¬ CFSG.Quasithin.ChapterA.Section02.IsTheoremCRankTwoModel (K ⧸ center K) f := by
  let := D.doubledOrbit_elementary h
  intro S w hw K hK f hm
  let q := QuotientGroup.mk' (center K)
  let P := ((B.pointResidual w).subgroupOf K).map q
  let U := ((⁅componentOrbit V (T : Subgroup G),B.pointResidual w⁆).subgroupOf K).map q
  obtain ⟨hperf,⟨e⟩,hne,hele,_,hnorm⟩ := D.doubleNatural_adapted_component_local_marking h B S w hw K hK
  let : Group.IsPerfect P := hperf
  let : IsElementaryAbelian 2 U := hele
  exact rankTwo_three_local_false P U e hne (IsElementaryAbelian.isPGroup 2 U) hnorm
    (D.doubleNatural_adapted_component_centralQuotient_rank h B S w hw K hK) hm

end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Nonsingular
