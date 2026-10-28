module
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFiveSource.Torus
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveSource.FieldTransfer
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFullNormalizer.Five
public import Theory.GroupTheory.Hall.ConjugateTorusConstruction

/-!
# Splitting the original U₅(4) Sylow over its inner intersection

Transport the native split torus through the supplied overlap equivalence.
Choose an odd Hall subgroup containing it in the solvable common Borel.
An element of S normalizing that Hall subgroup centralizes it, since its
commutators lie in the intersection of the two coprime factors. The native
torus calculation makes such an element trivial. Hall conjugacy then gives
a complement in the original T, and the actual PSL₂(16) field action makes
that complement cyclic of order [T:S]. Thus S<T supplies a genuine outer
involution, without assuming that a cyclic quotient splits.

On the same published full-normalizer marking, F.middle transports T to a
Sylow subgroup of E.middle. The full inner-preimage theorem identifies its
inner intersection with exactly the image of S. All endpoint, whole-D and
carrier/range equations are retained. Graph type, saturation of the inner
fixed Sylow, and ambient centralizer Sylow placement remain further steps.

Source: Aschbacher–Smith F.4.29(2) and 5.3.3, printed pp.289 and659
of refs/quasithin.pdf. This proves the splitting clause, not all of F.4.29(2).
-/

public noncomputable section
open Subgroup Subgroup.OddHall Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.UnitaryFive Theory.SpecificGroups.UnitaryFive
open ChapterF.SourceCompletion.UnitaryNonbinary
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H A C : Subgroup G} {n : ℕ}

omit [Finite G] in
private theorem source_common_borel_normalized
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hTH : (T : Subgroup G) ≤ H) :
    (T : Subgroup G) ≤ normalizer
      (ChapterF.Source.commonBorel ![L,residual H] (sourceS L H) : Set G) := by
  have hTS := sylow_normalizes_sourceS hTL hTH
  have hb (K : Subgroup G) (hTK : (T : Subgroup G) ≤ normalizer (K : Set G)) :
      (T : Subgroup G) ≤ normalizer (ChapterF.Source.borel K (sourceS L H) : Set G) := by
    have hi := (le_inf hTS hTK).trans inf_normalizer_le_normalizer_inf
    exact (le_inf hTK (hi.trans (normalizer _).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  exact (le_inf
    ((le_inf (hb L hTL) (hb (residual H) (hTH.trans (le_normalizer_residual H)))).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)) hTS).trans
    (normalizer_inf_normalizer_le_normalizer_sup _ _)

variable (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (U : Model 4)
    (hc : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam.reverse))

include d h hH hp hc in
/-- An odd Hall subgroup containing the marked split torus gives a genuine
normalizer complement. The torus map is retained for outer-action calculations. -/
theorem Preparation.unitaryFive_torus_split_of_overlap_equiv
    (e : ChapterF.Source.commonBorel ![L,residual H] (sourceS L H) ≃* U.overlap) :
    let B := ChapterF.Source.commonBorel ![L,residual H] (sourceS L H)
    ∃ D : Subgroup G, D ≤ B ∧ IsHallSubgroup oddPrimes (D.subgroupOf B) ∧
      (B.subtype.comp (e.symm.toMonoidHom.comp
        (SourceTorus.flagTorus U.form U.rightLeviTrace U.rightLeviTrace_spec U.matrix))).range ≤ D ∧
      Disjoint (sourceS L H) (normalizer (D : Set G)) ∧
      (T : Set G) = (sourceS L H : Set G) *
        ((T : Subgroup G) ⊓ normalizer (D : Set G) : Set G) := by
  let B := ChapterF.Source.commonBorel ![L,residual H] (sourceS L H)
  let hf := d.hypothesisF11 h hH.1.1.2
  have hSB : sourceS L H ≤ B := le_sup_right
  have hBS : B ≤ normalizer (sourceS L H : Set G) := by
    have hh := hf.commonBorel_normalizes_localSylow 0
    change B ≤ normalizer ((sourceS L H ⊓ L : Subgroup G) : Set G) at hh
    have hs := d.unitaryFive_sourceS_eq h hH.1.1.2 hp U hc
    simpa only [hs,inf_assoc,inf_idem] using hh
  let tau : ((FixedBy.subfield U.F U.form.conj)ˣ × (FixedBy.subfield U.F U.form.conj)ˣ) →* U.overlap :=
    SourceTorus.flagTorus U.form U.rightLeviTrace U.rightLeviTrace_spec U.matrix
  let rho := B.subtype.comp (e.symm.toMonoidHom.comp tau)
  have hR : rho.range ≤ B := by
    rintro _ ⟨x,rfl⟩
    exact (e.symm (tau x)).property
  have ho : Odd (Nat.card rho.range) := by
    apply Odd.of_dvd_nat _ (Subgroup.card_range_dvd rho)
    rw [SourceTorus.torus_parameter_card U.form U.conjugation U.local_field_card]
    decide
  obtain ⟨D,hRD,hDB,hHall⟩ := exists_hall_containing_odd B rho.range hf.commonBorel_solvable hR ho
  have hodd : ¬ 2 ∣ Nat.card D := by
    intro hd
    apply hHall.p_in_pi_of_p_dvd_card ⟨2,Nat.prime_two⟩ _ rfl
    rwa [Nat.card_congr (subgroupOfEquivOfLe hDB).toEquiv]
  have hdis : Disjoint (sourceS L H) D := by
    obtain ⟨k,hk⟩ := hf.S_isP.exists_card_eq
    apply disjoint_of_coprime_natCard
    rw [hk]
    exact (Nat.prime_two.coprime_iff_not_dvd.mpr hodd).pow_left k
  have hdisN : Disjoint (sourceS L H) (normalizer (D : Set G)) := by
    apply disjoint_def.mpr
    intro x hx hn
    have hcomm (y : G) (hy : y ∈ D) : Commute x y := by
      have hzD : x*y*x⁻¹*y⁻¹ ∈ D := D.mul_mem
        ((mem_normalizer_iff.mp hn y).mp hy) (D.inv_mem hy)
      have hzS : x*y*x⁻¹*y⁻¹ ∈ sourceS L H := by
        have hh := (sourceS L H).mul_mem hx
          ((mem_normalizer_iff.mp (hBS (hDB hy)) x⁻¹).mp ((sourceS L H).inv_mem hx))
        simpa only [mul_assoc] using hh
      have hz := disjoint_def.mp hdis hzS hzD
      calc
        x*y = (x*y*x⁻¹*y⁻¹)*(y*x) := by group
        _ = y*x := by rw [hz,one_mul]
    let xb : B := ⟨x,hSB hx⟩
    obtain ⟨k,hk⟩ := hf.S_isP.exists_pow_pow_eq_one ⟨x,hx⟩
    have hxp : (e xb).val^(2^k)=1 := by
      have hh : xb^(2^k)=1 := Subtype.ext (congrArg (fun z : sourceS L H => z.val) hk)
      exact congrArg Subtype.val ((map_pow e xb (2^k)).symm.trans
        ((congrArg e hh).trans e.map_one))
    have hxt (a b : (FixedBy.subfield U.F U.form.conj)ˣ) :
        Commute (e xb).val (project U.form
          (SmallCompletion.FiveFixed.torus U.form U.rightLeviTrace U.rightLeviTrace_spec U.matrix a b)) := by
      let y := e.symm (tau (a,b))
      have hxy : Commute xb y := Subtype.ext (hcomm y.val (hRD ⟨(a,b),rfl⟩))
      have hh := hxy.map e.toMonoidHom
      change Commute (e xb) (e y) at hh
      dsimp only [y] at hh
      rw [e.apply_symm_apply] at hh
      exact hh.map U.overlap.subtype
    have hxe := SourceTorus.projective_two_element_centralizer U.form U.rightLeviTrace
      U.rightLeviTrace_spec U.matrix U.conjugation U.local_field_card (e xb).val k hxp hxt
    have hxb : xb=1 := e.injective ((Subtype.ext hxe).trans e.map_one.symm)
    exact congrArg Subtype.val hxb
  obtain ⟨P,hP⟩ := hf.sylow_commonBorel
  exact ⟨D,hDB,hHall,hRD,hdisN,normal_sylow_frattini B (sourceS L H) (T : Subgroup G) D
    hf.commonBorel_solvable (sourceS_le_sylow h.sylow_normalizes hH.1.1.2)
    (source_common_borel_normalized h.sylow_normalizes hH.1.1.2) P hP hDB hHall⟩

include d h hH hp hc in
/-- The source Sylow splits over S, using the supplied full-normalizer marking. -/
theorem Preparation.unitaryFive_sylow_complement
    (r : UnitaryFiveNormalizerMarking L (residual H) ((T : Subgroup G) ⊓ L) U) :
    ∃ B : Subgroup G, B ≤ (T : Subgroup G) ∧ Disjoint (sourceS L H) B ∧
      (T : Set G) = (sourceS L H : Set G) * (B : Set G) ∧
      IsCyclic B ∧ Nat.card B = (sourceS L H).relIndex (T : Subgroup G) := by
  have hs := d.unitaryFive_sourceS_eq h hH.1.1.2 hp U hc
  have hf := d.hypothesisF11 h hH.1.1.2
  have he : Nonempty (ChapterF.Source.commonBorel ![L,residual H] (sourceS L H) ≃* U.overlap) := by
    rcases r.marking with ⟨a,f,hreal⟩ | ⟨a,f,hreal⟩
    · exfalso
      apply d.not_unitaryFive_unreversed h hH.1.1.2 hp U
      rw [hs]
      exact ⟨a.comparison⟩
    · have hh := ChapterF.Source.lemma_F_1_3_6 hf
      rw [hs] at hh ⊢
      exact ⟨(MulEquiv.subgroupCongr hh.symm).trans a.comparison.middle⟩
  obtain ⟨D,hDB,hHall,_,hdis,hsplit⟩ :=
    d.unitaryFive_torus_split_of_overlap_equiv h hH hp U hc he.some
  let B := (T : Subgroup G) ⊓ normalizer (D : Set G)
  have hBT : B ≤ (T : Subgroup G) := inf_le_left
  have hd : Disjoint (sourceS L H) B := hdis.mono_right inf_le_right
  have hST := sourceS_le_sylow h.sylow_normalizes hH.1.1.2
  have hcomp : IsComplement' ((sourceS L H).subgroupOf (T : Subgroup G))
      (B.subgroupOf (T : Subgroup G)) := by
    apply isComplement'_of_disjoint_and_mul_eq_univ
    · apply disjoint_def.mpr
      intro x hx hy
      exact Subtype.ext (disjoint_def.mp hd hx hy)
    · apply Set.eq_univ_iff_forall.mpr
      intro x
      have hx : x.val ∈ (sourceS L H : Set G) * (B : Set G) := hsplit ▸ x.property
      obtain ⟨s,hs,b,hb,he⟩ := hx
      exact ⟨⟨s,hST hs⟩,hs,⟨b,hBT hb⟩,hb,Subtype.ext he⟩
  refine ⟨B,hBT,hd,hsplit,?_,?_⟩
  · obtain ⟨F,_,_,hF,⟨e⟩⟩ := h.linear
    let := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using hF)
    let : IsCyclic (F ≃+* F) := Theory.PSL2.OuterSolvable.finiteFieldAut_isCyclic
    let phi := (unitaryFiveSylowFieldAction h.sylow_normalizes e).comp (inclusion hBT)
    apply isCyclic_of_injective phi
    apply (MonoidHom.ker_eq_bot_iff phi).mp
    apply bot_unique
    intro x hx
    have hxS : x.val ∈ sourceS L H := by
      have hh : inclusion hBT x ∈ (unitaryFiveSylowFieldAction h.sylow_normalizes e).ker := hx
      rw [d.unitaryFive_sylow_field_kernel h hH hp U hc e] at hh
      exact hh
    exact Subtype.ext (disjoint_def.mp hd hxS x.property)
  · rw [←Nat.card_congr (subgroupOfEquivOfLe hBT).toEquiv]
    exact hcomp.symm.index_eq_card.symm

include d h hH hp hc in
/-- Strict enlargement of S supplies an actual order-two element outside S. -/
theorem Preparation.unitaryFive_exists_outer_involution
    (r : UnitaryFiveNormalizerMarking L (residual H) ((T : Subgroup G) ⊓ L) U)
    (hST : sourceS L H < (T : Subgroup G)) :
    ∃ t : T, orderOf t=2 ∧ t.val ∉ sourceS L H := by
  obtain ⟨B,hBT,hdis,hsplit,hcyc,hcard⟩ := d.unitaryFive_sylow_complement h hH hp U hc r
  have hB : B ≠ ⊥ := by
    intro hb
    apply hST.ne
    apply le_antisymm hST.le
    apply relIndex_eq_one.mp
    rw [←hcard,hb,Nat.card_unique]
  let : Nontrivial B := B.nontrivial_iff_ne_bot.mpr hB
  obtain ⟨k,hk⟩ := (T.isPGroup'.to_le hBT).exists_card_eq
  have hkpos : 0<k := by
    have hh := Finite.one_lt_card (α := B)
    rw [hk] at hh
    by_contra hn
    have hz : k=0 := by omega
    simp [hz] at hh
  obtain ⟨b,hb⟩ := exists_prime_orderOf_dvd_card' (G := B) 2
    (hk ▸ dvd_pow_self 2 (by omega))
  refine ⟨⟨b.val,hBT b.property⟩,?_,?_⟩
  · exact (Subgroup.orderOf_coe ⟨b.val,hBT b.property⟩).symm.trans
      ((Subgroup.orderOf_coe b).trans hb)
  · intro hs
    have he := disjoint_def.mp hdis hs b.property
    have he' : b=1 := Subtype.ext he
    rw [he',orderOf_one] at hb
    omega

include d h hH hp hc in
/-- The same middle map transports the full Sylow and identifies its exact
inner intersection. If S<T, its image contains an outer involution. -/
theorem Preparation.unitaryFive_marked_sylow_split
    (r : UnitaryFiveNormalizerMarking L (residual H) ((T : Subgroup G) ⊓ L) U) :
    ∃ a : UnitarySource.MarkedMiddleAction L (residual H) ((T : Subgroup G) ⊓ L) U.amalgam.reverse,
    ∃ f : UnitaryNativeLift.Five.LiftReverse U a,
    ∃ F : RankTwoAmalgam.Iso (UnitaryCompletion.normalizerDiagram L (residual H))
        r.extension.amalgam.reverse,
      (∀ x, (F.left (inclusion r.left_le x)).val = MulAut.conj (a.comparison.left x).val) ∧
      (∀ x, (F.right (inclusion r.right_le x)).val = MulAut.conj (a.comparison.right x).val) ∧
      (∀ z, (F.middle z).val = (f.action z).val) ∧
      r.extension.carrier = ChapterF.SourceCompletion.UnitaryNonbinary.inner U.Carrier ⊔
        ((Chapter5.UnitaryNativeLift.Five.flagAutomorphisms U).subtype.comp f.action).range ∧
      r.extension.left = U.leftParabolic.map MulAut.conj ⊔
        ((Chapter5.UnitaryNativeLift.Five.flagAutomorphisms U).subtype.comp f.action).range ∧
      r.extension.right = U.rightParabolic.map MulAut.conj ⊔
        ((Chapter5.UnitaryNativeLift.Five.flagAutomorphisms U).subtype.comp f.action).range ∧
      r.extension.middle =
        ((Chapter5.UnitaryNativeLift.Five.flagAutomorphisms U).subtype.comp f.action).range ∧
      let D := normalizer (L : Set G) ⊓ normalizer (residual H : Set G)
      ∃ P : Sylow 2 r.extension.middle,
        (P : Subgroup r.extension.middle) =
          ((T : Subgroup G).subgroupOf D).map F.middle.toMonoidHom ∧
        (P : Subgroup r.extension.middle) ⊓ (ChapterF.SourceCompletion.UnitaryNonbinary.inner U.Carrier).comap r.extension.middle.subtype =
          ((sourceS L H).subgroupOf D).map F.middle.toMonoidHom ∧
        (sourceS L H < (T : Subgroup G) →
          ∃ t : D, t.val ∈ (T : Subgroup G) ∧ orderOf t=2 ∧
            F.middle t ∈ (P : Subgroup r.extension.middle) ∧
            (F.middle t).val ∉ ChapterF.SourceCompletion.UnitaryNonbinary.inner U.Carrier) := by
  have hs := d.unitaryFive_sourceS_eq h hH.1.1.2 hp U hc
  have hf := d.hypothesisF11 h hH.1.1.2
  have hST := sourceS_le_sylow h.sylow_normalizes hH.1.1.2
  rcases r.marking with ⟨a,f,F,h0,h1,hD,hE,hleft,hright,hmiddle⟩ |
    ⟨a,f,F,h0,h1,hD,hE,hleft,hright,hmiddle⟩
  · exfalso
    apply d.not_unitaryFive_unreversed h hH.1.1.2 hp U
    rw [hs]
    exact ⟨a.comparison⟩
  · let D := (normalizerAmalgam L (residual H)).M₁₂
    have hTD : (T : Subgroup G) ≤ D :=
      le_inf h.sylow_normalizes (hH.1.1.2.trans (le_normalizer_residual H))
    let P := (T.subtype hTD).mapSurjective (f := F.middle.toMonoidHom) F.middle.surjective
    let B := ChapterF.Source.commonBorel ![L,residual H] (sourceS L H)
    obtain ⟨Q,hQ⟩ := hf.sylow_commonBorel
    have hQT : (Q : Subgroup B) ≤ (T : Subgroup G).subgroupOf B :=
      map_le_iff_le_comap.mp (hQ.le.trans hST)
    have hTB : (T : Subgroup G).subgroupOf B = (Q : Subgroup B) :=
      Q.is_maximal' T.isPGroup'.comap_subtype hQT
    have hinner (z : D) (hz : z.val ∈ (T : Subgroup G)) :
        (F.middle z).val ∈ ChapterF.SourceCompletion.UnitaryNonbinary.inner U.Carrier ↔ z.val ∈ sourceS L H := by
      erw [hD z,UnitaryFullNormalizer.five_inner_preimage_reverse f z]
      have hBB := ChapterF.Source.lemma_F_1_3_6 hf
      rw [hs] at hBB
      rw [hBB,←hs]
      change z.val ∈ B ↔ z.val ∈ sourceS L H
      constructor
      · intro hb
        have hq : (⟨z.val,hb⟩ : B) ∈ (Q : Subgroup B) := hTB ▸ hz
        exact hQ ▸ mem_map_of_mem B.subtype hq
      · intro hzS
        exact (show sourceS L H ≤ B from le_sup_right) hzS
    refine ⟨a,f,F,h0,h1,hD,hE,hleft,hright,hmiddle,P,rfl,?_,?_⟩
    · ext x
      obtain ⟨z,rfl⟩ := F.middle.surjective x
      change (F.middle z ∈ ((T : Subgroup G).subgroupOf D).map F.middle.toMonoidHom ∧
        (F.middle z).val ∈ ChapterF.SourceCompletion.UnitaryNonbinary.inner U.Carrier) ↔
        F.middle z ∈ ((sourceS L H).subgroupOf D).map F.middle.toMonoidHom
      constructor
      · rintro ⟨⟨w,hw,hwz⟩,hi⟩
        have hwz' : w=z := F.middle.injective hwz
        subst w
        exact ⟨z,(hinner z hw).mp hi,rfl⟩
      · rintro ⟨w,hw,hwz⟩
        have hwz' : w=z := F.middle.injective hwz
        subst w
        exact ⟨⟨z,hST hw,rfl⟩,(hinner z (hST hw)).mpr hw⟩
    · intro hlt
      obtain ⟨t,ht,hto⟩ := d.unitaryFive_exists_outer_involution h hH hp U hc r hlt
      let z : D := ⟨t.val,hTD t.property⟩
      refine ⟨z,t.property,?_,mem_map_of_mem F.middle.toMonoidHom t.property,?_⟩
      · exact (Subgroup.orderOf_coe z).symm.trans ((Subgroup.orderOf_coe t).trans ht)
      · exact fun hi => hto ((hinner z t.property).mp hi)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
