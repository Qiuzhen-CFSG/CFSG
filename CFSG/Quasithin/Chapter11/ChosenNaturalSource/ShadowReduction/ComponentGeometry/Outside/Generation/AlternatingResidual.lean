module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Generation.CoreImage
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Generation.AlternatingResidual.Model
public import Theory.SpecificGroups.Alternating.FiveTwoCoreExtension

/-!
# The remaining original field-four residual and its cubic Hall actor

Every hypothetical outside H with n(H)>1 has O₂(H)=R₁ and a normal
escaping component equal to its literal O²(H). Its quasisimple two-core
quotient is A₅, so H/O₂(H) is A₅ or S₅ and n(H)=2. This proves the
universal upper bound two without an abstract uniqueness claim for A₅
subgroups in prime PSL₂.

The full source Hall actor is cyclic of order three. Point-intersection
geometry puts it in the original seed normalizer, so even in the SL₃ row
the proved seed-preserving cubic theorem places it in L. It lies in K
through the literal two-residual, acts faithfully on V, permutes with T,
and its normalizer escapes M. Excluding this remaining configuration,
and hence universal 11.4.4, remains unfinished.

Earlier geometry, full 11.3.2, fixed spaces and Kz=K retain the producers
listed in CoreImage. OddKernelNormalizer remains with
qt-d-1222-natural-odd-kernel-normalizer; the parent
qt-d-1222-shadow-components owns final discharge of these source inputs.
Source: Aschbacher–Smith 11.4.4, printed p.778 of refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Generation
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V}
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)

/-- A hypothetical counterexample has generation exactly two. Its escaping
residual has actual two-core quotient A₅, and H/O₂(H) is A₅ or S₅. -/
theorem ofFlag_large_generation_two_core_models
    (h : Comparison.EarlierGeometry (ofFlag S f X z H))
    (hcase : Source.ClassicalRefinementCase L (f.Li 0) (ofFlag S f X z H).K 1 S.field.degree)
    (he : (ofFlag S f X z H).Kz = (ofFlag S f X z H).K)
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ J, Hypothesis1131At D S (ofFlag S f X z H).point J →
      Proposition1132At D S (ofFlag S f X z H).point J)
    (hcontrol : LocalGeometry.WeakClosure.Generation.OddKernelNormalizer
      (T := T) (L := L) (V := V))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hHz : H ≤ Gz (ofFlag S f X z H))
    (hn : 1 < ChapterE.generationParameter H) :
    S.field.degree = 2 ∧ H.pCoreIn 2 = f.Ri 0 ∧
      ChapterE.generationParameter H = 2 ∧
      (Nonempty ((H ⧸ pCore 2 H) ≃* alternatingGroup (Fin 5)) ∨
        Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 5))) ∧
      let I := (pResidual 2 H).map H.subtype
      (I.subgroupOf H).IsCComponent ∧ (I.subgroupOf H).Normal ∧
        I ∈ Chapter1.L G (T : Subgroup G) ∧
        ¬ I ≤ normalizer (L : Set G) ∧ I ≤ (ofFlag S f X z H).K ∧
        Nonempty ((I ⧸ pCore 2 I) ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨hdeg,hcore,I,hIH,hI,hlocal,hout,hjoin,hIK,hnormal,hres,hm⟩ :=
    ofFlag_large_generation_alternating_five S f X z H h hcase he
      hlinear h1132 hcontrol hH hHz hn
  let I' := I.subgroupOf H
  let : I'.Normal := hnormal
  let ei : I' ≃* I := subgroupOfEquivOfLe hIH
  let er := QuotientGroup.congr (solvableRadical I') (solvableRadical I)
    ei (map_solvableRadical_equiv ei)
  have hm' : Nonempty ((I' ⧸ solvableRadical I') ≃* alternatingGroup (Fin 5)) :=
    hm.map fun e => er.trans e
  have hg : I' ⊔ (T.subtype hH.1.1.2 : Subgroup H) = ⊤ := by
    change I.subgroupOf H ⊔ (T : Subgroup G).subgroupOf H = ⊤
    rw [← subgroupOf_sup hIH hH.1.1.2,hjoin,subgroupOf_self]
  have hb := generation_le_two_of_alternating_radical_component (T.subtype hH.1.1.2)
    I' hI hg hm'
  have hQ : IsSQTK KnownSimple.IsKnownSimple H :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hHz)).mp
      ((S.source.simpleQTKE.twoLocal_sqtk
        (point_twoLocal (ofFlag S f X z H) h.point_mem h.point_fixed h.point_ne_one)).subgroup
          (H.subgroupOf (Gz (ofFlag S f X z H))))
  obtain ⟨hP,_,_,_,_⟩ := LocalGeometry.WeakClosure.Generation.hall_data D S hH hn
  let : IsQuasisimple (I' ⧸ pCore 2 I') :=
    normal_component_core_quasisimple hQ (T.subtype hH.1.1.2) hP I' hI hg
  obtain ⟨em⟩ := core_quotient_alternating_five_of_radical hm'
  let ec : (I' ⧸ pCore 2 I') ≃* (I ⧸ pCore 2 I) :=
    QuotientGroup.congr (pCore 2 I') (pCore 2 I) ei (pCore_map_iso 2 ei)
  let emI : (I ⧸ pCore 2 I) ≃* alternatingGroup (Fin 5) := ec.symm.trans em
  have hTI : (T : Subgroup G) ≤ normalizer (I : Set G) :=
    hH.1.1.2.trans ((normal_subgroupOf_iff_le_normalizer hIH).mp hnormal)
  have hmodels := Theory.SpecificGroups.Alternating.FiveExtensionAction.core_quotient_of_two_supplement
    I (T : Subgroup G) hTI T.isPGroup' emI
  rw [hjoin] at hmodels
  refine ⟨hdeg,hcore,by omega,hmodels,?_⟩
  dsimp only
  rw [←hres]
  exact ⟨hI,hnormal,hlocal,hout,hIK,⟨emI⟩⟩

/-- Every original outside H has E-generation parameter at most two.
The remaining value two has the full alternating residual described above. -/
theorem ofFlag_generation_le_two
    (h : Comparison.EarlierGeometry (ofFlag S f X z H))
    (hcase : Source.ClassicalRefinementCase L (f.Li 0) (ofFlag S f X z H).K 1 S.field.degree)
    (he : (ofFlag S f X z H).Kz = (ofFlag S f X z H).K)
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ J, Hypothesis1131At D S (ofFlag S f X z H).point J →
      Proposition1132At D S (ofFlag S f X z H).point J)
    (hcontrol : LocalGeometry.WeakClosure.Generation.OddKernelNormalizer
      (T := T) (L := L) (V := V))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hHz : H ≤ Gz (ofFlag S f X z H)) :
    ChapterE.generationParameter H ≤ 2 := by
  by_cases hn : ChapterE.generationParameter H ≤ 1
  · exact hn.trans (by decide)
  have heq := (ofFlag_large_generation_two_core_models S f X z H h hcase he
    hlinear h1132 hcontrol hH hHz (by omega)).2.2.1
  exact heq.le

open scoped Pointwise

private theorem field_four_cubic_le_component
    (h : Comparison.EarlierGeometry (ofFlag S f X z H))
    (hfour : S.field.degree = 2)
    (B : Subgroup G) (hcard : Nat.card B = 3)
    (hBM : B ≤ normalizer (L : Set G))
    (hBz : B ≤ Gz (ofFlag S f X z H)) : B ≤ L := by
  have hBV := (le_inf hBM hBz).trans
    (point_intersection_normalizes_seed (ofFlag S f X z H)
      ((ofFlag S f X z H).V₁_le h.point_mem) h.point_ne_one)
  intro b hb
  by_cases hb1 : b = 1
  · exact hb1 ▸ L.one_mem
  have hbo : orderOf b = 3 := by
    have hd := B.orderOf_dvd_natCard hb
    rw [hcard] at hd
    exact ((Nat.dvd_prime (by decide : Nat.Prime 3)).mp hd).resolve_left
      (fun hh => hb1 (orderOf_eq_one_iff.mp hh))
  cases c with
  | sl3 m =>
    exact LocalGeometry.Preliminary.sl3_orderThree_mem_of_normalizes_seed D S m
      (hfour ▸ (by decide)) (hBM hb) (hBV hb) hbo
  | sp4 m =>
    exact LocalGeometry.Preliminary.orderPrime_mem_component D S (by decide : Nat.Prime 3)
      (Or.inl ⟨Or.inl ⟨m⟩,by rw [hfour]; norm_num⟩) (hBM hb) hbo
  | g2 m =>
    exact LocalGeometry.Preliminary.orderPrime_mem_component D S (by decide : Nat.Prime 3)
      (Or.inl ⟨Or.inr ⟨m⟩,by rw [hfour]; norm_num⟩) (hBM hb) hbo

/-- The remaining original H has a faithful cubic Hall actor inside L and K.
Its Sylow product and escaping normalizer are the actual source ones. -/
theorem ofFlag_large_generation_cubic_hall
    (h : Comparison.EarlierGeometry (ofFlag S f X z H))
    (hcase : Source.ClassicalRefinementCase L (f.Li 0) (ofFlag S f X z H).K 1 S.field.degree)
    (he : (ofFlag S f X z H).Kz = (ofFlag S f X z H).K)
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ J, Hypothesis1131At D S (ofFlag S f X z H).point J →
      Proposition1132At D S (ofFlag S f X z H).point J)
    (hcontrol : LocalGeometry.WeakClosure.Generation.OddKernelNormalizer
      (T := T) (L := L) (V := V))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hHz : H ≤ Gz (ofFlag S f X z H))
    (hn : 1 < ChapterE.generationParameter H) :
    ∃ B : Subgroup G, Nat.card B = 3 ∧
      B ≤ H ⊓ normalizer (L : Set G) ∧ B ≤ L ⊓ (ofFlag S f X z H).K ∧
      B ⊓ centralizer (V : Set G) = ⊥ ∧
      (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G) ∧
      ¬ normalizer (B : Set G) ≤ normalizer (L : Set G) := by
  obtain ⟨hfour,_,hn2,hmodels,hr⟩ := ofFlag_large_generation_two_core_models S f X z H
    h hcase he hlinear h1132 hcontrol hH hHz hn
  obtain ⟨hP,n,_,hb,d,hm,hperm⟩ := LocalGeometry.WeakClosure.Generation.hall_data D S hH hn
  have hn' : 2 ≤ n := by omega
  obtain ⟨_,hcard,_⟩ := hall_card_three_of_five_core_models hmodels
    (T.subtype hH.1.1.2) hP hn' d
  let B := d.witness.abelianGroup.map H.subtype
  have hcardB : Nat.card B = 3 := by
    rw [card_map_of_injective H.subtype_injective,hcard]
  have hBM : B ≤ normalizer (L : Set G) :=
    map_le_iff_le_comap.mpr (d.hall_le.trans hm.le)
  have hBH : B ≤ H := map_subtype_le _
  have hBN : d.witness.abelianGroup ≤ pResidual 2 H := by
    intro b hb
    exact mem_pResidual_of_orderOf_coprime
      (d.witness.odd.coprime_two_left.of_dvd_right
        (d.witness.abelianGroup.orderOf_dvd_natCard hb))
  have hBK : B ≤ (ofFlag S f X z H).K := (map_mono hBN).trans hr.2.2.2.2.1
  have hBe : IsElementaryAbelian 3 d.witness.abelianGroup :=
    { toIsMulCommutative := d.witness.abelian
      exponent_dvd_p := hcard ▸ Group.exponent_dvd_nat_card }
  exact ⟨B,hcardB,le_inf hBH hBM,
    le_inf (field_four_cubic_le_component S f X z H h hfour B hcardB hBM (hBH.trans hHz)) hBK,
    LocalGeometry.WeakClosure.Generation.hall_faithful D S hcontrol hH hn hP d hm,
    hperm,LocalGeometry.WeakClosure.Generation.elementary_hall_escape D S hH hn hP d
      (by decide : Nat.Prime 3) d.witness.abelianGroup hBe le_rfl hperm⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Generation
