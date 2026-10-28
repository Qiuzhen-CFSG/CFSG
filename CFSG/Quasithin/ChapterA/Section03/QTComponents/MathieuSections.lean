module
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.SimpleException
public import CFSG.Quasithin.ChapterI.Section03.ComponentQuotients
public import Theory.SpecificGroups.SU3.Quasisimplicity
public import Theory.Mathieu.PositiveLocalCubicRank
public import Theory.Mathieu.M22.Properties.FixedHexads
public import Theory.Mathieu.M22.Properties.ThreeRank
public import Theory.Quasithin.ProductLocalRank
public import Theory.GroupTheory.SimpleSectionSolvableReduction.Model
public import Theory.GroupTheory.GeneralizedFitting.TwoCoreImageComparison

/-!
# Mathieu sections in a quasithin K-group

Two M₂₂ factors have local cubic rank at least three. Theorem A's exceptional
unitary pair cannot have an M₂₂ quotient: the defining two-part of either
unitary factor's simple quotient is already larger than the two-part of M₂₂.
Thus no such product is a section of a quasithin K-group. Passing through
the literal solvable cores of distinct two-components then proves that a
two-component containing an M₂₂ section is normal.

The actual simple core quotient of every two-component is also placed on
the full Theorem B list, applying Theorem A to the actual section and
retaining its exceptional alternative. No quotient quasithinness is assumed.

Source: Aschbacher--Smith A.2.1--2 and I.3.2; the component promotion in
4.2.13, printed p.612.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin CFSG.Quasithin.ChapterA.Section02
open BenderSuzuki.MatrixGroups Sporadic.Mathieu

namespace CFSG.Quasithin.ChapterA.QTComponents
universe u
private theorem m22_quasisimple : IsQuasisimple M22 := by
  let : IsSimpleGroup M22 := m22_isSimpleGroup
  have hna : ¬ IsMulCommutative M22 := by
    intro ha
    let := ha
    exact bot_ne_top (m22_center_eq_bot.symm.trans center_eq_top)
  let : Group.IsPerfect M22 := ⟨
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal (_root_.commutator M22) inferInstance).resolve_left
      (fun h => hna ((commutator_eq_bot_iff M22).mp h))⟩
  exact ⟨((QuotientGroup.quotientMulEquivOfEq m22_center_eq_bot).trans
    QuotientGroup.quotientBot).isSimpleGroup⟩

private theorem unitary_hom_m22_trivial {U : Type*} [Group U] [Finite U]
    [IsQuasisimple U] {n : ℕ} (hn : 3 ≤ n)
    (hm : IsSpecialUnitaryModel U 3 (2 ^ n)) (f : U →* M22) : f.range = ⊥ := by
  by_contra hne
  let : Nontrivial f.range := (nontrivial_iff_ne_bot _).mpr hne
  let : IsQuasisimple f.range := IsQuasisimple.of_surjective f.rangeRestrict
    f.rangeRestrict_surjective
  let e := IsQuasisimple.centralQuotientEquiv f.rangeRestrict f.rangeRestrict_surjective
  have hd : Nat.card (U ⧸ center U) ∣ Nat.card M22 := by
    rw [Nat.card_congr e.toEquiv]
    exact (card_quotient_dvd_card _).trans f.range.card_subgroup_dvd_card
  obtain ⟨F,_,_,J,hF,hconj,⟨a⟩⟩ := hm.projectiveModel (by omega)
  have hc := J.cube_dvd_card_projective hF
    (FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n (by omega) hF hconj)
  rw [← Nat.card_congr a.toEquiv] at hc
  have h512 : 2 ^ 9 ∣ Nat.card M22 :=
    (pow_dvd_pow 2 (by omega : 9 ≤ n * 3)).trans (by simpa only [pow_mul] using hc.trans hd)
  rw [m22_order] at h512
  norm_num at h512

private theorem no_unitary_exception_m22_quotient {G S : Type*} [Group G] [Finite G]
    [Group S] (f : S →* M22) (hf : Function.Surjective f) :
    ¬ TheoremAException G S 3 := by
  rintro ⟨_,U,_,⟨e⟩,⟨d⟩⟩
  let g := f.comp (e.symm.toMonoidHom.comp (QuotientGroup.mk' (center U)))
  have hg : Function.Surjective g := hf.comp
    (e.symm.surjective.comp (QuotientGroup.mk'_surjective _))
  let := d.first_component.2
  let := d.second_component.2
  have ha := unitary_hom_m22_trivial d.first_large d.first_model (g.comp d.first.subtype)
  have hb := unitary_hom_m22_trivial d.second_large d.second_model (g.comp d.second.subtype)
  let : IsSimpleGroup M22 := m22_isSimpleGroup
  obtain ⟨y,hy⟩ := exists_ne (1 : M22)
  obtain ⟨u,rfl⟩ := hg y
  obtain ⟨a,b,hab⟩ := d.product u
  apply hy
  rw [← hab,map_mul]
  have ha1 := mem_bot.mp (ha ▸ (show (g.comp d.first.subtype) a ∈
    (g.comp d.first.subtype).range from ⟨a,rfl⟩))
  have hb1 := mem_bot.mp (hb ▸ (show (g.comp d.second.subtype) b ∈
    (g.comp d.second.subtype).range from ⟨b,rfl⟩))
  exact (congrArg₂ (· * ·) ha1 hb1).trans (one_mul 1)

private theorem semisimple_prod {A B : Type*} [Group A] [Group B]
    [IsQuasisimple A] [IsQuasisimple B] : IsSemisimple (A × B) := by
  let X := (MonoidHom.inl A B).range
  let Y := (MonoidHom.inr A B).range
  have hX : X = (MonoidHom.snd A B).ker := by
    ext x
    simp only [X,MonoidHom.mem_range,MonoidHom.mem_ker]
    constructor
    · rintro ⟨a,rfl⟩; rfl
    · intro hx; exact ⟨x.1,Prod.ext rfl hx.symm⟩
  have hY : Y = (MonoidHom.fst A B).ker := by
    ext x
    simp only [Y,MonoidHom.mem_range,MonoidHom.mem_ker]
    constructor
    · rintro ⟨b,rfl⟩; rfl
    · intro hx; exact ⟨x.2,Prod.ext hx.symm rfl⟩
  let : X.Normal := hX ▸ inferInstance
  let : Y.Normal := hY ▸ inferInstance
  have hcX : IsComponent (A × B) X := ⟨(inferInstance : X.Normal).isSubnormal,
    IsQuasisimple.of_mulEquiv (MonoidHom.ofInjective
      (show Function.Injective (MonoidHom.inl A B) from fun _ _ he => congrArg Prod.fst he))⟩
  have hcY : IsComponent (A × B) Y := ⟨(inferInstance : Y.Normal).isSubnormal,
    IsQuasisimple.of_mulEquiv (MonoidHom.ofInjective
      (show Function.Injective (MonoidHom.inr A B) from fun _ _ he => congrArg Prod.snd he))⟩
  have hXL : X ≤ componentLayer (A × B) := le_sSup hcX
  have hYL : Y ≤ componentLayer (A × B) := le_sSup hcY
  apply top_unique
  rintro ⟨a,b⟩ _
  simpa using (componentLayer (A × B)).mul_mem (hXL ⟨a,rfl⟩) (hYL ⟨b,rfl⟩)

/-- A quasithin K-group has no section consisting of two actual M₂₂ factors. -/
theorem no_m22_pair_section {G A B : Type u} [Group G] [Finite G]
    [Group A] [Finite A] [Group B] [Finite B]
    (hG : IsQuasithin G) (hκ : IsKGroup KnownSimple.IsKnownSimple G)
    (a : A ≃* M22) (b : B ≃* M22) (hs : IsSectionOf (A × B) G) : False := by
  let := m22_quasisimple
  let : IsQuasisimple A := IsQuasisimple.of_mulEquiv a.symm
  let : IsQuasisimple B := IsQuasisimple.of_mulEquiv b.symm
  have hc := (ChapterA.Section02.theoremA_knownSimple hG hκ (A × B) hs
    semisimple_prod 3 (by decide) (by decide)).1
  have hno := no_unitary_exception_m22_quotient (G := G) (a.toMonoidHom.comp (MonoidHom.fst A B))
    (a.surjective.comp (fun x => ⟨(x,1),rfl⟩))
  have hup := (hc.resolve_right hno).1.trans (hc.resolve_right hno).2
  have hr : primeRank 3 B = 2 := (primeRank_equiv 3 b).trans m22_primeRank_three
  have hl : 1 ≤ twoLocalPrimeRank 3 A := m22_one_le_twoLocalPrimeRank_three.trans
    (twoLocalPrimeRank_le_of_injective 3 a.symm.toMonoidHom a.symm.injective)
  have hex : ∃ M : Subgroup A, IsTwoLocal M := by
    obtain ⟨P,hP,hne⟩ := (show IsComponent A ⊤ from
      ⟨.top,IsQuasisimple.of_mulEquiv topEquiv.symm⟩).exists_nontrivial_two_subgroup
    let Q := P.map (⊤ : Subgroup A).subtype
    have hQ : Q ≠ ⊥ := fun hh => hne
      ((map_eq_bot_iff_of_injective P (⊤ : Subgroup A).subtype_injective).mp hh)
    exact ⟨normalizer (Q : Set A),Q,hQ,hP.map _,rfl⟩
  have hp := Theory.Quasithin.ProductLocalRank.local_add_ordinary_le (B := B) 3 hex
  omega
end CFSG.Quasithin.ChapterA.QTComponents

namespace CFSG.Quasithin.ChapterA.QTComponents
/-- The genuine simple core quotient of an ambient two-component has a full
Theorem B model. Theorem A is applied to the actual section, including its
exceptional alternative, rather than assuming quotient quasithinness. -/
theorem twoComponent_simple_quotient_model
    {G : Type*} [Group G] [Finite G]
    (hG : IsQuasithin G) (hκ : IsKGroup KnownSimple.IsKnownSimple G)
    (X : Subgroup G) (hX : X.IsTwoComponent) :
    IsTheoremBModel (X ⧸ oddTwoCore X) := by
  let S := X ⧸ oddTwoCore X
  let := hX.isSimpleGroup_quotient_oddTwoCore
  let := hX.1.perfect
  let : Group.IsPerfect S := Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
  have hz : center S = ⊥ := (inferInstance : (center S).Normal).eq_bot_or_eq_top.resolve_right
    (fun hh => Group.IsPerfect.not_isMulCommutative S (center_eq_top_iff.mp hh))
  let : IsQuasisimple S := ⟨((QuotientGroup.quotientMulEquivOfEq hz).trans
    QuotientGroup.quotientBot).isSimpleGroup⟩
  have hs : IsSectionOf S G := ⟨X,QuotientGroup.mk' _,QuotientGroup.mk'_surjective _⟩
  have hsemi : IsSemisimple S := top_unique (le_sSup (show IsComponent S ⊤ from
    ⟨.top,IsQuasisimple.of_mulEquiv topEquiv.symm⟩))
  by_cases he : ∃ p, TheoremAException G S p
  · obtain ⟨p,hp⟩ := he
    exact hp.theoremBModel_of_simple
  · have hqt : IsQuasithin S := by
      apply isQuasithin_iff_twoLocalPrimeRank.mpr
      intro p hp ho
      have h := (ChapterA.Section02.theoremA_knownSimple hG hκ S hs hsemi p hp ho).1
      exact (h.resolve_right (fun hh => he ⟨p,hh⟩)).1.trans
        (h.resolve_right (fun hh => he ⟨p,hh⟩)).2
    exact ChapterA.Section02.theoremB_knownSimple inferInstance
      (Group.IsPerfect.not_isMulCommutative S) hqt ((hκ.subgroup X).quotient _)
end CFSG.Quasithin.ChapterA.QTComponents

namespace CFSG.Quasithin.ChapterA.QTComponents
universe u
private theorem product_sections {A B S : Type u} [Group A] [Group B] [Group S]
    (hA : IsSectionOf S A) (hB : IsSectionOf S B) : IsSectionOf (S × S) (A × B) := by
  obtain ⟨U,f,hf⟩ := hA
  obtain ⟨V,g,hg⟩ := hB
  refine ⟨U.prod V,(f.prodMap g).comp (U.prodEquiv V).toMonoidHom,?_⟩
  have hfg : Function.Surjective (f.prodMap g) := by
    rintro ⟨s,t⟩
    obtain ⟨u,rfl⟩ := hf s
    obtain ⟨v,rfl⟩ := hg t
    exact ⟨(u,v),rfl⟩
  exact hfg.comp (U.prodEquiv V).surjective

private theorem twoComponent_retains_simple_section
    {G S : Type u} [Group G] [Finite G] [Group S]
    [IsSimpleGroup S] [Group.IsPerfect S]
    (X : Subgroup G) (hX : X.IsTwoComponent) (hS : IsSectionOf S X) :
    IsSectionOf S (X ⧸ oddTwoCore X) := by
  let : Group.IsSolvable (pPrimeCore 2 X) := odd_order_theorem _
    (Nat.coprime_two_left.mp pPrimeCore_coprime_card)
  let : Group.IsSolvable (oddTwoCore X) := by
    rw [hX.oddTwoCore_eq_solvableRadical]
    infer_instance
  let m : Group.SolvableKernelModel X (X ⧸ oddTwoCore X) :=
    ⟨oddTwoCore X,inferInstance,inferInstance,MulEquiv.refl _⟩
  obtain ⟨U,f,hf⟩ := hS
  exact m.simple_section (Group.IsPerfect.not_isSolvable S) U f hf

/-- A two-component containing an actual M₂₂ section is normal even in a
merely quasithin K-group: distinct conjugates would give two such sections. -/
theorem twoComponent_normal_of_m22_section
    {G S : Type u} [Group G] [Finite G] [Group S]
    (hG : IsQuasithin G) (hκ : IsKGroup KnownSimple.IsKnownSimple G)
    (X : Subgroup G) (hX : X.IsTwoComponent)
    (e : S ≃* M22) (hS : IsSectionOf S X) : X.Normal := by
  let := m22_quasisimple
  let : IsSimpleGroup M22 := m22_isSimpleGroup
  let : IsSimpleGroup S := e.isSimpleGroup
  let : Group.IsPerfect S := Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  let : Finite S := Finite.of_injective e e.injective
  apply normal_iff_map_conj_eq.mpr
  intro g
  by_contra hne
  let Y := X.map (MulAut.conj g).toMonoidHom
  have hY := hX.map_equiv (MulAut.conj g)
  let a : X ≃* Y := (MulAut.conj g).subgroupMap X
  have hSY : IsSectionOf S Y := hS.ambient_injective a.toMonoidHom a.injective
  obtain ⟨f,_,_⟩ := ChapterI.ComponentQuotients.pair_quotient_equiv hX hY (fun hh => hne hh.symm)
  have hpair : IsSectionOf ((X ⧸ oddTwoCore X) × (Y ⧸ oddTwoCore Y)) G :=
    ⟨X ⊔ Y,f.toMonoidHom.comp (QuotientGroup.mk' (oddTwoCore ↥(X ⊔ Y))),
      f.surjective.comp (QuotientGroup.mk'_surjective _)⟩
  exact no_m22_pair_section hG hκ e e
    ((product_sections (twoComponent_retains_simple_section X hX hS)
      (twoComponent_retains_simple_section Y hY hSY)).trans hpair)
end CFSG.Quasithin.ChapterA.QTComponents
