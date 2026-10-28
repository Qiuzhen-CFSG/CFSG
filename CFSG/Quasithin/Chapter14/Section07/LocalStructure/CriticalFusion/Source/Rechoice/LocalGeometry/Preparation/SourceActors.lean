module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.RankThree.SourceAssembly
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.Preparation.Assembly
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Remarking
public import Theory.SpecificGroups.SL2.UpperUnipotent

/-!
# Reciprocal source actors without a simultaneous root marking

The reciprocal 14.7.39/66 placement, alternating image and the actual
14.7.69 order-two calculation produce a nonidentity alternating involution.
Sylow conjugacy aligns that involution in an auxiliary target marking.
Changing this marking keeps qH, the original conjugation action, U₀ and
all prepared source subgroups. The existing restricted-pairing theorem
therefore constructs both actual axes and the full four-group action.

The auxiliary coordinates are discarded before the original marked
normalizer and span calculations. No second critical rechoice and no
simultaneous alignment of the two upper roots is needed. The final theorem
constructs SourceGeometry from the genuine reciprocal source inputs,
removing the explicit marked reciprocal actor from SourceAssembly.

Source: Aschbacher–Smith, Remark14.7.39, Lemmas14.7.65–66, 14.7.69,
and the proof of14.7.70, printed pp.1073–1074.
-/

public section
noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.Preparation.SourceActors
open Subgroup Representation Chapter12.Section08
open Matrix.SpecialLinearGroup
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]

private theorem involution_conjugate_upper (g : SL2FourNatural.SL)
    (hg : g ≠ 1) (hg2 : g * g = 1) :
    ∃ k : SL2FourNatural.SL, ∃ t : SL2FourNatural.F, t ≠ 0 ∧
      g = k * SL2FourNatural.upper t * k⁻¹ := by
  have hp : IsPGroup 2 (zpowers g) := IsPGroup.of_card_dvd_pow (n := 1) (by
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_dvd_of_pow_eq_one (by simpa only [pow_two] using hg2))
  obtain ⟨P, hP⟩ := hp.exists_le_sylow
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq SL2FourNatural.SL
    (upperUnipotentSylow SL2FourNatural.F 2) P
  have hm : g ∈ (k • upperUnipotentSylow SL2FourNatural.F 2 : Sylow 2 SL2FourNatural.SL) :=
    hk ▸ hP (mem_zpowers g)
  have hm' : ∃ b ∈ upperUnipotent SL2FourNatural.F, k * b * k⁻¹ = g := by
    change g ∈ ((k • upperUnipotentSylow SL2FourNatural.F 2 :
      Sylow 2 SL2FourNatural.SL) : Subgroup SL2FourNatural.SL) at hm
    rw [Sylow.coe_subgroup_smul] at hm
    exact hm
  obtain ⟨b, hb, he⟩ := hm'
  obtain ⟨t, ht⟩ := (mem_upperUnipotent SL2FourNatural.F b).mp hb
  have hbt : b = SL2FourNatural.upper t :=
    ht.symm.trans (SL2FourCentralCover.upper_transvection t).symm
  refine ⟨k, t, ?_, (hbt ▸ he).symm⟩
  intro hz
  subst t
  have hb1 : b = 1 := by rw [← ht]; simp
  apply hg
  simpa [hb1] using he.symm

/-- An actual opposite actor, aligned only in auxiliary target coordinates. -/
theorem exists_reciprocal_marked_actor (d : Data T L V F W)
    (c : CriticalPath (L := L) F)
    (hUH : F.U ≤ conjugate F.H c.conjugator)
    (selection : c.RankSelection) (h69 : Nat.card (star F c.Uα) = 2)
    (heven : (F.U.subgroupOf (conjugate F.H c.conjugator)).map (reciprocalQuotient d c) ≤
      alternatingGroup (Fin 5)) :
    ∃ k : ChapterJ.S5, ∃ a : F.H, (a : G) ∈ conjugate F.U c.conjugator⁻¹ ∧
      ∃ t : SL2FourNatural.F, t ≠ 0 ∧
        (d.remark k).qH a = alternatingActor (d.remark k).naturalQuotient (SL2FourNatural.upper t) := by
  let A := (F.U.subgroupOf (conjugate F.H c.conjugator)).map (reciprocalQuotient d c)
  have hc : Nat.card A = 2 := opposite_image_card d c hUH selection h69
  obtain ⟨a, ha, _⟩ := (Nat.card_eq_two_iff' (1 : A)).mp hc
  obtain ⟨y, hy, he⟩ := a.property
  have hn : reciprocalQuotient d c y ≠ 1 := by
    intro hz
    exact ha (Subtype.ext (he.symm.trans hz))
  have hsq : reciprocalQuotient d c y * reciprocalQuotient d c y = 1 := by
    have hp : a ^ Nat.card A = 1 := pow_card_eq_one'
    rw [hc, pow_two] at hp
    have hp' : (a : ChapterJ.S5) * a = 1 := congrArg Subtype.val hp
    rwa [← he] at hp'
  have hmem : reciprocalQuotient d c y ∈ alternatingGroup (Fin 5) :=
    heven (mem_map_of_mem _ hy)
  let g := d.naturalQuotient.marking.symm ⟨reciprocalQuotient d c y, hmem⟩
  have hg : alternatingActor d.naturalQuotient g = reciprocalQuotient d c y :=
    congrArg Subtype.val (d.naturalQuotient.marking.apply_symm_apply _)
  have hg1 : g ≠ 1 := by intro hz; apply hn; rw [← hg, hz, map_one]
  have hg2 : g * g = 1 := by
    apply (Subtype.val_injective.comp d.naturalQuotient.marking.injective)
    change alternatingActor d.naturalQuotient (g * g) = alternatingActor d.naturalQuotient 1
    rw [map_mul, map_one, hg, hsq]
  obtain ⟨k, t, ht, hgt⟩ := involution_conjugate_upper g hg1 hg2
  refine ⟨alternatingActor d.naturalQuotient k, conjugateBack F.H c.conjugator y,
    ?_, t, ht, ?_⟩
  · apply mem_map.mpr
    refine ⟨y, hy, ?_⟩
    change c.conjugator⁻¹⁻¹ * (y : G) * (c.conjugator⁻¹⁻¹)⁻¹ = _
    simp only [inv_inv]
    rfl
  · change reciprocalQuotient d c y = alternatingActor d.naturalQuotient k *
      alternatingActor d.naturalQuotient (SL2FourNatural.upper t) *
      (alternatingActor d.naturalQuotient k)⁻¹
    rw [← hg, hgt, map_mul, map_mul, map_inv]

/-- The prepared source subgroups are unchanged by target remarking. -/
theorem preliminary_remark (d : Data T L V F W) (c : CriticalPath (L := L) F)
    (h : RankThree.Preliminary d c) (k : ChapterJ.S5) :
    RankThree.Preliminary (d.remark k) c := { h with }

open RankThree

/-- The literal pairing and four-group action from the reciprocal source
placement and alternating image. The cross commutators are also outputs. -/
theorem pairing_source_of_reciprocal (d : Data T L V F W)
    (c : CriticalPath (L := L) F) (h : Preliminary d c) (s : d.ActionDescent)
    (h21 : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1)
    (hUH : F.U ≤ conjugate F.H c.conjugator) (selection : c.RankSelection)
    (heven : (F.U.subgroupOf (conjugate F.H c.conjugator)).map (reciprocalQuotient d c) ≤
      alternatingGroup (Fin 5)) :
    CoreAxes c ∧
    Function.Surjective ((E c).normalizerMonoidHom.comp
      (inclusion (h.YE_normalizes h21.le))) ∧
    ((YE c).subgroupOf (normalizer (E c : Set G))).Normal ∧
    normalizer (E c : Set G) = YE c ⊔ centralizer (E c : Set G) ∧
    E c = conjugateSpanBy (F.Vi 1) (Y c) ∧
    ⁅c.Zα, F.H.pCoreIn 2⁆ = F.Vi 1 ∧ ⁅F.Vi 1, c.Qα⁆ = c.Zα := by
  obtain ⟨k, a, ha, t, ht, hmark⟩ :=
    exists_reciprocal_marked_actor d c hUH selection h.star_card heven
  have h' := preliminary_remark d c h k
  let s' : (d.remark k).ActionDescent := ⟨s.action, s.original⟩
  obtain ⟨axes, hfull, hn, hnormalizer, hresidual⟩ :=
    h'.pairing_action_source s' h21 a ha t ht hmark
  exact ⟨axes, hfull, hn, hnormalizer, hresidual,
    h.opposite_commutator s h21, h'.point_commutator s' h21 a ha t ht hmark⟩

open MarkedSpans

/-- The rank-three source geometry uses the original upper marking;
reciprocal alignment is constructed and discharged in the pairing step. -/
theorem source_rank_three_geometry (d : Data T L V F W)
    (c : CriticalPath (L := L) F) (h : Preliminary d c)
    (hcore : ∀ x : F.H, x ∈ pCore 2 F.H → d.action x = 1)
    (mark : UpperMarking d) (sep : d.ModuleSeparation) (actors : LocalActors d)
    (h21 : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1)
    (hUH : F.U ≤ conjugate F.H c.conjugator) (selection : c.RankSelection)
    (heven : (F.U.subgroupOf (conjugate F.H c.conjugator)).map (reciprocalQuotient d c) ≤
      alternatingGroup (Fin 5)) : SourceGeometry d c := by
  let s := d.actionDescentOfCore hcore
  obtain ⟨axes, hfull, hn, hnormalizer, hresidual, hopposite, hpoint⟩ :=
    pairing_source_of_reciprocal d c h s h21 hUH selection heven
  have hN := MarkedControl.normalizer_eq_T d c h s mark
  have hT : (T : Subgroup G) ≤ normalizer (E c : Set G) := by
    intro t ht
    by_contra hm
    exact MovedPlane.cubic_contradiction_of_normalizer_bound h hN.le t
      (ThreeAxes.source_action d c h h21.le axes t ht hm)
  obtain ⟨hfixed, hplane, horbit, hrank, hL⟩ :=
    Span.source_span_geometry d c h hcore mark sep actors hT
  exact {
    rank_three := h.rank_three
    star_central := h.star_central
    Zα_not_le := h.opposite_not_le_seed
    elementary := h.E_elementary
    rank_two := h.E_rank
    T_normalizes := hT
    span := hresidual
    YE_normalizes := h.YE_normalizes h21.le
    full_action := hfull
    YE_normal := hn
    centralizer_two := h.E_centralizer_two
    L₁_not_normalizes := hL
    opposite_commutator := hopposite
    point_commutator := hpoint
    R₁_normalizes := h.R₁_normalizes_E s mark sep actors
    T_normalizes_residual := Preliminary.T_normalizes_residual (h.YE_normalizes h21.le) hn hT
    commutator_normalizer := hN
    normalizer_eq := hnormalizer
    orbit_eq := horbit
    orbit_rank := hrank
    fixed_opposite := hfixed
    fixed_plane := hplane }

/-- Apply the reciprocal producer on the very same single reselected path
supplied by Preparation.exists_prepared_rechoice. -/
theorem source_rank_three_geometry_reselect (d : Data T L V F W)
    (c : CriticalPath (L := L) F) (n : group F L) (earlier : c.EarlierImages)
    (h : Preliminary d (c.reselect n))
    (hcore : ∀ x : F.H, x ∈ pCore 2 F.H → d.action x = 1)
    (mark : UpperMarking d) (sep : d.ModuleSeparation) (actors : LocalActors d)
    (h21 : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1)
    (hUH : F.U ≤ conjugate F.H c.conjugator) (selection : c.RankSelection)
    (heven : (F.U.subgroupOf (conjugate F.H c.conjugator)).map (reciprocalQuotient d c) ≤
      alternatingGroup (Fin 5)) : SourceGeometry d (c.reselect n) :=
  source_rank_three_geometry d (c.reselect n) h hcore mark sep actors h21
    (reselect_reciprocal_placement d c n hUH)
    (reselect_rankSelection d c earlier selection n)
    (reselect_reciprocal_even d c n hUH heven)

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.Preparation.SourceActors
