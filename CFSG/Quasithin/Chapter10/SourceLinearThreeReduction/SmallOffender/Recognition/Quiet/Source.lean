module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Recognition.Quiet.Kernel
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Recognition.Quiet.FullTI
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Recognition.Semisimple.Source
public import Theory.Representation.BinaryOffender.PerfectCentralizerDisplacement
public import CFSG.Quasithin.ChapterE.Section03.Parameters.AutomizerFF

/-!
# Quiet moved TI reduction under the original small-offender hypotheses

The moved kernel vanishes before classification. In the separated-factor
branch the existing outside-intersection theorem and the actual M-conjugate
pair give TI. In the fully moved branch, point control and full Thompson
fusion give TI. The latter uses the proved local/full comparison when three
divides the component quotient order.

For binary three, the checked small-quotient recognition leaves a TI moved
group of order at least 512. If it is the full module, the attained offender
contains a noncentralizing component-normalizing involution of corank at
most two. A perfect fixed-point-free component cannot commute with its
image in the full faithful automizer. These are reductions, not recognition
of the remaining quiet rows.

The final adapter passes the proved kernel, TI and involution facts to the
original survivor consumer. Quiet row selection remains with
qt-d-10-nona5-small-offender. HalfSylowUniqueAt retains its existing producer
qt-d-10-nona5-half-sylow-unique and final discharge by
qt-d-10-nona5-point-control.
Source: Aschbacher–Smith 10.1.1 and 10.2.12, pp.741,754–755.
-/

public noncomputable section
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.SmallOffender.Recognition
open Subgroup Theory.GroupTheory Representation
open Chapter3.Section02 ChapterE ChapterI.Section06To08 PointControl.Selection
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The quiet moved group is TI in the separated-factor branch. -/
theorem quiet_moved_ti_of_crossed
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) {g : G}
    (c : Configuration T D g)
    (hJ : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (hNL : normalizer (L : Set G) ≤ D.maximalLocal)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G)) :
    IsTISubgroup ⁅D.fullModule,L⁆ := by
  have hz := quiet_moved_fixed_eq_bot D c.many c.minimal c.nonnormal hJ
  have hperm (m : G) (hm : m ∈ D.maximalLocal) :
      (⁅D.fullModule,L⁆).map (MulAut.conj m).toMonoidHom = ⁅D.fullModule,L⁆ ∨
      (⁅D.fullModule,L⁆).map (MulAut.conj m).toMonoidHom =
        (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom := by
    have hV (x : G) (hx : x ∈ D.maximalLocal) :
        D.fullModule.map (MulAut.conj x).toMonoidHom = D.fullModule :=
      mem_normalizer_iff_map_conj_eq.mp (D.maximalLocal_normalizes_fullModule hx)
    rcases source_nonnormal_maximal_pair D c.nonnormal ht htn m hm with he | he
    · left; rw [map_commutator,hV m hm,he]
    · right; rw [map_commutator,map_commutator,hV m hm,
        hV t (le_normalizer_componentOrbit L T ht),he]
  have hdis : ⁅D.fullModule,L⁆ ⊓
      (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom = ⊥ :=
    bot_unique ((inf_le_inf_left _ hcross).trans_eq hz)
  have hti := map_conj_eq_or_inf_eq_bot_of_conj_pair D.maximalLocal ⁅D.fullModule,L⁆
    ((⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom) hperm hdis
    (fun _ hx => FixedSpaces.moved_inf_conjugate_eq_bot D c.nonnormal t ht hcross
      c.pointCentralizers hNL hx)
  intro x hx v hv
  have he := (hti x).resolve_left (fun he => hx (mem_normalizer_iff_map_conj_eq.mpr he))
  exact he.le hv

/-- Point control applies to the entire module in the fully moved branch. -/
theorem quiet_full_ti_of_moved_eq_full
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) {g : G}
    (c : Configuration T D g)
    (hJ : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (hthree : 3 ∣ Nat.card (L ⧸ pCore 2 L))
    (hfull : ⁅D.fullModule,L⁆ = D.fullModule) :
    IsTISubgroup D.fullModule := by
  apply fullModule_ti_of_point_control D
    (ModuleChoice.full_thompson_centralizes_of_local_three D c.nonnormal hthree hJ)
  simpa only [hfull] using c.pointCentralizers

/-- The original quiet moved group is TI in both branches. -/
theorem quiet_moved_ti_of_three
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) {g : G}
    (c : Configuration T D g)
    (hJ : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (hNL : normalizer (L : Set G) ≤ D.maximalLocal)
    (hthree : 3 ∣ Nat.card (L ⧸ pCore 2 L)) :
    IsTISubgroup ⁅D.fullModule,L⁆ := by
  obtain ⟨t,ht,htn⟩ := SetLike.not_le_iff_exists.mp c.nonnormal
  rcases quiet_crossed_or_moved_eq_full D c.many c.minimal hJ ht htn with hcross | hfull
  · exact quiet_moved_ti_of_crossed D c hJ hNL ht htn hcross
  · rw [hfull]
    exact quiet_full_ti_of_moved_eq_full D c hJ hthree hfull

/-- Unrecognized binary-three quiet modules have a large center-free TI moved group. -/
theorem quiet_binary_three_natural_or_large_ti
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) {g : G}
    (c : Configuration T D g)
    (hJ : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (hNL : normalizer (L : Set G) ≤ D.maximalLocal)
    (e : (L ⧸ pCore 2 L) ≃* BinaryLinearThree.Group) :
    BinaryThreeNatural D ∨
      (512 ≤ Nat.card (⁅D.fullModule,L⁆ : Subgroup G) ∧
       ⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G) = ⊥ ∧
       IsTISubgroup ⁅D.fullModule,L⁆) := by
  rcases quiet_binary_three_natural_or_large_quotient D c hJ hNL e with hnat | hlarge
  · exact Or.inl hnat
  have hz := quiet_moved_fixed_eq_bot D c.many c.minimal c.nonnormal hJ
  have hcard : (centralizer (L : Set G)).relIndex ⁅D.fullModule,L⁆ =
      Nat.card (⁅D.fullModule,L⁆ : Subgroup G) := by
    rw [←inf_relIndex_left,hz,relIndex_bot_left]
  have hthree : 3 ∣ Nat.card (L ⧸ pCore 2 L) := by
    rw [Nat.card_congr e.toEquiv,Matrix.PSL3Two.card_SL]
    decide
  exact Or.inr ⟨hcard ▸ hlarge,hz,quiet_moved_ti_of_three D c hJ hNL hthree⟩

/-- The fully moved case supplies the literal small actor unless already recognized. -/
theorem quiet_binary_three_full_natural_or_small_involution
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) {g : G}
    (c : Configuration T D g)
    (hJ : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (hNL : normalizer (L : Set G) ≤ D.maximalLocal)
    (e : (L ⧸ pCore 2 L) ≃* BinaryLinearThree.Group)
    (hfull : ⁅D.fullModule,L⁆ = D.fullModule) :
    BinaryThreeNatural D ∨
      (512 ≤ Nat.card D.fullModule ∧
       D.fullModule ⊓ centralizer (L : Set G) = ⊥ ∧
       IsTISubgroup D.fullModule ∧
       ∃ b ∈ D.fullModule.map (MulAut.conj g).toMonoidHom,
         b ∈ D.maximalLocal ∧ b ∈ normalizer (L : Set G) ∧ b ^ 2 = 1 ∧
         b ∉ centralizer (D.fullModule : Set G) ∧
         subgroupCorank D.fullModule (D.fullModule ⊓ centralizer ({b} : Set G)) ≤ 2) := by
  rcases quiet_binary_three_natural_or_large_ti D c hJ hNL e with hnat | hlarge
  · exact Or.inl hnat
  rw [hfull] at hlarge
  exact Or.inr ⟨hlarge.1,hlarge.2.1,hlarge.2.2,
    full_ti_exists_small_normalizing_involution D c hlarge.2.2 (by omega)⟩

/-- A nonzero moved group with crossed centralization cannot equal the full module. -/
theorem moved_ne_full_of_crossed
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    {t : G} (ht : t ∈ (T : Subgroup G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G)) :
    ⁅D.fullModule,L⁆ ≠ D.fullModule := by
  intro hfull
  have hV : D.fullModule.map (MulAut.conj t).toMonoidHom = D.fullModule :=
    mem_normalizer_iff_map_conj_eq.mp
      (D.maximalLocal_normalizes_fullModule (le_normalizer_componentOrbit L T ht))
  rw [hfull,hV] at hcross
  exact source_full_moved_ne_bot D (commutator_eq_bot_iff_le_centralizer.mpr hcross)

/-- The natural marking forces separated moved factors. -/
theorem not_binary_three_natural_of_moved_eq_full
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hfull : ⁅D.fullModule,L⁆ = D.fullModule) : ¬ BinaryThreeNatural D := by
  intro hnat
  obtain ⟨t,ht,htn⟩ := SetLike.not_le_iff_exists.mp hn
  exact moved_ne_full_of_crossed D ht (binary_three_crossed_of_marking D hnat ht htn) hfull

/-- The remaining fully moved binary-three case has a large full TI group and a small actor. -/
theorem quiet_binary_three_full_small_involution
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) {g : G}
    (c : Configuration T D g)
    (hJ : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (hNL : normalizer (L : Set G) ≤ D.maximalLocal)
    (e : (L ⧸ pCore 2 L) ≃* BinaryLinearThree.Group)
    (hfull : ⁅D.fullModule,L⁆ = D.fullModule) :
    512 ≤ Nat.card D.fullModule ∧
      D.fullModule ⊓ centralizer (L : Set G) = ⊥ ∧
      IsTISubgroup D.fullModule ∧
      ∃ b ∈ D.fullModule.map (MulAut.conj g).toMonoidHom,
        b ∈ D.maximalLocal ∧ b ∈ normalizer (L : Set G) ∧ b ^ 2 = 1 ∧
        b ∉ centralizer (D.fullModule : Set G) ∧
        subgroupCorank D.fullModule (D.fullModule ⊓ centralizer ({b} : Set G)) ≤ 2 := by
  exact (quiet_binary_three_full_natural_or_small_involution D c hJ hNL e hfull).resolve_left
    (not_binary_three_natural_of_moved_eq_full D c.nonnormal hfull)

/-- A small nontrivial full-module actor cannot commute with the component
in the actual faithful action image. This controls quotient action, rather
than merely the element's commutators with an abstract group label. -/
theorem small_actor_not_commuting_component_image
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hz : D.fullModule ⊓ centralizer (L : Set G) = ⊥)
    {b : G} (hbM : b ∈ D.maximalLocal)
    (hb : b ∉ centralizer (D.fullModule : Set G))
    (hsmall : subgroupCorank D.fullModule
      (D.fullModule ⊓ centralizer ({b} : Set G)) ≤ 2) :
    ⁅inducedAutomizer D.fullModule L,inducedAutomizer D.fullModule (zpowers b)⁆ ≠ ⊥ := by
  let V := D.fullModule
  let := D.fullModule_elementary (source_module_nonsolvable_uniqueness D)
  let ρ := automizerRepresentation V
  have hLN : L ≤ normalizer (V : Set G) :=
    ((le_componentOrbit L T).trans (localOrbit T L).le_normalizer).trans
      D.maximalLocal_normalizes_fullModule
  have hBN : zpowers b ≤ normalizer (V : Set G) :=
    zpowers_le.mpr (D.maximalLocal_normalizes_fullModule hbM)
  let S := inducedAutomizer V L
  let A := inducedAutomizer V (zpowers b)
  let : Group.IsPerfect L := by
    let := D.maximal.1.1.perfect
    exact Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe
      (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)).toMonoidHom)
      (subgroupOfEquivOfLe le_sup_left).surjective
  let : Group.IsPerfect (L.subgroupOf (normalizer (V : Set G))) :=
    Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hLN).symm.toMonoidHom)
      (subgroupOfEquivOfLe hLN).symm.surjective
  let : Group.IsPerfect S := Group.IsPerfect.map _
  have hfix : Representation.BinaryOffender.fixedSpace ρ S = ⊥ := by
    apply bot_unique
    intro v hv
    apply Additive.toMul.injective
    apply Subtype.ext
    exact hz.le ⟨v.toMul.property,(mem_fixedSpace_inducedAutomizer V L hLN v).mp hv⟩
  have hnot : ¬ A ≤ ρ.ker := by
    intro hk
    have hkbot : ρ.ker = ⊥ :=
      (MonoidHom.ker_eq_bot_iff ρ).mpr (automizerRepresentation_injective V)
    have hAbot : A = ⊥ := bot_unique (hk.trans_eq hkbot)
    exact hb ((inducedAutomizer_eq_bot_iff hBN).mp hAbot (mem_zpowers b))
  have hbound : Representation.BinaryOffender.fixedCodim ρ A ≤ 2 := by
    rw [fixedCodim_inducedAutomizer V (zpowers b) hBN]
    simpa only [zpowers_eq_closure, centralizer_closure] using hsmall
  intro hc
  have hh := Representation.BinaryOffender.three_le_fixedCodim_of_perfect_fixedSpace_eq_bot
    ρ S A hfix hnot hc
  omega

/-- The original survivor assembly receives the proved kernel and TI facts.
Quiet marking construction remains with this task; the existing half-Sylow
producer supplies the earlier component-normalizer bound. -/
theorem nonnormalSmallOffender_of_quiet_centerfree_ti_rows_and_halfSylow
    (hhalf : PointControl.HalfSylowUniqueAt T)
    (hquiet : ∀ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L) (g : G),
      Configuration T D g →
      Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G) →
      ⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G) = ⊥ →
      (3 ∣ Nat.card (L ⧸ pCore 2 L) → IsTISubgroup ⁅D.fullModule,L⁆) →
      (Nonempty ((L ⧸ pCore 2 L) ≃* BinaryLinearThree.Group) →
        ⁅D.fullModule,L⁆ = D.fullModule →
        512 ≤ Nat.card D.fullModule ∧
        ∃ b ∈ D.fullModule.map (MulAut.conj g).toMonoidHom,
          b ∈ D.maximalLocal ∧ b ∈ normalizer (L : Set G) ∧ b ^ 2 = 1 ∧
          b ∉ centralizer (D.fullModule : Set G) ∧
          subgroupCorank D.fullModule (D.fullModule ⊓ centralizer ({b} : Set G)) ≤ 2) →
      ∃ E : FundamentalSetup KnownSimple.IsKnownSimple T L,
        E.fullModule ≤ D.fullModule ∧
        ((Nonempty ((L ⧸ pCore 2 L) ≃* BinaryLinearThree.Group) ∧
            (centralizer (L : Set G)).relIndex ⁅E.fullModule,L⁆ < 512) ∨
          RankOneNatural E ∨ NaturalDualRow E ∨ FourNaturalRow E ∨
          OrthogonalFourMinusRow E ∨ SuzukiNaturalRow E)) :
    SourceNonnormalSmallOffenderAt T := by
  apply nonnormalSmallOffender_of_quiet_small_quotients_and_halfSylow hhalf
  intro L D g c hJ
  have hNL : normalizer (L : Set G) ≤ D.maximalLocal :=
    PointControl.component_normalizer_le_of_halfSylowUnique D c.nonnormal
      (hhalf c.many L D c.nonnormal c.notA5)
  exact hquiet L D g c hJ
    (quiet_moved_fixed_eq_bot D c.many c.minimal c.nonnormal hJ)
    (quiet_moved_ti_of_three D c hJ hNL) (by
      rintro ⟨e⟩ hfull
      have h := quiet_binary_three_full_small_involution D c hJ hNL e hfull
      exact ⟨h.1,h.2.2.2⟩)

end CFSG.Quasithin.Chapter10.SmallOffender.Recognition
