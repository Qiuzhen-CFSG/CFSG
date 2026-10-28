module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.NaturalCorank.Terminal.Exchange

/-!
# Completion of the natural terminal TI construction

Select an active conjugate factor, construct a swapping offender element,
and align its nonzero diagonal commutator to the T-central diagonal.
The literal pair already escapes its intrinsic two-core. This proves
TerminalConstructionAt with every terminal geometric premise discharged.

The actual natural-exclusion and small-offender consumers below retain the
earlier half-Sylow, diagonal-core and recognition inputs. Their final
discharge remains with qt-d-10-nona5-small-offender; this module does not
claim the complete source small-offender theorem.
Source: Aschbacher--Smith, 10.2.12, last paragraph on printed p.755.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Matrix
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.SmallOffender.NaturalCorank
open Chapter3.Section02 ChapterE ChapterI.Section06To08
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {g : G}


omit [Finite G] in
private theorem map_conj_mul (H : Subgroup G) (a b : G) :
    H.map (MulAut.conj (a*b)).toMonoidHom =
      (H.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom :=
  Subgroup.conjBy_mul H a b

omit [Finite G] in
private theorem map_conj_commutator (H K : Subgroup G) (a : G) :
    (⁅H,K⁆).map (MulAut.conj a).toMonoidHom =
      ⁅H.map (MulAut.conj a).toMonoidHom,K.map (MulAut.conj a).toMonoidHom⁆ :=
  map_commutator H K (MulAut.conj a).toMonoidHom

omit [Finite G] in
private theorem conjugate_eq_of_mem_normalizer (H : Subgroup G) {a : G}
    (ha : a ∈ normalizer (H : Set G)) :
    H.map (MulAut.conj a).toMonoidHom = H :=
  mem_normalizer_iff_map_conj_eq.mp ha

theorem terminalWitness_of_active_pair
    (c : Configuration T D g) (m : SourceLinearThreeGeometry T D)
    (hsmall : subgroupCorank (D.fullModule.map (MulAut.conj g).toMonoidHom)
      (D.fullModule.map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal) ≤ 1)
    (hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥)
    (hti : IsTISubgroup ⁅D.fullModule,L⁆)
    (hactive : ¬ (⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom ≤
      centralizer ((⁅D.fullModule,L⁆ : Subgroup G) : Set G)) :
    Nonempty (TerminalWitness T D g) := by
  obtain ⟨t,ht,htn⟩ := SetLike.not_le_iff_exists.mp c.nonnormal
  obtain ⟨d,hd,hswap⟩ := natural_active_exists_swapping_offender c m hsmall hz hti ht htn hactive
  exact terminalWitness_of_active_pair_swapping_offender c m hsmall hz hti ht htn hactive hd.1 hswap

theorem natural_active_pair_common_central_point
    (c : Configuration T D g) (m : SourceLinearThreeGeometry T D)
    (hsmall : subgroupCorank (D.fullModule.map (MulAut.conj g).toMonoidHom)
      (D.fullModule.map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal) ≤ 1)
    (hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥)
    (hti : IsTISubgroup ⁅D.fullModule,L⁆)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hactive : ¬ (⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom ≤
      centralizer ((⁅D.fullModule,L⁆ : Subgroup G) : Set G)) :
    ∃ a ∈ D.maximalLocal, a ∈ normalizer ((⁅D.fullModule,L⁆ : Subgroup G) : Set G) ∧
      ∃ z : G, z ∈ D.fullModule ⊓ D.fullModule.map (MulAut.conj (a*g)).toMonoidHom ∧
        z ∈ centralizer ((T : Subgroup G) : Set G) ∧ z ≠ 1 := by
  obtain ⟨d,hd,hswap⟩ := natural_active_exists_swapping_offender c m hsmall hz hti ht htn hactive
  obtain ⟨_,_,_,hU⟩ := natural_active_pair_normalizers c m hsmall hz hti hactive
  have hne : ⁅D.fullModule,L⁆ ⊓ normalizer
      (((⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) ≠ ⊥ := by
    intro he
    rw [he,card_bot] at hU
    omega
  obtain ⟨u,hu1⟩ := ne_bot_iff_exists_ne_one.mp hne
  have hune : (u : G) ≠ 1 := fun hh => hu1 (Subtype.ext hh)
  have huN : (u : G) ∈ normalizer
      ((D.fullModule.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
    rw [←map_equiv_normalizer_eq,source_fullModule_normalizer D]
    exact natural_active_axis_le_conjugate_maximal c m hsmall hz hti hactive u.property
  have huv : (u : G)⁻¹ * (MulAut.conj d) (u : G) ∈
      D.fullModule.map (MulAut.conj g).toMonoidHom := by
    have hh := (mem_normalizer_iff.mp ((normalizer
      ((D.fullModule.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G)).inv_mem huN) d).mp hd.1
    have hp := (D.fullModule.map (MulAut.conj g).toMonoidHom).mul_mem hh
      ((D.fullModule.map (MulAut.conj g).toMonoidHom).inv_mem hd.1)
    simpa only [MulAut.conj_apply,inv_inv,mul_assoc] using hp
  obtain ⟨u',v',hu',hv',hu1',hv1',_,_,hzT,hzorder⟩ :=
    exists_natural_diagonal m c.nonnormal ht htn hz
  obtain ⟨a,ha,haW,he⟩ := natural_diagonal_transitive m c.nonnormal hz ht htn
    ((⁅D.fullModule,L⁆).inv_mem u.property.1)
    (hswap ▸ mem_map_of_mem (MulAut.conj d).toMonoidHom u.property.1)
    hu' hv' (inv_ne_one.mpr hune)
    (fun he => hune ((MulAut.conj d).injective (he.trans (map_one _).symm))) hu1' hv1'
  refine ⟨a,(localOrbit T L).le_normalizer ha,haW,u'*v',⟨?_,?_⟩,hzT.2,?_⟩
  · rw [source_nonnormal_fullModule_eq_moved_pair D c.nonnormal ht (m.crossed t ht htn)]
    exact mul_mem_sup hu' hv'
  · rw [map_conj_mul,←he]
    exact mem_map_of_mem _ huv
  · intro he
    rw [he,orderOf_one] at hzorder
    omega

theorem terminalConstructionAt (T : Sylow 2 G) : TerminalConstructionAt T := by
  intro L D g c m hone hz hti
  obtain ⟨t,ht,htn⟩ := SetLike.not_le_iff_exists.mp c.nonnormal
  obtain ⟨a,ha,x,hx,cx,hactive⟩ := exists_active_alignment c m ht htn
  have hs : subgroupCorank (D.fullModule.map (MulAut.conj x).toMonoidHom)
      (D.fullModule.map (MulAut.conj x).toMonoidHom ⊓ D.maximalLocal) ≤ 1 := by
    have he := cx.attained.symm.trans c.attained
    have hh : subgroupCorank (D.fullModule.map (MulAut.conj x).toMonoidHom)
        (D.fullModule.map (MulAut.conj x).toMonoidHom ⊓ D.maximalLocal) = 1 := by
      rw [hone] at he
      exact_mod_cast he
    exact hh.le
  obtain ⟨r,hr,hrW,z,hzcommon,hzT,hz1⟩ :=
    natural_active_pair_common_central_point cx m hs hz hti ht htn hactive
  have hractive : ¬ (⁅D.fullModule,L⁆).map (MulAut.conj (r*x)).toMonoidHom ≤
      centralizer ((⁅D.fullModule,L⁆ : Subgroup G) : Set G) := by
    intro hh
    apply hactive
    apply (map_le_map_iff_of_injective (f := (MulAut.conj r).toMonoidHom) (MulAut.conj r).injective).mp
    rw [Theory.Quasithin.map_centralizer,conjugate_eq_of_mem_normalizer _ hrW,
      ←map_conj_mul]
    exact hh
  have hconj : D.fullModule.map (MulAut.conj (r*x)).toMonoidHom =
      D.fullModule.map (MulAut.conj ((r*a)*g)).toMonoidHom := by
    rcases hx with hx | hx
    · rw [hx,mul_assoc]
    · rw [hx,←mul_assoc r (a*g) t,map_conj_mul,
        conjugate_eq_of_mem_normalizer _
          (D.maximalLocal_normalizes_fullModule (le_normalizer_componentOrbit L T ht)),
        mul_assoc]
  have hxr : r*x = (r*a)*g ∨ r*x = ((r*a)*g)*t := by
    rcases hx with hx | hx
    · exact Or.inl (by rw [hx,mul_assoc])
    · exact Or.inr (by rw [hx]; simp only [mul_assoc])
  exact terminalWitness_of_common_central_point c m hone.le hz hti
    (r*a) t (r*x) z (D.maximalLocal.mul_mem hr ha) ht htn hxr hractive
    ⟨hzcommon.1,hconj ▸ hzcommon.2⟩ hzT hz1

/-- The terminal construction discharges its callback in the literal natural
small-corank exclusion; the earlier half-Sylow and diagonal-core inputs remain. -/
theorem naturalSmallCorankExclusion_of_halfSylow_core
    (hhalf : PointControl.HalfSylowUniqueAt T) (hcore : DiagonalCoreAt T) :
    NaturalSmallCorankExclusionAt T :=
  naturalSmallCorankExclusion_of_halfSylow_core_terminal hhalf hcore (terminalConstructionAt T)

/-- Actual application to the original survivor consumer, with terminal
geometry proved and only the earlier source obligations retained. -/
theorem nonnormalSmallOffender_of_recognition_halfSylow_core
    (hrecognition : RecognitionAt T) (hhalf : PointControl.HalfSylowUniqueAt T)
    (hcore : DiagonalCoreAt T) : SourceNonnormalSmallOffenderAt T :=
  source_nonnormalSmallOffender_of_source_steps hrecognition
    (naturalSmallCorankExclusion_of_halfSylow_core hhalf hcore)

end CFSG.Quasithin.Chapter10.SmallOffender.NaturalCorank
