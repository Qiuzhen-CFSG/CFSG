module
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.NaturalSetup
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalTransport
public import CFSG.Quasithin.Chapter12.Section06.CentralLine.Transport
public import CFSG.Quasithin.Chapter13.Section07.OrdinarySource.F9Application
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.SixCentralChoice
public import CFSG.Quasithin.Chapter14.Section03.Prelim.FaithfulSource.Hypothesis1311

/-!
# The actual escaping point family in the natural-six branch

The natural A₆ action is transitive on the fifteen nonzero vectors. Transport
an earlier escaping vector to a generator of the source line by an actual
element of L. Its centralizer is exactly the line normalizer, so the latter
escapes M and belongs to H_z. This supplies the actual nonempty family for
the ordinary F.9 application, with the original point-core noncentrality
still explicit.
Source: Aschbacher–Smith 13.3.5–6 and 13.5.5–7, pp.886,916–918.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section05.Preparation
open Section08.SourceCompletion
open Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
  {L V V₁ V₂ V₃ M G₁ : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d

/-- Original 13.3.6: the natural action carries any escaping vector to the
actual invariant line, without changing the local component. -/
theorem six_point_escape_of_vector_escape
    (hex : ∃ x ∈ V, x ≠ 1 ∧ ¬ centralizer ({x} : Set G) ≤ M) : ¬ G₁ ≤ M := by
  obtain ⟨x,hx,hx1,hout⟩ := hex
  obtain ⟨z,hz,hz1⟩ : ∃ z ∈ V₁, z ≠ 1 := by
    let : Nontrivial V₁ := Finite.one_lt_card_iff_nontrivial.mp (by rw [d.line_card]; decide)
    obtain ⟨z,hz⟩ := exists_ne (1 : V₁)
    exact ⟨z,z.property,fun he => hz (Subtype.ext he)⟩
  let v : V := ⟨x,hx⟩
  let w : V := ⟨z,(d.line_le_plane.trans (d.plane_le_seed.trans d.seed_le)) hz⟩
  have hv : (d.coordinate v).toAdd ≠ 0 := by
    intro hh
    have hv1 : v = 1 := d.coordinate.injective (hh.trans d.coordinate.map_one.symm)
    exact hx1 (congrArg Subtype.val hv1)
  have hw : (d.coordinate w).toAdd ≠ 0 := by
    intro hh
    have hw1 : w = 1 := d.coordinate.injective (hh.trans d.coordinate.map_one.symm)
    exact hz1 (congrArg Subtype.val hw1)
  obtain ⟨a,ha⟩ := Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalTransport.transitive_nonzero
    (d.coordinate v).toAdd (d.coordinate w).toAdd hv hw
  obtain ⟨l,hl⟩ := (d.local_quotient.surjective.comp
    (QuotientGroup.mk'_surjective (centralCore L))) a
  change d.local_quotient (QuotientGroup.mk' (centralCore L) l) = a at hl
  have he : MulAut.conj l.val x = z := by
    have hh := d.conjugation l v
    rw [hl] at hh
    have hh' : V.normalizerMonoidHom
        ⟨l.val,d.normalizes_V (mem_sup_left l.property)⟩ v = w :=
      d.coordinate.injective (hh.trans ha)
    exact congrArg Subtype.val hh'
  intro hGM
  apply hout
  apply Chapter12.Section06.CentralLine.centralizer_le_of_conjugate
    (show l.val ∈ M from d.local_normalizer.symm ▸ L.le_normalizer l.property)
  rw [he]
  have hline : zpowers z = V₁ := by
    have hh : zpowers (⟨z,hz⟩ : V₁) = ⊤ :=
      zpowers_eq_top_of_prime_card d.line_card (by intro he; exact hz1 (congrArg Subtype.val he))
    have hh' := congrArg (Subgroup.map V₁.subtype) hh
    simpa only [MonoidHom.map_zpowers,subtype_apply,←MonoidHom.range_eq_map,range_subtype] using hh'
  have hc : centralizer ({z} : Set G) = centralizer (V₁ : Set G) := by
    rw [←hline,zpowers_eq_closure,centralizer_closure]
  rw [hc]
  exact (Subgroup.centralizer_le_normalizer _).trans (d.first_normalizer ▸ hGM)

/-- The full original point normalizer is an actual member of H_z. -/
theorem six_point_mem_family_of_vector_escape
    (hex : ∃ x ∈ V, x ≠ 1 ∧ ¬ centralizer ({x} : Set G) ≤ M) :
    G₁ ∈ Section08.Source.Hz (sourceOne L T V₁) T G₁ M := by
  have hPT : V₁ ≤ (T : Subgroup G) :=
    d.line_le_plane.trans (d.plane_le_seed.trans (d.seed_le.trans d.chosen.le_sylow))
  have hcore : V₁ ≤ G₁.pCoreIn 2 := le_pCoreIn_of_normalizes
    (T.isPGroup'.to_le hPT) (hPT.trans (d.first_normalizer ▸ d.line_stable))
      d.first_normalizer.le
  refine ⟨⟨?_,sup_le ?_ (d.first_normalizer ▸ d.line_stable)⟩,
    le_rfl,six_point_escape_of_vector_escape d hex⟩
  · intro he
    have hb : V₁ = ⊥ := bot_unique (hcore.trans_eq he)
    have hc := d.line_card
    simp [hb] at hc
  · rw [d.first_normalizer]
    exact (map_subtype_le _).trans inf_le_right

/-- The actual earlier 12.2.13 theorem supplies an escaping vector; all its
other alternatives are excluded by the original counterexample. -/
theorem six_point_family_of_source12213
    (hmax : Maximal (Counterexample T) L)
    (h12213 : Chapter12.Section02.Theorem12213.{u} KnownSimple.IsKnownSimple) :
    G₁ ∈ Section08.Source.Hz (sourceOne L T V₁) T G₁ M := by
  have h1223 := (Section03.SourceCompletion.SixCentralChoice.chosen_setup_of_maximal_central_six
    hmax d.local_quotient).1
  apply six_point_mem_family_of_vector_escape d
  rcases h12213 G T L V h1223 d.chosen with hx | hl | ha | hm
  · simpa only [d.local_normalizer] using hx
  · obtain ⟨n,hn,_,hg⟩ := hl
    exact (d.counterexample.no_linear (n+1) (by rcases hn with rfl | rfl <;> simp) hg).elim
  · exact (d.counterexample.no_alternating_nine ha.2).elim
  · exact ((Chapter14.Section03.FaithfulSource.Counterexample.hypothesis1311
      d.counterexample).no_M24 hm.2).elim

/-- Original 13.5.7 on every actual member of H_z. The separate earlier
13.3.14 plane noncentrality premise is the only additional local input. -/
theorem six_family_f9_of_plane_noncentral
    (hmax : Maximal (Counterexample T) L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    {H : Subgroup G}
    (hH : H ∈ Section08.Source.Hz (sourceOne L T V₁) T G₁ M)
    (hm : ⁅G₁.pCoreIn 2,V₂⁆ ≠ ⊥) :
    (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis := by
  let F := Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H
  have he : G₁ = F.Gz := d.first_normalizer.trans
    (le_antisymm (normalizer_le_centralizer_of_card_two V₁ d.line_card)
      (Subgroup.centralizer_le_normalizer _))
  have d' : NaturalSetup F.T F.L F.V F.V₁ V₂ F.Vplus M F.Gz := he ▸ d
  have hL : F.L₁ = sourceOne L T V₁ := by
    have hh := Section08.TransvectionQuotients.FiveSeed.BarMarking.normalizer_residual_eq
      L V₁ (T : Subgroup G) T.isPGroup' d.normalizes_L
    change sourceOne L T V₁ =
      (pResidual 2 (L ⊓ normalizer (V₁ : Set G) : Subgroup G)).map
        (L ⊓ normalizer (V₁ : Set G)).subtype at hh
    have hc : normalizer (V₁ : Set G) = centralizer (V₁ : Set G) :=
      le_antisymm (normalizer_le_centralizer_of_card_two V₁ d.line_card)
        (Subgroup.centralizer_le_normalizer _)
    rw [hc] at hh
    exact hh.symm
  have hHF : F.H ∈ Section08.Source.Hz F.L₁ F.T F.Gz M := by
    change H ∈ Section08.Source.Hz F.L₁ T F.Gz M
    rwa [hL,←he]
  apply Section07.OrdinarySource.f9_of_plane_noncentral d' e
    (Section03.SourceCompletion.SixCentralChoice.hypothesis1221_of_maximal_central_six
      hmax d.local_quotient) hHF
  change ⁅(normalizer (V₁ : Set G)).pCoreIn 2,V₂⁆ ≠ ⊥
  rwa [←d.first_normalizer]

/-- F.9 on the literal full point centralizer, with its H_z membership
constructed from the earlier escaping-vector theorem. -/
theorem six_point_f9_of_source12213
    (hmax : Maximal (Counterexample T) L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (h12213 : Chapter12.Section02.Theorem12213.{u} KnownSimple.IsKnownSimple)
    (hm : ⁅G₁.pCoreIn 2,V₂⁆ ≠ ⊥) :
    (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ G₁).Hypothesis :=
  six_family_f9_of_plane_noncentral d hmax e
    (six_point_family_of_source12213 d hmax h12213) hm

end CFSG.Quasithin.Chapter13.Section05.Preparation
