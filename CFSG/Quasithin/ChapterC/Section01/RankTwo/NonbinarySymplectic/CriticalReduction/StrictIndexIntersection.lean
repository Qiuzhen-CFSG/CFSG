module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.StrictIndexPathSelection

/-!
# The full R₃ intersection on the selected strict-index path

Keep the source (5.9)(**) conjugator, terminal path, whole-H₂ centralizer,
and both second spans. If the smaller second span Z had terminal
commutator in Z_c, adjoining Z_c would give a normal radius section. The
actual simple quotient and escaping critical endpoint would put the
original seed Z_mu in B_c, contradicting its selected movement. Hence
that displacement escapes Z_c. The critical comparison forces both
literal critical indices to equal the original field order.

If R₃ = [Z, X_e intersect Q_c] vanished, the full fixed-intersection
comparison would give the forbidden displacement bound. Thus R₃ is
nontrivial and has order at least q. The existing whole-X splitting
identifies it with [Z, U_e intersect Q_c], retaining the entire central
attachment. Q_c normalizes the smaller span because H₂ lies in Z_c,
so R₃ lies in Z intersect U_e. A conjugate of Z_mu by the same full
centralizer already has nontrivial commutator with the literal A₀.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (3.3) and (5.9), printed pp.866--867 and 921. The source upper
bound |R₃| ≤ q, R₃ centrality, the displacement comparison and strict-index
contradiction remain required, as do the later exclusions and actual
minimum-replacement distance-two witness. No degree restriction, central
complement or transferred odd-index witness is introduced.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.StrictIndex
open CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison
open scoped Pointwise IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The generating centralizer forces displacement beyond the starting seed.
Consequently both actual critical indices are q, and the complete distant
X-intersection has a nonzero commutator of order at least q. -/
theorem Input.replacement_generated_radius_intersection
    {geometry : Geometry d.radical} {a e : Vertex d.radical}
    (path : CriticalPath d.radical geometry a e) (hb : 4 ≤ geometry.b d.radical)
    (Y C₀ : Subgroup (FreeAmalgam d.radical))
    (hYV : Y ≤ V d.radical a) (hYS : Y ≤ stabilizer d.radical e)
    (hC : C₀ ≤ stabilizer d.radical a)
    (hYN : C₀ ≤ normalizer (Y : Set (FreeAmalgam d.radical)))
    (hgen : C₀ ⊔ Z d.radical e=stabilizer d.radical a)
    (hnotB : ¬ Y ≤ B d.radical a (geometry.Z_normal a)) :
    ¬ ⁅Y,Z d.radical e⁆ ≤ Z d.radical a ∧
    (Q d.radical e).relIndex (Z d.radical a)=Nat.card F ∧
    (Q d.radical a).relIndex (Z d.radical e)=Nat.card F ∧
    ⁅Y,X d.radical e ⊓ Q d.radical a⁆ ≠ ⊥ ∧
    Nat.card F ≤ Nat.card (⁅Y,X d.radical e ⊓ Q d.radical a⁆ :
      Subgroup (FreeAmalgam d.radical)) ∧
    ⁅Y,X d.radical e ⊓ Q d.radical a⁆ = ⁅Y,U d.radical e ⊓ Q d.radical a⁆ := by
  have hYQ := hYV.trans (geometry.V_le_Q (by omega) a path.start_color)
  have hYSa : Y ≤ stabilizer d.radical a := hYQ.trans (fun _ hx => hx.1)
  have heS := path.endpoint_Z_le_start_stabilizer (by omega : 0 < geometry.b d.radical)
  have hbad : ¬ ⁅Y,Z d.radical e⁆ ≤ Z d.radical a := by
    intro hdisp
    let J := Y ⊔ Z d.radical a
    have hJN : stabilizer d.radical a ≤ normalizer (J : Set (FreeAmalgam d.radical)) := by
      rw [←hgen]
      exact sup_le ((le_inf hYN (hC.trans (Z_normalized d.radical a))).trans
        (normalizer_inf_normalizer_le_normalizer_sup _ _))
        (normalizes_sup_of_displacement _ _ _ (heS.trans (Z_normalized d.radical a)) hdisp)
    have hJV : J ≤ V d.radical a := sup_le hYV (Z_le_VBall d.radical a 2)
    have hJdisp : ⁅J,Z d.radical e⁆ ≤ Z d.radical a :=
      commutator_sup_le_of_relative_normal (stabilizer d.radical a) Y (Z d.radical a)
        (Z d.radical e) (Z d.radical a) (Z_normalized d.radical a) hYSa
        (Z_le_stabilizer d.radical a) hdisp
        (le_normalizer_iff_commutator_le_left.mp (heS.trans (Z_normalized d.radical a)))
    obtain ⟨E,hE,f,hf,hfQ,_⟩ := h.replacement_inner_natural_action d geometry hb path.start_color
    have hlarge : 3 < Nat.card E.Carrier := by
      rw [E.card_eq,hE]
      exact (by decide : 3 < 2^2).trans_le (Nat.pow_le_pow_right (by decide) h.nonbinary)
    let := Theory.SpecificGroups.SymplecticFour.SimpleQuotients.isSimpleGroup hlarge
    let : IsSimpleGroup (Sp E.Carrier) :=
      Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.isSimpleGroup
    have hk : f.ker=(Q d.radical a).subgroupOf (stabilizer d.radical a) := by
      apply map_injective (stabilizer d.radical a).subtype_injective
      rw [hfQ,map_subgroupOf_eq_of_le (show Q d.radical a ≤ stabilizer d.radical a from fun _ hv => hv.1)]
    have heQ := (critical_reverse d.radical geometry
      (MSCentralOrbit.edgeCentralizerCondition d.radical (h.replacement_two_group d)
        (h.replacement_core_le d) (h.replacement_omegaOrbit_centralizer d)) a path.start_color
      (by rw [geometry.distance_constant a path.start_color]; change 0 < geometry.b d.radical; omega)
      e path.end_color path.critical).2
    exact hnotB (le_sup_left.trans (normal_radius_le_B_of_kernel_escape geometry (by omega)
      path.start_color f hf hk
      (Q_isPGroup d.radical (h.replacement_two_group d) (h.replacement_core_le d) a path.start_color)
      J (Z d.radical e) hJV hJN heS heQ hJdisp))
  have hcent : Y ≤ centralizer ((⁅Z d.radical a,Z d.radical e⁆ :
      Subgroup (FreeAmalgam d.radical)) : Set _) :=
    (hYQ.trans (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (geometry.centralizes a path.start_color)))).trans
      (centralizer_le (critical_commutator_le_start_seed path))
  have hsmall := h.replacement_critical_index_lt_square_of_escape d path (by omega) Y hYS hcent
    (by intro hh; exact hbad (by rw [commutator_comm]; exact hh.trans (critical_commutator_le_start_seed path)))
  obtain ⟨hi,hi'⟩ := h.replacement_small_critical_indices_eq_field d path (by omega) hsmall
  have hne : ⁅Y,X d.radical e ⊓ Q d.radical a⁆ ≠ ⊥ := by
    intro hz
    have hfix : Y ≤ centralizer ((Z d.radical e ⊓ Q d.radical a :
        Subgroup (FreeAmalgam d.radical)) : Set _) :=
      (commutator_eq_bot_iff_le_centralizer.mp hz).trans
        (centralizer_le (inf_le_inf_right _ (geometry.omega_bound e path.end_color (by
          rw [geometry.distance_constant e path.end_color]
          exact lt_of_lt_of_le (by decide : 0 < 4) hb))))
    apply hbad
    rw [commutator_comm]
    exact (h.replacement_critical_fixed_intersection_displacement d path (by omega)
      Y hYS hYQ hfix).trans (critical_commutator_le_start_seed path)
  exact ⟨hbad,hi,hi',hne,
    h.replacement_root_intersection_commutator_card_ge_field d path hb hsmall Y hYS hne,
    (h.replacement_root_intersection_fixed_and_commutator d path hb hsmall Y hYS).1⟩


/-- The same source selector supplies both field-sized critical indices and
a nontrivial literal R₃. The X/U identity retains the complete central
attachment, and one conjugate in the original centralizer already moves A₀. -/
theorem Input.replacement_strict_index_selected_intersection
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 < geometry.b d.radical)
    (hsmall : (B d.radical a (geometry.Z_normal a)).relIndex
      (U d.radical (path.walk.getVert 2)) ≤ Nat.card F) :
    (B d.radical a (geometry.Z_normal a)).relIndex
      (U d.radical (path.walk.getVert 2))=Nat.card F ∧
    ∃ y ∈ stabilizer d.radical (path.walk.getVert 2),
    let c := path.walk.getVert 2
    let mu := act d.radical y a
    let T₂ := (kernelCentralizer geometry a c).map (MulAut.conj y⁻¹).toMonoidHom
    let H₂ := conjugatedKernelCommutator geometry a c y
    let C₀ := stabilizer d.radical c ⊓ centralizer (H₂ : Set (FreeAmalgam d.radical))
    let Z₀ := conjugateSpanBy (Z d.radical mu) C₀
    let W := sourceCentralizerSpan d.radical c mu H₂
    ¬ Z d.radical mu ≤ B d.radical c (geometry.Z_normal c) ∧
    ¬ T₂ ≤ Q d.radical c ∧
    ¬ H₂ ≤ centralizer (V d.radical z : Set (FreeAmalgam d.radical)) ∧
    ∃ e, ∃ selected : CriticalPath d.radical geometry c e,
      (cosetGraph d.radical).dist e z=2 ∧
      (∀ i ≤ path.walk.length-2, selected.walk.getVert i=path.walk.getVert (i+2)) ∧
      ¬ H₂ ≤ centralizer (Z d.radical e : Set (FreeAmalgam d.radical)) ∧
      C₀ ⊔ Z d.radical e=stabilizer d.radical c ∧
      Z₀ ≤ W ∧ W ≤ Q d.radical c ∧
      W ≤ Q d.radical (path.walk.getVert (path.walk.length-2)) ∧ W ≤ Q d.radical z ∧
      (Q d.radical e).relIndex (Z d.radical c)=Nat.card F ∧
      (Q d.radical c).relIndex (Z d.radical e)=Nat.card F ∧
      let A₀ := X d.radical e ⊓ Q d.radical c
      let R₃ := ⁅Z₀,A₀⁆
      ¬ ⁅Z₀,Z d.radical e⁆ ≤ Z d.radical c ∧
      R₃ ≠ ⊥ ∧ Nat.card F ≤ Nat.card R₃ ∧
      R₃=⁅Z₀,U d.radical e ⊓ Q d.radical c⁆ ∧
      R₃ ≤ Z₀ ⊓ U d.radical e ∧
      ∃ t ∈ C₀, ⁅Z d.radical (act d.radical t mu),A₀⁆ ≠ ⊥ := by
  obtain ⟨hi,y,hy,hnotB,hT,hmove,e,selected,hez,hover,hmoveE,hgen,hZW,hWQ,hWp,hWz⟩ :=
    h.replacement_strict_index_selected_path d path hb hsmall
  let c := path.walk.getVert 2
  let mu := act d.radical y a
  let H₂ := conjugatedKernelCommutator geometry a c y
  let C₀ := stabilizer d.radical c ⊓ centralizer (H₂ : Set (FreeAmalgam d.radical))
  let Z₀ := conjugateSpanBy (Z d.radical mu) C₀
  let A₀ := X d.radical e ⊓ Q d.radical c
  have hc : color d.radical c=false := selected.start_color
  have hdist : (cosetGraph d.radical).dist mu c=2 := by
    have hh := dist_act d.radical y a c
    rw [show act d.radical y c=c from hy] at hh
    exact hh.trans (path.dist_start (by rw [path.length_eq_b]; omega))
  have hZmuV : Z d.radical mu ≤ V d.radical c :=
    le_iSup_of_le _ (le_iSup_of_le hdist.le le_rfl)
  have hZV : Z₀ ≤ V d.radical c := conjugateSpanBy_le hZmuV
    (inf_le_left.trans (DistanceEight.V_normalized d.radical c))
  have hZS : Z₀ ≤ stabilizer d.radical e := (hZW.trans hWz).trans
    (Q_le_stabilizer_of_dist_le_two z e path.end_color selected.end_color
      (by rw [SimpleGraph.dist_comm]; exact hez.le))
  obtain ⟨hbad,hic,hie,hne,hcard,heq⟩ :=
    h.replacement_generated_radius_intersection d selected hb.le Z₀ C₀ hZV hZS inf_le_left
      (le_normalizer_conjugateSpanBy _ _) hgen
      (fun hh => hnotB ((le_conjugateSpanBy _ _).trans hh))
  obtain ⟨_,_,_,_,_,_,_,_,hH₂Z,_⟩ :=
    h.replacement_strict_index_conjugated_span d path hb hsmall y hy
  have hQC : Q d.radical c ≤ C₀ := le_inf (fun _ hx => hx.1)
    ((le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (geometry.centralizes c hc))).trans (centralizer_le hH₂Z))
  have hRZ : ⁅Z₀,A₀⁆ ≤ Z₀ := le_normalizer_iff_commutator_le_left.mp
    ((inf_le_right.trans hQC).trans (le_normalizer_conjugateSpanBy _ _))
  have hRU : ⁅Z₀,A₀⁆ ≤ U d.radical e := by
    rw [heq,commutator_comm]
    exact (commutator_mono inf_le_left le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp (hZS.trans (U_normalized e)))
  have ht : ∃ t ∈ C₀, ⁅Z d.radical (act d.radical t mu),A₀⁆ ≠ ⊥ := by
    by_contra! hn
    apply hne
    apply commutator_eq_bot_iff_le_centralizer.mpr
    apply (closure_le _).mpr
    rintro _ ⟨t,ht,u,hu,rfl⟩
    apply commutator_eq_bot_iff_le_centralizer.mp (hn t⁻¹ (C₀.inv_mem ht))
    rw [Z_act]
    exact ⟨u,hu,by simp only [inv_inv]; rfl⟩
  exact ⟨hi,y,hy,hnotB,hT,hmove,e,selected,hez,hover,hmoveE,hgen,hZW,hWQ,hWp,hWz,
    hic,hie,hbad,hne,hcard,heq,le_inf hRZ hRU,ht⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
