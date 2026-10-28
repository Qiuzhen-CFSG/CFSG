module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CommonKernel

/-!
# Strict forward slices on the actual characteristic replacement

Above critical distance four, the full-point, small-critical-image branch
has forward Baumann index greater than two. The already constructed shifted
seed span gives an order-two commutator with the reverse seed kernel, realized
by one conjugated seed. The whole predecessor core has commutator order at
most two with that same kernel. Consequently the original shifted span, on
the same conjugate, has displacement inside the seed witness's displacement.

Transporting the actor back makes the entire shifted span fixed modulo its
own seed. This span is locally normal and escapes its Baumann slice, so the
actor must lie in the local two-core. But the two-core centralizes the seed,
contradicting the nonzero seed witness. All choices are from the actual
characteristic replacement: the endpoint, overlapping walk and component
conjugator are retained, as are both moved-cover orders sixteen and thirty-two.

This gives the strict slice directly from the seed kernel `Z_z intersect Q_c`.
It does not identify that kernel with the source's larger `X_z intersect Q_c`,
or assert a new central-generation clause. In this branch it bypasses the
intermediate full-X normalization and span-comparison argument. Transport
makes the estimate available at every component vertex; the final consumer
discharges the numerical premise in the original backward critical shift.

The large-critical-image and other radical-image branches, exact-four
exclusion, intermediate R4/R6 noncentrality and terminal (5.11)--(5.12)
contradictions remain necessary for the unconditional distance bound.

Source: Meierfrankenfeld--Stellmacher (1993), (3.3)(ii), pp.866--867,
and the shifted-span argument of (5.9), pp.920--922. The seed-witness
contradiction follows the argument in Exceptional/Exhaustion/LargeDistance/
CubicStrictSlices, proved here using this replacement's own carriers and
checked seed-line, predecessor-core and normal-section interfaces.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement Pointwise
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)

include s in
private theorem normalized_radius_le_slice_of_actor
    (hb : 2 < replacementDistance h d)
    (D A : Subgroup (FreeAmalgam d.radical))
    (hDV : D ≤ V d.radical (alpha d.radical))
    (hDN : stabilizer d.radical (alpha d.radical) ≤ normalizer (D : Set (FreeAmalgam d.radical)))
    (hAG : A ≤ stabilizer d.radical (alpha d.radical))
    (hne : ¬ A ≤ Q d.radical (alpha d.radical))
    (hcomm : ⁅D,A⁆ ≤ Z d.radical (alpha d.radical)) :
    D ≤ B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) := by
  let D₀ := D.comap (embedM d.radical)
  let Z₀ := (Z d.radical (alpha d.radical)).comap (embedM d.radical)
  let A₀ := A.comap (embedM d.radical)
  have hDG : D ≤ (embedM d.radical).range :=
    (hDV.trans ((replacementGeometry h d).V_local (alpha d.radical) rfl hb)).trans_eq (stabilizer_m_base d.radical)
  have hDm : D₀.map (embedM d.radical) = D := map_comap_eq_self hDG
  have hZm : Z₀.map (embedM d.radical) = Z d.radical (alpha d.radical) :=
    map_comap_eq_self ((Z_le_stabilizer d.radical (alpha d.radical)).trans_eq (stabilizer_m_base d.radical))
  have hAm : A₀.map (embedM d.radical) = A := map_comap_eq_self
    (hAG.trans_eq (stabilizer_m_base d.radical))
  have hg (m : d.overgroup) : embedM d.radical m ∈ stabilizer d.radical (alpha d.radical) := by
    change embedM d.radical m ∈ stabilizer d.radical (mVertex d.radical 1)
    rw [stabilizer_m_base]
    exact ⟨m,rfl⟩
  let : D₀.Normal := ⟨by
    intro z hd m
    change embedM d.radical (m*z*m⁻¹) ∈ D
    rw [map_mul,map_mul,map_inv]
    exact (mem_normalizer_iff.mp (hDN (hg m)) (embedM d.radical z)).mp hd⟩
  let : Z₀.Normal := ⟨by
    intro z hd m
    change embedM d.radical (m*z*m⁻¹) ∈ Z d.radical (alpha d.radical)
    rw [map_mul,map_mul,map_inv]
    exact (mem_normalizer_iff.mp ((Z_normalized d.radical _) (hg m)) (embedM d.radical z)).mp hd⟩
  have hcomm₀ : ⁅D₀,A₀⁆ ≤ Z₀ := by
    apply (map_le_map_iff_of_injective (embedM_injective d.radical)).mp
    rwa [map_commutator,hDm,hAm,hZm]
  have hne : ¬ A₀ ≤ pCore 2 d.overgroup := by
    intro he
    have hh := map_mono (f := embedM d.radical) he
    rw [hAm,←Q_alpha d.radical (replacement_radical_isPGroup h d) (replacement_core_le_radical h d)] at hh
    exact hne hh
  have hDL := component_commutator_le_of_section_fixed s D₀ Z₀ A₀ hcomm₀ hne
  have hm := map_mono (f := embedM d.radical) hDL
  rw [map_commutator,hDm,hZm,show (replacementComponent d).map (embedM d.radical) = Ltilde d.radical (alpha d.radical) by
    rw [Ltilde_alpha,replacement_residual h d]] at hm
  intro z hd
  apply (mem_B_iff d.radical (alpha d.radical) _ ((replacementGeometry h d).V_local (alpha d.radical) rfl hb) z).mpr
  refine ⟨hDV hd,?_⟩
  intro l hl
  rw [commutator_comm] at hm
  exact hm (commutator_mem_commutator hl hd)

include s in
/-- A locally normal radius subgroup controlled modulo the seed by an
escaping actor lies in the literal Baumann slice. -/
theorem normalized_radius_le_slice_of_actor_at
    (hb : 2 < replacementDistance h d) {a : Vertex d.radical}
    (ha : color d.radical a = false)
    (D A : Subgroup (FreeAmalgam d.radical)) (hDV : D ≤ V d.radical a)
    (hDN : stabilizer d.radical a ≤ normalizer (D : Set (FreeAmalgam d.radical)))
    (hAG : A ≤ stabilizer d.radical a) (hne : ¬ A ≤ Q d.radical a)
    (hcomm : ⁅D,A⁆ ≤ Z d.radical a) :
    D ≤ B d.radical a ((replacementGeometry h d).Z_normal _) := by
  obtain ⟨g,hga⟩ := exists_mVertex_of_color d.radical ha
  subst a
  have hbase : act d.radical g⁻¹ (mVertex d.radical g) = alpha d.radical := by
    simp only [act_mVertex,mul_inv_cancel]
    rfl
  let j := (MulAut.conj (g⁻¹)⁻¹).toMonoidHom
  have hi : Function.Injective j := (MulAut.conj (g⁻¹)⁻¹).injective
  have hh := normalized_radius_le_slice_of_actor s hb
  rw [←hbase] at hh
  have hm := hh (D.map j) (A.map j)
    (by rw [V_act]; exact map_mono hDV)
    (by rw [stabilizer_act]; exact (map_mono hDN).trans (D.le_normalizer_map j))
    (by rw [stabilizer_act]; exact map_mono hAG)
    (by rw [Q_act]; exact fun hn => hne ((map_le_map_iff_of_injective hi).mp hn))
    (by rw [Z_act,←map_commutator]; exact map_mono hcomm)
  rw [Escape.PairingControl.FirstPairing.B_act hb g⁻¹ (mVertex d.radical g) ha] at hm
  exact (map_le_map_iff_of_injective hi).mp hm

include s in
/-- A nonzero seed-kernel witness cannot control a normal escaping span
on the same conjugate. All groups and maps belong to the original graph. -/
theorem predecessor_seed_witness_false
    (hc : DistanceTwo.CentralLayer d) (hb : 2 < replacementDistance h d)
    (u : Equiv.Perm (Fin 6))
    (hR : d.radical.map s.projection ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {c z a : Vertex d.radical}
    (q : CriticalPath d.radical (replacementGeometry h d) c z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical c) < 4)
    (ha : color d.radical a = false) (hca : (cosetGraph d.radical).dist c a ≤ 2)
    (Y : Subgroup (FreeAmalgam d.radical)) (hYV : Y ≤ V d.radical a)
    (hYN : stabilizer d.radical a ≤ normalizer (Y : Set (FreeAmalgam d.radical)))
    (hYB : ¬ Y ≤ B d.radical a ((replacementGeometry h d).Z_normal _))
    (x : FreeAmalgam d.radical) (hx : x ∈ stabilizer d.radical c)
    (hZpre : (Z d.radical a).map (MulAut.conj x).toMonoidHom ≤
      Q d.radical (q.walk.getVert (q.walk.length-2)))
    (hYpre : Y.map (MulAut.conj x).toMonoidHom ≤
      Q d.radical (q.walk.getVert (q.walk.length-2)))
    (hcard : Nat.card (⁅(Z d.radical a).map (MulAut.conj x).toMonoidHom,
      Z d.radical z ⊓ Q d.radical c⁆ : Subgroup (FreeAmalgam d.radical)) = 2) :
    False := by
  let K := Z d.radical z ⊓ Q d.radical c
  let f := (MulAut.conj x).toMonoidHom
  let fi := (MulAut.conj x⁻¹).toMonoidHom
  let A := K.map fi
  let J := ⁅(Z d.radical a).map f,K⁆
  let N := ⁅K,Q d.radical (q.walk.getVert (q.walk.length-2))⁆
  have hAf : A.map f = K := by
    rw [map_map]
    have he : f.comp fi = MonoidHom.id (FreeAmalgam d.radical) := by
      apply MonoidHom.ext
      intro v
      change x*(x⁻¹*v*(x⁻¹)⁻¹)*x⁻¹ = v
      group
    rw [he,map_id]
  have hAQ : A ≤ Q d.radical c :=
    (map_mono (show K ≤ Q d.radical c from inf_le_right)).trans_eq
      (mem_normalizer_iff_map_conj_eq.mp
        ((Q_normalized d.radical c) ((stabilizer d.radical c).inv_mem hx)))
  have hAG : A ≤ stabilizer d.radical a := hAQ.trans
    (Q_le_stabilizer_of_dist_le_two c a q.start_color ha hca)
  have hZA : ⁅Z d.radical a,A⁆ ≤ Z d.radical a :=
    le_normalizer_iff_commutator_le_left.mp (hAG.trans (Z_normalized d.radical a))
  have hZAmap : (⁅Z d.radical a,A⁆ : Subgroup (FreeAmalgam d.radical)).map f = J := by
    rw [map_commutator,hAf]
  have hcardN : Nat.card N ≤ 2 := small_critical_kernel_predecessor_card s hc hb u hR q hsmall
  have hJN : J ≤ N := by
    dsimp only [J,N]
    rw [commutator_comm ((Z d.radical a).map f)]
    exact commutator_mono le_rfl hZpre
  let v := q.walk.getVert (q.walk.length-2)
  have hvcol : color d.radical v = false := by
    apply (q.vertex_color (Nat.sub_le _ _)).mpr
    have he := replacementDistance_even h d
    rw [Nat.even_iff] at he ⊢
    have hl : q.walk.length = replacementDistance h d := q.length_eq_b
    omega
  have hvz : (cosetGraph d.radical).dist v z = 2 := by
    rw [q.dist_end]
    have hl : q.walk.length = replacementDistance h d := q.length_eq_b
    omega
  have hNZ : N ≤ Z d.radical z :=
    (commutator_mono inf_le_left le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp
        ((Q_le_stabilizer_of_dist_two d.radical v z hvcol hvz).trans (Z_normalized d.radical z)))
  let := finite_Z d.radical z
  let : Finite N := Finite.of_injective (inclusion hNZ) (inclusion_injective _)
  have hJN' : J = N := eq_of_le_of_card_ge hJN (by rw [hcard]; exact hcardN)
  have hYA : ⁅Y,A⁆ ≤ Z d.radical a := by
    apply le_trans _ hZA
    apply (map_le_map_iff_of_injective (f := f) (MulAut.conj x).injective).mp
    rw [hZAmap,map_commutator,hAf,hJN',commutator_comm (Y.map f)]
    exact commutator_mono le_rfl hYpre
  have hAcore : A ≤ Q d.radical a := by
    by_contra hnA
    exact hYB (normalized_radius_le_slice_of_actor_at s hb ha Y A hYV hYN hAG hnA hYA)
  have hzero : ⁅Z d.radical a,A⁆ = ⊥ := le_bot_iff.mp
    ((commutator_mono le_rfl hAcore).trans_eq (Z_centralizes_Q d.radical a ha))
  rw [hzero,Subgroup.map_bot] at hZAmap
  change Nat.card J = 2 at hcard
  rw [←hZAmap] at hcard
  simp at hcard


/-- The actual full-point, small-image forward slice is strictly greater
than two above distance four. The seed-kernel witness controls the entire
shifted span, so its escaping normal section gives a contradiction. -/
theorem full_point_small_forward_slice_gt_two_knownSimple
    {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
    {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
    {d : Replacement L R} (hb : 4 < replacementDistance h d)
    (u : Equiv.Perm (Fin 6))
    (hfull : d.radical.map (SourceReduction.projection h e hz hn d) =
      pointCore.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4) :
    2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)) := by
  by_contra! hslice
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hfull' : d.radical.map s.projection = pointCore.map (MulAut.conj u).toMonoidHom := by
    rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
  obtain ⟨z,q,haz,_,hpre,t,_,_,y,hy,_,hPgen,hHmove,hDQ,
    hidx,hJcard,_,_,_,_,_,_,x,hx,hxJ⟩ :=
    full_point_small_shifted_central_line_knownSimple hb u hfull p hslice hsmall
  have hline := full_point_small_forward_line_knownSimple (by omega) u hfull p hslice hsmall
  have cfg := small_shifted_forward_configuration_of_choice s hc u hfull' hb p hsmall
    hline.1 z q.end_color haz y (Ltilde_le_stabilizer _ hy) hPgen hHmove
  obtain ⟨_,_,_,_,hYV,hYN,hYB,_,_,_,_,_,_,_,hWQ⟩ := cfg
  let c := p.walk.getVert 2
  let a := act d.radical y⁻¹ (alpha d.radical)
  let T := Q d.radical (alpha d.radical) ⊓ centralizer
    (U d.radical c ⊓ B d.radical (alpha d.radical)
      ((replacementGeometry h d).Z_normal _) : Set (FreeAmalgam d.radical))
  let H₂ := (⁅U d.radical c,T⁆ : Subgroup (FreeAmalgam d.radical)).map (MulAut.conj y).toMonoidHom
  let P := stabilizer d.radical c ⊓ centralizer (H₂ : Set (FreeAmalgam d.radical))
  let D := conjugateSpanBy (Z d.radical a) P
  let Y := (localZSpan d.radical c (alpha d.radical)).map (MulAut.conj y).toMonoidHom
  have hxP : x ∈ P := hx
  have hZxD : (Z d.radical a).map (MulAut.conj x).toMonoidHom ≤ D := by
    dsimp only [D]
    rw [conjugateSpanBy_eq_iSup_conj]
    exact le_iSup (fun k : P => (Z d.radical a).map
      (MulAut.conj (k : FreeAmalgam d.radical)).toMonoidHom) ⟨x,hxP⟩
  have hYxW : Y.map (MulAut.conj x).toMonoidHom ≤ conjugateSpanBy Y P := by
    rw [conjugateSpanBy_eq_iSup_conj]
    exact le_iSup (fun k : P => Y.map
      (MulAut.conj (k : FreeAmalgam d.radical)).toMonoidHom) ⟨x,hxP⟩
  have ha : color d.radical a = false := by
    rw [action_preserves_color]
    rfl
  have hca : (cosetGraph d.radical).dist c a = 2 := by
    have hfix : act d.radical y⁻¹ c = c :=
      (stabilizer d.radical c).inv_mem (Ltilde_le_stabilizer c hy)
    have hh := dist_act d.radical y⁻¹ c (alpha d.radical)
    rw [hfix,SimpleGraph.dist_comm (u := c) (v := alpha d.radical)] at hh
    exact hh.trans (p.dist_start (by
      have hl : p.walk.length = replacementDistance h d := p.length_eq_b
      omega))
  apply predecessor_seed_witness_false s hc (by omega) u hfull'.le q
    (by rw [hidx]; decide) ha hca.le Y hYV hYN hYB x hxP.1
  · rw [hpre]
    exact hZxD.trans hDQ
  · rw [hpre]
    exact hYxW.trans hWQ
  · rw [hxJ]
    exact hJcard


/-- Vertex-transitive transport of the strict forward slice uses the same
critical walk, second vertex and Baumann subgroup. -/
theorem full_point_small_forward_slice_gt_two_at_knownSimple
    {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
    {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
    {d : Replacement L R} (hb : 4 < replacementDistance h d)
    (u : Equiv.Perm (Fin 6))
    (hfull : d.radical.map (SourceReduction.projection h e hz hn d) =
      pointCore.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4) :
    2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)) := by
  obtain ⟨g,hg⟩ := exists_mVertex_of_color d.radical p.start_color
  have hbase : act d.radical g⁻¹ a = alpha d.radical := by
    rw [hg,act_mVertex,mul_inv_cancel]
    rfl
  have hpact : ∃ p₀ : CriticalPath d.radical (replacementGeometry h d)
      (act d.radical g⁻¹ a) (act d.radical g⁻¹ a'),
      p₀.walk.getVert 2 = act d.radical g⁻¹ (p.walk.getVert 2) :=
    ⟨p.act g⁻¹,by simp only [CriticalPath.act,actWalk_getVert]⟩
  rw [hbase] at hpact
  obtain ⟨p₀,hvert⟩ := hpact
  have hsmall₀ : (Q d.radical (act d.radical g⁻¹ a')).relIndex
      (Z d.radical (alpha d.radical)) < 4 := by
    rw [←hbase,Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹⁻¹).injective]
    exact hsmall
  have hB := Escape.PairingControl.FirstPairing.B_act
    (geometry := replacementGeometry h d) (by change 2 < replacementDistance h d; omega)
    g⁻¹ a p.start_color
  rw [hbase,inv_inv] at hB
  have hi := full_point_small_forward_slice_gt_two_knownSimple hb u hfull p₀ hsmall₀
  rw [hvert,U_act,inv_inv,hB,relIndex_map_map_of_injective _ _ (MulAut.conj g).injective] at hi
  exact hi

/-- The strict estimate discharges the numerical premise of the actual
backward shift. One transporter preserves the prescribed first edge and
every overlapping vertex, for both full covers. -/
theorem full_point_small_backward_shift_of_four_lt_knownSimple
    {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
    {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
    {d : Replacement L R} (hb : 4 < replacementDistance h d)
    (u : Equiv.Perm (Fin 6))
    (hfull : d.radical.map (SourceReduction.projection h e hz hn d) =
      pointCore.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4) :
    ∃ t, Adjacent d.radical (alpha d.radical) t ∧
      Q d.radical t ⊔ Z d.radical a' = stabilizer d.radical (alpha d.radical) ∧
      ∃ g ∈ stabilizer d.radical (alpha d.radical),
        act d.radical g (p.walk.getVert 1) = t ∧
        ∃ q : CriticalPath d.radical (replacementGeometry h d)
          (act d.radical g (p.walk.getVert 2)) (p.walk.getVert (p.walk.length-2)),
          q.walk.getVert 1 = t ∧
          (∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i) ∧
          2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
            (U d.radical (act d.radical g (p.walk.getVert 2))) := by
  apply full_point_backward_shift_knownSimple (by omega) u hfull p
  · exact adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by
        have hl : p.walk.length = replacementDistance h d := p.length_eq_b
        omega)))
  · exact full_point_small_forward_slice_gt_two_knownSimple hb u hfull p hsmall


end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
