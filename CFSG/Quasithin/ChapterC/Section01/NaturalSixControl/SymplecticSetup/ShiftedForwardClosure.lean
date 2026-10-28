module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.ForwardClosure
/-!
# The shifted forward controlled-line contradiction

Let Y be a normal subgroup of the starting critical radius that is not in
its Baumann subgroup. Suppose [Y,T] lies in a line H noncentral on a nearby
endpoint layer Zd, while T contains the predecessor layer and Ze ∩ Qα.
The commutator with the predecessor layer lies both in H and that layer;
the distance bound makes it centralize Zd, so it must vanish. This places
Y in the predecessor kernel and hence in the endpoint stabilizer. The same
argument now makes Y centralize Ze ∩ Qα. The critical commutator bound and
normal-section control force Y into Bα, a contradiction.

The two successive centralizer steps use only the stated distance bounds,
including critical distance six. This is the critical-pair exclusion in
the second paragraph of MS93 (5.9), printed pp.920--921.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
variable {M : Type*} [Group M] [Finite M] {L R W : Subgroup M} [L.Normal] [W.Normal]
  (s : Source L R W)

/-- A normal radius subgroup with a controlled line noncentral on the nearby
endpoint cannot remain outside the starting Baumann subgroup. -/
theorem shifted_critical_controlled_line_false
    (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection=Model.E.map (MulAut.conj u).toMonoidHom)
    (hb : 4<s.geometry.b R) {e : Vertex R}
    (p : CriticalPath R s.geometry (alpha R) e)
    (d : Vertex R) (hd : color R d=false)
    (hed : (cosetGraph R).dist e d≤2)
    (hpd : (cosetGraph R).dist (p.walk.getVert (p.walk.length-2)) d≤4)
    (Y T₀ H₁ : Subgroup (FreeAmalgam R))
    (hYV : Y≤V R (alpha R))
    (hYN : stabilizer R (alpha R)≤normalizer (Y:Set (FreeAmalgam R)))
    (hYB : ¬Y≤B R (alpha R) (s.geometry.Z_normal _))
    (hHZ : H₁≤Z R (alpha R)) (hcard : Nat.card H₁≤2)
    (hHd : ¬H₁≤centralizer (Z R d:Set (FreeAmalgam R)))
    (hcomm : ⁅Y,T₀⁆≤H₁)
    (hinner : Z R (p.walk.getVert (p.walk.length-2)) ⊔ (Z R e⊓Q R (alpha R))≤T₀) :
    False := by
  have hb2 : 2<s.geometry.b R := by omega
  have hl := p.length_eq_b
  have hc : color R (p.walk.getVert (p.walk.length-2))=false := by
    apply (p.vertex_color (Nat.sub_le _ _)).mpr
    have he := s.geometry.even (alpha R) rfl
    change Even (s.geometry.b R) at he
    rw [Nat.even_iff] at he ⊢
    omega
  let := finite_Z R (alpha R)
  let : Finite H₁ := Finite.of_injective (inclusion hHZ) (inclusion_injective _)
  have hsmall (A : Subgroup (FreeAmalgam R)) (hAH : A≤H₁)
      (hAC : A≤centralizer (Z R d:Set (FreeAmalgam R))) : A=⊥ := by
    by_contra hn
    let : Finite A := Finite.of_injective (inclusion hAH) (inclusion_injective _)
    have hpos := (one_lt_card_iff_ne_bot A).mpr hn
    have he : A=H₁ := eq_of_le_of_card_ge hAH (by omega)
    exact hHd (he ▸ hAC)
  have hQd : Q R d≤centralizer (Z R d:Set (FreeAmalgam R)) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q R d hd))
  have hZpd : Z R (p.walk.getVert (p.walk.length-2))≤centralizer (Z R d:Set (FreeAmalgam R)) := by
    apply le_trans _ hQd
    apply Z_le_Q_of_dist_lt R _ (s.geometry.exists_critical _ hc)
    rw [s.geometry.distance_constant _ hc]
    exact lt_of_le_of_lt hpd hb
  have hZed : Z R e≤centralizer (Z R d:Set (FreeAmalgam R)) := by
    apply le_trans _ hQd
    apply Z_le_Q_of_dist_lt R e (s.geometry.exists_critical e p.end_color)
    rw [s.geometry.distance_constant e p.end_color]
    change (cosetGraph R).dist e d<s.geometry.b R
    exact lt_of_le_of_lt hed (by omega)
  have hYGp : Y≤stabilizer R (p.walk.getVert (p.walk.length-2)) :=
    hYV.trans (s.critical_radius_le_predecessor_stabilizer hb2 p)
  have hYp : ⁅Y,Z R (p.walk.getVert (p.walk.length-2))⁆=⊥ := by
    apply hsmall _ ((commutator_mono le_rfl (le_sup_left.trans hinner)).trans hcomm)
    exact (le_normalizer_iff_commutator_le_right.mp (hYGp.trans (Z_normalized R _))).trans hZpd
  have hYfixp := commutator_eq_bot_iff_le_centralizer.mp hYp
  have hYQp : Y≤Q R (p.walk.getVert (p.walk.length-2)) := by
    rw [←s.C_eq_Q _ hc]
    exact le_inf hYGp hYfixp
  have hedge := s.critical_last_edge_inputs hb2 p
  have hYGe : Y≤stabilizer R e :=
    (hYQp.trans hedge.2.1).trans (fun _ hx => hx.2 _ (adjacent_symm R hedge.1))
  have hYQa : Y≤Q R (alpha R) := hYV.trans (s.geometry.V_le_Q hb2 (alpha R) rfl)
  have hYNK : Y≤normalizer (Z R e⊓Q R (alpha R):Set (FreeAmalgam R)) :=
    (le_inf (hYGe.trans (Z_normalized R e))
      (hYQa.trans (Q R (alpha R)).le_normalizer)).trans inf_normalizer_le_normalizer_inf
  have hYK : ⁅Y,Z R e⊓Q R (alpha R)⁆=⊥ := by
    apply hsmall _ ((commutator_mono le_rfl (le_sup_right.trans hinner)).trans hcomm)
    exact (le_normalizer_iff_commutator_le_right.mp hYNK).trans (inf_le_left.trans hZed)
  have hYe := s.critical_commutator_le_start_of_predecessor_fixed h u hfull hb2 p
    Y hYV hYfixp (commutator_eq_bot_iff_le_centralizer.mp hYK)
  exact hYB (s.normalized_radius_le_B_of_critical_commutator u hfull hb2 p Y hYV hYN hYe)

/-- The controlled-line exclusion at any original-group vertex, with the
actual critical walk transported by the right-coset action. -/
theorem shifted_critical_controlled_line_false_at
    (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection=Model.E.map (MulAut.conj u).toMonoidHom)
    (hb : 4<s.geometry.b R) {a e : Vertex R} (ha : color R a=false)
    (p : CriticalPath R s.geometry a e)
    (d : Vertex R) (hd : color R d=false)
    (hed : (cosetGraph R).dist e d≤2)
    (hpd : (cosetGraph R).dist (p.walk.getVert (p.walk.length-2)) d≤4)
    (Y T₀ H₁ : Subgroup (FreeAmalgam R))
    (hYV : Y≤V R a)
    (hYN : stabilizer R a≤normalizer (Y:Set (FreeAmalgam R)))
    (hYB : ¬Y≤B R a (s.geometry.Z_normal _))
    (hHZ : H₁≤Z R a) (hcard : Nat.card H₁≤2)
    (hHd : ¬H₁≤centralizer (Z R d:Set (FreeAmalgam R)))
    (hcomm : ⁅Y,T₀⁆≤H₁)
    (hinner : Z R (p.walk.getVert (p.walk.length-2)) ⊔ (Z R e⊓Q R a)≤T₀) :
    False := by
  obtain ⟨g,rfl⟩ := exists_mVertex_of_color R ha
  have hbase : act R g⁻¹ (mVertex R g)=alpha R := by
    simp only [act_mVertex,mul_inv_cancel]
    rfl
  let j := (MulAut.conj (g⁻¹)⁻¹).toMonoidHom
  have base := s.shifted_critical_controlled_line_false h u hfull hb (e:=act R g⁻¹ e)
  rw [←hbase] at base
  refine base (p.act g⁻¹) (act R g⁻¹ d) (by rwa [action_preserves_color])
    (by rwa [dist_act]) ?_ (Y.map j) (T₀.map j) (H₁.map j) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · change (cosetGraph R).dist
      ((actWalk R g⁻¹ p.walk).getVert ((actWalk R g⁻¹ p.walk).length-2)) (act R g⁻¹ d)≤4
    rwa [actWalk_length,actWalk_getVert,dist_act]
  · rw [V_act]
    exact map_mono hYV
  · rw [stabilizer_act]
    exact (map_mono hYN).trans (Y.le_normalizer_map j)
  · rw [Escape.PairingControl.FirstPairing.B_act (by omega : 2<s.geometry.b R) g⁻¹ (mVertex R g) ha]
    exact fun hh => hYB ((map_le_map_iff_of_injective (MulAut.conj (g⁻¹)⁻¹).injective).mp hh)
  · rw [Z_act]
    exact map_mono hHZ
  · rwa [card_map_of_injective (MulAut.conj (g⁻¹)⁻¹).injective]
  · intro hh
    apply hHd
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply map_injective (f:=j) (MulAut.conj (g⁻¹)⁻¹).injective
    rw [map_commutator,Subgroup.map_bot]
    rw [Z_act] at hh
    exact commutator_eq_bot_iff_le_centralizer.mpr hh
  · rw [←map_commutator]
    exact map_mono hcomm
  · change Z R ((actWalk R g⁻¹ p.walk).getVert ((actWalk R g⁻¹ p.walk).length-2)) ⊔
      (Z R (act R g⁻¹ e)⊓Q R (act R g⁻¹ (mVertex R g)))≤T₀.map j
    rw [actWalk_length,actWalk_getVert,Z_act,Z_act,Q_act,←map_inf _ _ j
      (MulAut.conj (g⁻¹)⁻¹).injective,←Subgroup.map_sup]
    exact map_mono hinner

end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source

namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.SourceData
variable {K : Type*} [Group K] [Finite K] {L W : Subgroup K} [L.Normal] [W.Normal]
  {T : Sylow 2 K} (d : NaturalSixControl.SourceData L W T)

/-- A shifted controlled-line configuration in a literal replacement forces
its alternating-block alternative. -/
theorem reducedSource_block_of_shifted_controlled_line (hm : IntrinsicMSPair d)
    (r : CharacteristicReduction (L.subgroupOf (L⊔d.B)) (d.B.subgroupOf (L⊔d.B)))
    {e : Vertex r.radical}
    (p : CriticalPath r.radical ((originalSource d hm).reduce r).geometry (alpha r.radical) e)
    (hb : 4<((originalSource d hm).reduce r).geometry.b r.radical)
    (f : Vertex r.radical) (hf : color r.radical f=false)
    (hef : (cosetGraph r.radical).dist e f≤2)
    (hpf : (cosetGraph r.radical).dist (p.walk.getVert (p.walk.length-2)) f≤4)
    (Y T₀ H₁ : Subgroup (FreeAmalgam r.radical))
    (hYV : Y≤V r.radical (alpha r.radical))
    (hYN : stabilizer r.radical (alpha r.radical)≤normalizer (Y:Set (FreeAmalgam r.radical)))
    (hYB : ¬Y≤B r.radical (alpha r.radical) (((originalSource d hm).reduce r).geometry.Z_normal _))
    (hHZ : H₁≤Z r.radical (alpha r.radical)) (hcard : Nat.card H₁≤2)
    (hHf : ¬H₁≤centralizer (Z r.radical f:Set (FreeAmalgam r.radical)))
    (hcomm : ⁅Y,T₀⁆≤H₁)
    (hinner : Z r.radical (p.walk.getVert (p.walk.length-2)) ⊔
      (Z r.radical e⊓Q r.radical (alpha r.radical))≤T₀) :
    IsAlternatingBlock L 6 := by
  rcases reducedSource_block_or_full_point_image d hm r with hblock|hfull
  · exact hblock
  · exact (Source.shifted_critical_controlled_line_false ((originalSource d hm).reduce r)
      (reduced_nativeCentralLayer d hm r) d.relabeler.val⁻¹
      (by simpa only [Model.pointCore_eq_exceptional] using hfull) hb p f hf hef hpf
      Y T₀ H₁ hYV hYN hYB hHZ hcard hHf hcomm hinner).elim

/-- At an arbitrary starting vertex, a controlled-line configuration in the
literal replacement forces its alternating-block alternative. -/
theorem reducedSource_block_of_shifted_controlled_line_at (hm : IntrinsicMSPair d)
    (r : CharacteristicReduction (L.subgroupOf (L⊔d.B)) (d.B.subgroupOf (L⊔d.B)))
    {a e : Vertex r.radical}
    (ha : color r.radical a=false)
    (p : CriticalPath r.radical ((originalSource d hm).reduce r).geometry a e)
    (hb : 4<((originalSource d hm).reduce r).geometry.b r.radical)
    (f : Vertex r.radical) (hf : color r.radical f=false)
    (hef : (cosetGraph r.radical).dist e f≤2)
    (hpf : (cosetGraph r.radical).dist (p.walk.getVert (p.walk.length-2)) f≤4)
    (Y T₀ H₁ : Subgroup (FreeAmalgam r.radical))
    (hYV : Y≤V r.radical a)
    (hYN : stabilizer r.radical a≤normalizer (Y:Set (FreeAmalgam r.radical)))
    (hYB : ¬Y≤B r.radical a (((originalSource d hm).reduce r).geometry.Z_normal _))
    (hHZ : H₁≤Z r.radical a) (hcard : Nat.card H₁≤2)
    (hHf : ¬H₁≤centralizer (Z r.radical f:Set (FreeAmalgam r.radical)))
    (hcomm : ⁅Y,T₀⁆≤H₁)
    (hinner : Z r.radical (p.walk.getVert (p.walk.length-2)) ⊔
      (Z r.radical e⊓Q r.radical a)≤T₀) :
    IsAlternatingBlock L 6 := by
  rcases reducedSource_block_or_full_point_image d hm r with hblock|hfull
  · exact hblock
  · exact (Source.shifted_critical_controlled_line_false_at ((originalSource d hm).reduce r)
      (reduced_nativeCentralLayer d hm r) d.relabeler.val⁻¹
      (by simpa only [Model.pointCore_eq_exceptional] using hfull) hb ha p f hf hef hpf
      Y T₀ H₁ hYV hYN hYB hHZ hcard hHf hcomm hinner).elim

end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.SourceData
