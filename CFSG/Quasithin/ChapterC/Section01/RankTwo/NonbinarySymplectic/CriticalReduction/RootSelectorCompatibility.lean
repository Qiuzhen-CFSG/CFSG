module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.SelectedNontrapping

/-!
# Source-compatible backward selection in the critical-root branch

A uniform bound of q on neighboring U-indices excludes trapping of the very
seed chosen by the original smaller-mover selectors. Combining this with the
strict-index alternative removes that numerical premise from the root-image
selection. Every branch retains its actual residual conjugators, individual
movers, generation identities, whole-Z fixed subgroups and path overlaps.

Vertex and edge transitivity and the literal terminal-intersection calculation
supply a neighbor of B-relative U-index at least q. The final application thus
starts with a genuine moving neighbor and constructs its complete selector.
No uniform bound or preselected neighbor remains as an extra input.

Source: MS93 (5.5)--(5.8), printed pp.915--920. The larger critical-image
selector compatibility and terminal distance exclusions remain separate.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource
private theorem global_neighbor_bound_of_edge
    {M : Type*} [Group M] [Finite M] {R : Subgroup M}
    (geometry : Geometry R) (hb : 2 < geometry.b R)
    {a t : Vertex R} (ha : color R a=false) (hat : Adjacent R a t) (q : ℕ)
    (hbound : ∀ c, Adjacent R c t → (B R a (geometry.Z_normal a)).relIndex (U R c) ≤ q)
    {v w c : Vertex R} (hv : color R v=false)
    (hvw : Adjacent R v w) (hcw : Adjacent R c w) :
    (B R v (geometry.Z_normal v)).relIndex (U R c) ≤ q := by
  obtain ⟨g,hg⟩ := exists_mVertex_of_color R hv
  obtain ⟨j,hj⟩ := exists_mVertex_of_color R ha
  let y := g⁻¹*j
  have hy : act R y v=a := by
    rw [hg,act_mVertex]
    dsimp [y]
    rw [mul_inv_cancel_left,←hj]
  have had : Adjacent R a (act R y w) := by
    rw [←hy]
    exact (adjacent_act_iff R y _ _).mpr hvw
  obtain ⟨x,hx,hxt⟩ := stabilizer_transitive_neighbors R a had hat
  have hc : Adjacent R (act R x (act R y c)) t := by
    rw [←hxt]
    exact (adjacent_act_iff R x _ _).mpr ((adjacent_act_iff R y _ _).mpr hcw)
  have hi := hbound _ hc
  rw [movingIndex_act geometry hb ha x hx] at hi
  rw [←hy,Escape.PairingControl.FirstPairing.B_act hb y v hv,U_act,
    relIndex_map_map_of_injective _ _ (MulAut.conj y⁻¹).injective] at hi
  exact hi

variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- Every original edge has a neighboring whole U-layer with B-relative index
at least the field order. The proof keeps the full B-preimage. -/
theorem Input.replacement_exists_neighbor_index_ge_field
    {geometry : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hat : Adjacent d.radical a t) :
    ∃ c, Adjacent d.radical c t ∧
      Nat.card F ≤ (B d.radical a (geometry.Z_normal a)).relIndex (U d.radical c) := by
  by_contra! hsmall
  have hlocal : ∀ c, Adjacent d.radical c t →
      (B d.radical a (geometry.Z_normal a)).relIndex (U d.radical c) ≤ Nat.card F-1 := by
    intro c hc
    have hi := hsmall c hc
    omega
  have hbound : ∀ v w c : Vertex d.radical, color d.radical v=false →
      Adjacent d.radical v w → Adjacent d.radical c w →
      (B d.radical v (geometry.Z_normal v)).relIndex (U d.radical c) ≤ Nat.card F-1 := by
    intro v w c hv hvw hcw
    exact global_neighbor_bound_of_edge geometry (by omega) path.start_color hat
      (Nat.card F-1) hlocal hv hvw hcw
  have hboundq : ∀ v w c : Vertex d.radical, color d.radical v=false →
      Adjacent d.radical v w → Adjacent d.radical c w →
      (B d.radical v (geometry.Z_normal v)).relIndex (U d.radical c) ≤ Nat.card F := by
    intro v w c hv hvw hcw
    exact (hbound v w c hv hvw hcw).trans (Nat.sub_le _ _)
  obtain ⟨_,_,he⟩ := h.replacement_terminal_intersection_of_uniform_bound d path hb hboundq
  have hlen : 4 ≤ path.walk.length := by rw [path.length_eq_b]; exact hb
  have hp : color d.radical (path.walk.getVert (path.walk.length-2))=false := by
    apply (path.vertex_color (Nat.sub_le _ _)).mpr
    have he : Even path.walk.length := by
      rw [path.shortest,path.critical.1]
      exact geometry.even a path.start_color
    rw [Nat.even_iff] at he ⊢
    omega
  have ht : Adjacent d.radical (path.walk.getVert (path.walk.length-2))
      (path.walk.getVert (path.walk.length-1)) := by
    have hh := path.walk.adj_getVert_succ (by omega : path.walk.length-2 < path.walk.length)
    rw [show path.walk.length-2+1=path.walk.length-1 by omega] at hh
    exact (cosetGraph_adj d.radical _ _).mp hh
  have hz : Adjacent d.radical z (path.walk.getVert (path.walk.length-1)) := by
    apply adjacent_symm d.radical
    have hh := path.walk.adj_getVert_succ (by omega : path.walk.length-1 < path.walk.length)
    rw [show path.walk.length-1+1=path.walk.length by omega,SimpleGraph.Walk.getVert_length] at hh
    exact (cosetGraph_adj d.radical _ _).mp hh
  have hi := hbound _ _ _ hp ht hz
  rw [he] at hi
  have hq : 0 < Nat.card F := Nat.card_pos
  omega

/-- Under the global field-sized upper bound, the original selector for a
prescribed moving neighbor yields its backward path with all source data. -/
theorem Input.replacement_root_backward_selection_of_uniform_bound
    {geometry : Geometry d.radical} {a z t c : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hat : Adjacent d.radical a t) (hfirst : path.walk.getVert 1 = t)
    (hct : Adjacent d.radical c t)
    (hmove : 1 < (B d.radical a (geometry.Z_normal a)).relIndex (U d.radical c))
    (hsmall : (Q d.radical a).relIndex (Z d.radical z) < Nat.card F^2)
    (hbound : ∀ v w c : Vertex d.radical, color d.radical v=false →
      Adjacent d.radical v w → Adjacent d.radical c w →
      (B d.radical v (geometry.Z_normal v)).relIndex (U d.radical c) ≤ Nat.card F) :
    ∃ g ∈ Ltilde d.radical a, ∃ x ∈ Ltilde d.radical a,
      let t₁ := act d.radical g⁻¹ t
      let c₁ := act d.radical g⁻¹ c
      let t₂ := act d.radical x t₁
      let c₂ := act d.radical x c₁
      let Ja₁ := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical t₁) (Nat.card F^2)
      let J₁ := Subgroup.SmallMover.join (U d.radical c₁) (Q d.radical c₁)
        (Q d.radical t₁) (Nat.card F^2)
      let J₂ := Subgroup.SmallMover.join (U d.radical c₂) (Q d.radical c₂)
        (Q d.radical t₂) (Nat.card F^2)
      Adjacent d.radical a t₁ ∧ Adjacent d.radical c₁ t₁ ∧
      Adjacent d.radical a t₂ ∧ Adjacent d.radical c₂ t₂ ∧
      (B d.radical a (geometry.Z_normal a)).relIndex (U d.radical c₁) =
        (B d.radical a (geometry.Z_normal a)).relIndex (U d.radical c) ∧
      (B d.radical a (geometry.Z_normal a)).relIndex (U d.radical c₂) =
        (B d.radical a (geometry.Z_normal a)).relIndex (U d.radical c) ∧
      ((x = 1 ∧ Ltilde d.radical a ≤ J₁ ⊔ Z d.radical z ∧
        (Ja₁ ⊔ J₁) ⊔ Z d.radical z = stabilizer d.radical a ∧
        (Z d.radical t ⊓ centralizer (Ja₁ : Set (FreeAmalgam d.radical)) =
          Z d.radical t ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) ∨
         Z d.radical t ⊓ centralizer (J₁ : Set (FreeAmalgam d.radical)) =
          Z d.radical t ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)))) ∨
      (∃ E : BinaryField, E.degree = n ∧
        ∃ f : stabilizer d.radical a →* Sp E.Carrier,
          Function.Surjective f ∧ f.ker.map (stabilizer d.radical a).subtype = Q d.radical a ∧
          ((Q d.radical t).subgroupOf (stabilizer d.radical a)).map f ≤ unipotent ∧
          (∀ A : Subgroup (stabilizer d.radical a),
            (centralizer (A : Set (stabilizer d.radical a))).relIndex
              ((U d.radical a).subgroupOf (stabilizer d.radical a)) =
              2 ^ BinaryOffender.fixedCodim (restrictScalars (k := ZMod 2)
                (symplecticNatural (k := E.Carrier) 2)) (A.map f)) ∧
          (J₁ ⊔ Z d.radical z) ⊔ (Z d.radical z).map (MulAut.conj x).toMonoidHom =
            stabilizer d.radical a ∧
          (J₂ ⊔ Z d.radical z) ⊔ (Z d.radical z).map (MulAut.conj x⁻¹).toMonoidHom =
            stabilizer d.radical a ∧
          ((Z d.radical a ⊓ centralizer (J₁ : Set (FreeAmalgam d.radical))) ⊓
            centralizer (J₂ : Set (FreeAmalgam d.radical)) =
              Z d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) ∧
          x ∈ normalizer (((((CentralRootGeometry.wing (F := E.Carrier) true).map unipotent.subtype).comap f).map
            (stabilizer d.radical a).subtype : Subgroup (FreeAmalgam d.radical)) : Set _) ∧
          x ∈ (planeParabolic.comap f).map (stabilizer d.radical a).subtype)) ∧
      ∃ v ∈ ({c₁,c₂} : Set (Vertex d.radical)), ∃ w,
        (v = c₁ ∧ w = t₁ ∨ v = c₂ ∧ w = t₂) ∧
        Adjacent d.radical a w ∧ Adjacent d.radical v w ∧
        ∃ back : CriticalPath d.radical geometry v (path.walk.getVert (path.walk.length-2)),
          back.walk.getVert 1 = w ∧
          ∀ i ≤ path.walk.length-2, back.walk.getVert (i+2) = path.walk.getVert i := by
  classical
  have hnormal : ¬ stabilizer d.radical a ≤ normalizer
      ((Z d.radical c ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _) := by
    intro hn
    have hidx := (neighbor_seed_join_index_le geometry (by omega) path.start_color hat hct).trans
      (h.replacement_root_neighbor_seed_index_le_cube d path hb hat hct hsmall)
    have hq : 1 < Nat.card F := Finite.one_lt_card
    have hBY := h.replacement_small_radius_le_B d geometry (by omega) path.start_color
      (Z d.radical c ⊔ Z d.radical a) (neighbor_seed_join_le_radius hat hct)
      ((Ltilde_le_stabilizer a).trans hn)
      (lt_of_le_of_lt hidx ((pow_lt_pow_iff_right₀ hq).mpr (by decide)))
    have hone := relIndex_eq_one.mpr (((U_le_Z c).trans le_sup_left).trans hBY)
    rw [hone] at hmove
    exact (lt_irrefl 1) hmove
  by_cases hJm : (centralizer (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2) : Set (FreeAmalgam d.radical))).relIndex
        (U d.radical a) ≤ Nat.card F^2
  · by_cases hequal : Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
        (Q d.radical t) (Nat.card F^2) =
      Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical t) (Nat.card F^2)
    · obtain ⟨E,hE,f,hf,hfQ,hTf,hidx,g,hg,x,hx,ha₁,hc₁,ha₂,hc₂,
        hgen₁,hgen₂,hfixed,hmove₁,hmove₂,hxn,hxp,v,hv,w,hvw,haw,hvw',hn,_⟩ :=
        h.replacement_equal_small_index_selected_root_alternative d path hb hat hfirst hct
          hnormal hequal hsmall hJm
      have hi₁ := movingIndex_act geometry (d := c) (by omega) path.start_color g⁻¹
        ((stabilizer d.radical a).inv_mem (Ltilde_le_stabilizer a hg))
      have hi₂ := movingIndex_act geometry (d := act d.radical g⁻¹ c) (by omega)
        path.start_color x (Ltilde_le_stabilizer a hx)
      refine ⟨g,hg,x,hx,ha₁,hc₁,ha₂,hc₂,hi₁,hi₂.trans hi₁,
        Or.inr ⟨E,hE,f,hf,hfQ,hTf,hidx,hgen₁,hgen₂,hfixed,hxn,hxp⟩,
        v,hv,w,hvw,haw,hvw',?_⟩
      exact h.replacement_selected_seed_backward_of_uniform_bound d path hb haw hvw' hn hbound
    · obtain ⟨g,hg,haw,hvw,hidx,htransport,hgen,hres,hfixed,hindividual,
        hquadA,hquadC,hcube,hnot,hlarge,hn,_⟩ :=
        h.replacement_unequal_individual_generation_root_at_neighbor d path hb hat hfirst hct
          hnormal hsmall hequal
      refine ⟨g,hg,1,(Ltilde d.radical a).one_mem,?_⟩
      dsimp only
      simp only [act_one]
      refine ⟨haw,hvw,haw,hvw,hidx,hidx,Or.inl ⟨True.intro,hres,?_,Or.inl hindividual⟩,?_⟩
      · rwa [htransport] at hgen
      · exact ⟨act d.radical g⁻¹ c,by simp,act d.radical g⁻¹ t,
          Or.inl ⟨rfl,rfl⟩,haw,hvw,
          h.replacement_selected_seed_backward_of_uniform_bound d path hb haw hvw hn hbound⟩
  · obtain ⟨g,hg,haw,hvw,hidx,htransport,hgen,hfixed,hn,_⟩ :=
      h.replacement_large_movement_selected_root_at_neighbor d path hb hat hfirst hct
        hnormal hsmall (lt_of_not_ge hJm)
    have hgen' : Subgroup.SmallMover.join (U d.radical (act d.radical g⁻¹ c))
        (Q d.radical (act d.radical g⁻¹ c)) (Q d.radical (act d.radical g⁻¹ t))
        (Nat.card F^2) ⊔ Z d.radical z = stabilizer d.radical a := by
      rwa [htransport] at hgen
    have hJa : Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical (act d.radical g⁻¹ t)) (Nat.card F^2) ≤ stabilizer d.radical a :=
      (Subgroup.SmallMover.join_le _ _ _ _).trans
        (fun _ hy => hy.2 a (adjacent_symm d.radical haw))
    refine ⟨g,hg,1,(Ltilde d.radical a).one_mem,?_⟩
    dsimp only
    simp only [act_one]
    refine ⟨haw,hvw,haw,hvw,hidx,hidx,Or.inl ⟨True.intro,?_,?_,Or.inr ?_⟩,?_⟩
    · rw [hgen']; exact Ltilde_le_stabilizer a
    · rw [sup_assoc,hgen',sup_eq_right.mpr hJa]
    · rwa [htransport] at hfixed
    · exact ⟨act d.radical g⁻¹ c,by simp,act d.radical g⁻¹ t,
        Or.inl ⟨rfl,rfl⟩,haw,hvw,
        h.replacement_selected_seed_backward_of_uniform_bound d path hb haw hvw hn hbound⟩

/-- The root-image case of source (5.8), with a genuine moving neighbor,
the actual original selector and its complete backward critical path. No
moving-index, uniform-bound or selected-path premise is assumed. -/
theorem Input.replacement_root_source_backward_selection
    {geometry : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hat : Adjacent d.radical a t) (hfirst : path.walk.getVert 1 = t)
    (hsmall : (Q d.radical a).relIndex (Z d.radical z) < Nat.card F^2) :
    ∃ c, Adjacent d.radical c t ∧
      Nat.card F ≤ (B d.radical a (geometry.Z_normal a)).relIndex (U d.radical c) ∧
    ∃ g ∈ Ltilde d.radical a, ∃ x ∈ Ltilde d.radical a,
      let t₁ := act d.radical g⁻¹ t
      let c₁ := act d.radical g⁻¹ c
      let t₂ := act d.radical x t₁
      let c₂ := act d.radical x c₁
      let Ja₁ := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical t₁) (Nat.card F^2)
      let J₁ := Subgroup.SmallMover.join (U d.radical c₁) (Q d.radical c₁)
        (Q d.radical t₁) (Nat.card F^2)
      let J₂ := Subgroup.SmallMover.join (U d.radical c₂) (Q d.radical c₂)
        (Q d.radical t₂) (Nat.card F^2)
      Adjacent d.radical a t₁ ∧ Adjacent d.radical c₁ t₁ ∧
      Adjacent d.radical a t₂ ∧ Adjacent d.radical c₂ t₂ ∧
      (B d.radical a (geometry.Z_normal a)).relIndex (U d.radical c₁) =
        (B d.radical a (geometry.Z_normal a)).relIndex (U d.radical c) ∧
      (B d.radical a (geometry.Z_normal a)).relIndex (U d.radical c₂) =
        (B d.radical a (geometry.Z_normal a)).relIndex (U d.radical c) ∧
      ((x = 1 ∧ Ltilde d.radical a ≤ J₁ ⊔ Z d.radical z ∧
        (Ja₁ ⊔ J₁) ⊔ Z d.radical z = stabilizer d.radical a ∧
        (Z d.radical t ⊓ centralizer (Ja₁ : Set (FreeAmalgam d.radical)) =
          Z d.radical t ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) ∨
         Z d.radical t ⊓ centralizer (J₁ : Set (FreeAmalgam d.radical)) =
          Z d.radical t ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)))) ∨
      (∃ E : BinaryField, E.degree = n ∧
        ∃ f : stabilizer d.radical a →* Sp E.Carrier,
          Function.Surjective f ∧ f.ker.map (stabilizer d.radical a).subtype = Q d.radical a ∧
          ((Q d.radical t).subgroupOf (stabilizer d.radical a)).map f ≤ unipotent ∧
          (∀ A : Subgroup (stabilizer d.radical a),
            (centralizer (A : Set (stabilizer d.radical a))).relIndex
              ((U d.radical a).subgroupOf (stabilizer d.radical a)) =
              2 ^ BinaryOffender.fixedCodim (restrictScalars (k := ZMod 2)
                (symplecticNatural (k := E.Carrier) 2)) (A.map f)) ∧
          (J₁ ⊔ Z d.radical z) ⊔ (Z d.radical z).map (MulAut.conj x).toMonoidHom =
            stabilizer d.radical a ∧
          (J₂ ⊔ Z d.radical z) ⊔ (Z d.radical z).map (MulAut.conj x⁻¹).toMonoidHom =
            stabilizer d.radical a ∧
          ((Z d.radical a ⊓ centralizer (J₁ : Set (FreeAmalgam d.radical))) ⊓
            centralizer (J₂ : Set (FreeAmalgam d.radical)) =
              Z d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) ∧
          x ∈ normalizer (((((CentralRootGeometry.wing (F := E.Carrier) true).map unipotent.subtype).comap f).map
            (stabilizer d.radical a).subtype : Subgroup (FreeAmalgam d.radical)) : Set _) ∧
          x ∈ (planeParabolic.comap f).map (stabilizer d.radical a).subtype)) ∧
      ∃ v ∈ ({c₁,c₂} : Set (Vertex d.radical)), ∃ w,
        (v = c₁ ∧ w = t₁ ∨ v = c₂ ∧ w = t₂) ∧
        Adjacent d.radical a w ∧ Adjacent d.radical v w ∧
        ∃ back : CriticalPath d.radical geometry v (path.walk.getVert (path.walk.length-2)),
          back.walk.getVert 1 = w ∧
          ∀ i ≤ path.walk.length-2, back.walk.getVert (i+2) = path.walk.getVert i := by
  classical
  by_cases hlarge : ∃ c, Adjacent d.radical c t ∧
      Nat.card F < (B d.radical a (geometry.Z_normal a)).relIndex (U d.radical c)
  · obtain ⟨c,hct,hmove⟩ := hlarge
    exact ⟨c,hct,hmove.le,h.replacement_root_backward_selection d path hb hat hfirst hct hmove hsmall⟩
  · have hlocal : ∀ c, Adjacent d.radical c t →
        (B d.radical a (geometry.Z_normal a)).relIndex (U d.radical c) ≤ Nat.card F := by
      intro c hct
      exact le_of_not_gt (fun hi => hlarge ⟨c,hct,hi⟩)
    have hbound : ∀ v w c : Vertex d.radical, color d.radical v=false →
        Adjacent d.radical v w → Adjacent d.radical c w →
        (B d.radical v (geometry.Z_normal v)).relIndex (U d.radical c) ≤ Nat.card F := by
      intro v w c hv hvw hcw
      exact global_neighbor_bound_of_edge geometry (by omega) path.start_color hat
        (Nat.card F) hlocal hv hvw hcw
    obtain ⟨c,hct,hmove⟩ := h.replacement_exists_neighbor_index_ge_field d path hb hat
    have hq : 1 < Nat.card F := Finite.one_lt_card
    exact ⟨c,hct,hmove,h.replacement_root_backward_selection_of_uniform_bound d path hb hat hfirst
      hct (hq.trans_le hmove) hsmall hbound⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
