module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.RootSelectedMovement
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.RootEscape
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.DistanceReduction.PairedChoice

/-!
# The literal selected pair in the smaller-mover root branch

Transport the smaller-J selector through the graph's right action. The
same two neighboring movers generate with their prescribed endpoint roots,
have the ambient fixed subgroup on all of Z, and both move the critical
commutator. The selected element retains its original parabolic position.

If the endpoint normalized both selected seed joins, inverse conjugation
and the first generating triple would make the original nonnormal neighbor
join locally normal. Thus one of these exact two neighbors escapes. Its
seed either yields the native backward critical path with every overlap
identified, or is trapped and has field-sized movement on the full endpoint
intersection, together with the source normalization and quadratic action.

The final application constructs the maximizing parabolic and discharges
its marking, full-kernel, placement and quadratic-action premises from the
original fixed-index bound. The nonnormal neighbor is the one supplied by
ShiftedPaths.replacement_exists_critical_neighbor_escape; equality of its
mover is the literal source branch. No cubic-order premise is used.

This proves the selected root alternative, not the exclusion of its trapped
case. That exclusion, the proper-J large-image and unequal-mover selections,
and the terminal distance arguments remain with this reduction.
Source: MS93 (5.6)--(5.8), printed pp.917--920.
-/

public noncomputable section
open Subgroup Representation Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource MSCentralOrbit

private theorem mover_act {M : Type*} [Group M] [Finite M]
    (R : Subgroup M) (g : FreeAmalgam R) (a t : Vertex R) (q : ℕ) :
    Subgroup.SmallMover.join (U R (act R g a)) (Q R (act R g a))
      (Q R (act R g t)) q =
      (Subgroup.SmallMover.join (U R a) (Q R a) (Q R t) q).map
        (MulAut.conj g⁻¹).toMonoidHom := by
  rw [U_act,Q_act,Q_act,Subgroup.SmallMover.join_map _ (MulAut.conj g⁻¹).injective]

private theorem nonnormal_map_conj {G : Type*} [Group G]
    (S W : Subgroup G) (hn : ¬ S ≤ normalizer (W : Set G))
    {g : G} (hg : g ∈ S) :
    ¬ S ≤ normalizer (W.map (MulAut.conj g).toMonoidHom : Set G) := by
  intro he
  have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) he
  rw [map_normalizer_eq_of_bijective _ (MulAut.conj g⁻¹).bijective] at hh
  have hs : S.map (MulAut.conj g⁻¹).toMonoidHom = S :=
    mem_normalizer_iff_map_conj_eq.mp (S.le_normalizer (S.inv_mem hg))
  have hc : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom = MonoidHom.id G := by
    ext y
    simp [MulAut.conj_apply,mul_assoc]
  rw [hs,Subgroup.map_map,hc,Subgroup.map_id] at hh
  exact hn hh

variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The equal smaller-mover root branch gives the literal pair of selected
neighbors. Both movers move the critical commutator. One member supplies
a backward path or the full nonsplit root obstruction on that same member. -/
theorem Input.replacement_equal_smaller_selected_root_alternative
    {geometry : Geometry d.radical} {a z t c : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hat : Adjacent d.radical a t) (hfirst : path.walk.getVert 1 = t)
    (hct : Adjacent d.radical c t)
    (hnormal : ¬ stabilizer d.radical a ≤ normalizer
      ((Z d.radical c ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _))
    (hequal : Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
        (Q d.radical t) (Nat.card F^2) =
      Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical t) (Nat.card F^2))
    (hsmall : (Q d.radical a).relIndex (Z d.radical z) < Nat.card F^2)
    (B : BinaryField) (hB : B.degree = n)
    (f : stabilizer d.radical a →* Sp B.Carrier) (hf : Function.Surjective f)
    (hfQ : f.ker.map (stabilizer d.radical a).subtype = Q d.radical a)
    (hTf : ((Q d.radical t).subgroupOf (stabilizer d.radical a)).map f ≤ unipotent)
    (hindex : ∀ A : Subgroup (stabilizer d.radical a),
      (centralizer (A : Set (stabilizer d.radical a))).relIndex
        ((U d.radical a).subgroupOf (stabilizer d.radical a)) =
        2 ^ BinaryOffender.fixedCodim (restrictScalars (k := ZMod 2)
          (symplecticNatural (k := B.Carrier) 2)) (A.map f))
    (hquad : ⁅⁅(U d.radical a).subgroupOf (stabilizer d.radical a),
      ((CentralRootGeometry.wing (F := B.Carrier) true).map unipotent.subtype).comap f⁆,
      ((CentralRootGeometry.wing (F := B.Carrier) true).map unipotent.subtype).comap f⁆ = ⊥)
    (hJplane : (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2)).subgroupOf (stabilizer d.radical a) ≤
        ((CentralRootGeometry.wing (F := B.Carrier) true).map unipotent.subtype).comap f) :
    ∃ g ∈ Ltilde d.radical a, ∃ x ∈ Ltilde d.radical a,
      let t₁ := act d.radical g⁻¹ t
      let c₁ := act d.radical g⁻¹ c
      let t₂ := act d.radical x t₁
      let c₂ := act d.radical x c₁
      let J₁ := Subgroup.SmallMover.join (U d.radical c₁) (Q d.radical c₁)
        (Q d.radical t₁) (Nat.card F^2)
      let J₂ := Subgroup.SmallMover.join (U d.radical c₂) (Q d.radical c₂)
        (Q d.radical t₂) (Nat.card F^2)
      Adjacent d.radical a t₁ ∧ Adjacent d.radical c₁ t₁ ∧
      Adjacent d.radical a t₂ ∧ Adjacent d.radical c₂ t₂ ∧
      (J₁ ⊔ Z d.radical z) ⊔ (Z d.radical z).map (MulAut.conj x).toMonoidHom =
        stabilizer d.radical a ∧
      (J₂ ⊔ Z d.radical z) ⊔ (Z d.radical z).map (MulAut.conj x⁻¹).toMonoidHom =
        stabilizer d.radical a ∧
      ((Z d.radical a ⊓ centralizer (J₁ : Set (FreeAmalgam d.radical))) ⊓
        centralizer (J₂ : Set (FreeAmalgam d.radical)) =
          Z d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) ∧
      (¬ ⁅Z d.radical z,U d.radical a⁆ ≤ centralizer (J₁ : Set (FreeAmalgam d.radical))) ∧
      (¬ ⁅Z d.radical z,U d.radical a⁆ ≤ centralizer (J₂ : Set (FreeAmalgam d.radical))) ∧
      x ∈ normalizer (((((CentralRootGeometry.wing (F := B.Carrier) true).map unipotent.subtype).comap f).map
        (stabilizer d.radical a).subtype : Subgroup (FreeAmalgam d.radical)) : Set _) ∧
      x ∈ (planeParabolic.comap f).map (stabilizer d.radical a).subtype ∧
      ∃ v ∈ ({c₁,c₂} : Set (Vertex d.radical)), ∃ w,
        (v = c₁ ∧ w = t₁ ∨ v = c₂ ∧ w = t₂) ∧
        Adjacent d.radical a w ∧ Adjacent d.radical v w ∧
        ¬ Z d.radical z ≤ normalizer
          ((Z d.radical v ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _) ∧
        ((∃ back : CriticalPath d.radical geometry v (path.walk.getVert (path.walk.length-2)),
          back.walk.getVert 1 = w ∧
          ∀ i ≤ path.walk.length-2, back.walk.getVert (i+2) = path.walk.getVert i) ∨
        (Z d.radical v ≤ Q d.radical (path.walk.getVert (path.walk.length-2)) ∧
          Nat.card F ≤ (centralizer (Z d.radical v : Set (FreeAmalgam d.radical))).relIndex
            (Z d.radical z ⊓ Q d.radical a) ∧
          X d.radical z ⊓ Q d.radical a ≤ normalizer (Z d.radical v : Set _) ∧
          ⁅⁅X d.radical z ⊓ Q d.radical a,Z d.radical v⁆,Z d.radical v⁆ = ⊥)) := by
  classical
  obtain ⟨g,hg,x,hx,hgen,hgen₂,hfixed,hxn,hxp,hmove₁,hmove₂⟩ :=
    h.replacement_smaller_mover_root_movement d path hb hat hfirst hsmall
      B hB f hf hfQ hTf hindex hquad hJplane
  let S := stabilizer d.radical a
  let t₁ := act d.radical g⁻¹ t
  let c₁ := act d.radical g⁻¹ c
  let t₂ := act d.radical x t₁
  let c₂ := act d.radical x c₁
  have hgS := Ltilde_le_stabilizer a hg
  have hxS := Ltilde_le_stabilizer a hx
  have hga : act d.radical g⁻¹ a = a := S.inv_mem hgS
  have hxa : act d.radical x a = a := hxS
  have ha₁ : Adjacent d.radical a t₁ := by
    rw [←hga]
    exact (adjacent_act_iff d.radical g⁻¹ _ _).mpr hat
  have hc₁ : Adjacent d.radical c₁ t₁ := (adjacent_act_iff d.radical g⁻¹ _ _).mpr hct
  have ha₂ : Adjacent d.radical a t₂ := by
    rw [←hxa]
    exact (adjacent_act_iff d.radical x _ _).mpr ha₁
  have hc₂ : Adjacent d.radical c₂ t₂ := (adjacent_act_iff d.radical x _ _).mpr hc₁
  refine ⟨g,hg,x,hx,ha₁,hc₁,ha₂,hc₂,?_,?_,?_,?_,?_,hxn,hxp,?_⟩
  · simpa only [mover_act,inv_inv,hequal] using hgen
  · simpa only [mover_act,inv_inv,hequal] using hgen₂
  · simpa only [mover_act,inv_inv,hequal] using hfixed
  · simpa only [mover_act,inv_inv,hequal] using hmove₁
  · simpa only [mover_act,inv_inv,hequal] using hmove₂
  have hn₁ : ¬ S ≤ normalizer
      ((Z d.radical c₁ ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _) := by
    have hh := nonnormal_map_conj S (Z d.radical c ⊔ Z d.radical a) hnormal hgS
    have hZa : (Z d.radical a).map (MulAut.conj g).toMonoidHom = Z d.radical a := by
      simpa only [hga,inv_inv] using (Z_act d.radical g⁻¹ a).symm
    rwa [Subgroup.map_sup,hZa,←show Z d.radical c₁ =
      (Z d.radical c).map (MulAut.conj g).toMonoidHom by simp only [c₁,Z_act,inv_inv]] at hh
  have hchoose : ∃ v ∈ ({c₁,c₂} : Set (Vertex d.radical)), ∃ w,
      (v=c₁ ∧ w=t₁ ∨ v=c₂ ∧ w=t₂) ∧ Adjacent d.radical a w ∧ Adjacent d.radical v w ∧
      ¬ Z d.radical z ≤ normalizer
        ((Z d.radical v ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _) := by
    by_cases hn : Z d.radical z ≤ normalizer
        ((Z d.radical c₁ ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _)
    · refine ⟨c₂,by simp,t₂,Or.inr ⟨rfl,rfl⟩,ha₂,hc₂,?_⟩
      intro hn₂
      have hb := paired_endpoint_normalizes_first_join x hxS hn₂
      have hJedge : (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
          (Q d.radical t) (Nat.card F^2)).map (MulAut.conj g).toMonoidHom ≤ Q d.radical t₁ := by
        simpa only [t₁,Q_act,inv_inv] using map_mono (f := (MulAut.conj g).toMonoidHom)
          (Subgroup.SmallMover.join_le (U d.radical a) (Q d.radical a) (Q d.radical t) (Nat.card F^2))
      apply hn₁
      change stabilizer d.radical a ≤ _
      rw [←hgen]
      refine sup_le (sup_le (hJedge.trans (edge_normalizes_neighbor_seed_join ha₁ hc₁)) hn) ?_
      simpa only [Z_act,inv_inv] using hb
    · exact ⟨c₁,by simp,t₁,Or.inl ⟨rfl,rfl⟩,ha₁,hc₁,hn⟩
  obtain ⟨v,hv,w,hvw,haw,hvw',hn⟩ := hchoose
  refine ⟨v,hv,w,hvw,haw,hvw',hn,?_⟩
  by_cases hk : Z d.radical v ≤ Q d.radical (path.walk.getVert (path.walk.length-2))
  · right
    have hYV : Z d.radical v ≤ V d.radical a := le_sup_left.trans
      (neighbor_seed_join_le_radius haw hvw')
    have hYS : Z d.radical v ≤ stabilizer d.radical z :=
      (le_inf hYV hk).trans (truncated_radius_le_endpoint_stabilizer path (by omega))
    have hYQ := hYV.trans (geometry.V_le_Q (by omega) a path.start_color)
    have hi := h.replacement_seed_actor_centralizer_index_ge_field d path (by omega)
      (Z d.radical v) hYS hYQ hn (Z d.radical v) le_rfl hYS
    have hcolor : color d.radical v = false := by
      have hn₁ := adjacent_color_ne d.radical haw
      have hn₂ := adjacent_color_ne d.radical hvw'
      rw [path.start_color] at hn₁
      cases ht : color d.radical w <;> cases hv : color d.radical v <;> simp_all
    have hAY : X d.radical z ⊓ Q d.radical a ≤ normalizer (Z d.radical v : Set _) :=
      (inf_le_right.trans (Q_le_stabilizer_of_dist_le_two a v path.start_color hcolor
        (by rw [SimpleGraph.dist_comm]; exact neighbor_distance_le_two haw hvw'))).trans
          (Z_normalized d.radical v)
    have htrip := (h.replacement_radius_commutator_bounds d geometry hb path.start_color z
      (path.walk.getVert (path.walk.length-2))).2
    exact ⟨hk,hi,hAY,le_bot_iff.mp
      ((commutator_mono (commutator_mono le_rfl (le_inf hYV hk)) (le_inf hYV hk)).trans_eq htrip)⟩
  · exact Or.inl (exists_backward_path_of_not_le geometry (by omega) path haw hvw' hk)

/-- Actual maximizing-parabolic application in the equal-mover root
branch. The original fixed-index bound supplies the parabolic containment;
the marking, full kernel and quadratic action are all constructed here. -/
theorem Input.replacement_equal_small_index_selected_root_alternative
    {geometry : Geometry d.radical} {a z t c : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hat : Adjacent d.radical a t) (hfirst : path.walk.getVert 1 = t)
    (hct : Adjacent d.radical c t)
    (hnormal : ¬ stabilizer d.radical a ≤ normalizer
      ((Z d.radical c ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _))
    (hequal : Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
        (Q d.radical t) (Nat.card F^2) =
      Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical t) (Nat.card F^2))
    (hsmall : (Q d.radical a).relIndex (Z d.radical z) < Nat.card F^2)
    (hJm : (centralizer (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2) : Set (FreeAmalgam d.radical))).relIndex
        (U d.radical a) ≤ Nat.card F^2) :
    ∃ B : BinaryField, B.degree = n ∧
      ∃ f : stabilizer d.radical a →* Sp B.Carrier,
        Function.Surjective f ∧ f.ker.map (stabilizer d.radical a).subtype = Q d.radical a ∧
        ((Q d.radical t).subgroupOf (stabilizer d.radical a)).map f ≤ unipotent ∧
        (∀ A : Subgroup (stabilizer d.radical a),
          (centralizer (A : Set (stabilizer d.radical a))).relIndex
            ((U d.radical a).subgroupOf (stabilizer d.radical a)) =
            2 ^ BinaryOffender.fixedCodim (restrictScalars (k := ZMod 2)
              (symplecticNatural (k := B.Carrier) 2)) (A.map f)) ∧
    ∃ g ∈ Ltilde d.radical a, ∃ x ∈ Ltilde d.radical a,
      let t₁ := act d.radical g⁻¹ t
      let c₁ := act d.radical g⁻¹ c
      let t₂ := act d.radical x t₁
      let c₂ := act d.radical x c₁
      let J₁ := Subgroup.SmallMover.join (U d.radical c₁) (Q d.radical c₁)
        (Q d.radical t₁) (Nat.card F^2)
      let J₂ := Subgroup.SmallMover.join (U d.radical c₂) (Q d.radical c₂)
        (Q d.radical t₂) (Nat.card F^2)
      Adjacent d.radical a t₁ ∧ Adjacent d.radical c₁ t₁ ∧
      Adjacent d.radical a t₂ ∧ Adjacent d.radical c₂ t₂ ∧
      (J₁ ⊔ Z d.radical z) ⊔ (Z d.radical z).map (MulAut.conj x).toMonoidHom =
        stabilizer d.radical a ∧
      (J₂ ⊔ Z d.radical z) ⊔ (Z d.radical z).map (MulAut.conj x⁻¹).toMonoidHom =
        stabilizer d.radical a ∧
      ((Z d.radical a ⊓ centralizer (J₁ : Set (FreeAmalgam d.radical))) ⊓
        centralizer (J₂ : Set (FreeAmalgam d.radical)) =
          Z d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) ∧
      (¬ ⁅Z d.radical z,U d.radical a⁆ ≤ centralizer (J₁ : Set (FreeAmalgam d.radical))) ∧
      (¬ ⁅Z d.radical z,U d.radical a⁆ ≤ centralizer (J₂ : Set (FreeAmalgam d.radical))) ∧
      x ∈ normalizer (((((CentralRootGeometry.wing (F := B.Carrier) true).map unipotent.subtype).comap f).map
        (stabilizer d.radical a).subtype : Subgroup (FreeAmalgam d.radical)) : Set _) ∧
      x ∈ (planeParabolic.comap f).map (stabilizer d.radical a).subtype ∧
      ∃ v ∈ ({c₁,c₂} : Set (Vertex d.radical)), ∃ w,
        (v = c₁ ∧ w = t₁ ∨ v = c₂ ∧ w = t₂) ∧
        Adjacent d.radical a w ∧ Adjacent d.radical v w ∧
        ¬ Z d.radical z ≤ normalizer
          ((Z d.radical v ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _) ∧
        ((∃ back : CriticalPath d.radical geometry v (path.walk.getVert (path.walk.length-2)),
          back.walk.getVert 1 = w ∧
          ∀ i ≤ path.walk.length-2, back.walk.getVert (i+2) = path.walk.getVert i) ∨
        (Z d.radical v ≤ Q d.radical (path.walk.getVert (path.walk.length-2)) ∧
          Nat.card F ≤ (centralizer (Z d.radical v : Set (FreeAmalgam d.radical))).relIndex
            (Z d.radical z ⊓ Q d.radical a) ∧
          X d.radical z ⊓ Q d.radical a ≤ normalizer (Z d.radical v : Set _) ∧
          ⁅⁅X d.radical z ⊓ Q d.radical a,Z d.radical v⁆,Z d.radical v⁆ = ⊥)) := by
  obtain ⟨B,hB,f,hf,hfQ,hTf,hindex,hcore,hTP,hquad,hmax⟩ :=
    h.replacement_maximizing_parabolic d geometry hb path.start_color hat
  have hJplane := h.replacement_small_mover_le_maximizing_plane_of_index_le d
    geometry hb path.start_color hat B hB f hfQ hTf hindex hmax hJm
  exact ⟨B,hB,f,hf,hfQ,hTf,hindex,
    h.replacement_equal_smaller_selected_root_alternative d path hb hat hfirst hct
      hnormal hequal hsmall B hB f hf hfQ hTf hindex hquad hJplane⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
