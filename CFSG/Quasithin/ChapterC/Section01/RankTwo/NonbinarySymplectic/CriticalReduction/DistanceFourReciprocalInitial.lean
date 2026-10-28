module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourCoherentComparison
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourEqualSmallCriticalFixed
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourEqualSmallSeedIntersection
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourCoherentComparison

/-!
# A new initial path retaining its reciprocal selection

In the strict equal-root branch, the original-fixed selector pair has an
untrapped member. Keep the original natural marking, both raw selectors and
all three generating actors while constructing its actual backward path.
The old equal-small relation is the terminal relation of this new path;
its transport is the new first relation. The original-versus-selected
full fixed identity is exactly the new midpoint certificate.

The intentional private import reuses the frozen nontrapping calculation.
No fixedness of a radius or reciprocal strict B-index is assumed.
Source: MS93 (5.12), printed pp.925--927.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Theory.SpecificGroups.SymplecticFour
open scoped Pointwise
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
open CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.LargeDistance
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- Construct a new initial path from the original strict equal-root witnesses,
retaining its literal reciprocal fixed identity and complete original marking. -/
theorem Input.replacement_distance_four_reciprocal_initial
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (hmove : Nat.card F < (B d.radical a (geometry.Z_normal a)).relIndex
      (U d.radical (path.walk.getVert 2)))
    (hequal : Subgroup.SmallMover.join (U d.radical (path.walk.getVert 2))
        (Q d.radical (path.walk.getVert 2)) (Q d.radical (path.walk.getVert 1)) (Nat.card F^2) =
      Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical (path.walk.getVert 1)) (Nat.card F^2))
    (hsmall : (Q d.radical a).relIndex (Z d.radical z) < Nat.card F^2)
    (hJm : (centralizer (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical (path.walk.getVert 1)) (Nat.card F^2) : Set (FreeAmalgam d.radical))).relIndex
        (U d.radical a) ≤ Nat.card F^2) :
    ∃ E : BinaryField, E.degree=n ∧
      ∃ f : stabilizer d.radical a →* Sp E.Carrier,
        Function.Surjective f ∧ f.ker.map (stabilizer d.radical a).subtype=Q d.radical a ∧
        ((Q d.radical (path.walk.getVert 1)).subgroupOf (stabilizer d.radical a)).map f ≤ unipotent ∧
        (∀ A : Subgroup (stabilizer d.radical a),
          (centralizer (A : Set (stabilizer d.radical a))).relIndex
            ((U d.radical a).subgroupOf (stabilizer d.radical a)) =
            2 ^ BinaryOffender.fixedCodim (restrictScalars (k := ZMod 2)
              (symplecticNatural (k := E.Carrier) 2)) (A.map f)) ∧
        (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
          (Q d.radical (path.walk.getVert 1)) (Nat.card F^2)).subgroupOf (stabilizer d.radical a) ≤
            ((CentralRootGeometry.wing (F := E.Carrier) true).map unipotent.subtype).comap f ∧
        ⁅⁅(U d.radical a).subgroupOf (stabilizer d.radical a),
          ((CentralRootGeometry.wing (F := E.Carrier) true).map unipotent.subtype).comap f⁆,
          ((CentralRootGeometry.wing (F := E.Carrier) true).map unipotent.subtype).comap f⁆=⊥ ∧
    let D := (((CentralRootGeometry.wing (F := E.Carrier) true).map unipotent.subtype).comap f).map
      (stabilizer d.radical a).subtype
    let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical (path.walk.getVert 1)) (Nat.card F^2)
    ∃ g ∈ Ltilde d.radical a, ∃ x ∈ Ltilde d.radical a,
      let J₁ := J.map (MulAut.conj g).toMonoidHom
      let J₂ := J₁.map (MulAut.conj x⁻¹).toMonoidHom
      (J₁ ⊔ Z d.radical z) ⊔ (Z d.radical z).map (MulAut.conj x).toMonoidHom =
        stabilizer d.radical a ∧
      (D.map (MulAut.conj g).toMonoidHom ⊔
        (D.map (MulAut.conj g).toMonoidHom).map (MulAut.conj x⁻¹).toMonoidHom =
          stabilizer d.radical a) ∧
      ((Z d.radical a ⊓ centralizer (J₁ : Set (FreeAmalgam d.radical))) ⊓
        centralizer (J₂ : Set (FreeAmalgam d.radical)) =
          Z d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) ∧
      x ∈ normalizer (D : Set (FreeAmalgam d.radical)) ∧
      x ∈ (planeParabolic.comap f).map (stabilizer d.radical a).subtype ∧
      ((Z d.radical a ⊓ centralizer (J : Set (FreeAmalgam d.radical))) ⊓
        centralizer (J₁ : Set (FreeAmalgam d.radical)) =
          Z d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) ∧
      ((Z d.radical a ⊓ centralizer (J : Set (FreeAmalgam d.radical))) ⊓
        centralizer (J₂ : Set (FreeAmalgam d.radical)) =
          Z d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) ∧
      ∃ u, ∃ r ∈ Ltilde d.radical a, ∃ k ∈ Ltilde d.radical a,
        (r=g⁻¹ ∧ k=x⁻¹ ∨ r=g⁻¹*x ∧ k=x) ∧
        act d.radical r (path.walk.getVert 2)=u ∧
        k ∈ normalizer (D : Set (FreeAmalgam d.radical)) ∧
        k ∈ (planeParabolic.comap f).map (stabilizer d.radical a).subtype ∧
        k ∈ normalizer ((Z d.radical a ⊓ Z d.radical (path.walk.getVert 2) :
          Subgroup (FreeAmalgam d.radical)) : Set _) ∧
        ∃ back : CriticalPath d.radical geometry u (path.walk.getVert 2),
          back.walk.getVert 1=act d.radical r (path.walk.getVert 1) ∧
          (∀ i ≤ path.walk.length-2, back.walk.getVert (i+2)=path.walk.getVert i) ∧
          back.walk.getVert 2=a ∧ back.walk.getVert 3=path.walk.getVert 1 ∧
          (Subgroup.SmallMover.join (U d.radical u) (Q d.radical u)
            (Q d.radical (back.walk.getVert 1)) (Nat.card F^2) ⊔ Z d.radical z) ⊔
              Z d.radical (act d.radical k z)=stabilizer d.radical a ∧
          (Subgroup.SmallMover.join (U d.radical (back.walk.getVert 2))
            (Q d.radical (back.walk.getVert 2)) (Q d.radical (back.walk.getVert 1)) (Nat.card F^2) =
            Subgroup.SmallMover.join (U d.radical u) (Q d.radical u)
              (Q d.radical (back.walk.getVert 1)) (Nat.card F^2)) ∧
          (centralizer (Subgroup.SmallMover.join (U d.radical u) (Q d.radical u)
            (Q d.radical (back.walk.getVert 1)) (Nat.card F^2) : Set (FreeAmalgam d.radical))).relIndex
              (U d.radical u) ≤ Nat.card F^2 ∧
          (Subgroup.SmallMover.join (U d.radical (path.walk.getVert 2))
            (Q d.radical (path.walk.getVert 2)) (Q d.radical (back.walk.getVert 3)) (Nat.card F^2) =
            Subgroup.SmallMover.join (U d.radical (back.walk.getVert 2))
              (Q d.radical (back.walk.getVert 2)) (Q d.radical (back.walk.getVert 3)) (Nat.card F^2)) ∧
          (centralizer (Subgroup.SmallMover.join (U d.radical (back.walk.getVert 2))
            (Q d.radical (back.walk.getVert 2)) (Q d.radical (back.walk.getVert 3)) (Nat.card F^2) :
              Set (FreeAmalgam d.radical))).relIndex (U d.radical (back.walk.getVert 2)) ≤ Nat.card F^2 ∧
          ((Z d.radical (back.walk.getVert 2) ⊓ centralizer
            (Subgroup.SmallMover.join (U d.radical u) (Q d.radical u)
              (Q d.radical (back.walk.getVert 1)) (Nat.card F^2) : Set (FreeAmalgam d.radical))) ⊓
              centralizer (Subgroup.SmallMover.join (U d.radical (path.walk.getVert 2))
                (Q d.radical (path.walk.getVert 2)) (Q d.radical (back.walk.getVert 3))
                (Nat.card F^2) : Set (FreeAmalgam d.radical)) =
            Z d.radical (back.walk.getVert 2) ⊓ centralizer
              (stabilizer d.radical (back.walk.getVert 2) : Set (FreeAmalgam d.radical))) ∧
          (¬ ⁅V d.radical a,Q d.radical a⁆ ≤ fixedCore d.radical a →
            (Q d.radical (path.walk.getVert 2)).relIndex (Z d.radical u)=Nat.card F ∧
              (Q d.radical u).relIndex (Z d.radical (path.walk.getVert 2))=Nat.card F) := by
  let t := path.walk.getVert 1
  let c := path.walk.getVert 2
  have hl : path.walk.length=4 := path.length_eq_b.trans hb
  have hat : Adjacent d.radical a t := by
    simpa only [SimpleGraph.Walk.getVert_zero] using (cosetGraph_adj d.radical _ _).mp
      (path.walk.adj_getVert_succ (by omega : 0<path.walk.length))
  have hct : Adjacent d.radical c t := adjacent_symm d.radical
    ((cosetGraph_adj d.radical _ _).mp (path.walk.adj_getVert_succ (by omega : 1<path.walk.length)))
  have hfirst : path.walk.getVert 1=t := rfl
  have hb4 : 4 ≤ geometry.b d.radical := by omega
  have hnormal : ¬ stabilizer d.radical a ≤ normalizer
      ((Z d.radical c ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _) := by
    intro hn
    have hidx := (neighbor_seed_join_index_le geometry (by omega) path.start_color hat hct).trans
      (h.replacement_root_neighbor_seed_index_le_cube d path hb4 hat hct hsmall)
    have hq : 1 < Nat.card F := Finite.one_lt_card
    have hBY := h.replacement_small_radius_le_B d geometry (by omega) path.start_color
      (Z d.radical c ⊔ Z d.radical a) (neighbor_seed_join_le_radius hat hct)
      ((Ltilde_le_stabilizer a).trans hn)
      (lt_of_le_of_lt hidx ((pow_lt_pow_iff_right₀ hq).mpr (by decide)))
    have hone := relIndex_eq_one.mpr (((U_le_Z c).trans le_sup_left).trans hBY)
    rw [hone] at hmove
    exact (not_lt_of_ge hq.le) hmove
  let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
    (Q d.radical t) (Nat.card F^2)
  obtain ⟨E,hE,f,hf,hfQ,hTf,hindex,hcore,hTP,hquad,hmax⟩ :=
    h.replacement_maximizing_parabolic d geometry hb4 path.start_color hat
  have hJP := h.replacement_small_mover_le_maximizing_plane_of_index_le d
    geometry hb4 path.start_color hat E hE f hfQ hTf hindex hmax hJm
  obtain ⟨g,hg,x,hx,hgen,hpair,hfixed,hxn,hxp,hO₁,hO₂⟩ :=
    h.replacement_smaller_mover_original_fixed_selection d path hb4 hat hfirst
      E hE f hf hfQ hTf hindex hJP
  let v := act d.radical g⁻¹ c
  let w := act d.radical g⁻¹ t
  let v' := act d.radical x v
  let w' := act d.radical x w
  let J₁ := Subgroup.SmallMover.join (U d.radical v) (Q d.radical v) (Q d.radical w) (Nat.card F^2)
  let J₂ := Subgroup.SmallMover.join (U d.radical v') (Q d.radical v') (Q d.radical w') (Nat.card F^2)
  have hgS := Ltilde_le_stabilizer a hg
  have hxS := Ltilde_le_stabilizer a hx
  have hga : act d.radical g⁻¹ a=a := (stabilizer d.radical a).inv_mem hgS
  have hxa : act d.radical x a=a := hxS
  have haw : Adjacent d.radical a w := by
    rw [←hga]
    exact (adjacent_act_iff _ _ _ _).mpr hat
  have hvw : Adjacent d.radical v w := (adjacent_act_iff _ _ _ _).mpr hct
  have haw' : Adjacent d.radical a w' := by
    rw [←hxa]
    exact (adjacent_act_iff _ _ _ _).mpr haw
  have hvw' : Adjacent d.radical v' w' := (adjacent_act_iff _ _ _ _).mpr hvw
  have hJ₁ : J₁=J.map (MulAut.conj g).toMonoidHom := by
    simpa only [J₁,v,w,mover_act,inv_inv] using
      congrArg (Subgroup.map (MulAut.conj g).toMonoidHom) hequal
  have hJ₂ : J₂=J₁.map (MulAut.conj x⁻¹).toMonoidHom := mover_act _ x v w
  have hgen₁ : (J₁ ⊔ Z d.radical z) ⊔ (Z d.radical z).map (MulAut.conj x).toMonoidHom =
      stabilizer d.radical a := by rwa [hJ₁]
  have hgen₂ : (J₂ ⊔ Z d.radical z) ⊔ (Z d.radical z).map (MulAut.conj x⁻¹).toMonoidHom =
      stabilizer d.radical a := by
    have hh := congrArg (Subgroup.map (MulAut.conj x⁻¹).toMonoidHom) hgen₁
    have hS : (stabilizer d.radical a).map (MulAut.conj x⁻¹).toMonoidHom=stabilizer d.radical a :=
      mem_normalizer_iff_map_conj_eq.mp ((stabilizer d.radical a).le_normalizer
        ((stabilizer d.radical a).inv_mem hxS))
    have hcomp : (MulAut.conj x⁻¹).toMonoidHom.comp (MulAut.conj x).toMonoidHom =
        MonoidHom.id (FreeAmalgam d.radical) := by
      apply MonoidHom.ext
      intro y
      change x⁻¹*(x*y*x⁻¹)*(x⁻¹)⁻¹=y
      group
    rw [Subgroup.map_sup,Subgroup.map_sup,Subgroup.map_map,hcomp,Subgroup.map_id,hS,←hJ₂] at hh
    rw [sup_assoc,sup_comm (Z d.radical z),←sup_assoc]
    exact hh
  have hfixed' : (Z d.radical a ⊓ centralizer (J₁ : Set (FreeAmalgam d.radical))) ⊓
      centralizer (J₂ : Set (FreeAmalgam d.radical)) =
      Z d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) := by
    rwa [hJ₂,hJ₁]
  have hO₁' : (Z d.radical a ⊓ centralizer (J : Set (FreeAmalgam d.radical))) ⊓
      centralizer (J₁ : Set (FreeAmalgam d.radical)) =
      Z d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) := by
    rwa [hJ₁]
  have hO₂' : (Z d.radical a ⊓ centralizer (J : Set (FreeAmalgam d.radical))) ⊓
      centralizer (J₂ : Set (FreeAmalgam d.radical)) =
      Z d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) := by
    rwa [hJ₂,hJ₁]
  have hi₁ := movingIndex_act geometry (d := c) (by omega) path.start_color g⁻¹
    ((stabilizer d.radical a).inv_mem hgS)
  have hi₂ := (movingIndex_act geometry (d := v) (by omega) path.start_color x hxS).trans hi₁
  have heq₁ : J₁=Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical w) (Nat.card F^2) := by
    have hh := congrArg (Subgroup.map (MulAut.conj (g⁻¹)⁻¹).toMonoidHom) hequal
    change (Subgroup.SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical t)
      (Nat.card F^2)).map _ = (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2)).map _ at hh
    rwa [←mover_act,←mover_act,hga] at hh
  have heq₂ : J₂=Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical w') (Nat.card F^2) := by
    have hh := congrArg (Subgroup.map (MulAut.conj x⁻¹).toMonoidHom) heq₁
    change (Subgroup.SmallMover.join (U d.radical v) (Q d.radical v) (Q d.radical w)
      (Nat.card F^2)).map _ = (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical w) (Nat.card F^2)).map _ at hh
    rwa [←mover_act,←mover_act,hxa] at hh
  have hjw : (centralizer (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical w) (Nat.card F^2) : Set (FreeAmalgam d.radical))).relIndex
        (U d.radical a) ≤ Nat.card F^2 := by
    have hh := own_index_act (Nat.card F^2) g⁻¹ a t
    rw [hga] at hh
    exact hh.trans_le hJm
  have hjw' : (centralizer (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical w') (Nat.card F^2) : Set (FreeAmalgam d.radical))).relIndex
        (U d.radical a) ≤ Nat.card F^2 := by
    have hh := own_index_act (Nat.card F^2) x a w
    rw [hxa] at hh
    exact hh.trans_le hjw
  have hcomm₁ := equal_root_kernel_displacement h d path hb4 haw hvw hsmall hjw heq₁
  have hcomm₂ := equal_root_kernel_displacement h d path hb4 haw' hvw' hsmall hjw' heq₂
  have hn : ¬ stabilizer d.radical a ≤ normalizer
      ((Z d.radical v ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _) := by
    intro hn
    have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hn
    rw [map_normalizer_eq_of_bijective _ (MulAut.conj g⁻¹).bijective,Subgroup.map_sup] at hh
    have hS : (stabilizer d.radical a).map (MulAut.conj g⁻¹).toMonoidHom=stabilizer d.radical a :=
      mem_normalizer_iff_map_conj_eq.mp ((stabilizer d.radical a).le_normalizer
        ((stabilizer d.radical a).inv_mem hgS))
    have hvc : act d.radical g v=c := by
      dsimp only [v]
      rw [←act_mul,inv_mul_cancel,act_one]
    have hga' : act d.radical g a=a := hgS
    rw [hS,←Z_act,←Z_act,hvc,hga'] at hh
    exact hnormal hh
  have hnot : ¬ (Z d.radical v ≤ Q d.radical (path.walk.getVert (path.walk.length-2)) ∧
      Z d.radical v' ≤ Q d.radical (path.walk.getVert (path.walk.length-2))) := by
    rintro ⟨ht₁,ht₂⟩
    by_cases hn₁ : Z d.radical z ≤ normalizer
        ((Z d.radical v ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _)
    · have hn₂ : ¬ Z d.radical z ≤ normalizer
          ((Z d.radical v' ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _) := by
        intro hn₂
        have hb' := paired_endpoint_normalizes_first_join x hxS hn₂
        apply hn
        rw [←hgen₁]
        refine sup_le (sup_le ((Subgroup.SmallMover.join_le _ _ _ _).trans
          (edge_normalizes_neighbor_seed_join haw hvw)) hn₁) ?_
        simpa only [Z_act,inv_inv] using hb'
      have hback : act d.radical x⁻¹ v'=v := by
        dsimp only [v']
        rw [←act_mul,mul_inv_cancel,act_one]
      exact trapped_pair_impossible h d path hb4 haw' hvw' haw hvw x⁻¹
        ((stabilizer d.radical a).inv_mem hxS) hback hcomm₂ hcomm₁
        ((inf_right_comm _ _ _).trans hfixed') hgen₂ (by rw [hi₂]; exact hmove) hn₂ ht₂ ht₁
    · exact trapped_pair_impossible h d path hb4 haw hvw haw' hvw' x hxS rfl
        hcomm₁ hcomm₂ hfixed' hgen₁ (by rw [hi₁]; exact hmove) hn₁ ht₁ ht₂
  have hxI := h.replacement_distance_four_equal_small_seed_intersection_normalized d geometry hb
    path.start_color hat hct hequal hmove hJm E hE f hf hfQ hindex hJP x hxS hxn
  refine ⟨E,hE,f,hf,hfQ,hTf,hindex,hJP,hquad,g,hg,x,hx,hgen,hpair,hfixed,hxn,hxp,hO₁,hO₂,?_⟩
  have complete (u w : Vertex d.radical) (r k : FreeAmalgam d.radical)
      (hr : r ∈ Ltilde d.radical a)
      (hrc : act d.radical r c=u) (hrt : act d.radical r t=w)
      (haw : Adjacent d.radical a w) (huw : Adjacent d.radical u w)
      (hgen : (Subgroup.SmallMover.join (U d.radical u) (Q d.radical u)
        (Q d.radical w) (Nat.card F^2) ⊔ Z d.radical z) ⊔
          Z d.radical (act d.radical k z)=stabilizer d.radical a)
      (hnot : ¬ Z d.radical u ≤ Q d.radical (path.walk.getVert (path.walk.length-2)))
      (hO : (Z d.radical a ⊓ centralizer (J : Set (FreeAmalgam d.radical))) ⊓
        centralizer (Subgroup.SmallMover.join (U d.radical u) (Q d.radical u)
          (Q d.radical w) (Nat.card F^2) : Set (FreeAmalgam d.radical)) =
        Z d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) :
      ∃ back : CriticalPath d.radical geometry u (path.walk.getVert 2),
        back.walk.getVert 1=w ∧
        (∀ i ≤ path.walk.length-2, back.walk.getVert (i+2)=path.walk.getVert i) ∧
        back.walk.getVert 2=a ∧ back.walk.getVert 3=t ∧
        (Subgroup.SmallMover.join (U d.radical u) (Q d.radical u)
          (Q d.radical (back.walk.getVert 1)) (Nat.card F^2) ⊔ Z d.radical z) ⊔
            Z d.radical (act d.radical k z)=stabilizer d.radical a ∧
        (Subgroup.SmallMover.join (U d.radical (back.walk.getVert 2))
          (Q d.radical (back.walk.getVert 2)) (Q d.radical (back.walk.getVert 1)) (Nat.card F^2) =
          Subgroup.SmallMover.join (U d.radical u) (Q d.radical u)
            (Q d.radical (back.walk.getVert 1)) (Nat.card F^2)) ∧
        (centralizer (Subgroup.SmallMover.join (U d.radical u) (Q d.radical u)
          (Q d.radical (back.walk.getVert 1)) (Nat.card F^2) : Set (FreeAmalgam d.radical))).relIndex
            (U d.radical u) ≤ Nat.card F^2 ∧
        (Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
          (Q d.radical (back.walk.getVert 3)) (Nat.card F^2) =
          Subgroup.SmallMover.join (U d.radical (back.walk.getVert 2))
            (Q d.radical (back.walk.getVert 2)) (Q d.radical (back.walk.getVert 3)) (Nat.card F^2)) ∧
        (centralizer (Subgroup.SmallMover.join (U d.radical (back.walk.getVert 2))
          (Q d.radical (back.walk.getVert 2)) (Q d.radical (back.walk.getVert 3)) (Nat.card F^2) :
            Set (FreeAmalgam d.radical))).relIndex (U d.radical (back.walk.getVert 2)) ≤ Nat.card F^2 ∧
        ((Z d.radical (back.walk.getVert 2) ⊓ centralizer
          (Subgroup.SmallMover.join (U d.radical u) (Q d.radical u)
            (Q d.radical (back.walk.getVert 1)) (Nat.card F^2) : Set (FreeAmalgam d.radical))) ⊓
            centralizer (Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
              (Q d.radical (back.walk.getVert 3)) (Nat.card F^2) : Set (FreeAmalgam d.radical)) =
          Z d.radical (back.walk.getVert 2) ⊓ centralizer
            (stabilizer d.radical (back.walk.getVert 2) : Set (FreeAmalgam d.radical))) ∧
        (¬ ⁅V d.radical a,Q d.radical a⁆ ≤ fixedCore d.radical a →
          (Q d.radical c).relIndex (Z d.radical u)=Nat.card F ∧
            (Q d.radical u).relIndex (Z d.radical c)=Nat.card F) := by
    have hlen : path.walk.length-2=2 := by omega
    obtain ⟨back,hback,hover⟩ :
        ∃ back : CriticalPath d.radical geometry u (path.walk.getVert 2),
          back.walk.getVert 1=w ∧
          ∀ i ≤ path.walk.length-2, back.walk.getVert (i+2)=path.walk.getVert i := by
      have hh := exists_backward_path_of_not_le geometry (by omega) path haw huw hnot
      have he : path.walk.getVert (path.walk.length-2)=path.walk.getVert 2 := congrArg _ hlen
      rw [he] at hh
      exact hh
    have hmid : back.walk.getVert 2=a := by
      simpa only [SimpleGraph.Walk.getVert_zero] using hover 0 (by omega)
    have hlast : back.walk.getVert 3=t := hover 1 (by omega)
    have hra : act d.radical r a=a := Ltilde_le_stabilizer a hr
    have he : Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical (back.walk.getVert 1)) (Nat.card F^2) =
      Subgroup.SmallMover.join (U d.radical u) (Q d.radical u)
        (Q d.radical (back.walk.getVert 1)) (Nat.card F^2) := by
      have hh := congrArg (Subgroup.map (MulAut.conj r⁻¹).toMonoidHom) hequal
      rw [←mover_act,←mover_act,hra,hrc,hrt] at hh
      simpa only [hback] using hh.symm
    have hi : (centralizer (Subgroup.SmallMover.join (U d.radical u) (Q d.radical u)
        (Q d.radical (back.walk.getVert 1)) (Nat.card F^2) : Set (FreeAmalgam d.radical))).relIndex
          (U d.radical u) ≤ Nat.card F^2 := by
      rw [hback,←hrc,←hrt,own_index_act,own_index_neighbors _ hat hct]
      exact hJm
    refine ⟨back,hback,hover,hmid,hlast,?_,?_,hi,?_,?_,?_,?_⟩
    · simpa only [hback] using hgen
    · simpa only [hmid] using he
    · simpa only [hmid,hlast] using hequal
    · simpa only [hmid,hlast] using hJm
    · rw [hmid,hback,hlast,hequal,inf_right_comm]
      exact hO
    · intro hn
      apply h.replacement_distance_four_equal_small_nonfixed_backward_root d path hb
        r (Ltilde_le_stabilizer a hr) hrc hrt hequal hJm _ back hn
      exact hO
  by_cases ht₁ : Z d.radical v ≤ Q d.radical (path.walk.getVert (path.walk.length-2))
  · let r := g⁻¹*x
    have hr : r ∈ Ltilde d.radical a :=
      (Ltilde d.radical a).mul_mem ((Ltilde d.radical a).inv_mem hg) hx
    have hrc : act d.radical r c=v' := by dsimp only [r,v']; rw [act_mul]
    have hrt : act d.radical r t=w' := by dsimp only [r,w']; rw [act_mul]
    have hg' : (J₂ ⊔ Z d.radical z) ⊔ Z d.radical (act d.radical x z)=stabilizer d.radical a := by
      simpa only [Z_act] using hgen₂
    obtain ⟨back,hback,hrest⟩ := complete v' w' r x hr
      hrc hrt haw' hvw' hg' (fun ht₂ => hnot ⟨ht₁,ht₂⟩) hO₂'
    exact ⟨v',r,hr,x,hx,Or.inr ⟨rfl,rfl⟩,hrc,hxn,hxp,hxI,back,hback.trans hrt.symm,hrest⟩
  · have hk := (Ltilde d.radical a).inv_mem hx
    have hkN := (normalizer _).inv_mem hxn
    have hkP := ((planeParabolic.comap f).map (stabilizer d.radical a).subtype).inv_mem hxp
    have hkI := (normalizer _).inv_mem hxI
    have hg' : (J₁ ⊔ Z d.radical z) ⊔ Z d.radical (act d.radical x⁻¹ z)=stabilizer d.radical a := by
      simpa only [Z_act,inv_inv] using hgen₁
    obtain ⟨back,hback,hrest⟩ := complete v w g⁻¹ x⁻¹ ((Ltilde d.radical a).inv_mem hg)
      rfl rfl haw hvw hg' ht₁ hO₁'
    exact ⟨v,g⁻¹,(Ltilde d.radical a).inv_mem hg,x⁻¹,hk,Or.inl ⟨rfl,rfl⟩,rfl,
      hkN,hkP,hkI,back,hback,hrest⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
