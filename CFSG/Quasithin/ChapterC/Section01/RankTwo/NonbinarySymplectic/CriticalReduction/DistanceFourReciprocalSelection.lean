module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourReciprocalInitial
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourEqualSmallCriticalFixed
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourEqualSmallSeedIntersection
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourCoherentComparison

/-!
# The complete second selector of a reciprocal initial path

Construct the original-fixed selector at the new start, retaining its natural
marking and both members. The reciprocal midpoint fixed identity makes the
actual first critical commutator fixed at the old start. Hence the escaping
member of this exact second pair is untrapped and gives an actual second path.
All three generating actors and the orientation of the selected twist remain.
The strict new B-index is used only conditionally to normalize its seed
intersection; it is not inferred from the old strict B-index.

The private import intentionally reuses the frozen nontrapping calculation.
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

/-- Complete the second actual selector from the reciprocal certificates
of the newly constructed initial path, retaining its original fixed identity. -/
theorem Input.replacement_distance_four_reciprocal_selection
    {geometry : Geometry d.radical} {e f₀ a : Vertex d.radical}
    (old : CriticalPath d.radical geometry e f₀)
    (path : CriticalPath d.radical geometry a (old.walk.getVert 2))
    (hb : geometry.b d.radical=4)
    (hmid : path.walk.getVert 2=e) (hlast : path.walk.getVert 3=old.walk.getVert 1)
    (hequal : Subgroup.SmallMover.join (U d.radical (path.walk.getVert 2))
        (Q d.radical (path.walk.getVert 2)) (Q d.radical (path.walk.getVert 1)) (Nat.card F^2) =
      Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical (path.walk.getVert 1)) (Nat.card F^2))
    (hsmall : (Q d.radical a).relIndex (Z d.radical (old.walk.getVert 2)) < Nat.card F^2)
    (hJm : (centralizer (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical (path.walk.getVert 1)) (Nat.card F^2) : Set (FreeAmalgam d.radical))).relIndex
        (U d.radical a) ≤ Nat.card F^2)
    (hfixe : (Z d.radical e ⊓ centralizer
        (Subgroup.SmallMover.join (U d.radical e) (Q d.radical e)
          (Q d.radical (old.walk.getVert 1)) (Nat.card F^2) : Set (FreeAmalgam d.radical))) ⊓
        centralizer (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
          (Q d.radical (path.walk.getVert 1)) (Nat.card F^2) : Set (FreeAmalgam d.radical)) =
      Z d.radical e ⊓ centralizer (stabilizer d.radical e : Set (FreeAmalgam d.radical))) :
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
      (J₁ ⊔ Z d.radical (old.walk.getVert 2)) ⊔ (Z d.radical (old.walk.getVert 2)).map (MulAut.conj x).toMonoidHom =
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
        (Nat.card F < (B d.radical a (geometry.Z_normal a)).relIndex
          (U d.radical (path.walk.getVert 2)) →
          k ∈ normalizer ((Z d.radical a ⊓ Z d.radical (path.walk.getVert 2) :
            Subgroup (FreeAmalgam d.radical)) : Set _)) ∧
        ∃ next : CriticalPath d.radical geometry u (path.walk.getVert 2),
          next.walk.getVert 1=act d.radical r (path.walk.getVert 1) ∧
          (∀ i ≤ path.walk.length-2, next.walk.getVert (i+2)=path.walk.getVert i) ∧
          Adjacent d.radical a (next.walk.getVert 1) ∧
          Adjacent d.radical u (next.walk.getVert 1) ∧
          (¬ Z d.radical (old.walk.getVert 2) ≤ normalizer
            ((Z d.radical u ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _)) ∧
          (Subgroup.SmallMover.join (U d.radical u) (Q d.radical u)
            (Q d.radical (next.walk.getVert 1)) (Nat.card F^2) ⊔ Z d.radical (old.walk.getVert 2)) ⊔
              Z d.radical (act d.radical k (old.walk.getVert 2))=stabilizer d.radical a ∧
          ((Z d.radical a ⊓ centralizer
            (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
              (Q d.radical (path.walk.getVert 1)) (Nat.card F^2) : Set (FreeAmalgam d.radical))) ⊓
              centralizer (Subgroup.SmallMover.join (U d.radical u) (Q d.radical u)
                (Q d.radical (next.walk.getVert 1)) (Nat.card F^2) : Set (FreeAmalgam d.radical)) =
            Z d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) ∧
          (¬ ⁅V d.radical a,Q d.radical a⁆ ≤ fixedCore d.radical a →
            (Q d.radical (path.walk.getVert 2)).relIndex (Z d.radical u)=Nat.card F ∧
              (Q d.radical u).relIndex (Z d.radical (path.walk.getVert 2))=Nat.card F) := by
  let z := old.walk.getVert 2
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
      ((Z d.radical c ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _) :=
    h.replacement_path_neighbor_join_not_normal_of_four_le d path hb4
  have hCa : ⁅Z d.radical a,Z d.radical z⁆ ≤
      centralizer (stabilizer d.radical e : Set (FreeAmalgam d.radical)) := by
    have hOroot := h.replacement_distance_four_root_original_fixed d old hb path hmid hlast hsmall
    have hSroot := h.replacement_root_critical_commutator_fixed_by_first_mover d path hb4 hsmall
    exact ((le_inf hOroot hSroot).trans_eq hfixe).trans inf_le_right
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
  let S := stabilizer d.radical a
  let D := (((CentralRootGeometry.wing (F := E.Carrier) true).map unipotent.subtype).comap f).map S.subtype
  have hJS : J ≤ S := (Subgroup.SmallMover.join_le _ _ _ _).trans
    (fun _ hx => hx.2 a (adjacent_symm d.radical hat))
  have hJD : J ≤ D := by
    have hh := map_mono (f := S.subtype) hJP
    rwa [map_subgroupOf_eq_of_le hJS] at hh
  have hDq : ⁅⁅U d.radical a,D⁆,D⁆ = ⊥ := by
    have hh := congrArg (Subgroup.map S.subtype) hquad
    rwa [map_commutator,map_commutator,
      map_subgroupOf_eq_of_le ((U_le_Z a).trans (Z_le_stabilizer d.radical a)),Subgroup.map_bot] at hh
  have hJq : ⁅⁅U d.radical a,J⁆,J⁆ = ⊥ := le_bot_iff.mp
    ((commutator_mono (commutator_mono le_rfl hJD) hJD).trans_eq hDq)
  have hJc : Nat.card F < (Q d.radical a).relIndex J := by
    have hi := h.replacement_small_mover_join_index d geometry hb4 path.start_color hat
    have hq : 1 < Nat.card F := Finite.one_lt_card
    have hlt : Nat.card F < Nat.card F^2 := by nlinarith
    exact hlt.trans_le hi
  have transport (E : Subgroup (FreeAmalgam d.radical))
      (hES : E ≤ S) (hEc : Nat.card F < (Q d.radical a).relIndex E)
      (hEq : ⁅⁅U d.radical a,E⁆,E⁆ = ⊥)
      (y : FreeAmalgam d.radical) (hy : y ∈ S) :
      E.map (MulAut.conj y).toMonoidHom ≤ S ∧
      Nat.card F < (Q d.radical a).relIndex (E.map (MulAut.conj y).toMonoidHom) ∧
      ⁅⁅U d.radical a,E.map (MulAut.conj y).toMonoidHom⁆,
        E.map (MulAut.conj y).toMonoidHom⁆ = ⊥ := by
    have hS : S.map (MulAut.conj y).toMonoidHom = S :=
      mem_normalizer_iff_map_conj_eq.mp (S.le_normalizer hy)
    have hU : (U d.radical a).map (MulAut.conj y).toMonoidHom = U d.radical a :=
      mem_normalizer_iff_map_conj_eq.mp (U_normalized a hy)
    have hQ : (Q d.radical a).map (MulAut.conj y).toMonoidHom = Q d.radical a :=
      mem_normalizer_iff_map_conj_eq.mp (Q_normalized d.radical a hy)
    refine ⟨hS ▸ map_mono hES,?_,?_⟩
    · conv_rhs => rw [←hQ]
      rwa [relIndex_map_map_of_injective _ _ (MulAut.conj y).injective]
    · have hh := congrArg (Subgroup.map (MulAut.conj y).toMonoidHom) hEq
      rwa [map_commutator,map_commutator,hU,Subgroup.map_bot] at hh
  obtain ⟨hJ₁S,hJ₁c,hJ₁q⟩ := transport J hJS hJc hJq g hgS
  obtain ⟨hJ₂S,hJ₂c,hJ₂q⟩ := transport _ hJ₁S hJ₁c hJ₁q x⁻¹ (S.inv_mem hxS)
  have hmove₁ : ¬ ⁅Z d.radical z,U d.radical a⁆ ≤ centralizer
      (J₁ : Set (FreeAmalgam d.radical)) := by
    rw [hJ₁]
    exact h.replacement_generated_root_not_centralized d path hb4 hsmall
      _ hJ₁S hJ₁c hJ₁q x hxS hgen
  have hmove₂ : ¬ ⁅Z d.radical z,U d.radical a⁆ ≤ centralizer
      (J₂ : Set (FreeAmalgam d.radical)) := by
    rw [hJ₂,hJ₁]
    apply h.replacement_generated_root_not_centralized d path hb4 hsmall
      _ hJ₂S hJ₂c hJ₂q x⁻¹ ((stabilizer d.radical a).inv_mem hxS)
    simpa only [hJ₂,hJ₁] using hgen₂
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
  refine ⟨E,hE,f,hf,hfQ,hTf,hindex,hJP,hquad,g,hg,x,hx,hgen,hpair,hfixed,hxn,hxp,hO₁,hO₂,?_⟩
  have complete (u w : Vertex d.radical) (r k : FreeAmalgam d.radical)
      (hr : r ∈ Ltilde d.radical a) (hk : k ∈ Ltilde d.radical a)
      (hrc : act d.radical r c=u) (hrt : act d.radical r t=w)
      (haw : Adjacent d.radical a w) (huw : Adjacent d.radical u w)
      (hkn : k ∈ normalizer (D : Set (FreeAmalgam d.radical)))
      (hn : ¬ Z d.radical z ≤ normalizer
        ((Z d.radical u ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _))
      (hmove : ¬ ⁅Z d.radical z,U d.radical a⁆ ≤ centralizer
        (Subgroup.SmallMover.join (U d.radical u) (Q d.radical u)
          (Q d.radical w) (Nat.card F^2) : Set (FreeAmalgam d.radical)))
      (hgen : (Subgroup.SmallMover.join (U d.radical u) (Q d.radical u)
        (Q d.radical w) (Nat.card F^2) ⊔ Z d.radical z) ⊔
          Z d.radical (act d.radical k z)=stabilizer d.radical a)
      (hO : (Z d.radical a ⊓ centralizer (J : Set (FreeAmalgam d.radical))) ⊓
        centralizer (Subgroup.SmallMover.join (U d.radical u) (Q d.radical u)
          (Q d.radical w) (Nat.card F^2) : Set (FreeAmalgam d.radical)) =
        Z d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) :
      (Nat.card F < (B d.radical a (geometry.Z_normal a)).relIndex (U d.radical c) →
        k ∈ normalizer ((Z d.radical a ⊓ Z d.radical c : Subgroup (FreeAmalgam d.radical)) : Set _)) ∧
      ∃ next : CriticalPath d.radical geometry u (path.walk.getVert 2),
        next.walk.getVert 1=w ∧
        (∀ i ≤ path.walk.length-2, next.walk.getVert (i+2)=path.walk.getVert i) ∧
        Adjacent d.radical a (next.walk.getVert 1) ∧ Adjacent d.radical u (next.walk.getVert 1) ∧
        (¬ Z d.radical z ≤ normalizer
          ((Z d.radical u ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _)) ∧
        (Subgroup.SmallMover.join (U d.radical u) (Q d.radical u)
          (Q d.radical (next.walk.getVert 1)) (Nat.card F^2) ⊔ Z d.radical z) ⊔
            Z d.radical (act d.radical k z)=stabilizer d.radical a ∧
        ((Z d.radical a ⊓ centralizer (J : Set (FreeAmalgam d.radical))) ⊓
          centralizer (Subgroup.SmallMover.join (U d.radical u) (Q d.radical u)
            (Q d.radical (next.walk.getVert 1)) (Nat.card F^2) : Set (FreeAmalgam d.radical)) =
          Z d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) ∧
        (¬ ⁅V d.radical a,Q d.radical a⁆ ≤ fixedCore d.radical a →
          (Q d.radical c).relIndex (Z d.radical u)=Nat.card F ∧
            (Q d.radical u).relIndex (Z d.radical c)=Nat.card F) := by
    constructor
    · intro hstrict
      exact h.replacement_distance_four_equal_small_seed_intersection_normalized d geometry hb
        path.start_color hat hct hequal hstrict hJm E hE f hf hfQ hindex hJP
        k (Ltilde_le_stabilizer a hk) hkn
    have hnot := second_selector_not_trapped h d old hb path haw huw r
      (Ltilde_le_stabilizer a hr) (by simpa only [c,hmid] using hrc) hn hCa hmove
    have hlen : path.walk.length-2=2 := by omega
    obtain ⟨next,hnext,hover⟩ :
        ∃ next : CriticalPath d.radical geometry u (path.walk.getVert 2),
          next.walk.getVert 1=w ∧
          ∀ i ≤ path.walk.length-2, next.walk.getVert (i+2)=path.walk.getVert i := by
      have hh := exists_backward_path_of_not_le geometry (by omega) path haw huw hnot
      have he : path.walk.getVert (path.walk.length-2)=path.walk.getVert 2 := congrArg _ hlen
      rw [he] at hh
      exact hh
    refine ⟨next,hnext,hover,?_,?_,hn,?_,?_,?_⟩
    · simpa only [hnext] using haw
    · simpa only [hnext] using huw
    · simpa only [hnext] using hgen
    · simpa only [hnext] using hO
    · intro hnotfixed
      exact h.replacement_distance_four_equal_small_nonfixed_backward_root d path hb
        r (Ltilde_le_stabilizer a hr) hrc hrt hequal hJm hO next hnotfixed
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
    let r := g⁻¹*x
    have hr : r ∈ Ltilde d.radical a :=
      (Ltilde d.radical a).mul_mem ((Ltilde d.radical a).inv_mem hg) hx
    have hrc : act d.radical r c=v' := by dsimp only [r,v']; rw [act_mul]
    have hrt : act d.radical r t=w' := by dsimp only [r,w']; rw [act_mul]
    have hg' : (J₂ ⊔ Z d.radical z) ⊔ Z d.radical (act d.radical x z)=stabilizer d.radical a := by
      simpa only [Z_act] using hgen₂
    obtain ⟨hkI,next,hnext,hrest⟩ := complete v' w' r x hr hx
      hrc hrt haw' hvw' hxn hn₂ hmove₂ hg' hO₂'
    exact ⟨v',r,hr,x,hx,Or.inr ⟨rfl,rfl⟩,hrc,hxn,hxp,hkI,next,hnext.trans hrt.symm,hrest⟩
  · have hk := (Ltilde d.radical a).inv_mem hx
    have hkN := (normalizer _).inv_mem hxn
    have hkP := ((planeParabolic.comap f).map (stabilizer d.radical a).subtype).inv_mem hxp
    have hg' : (J₁ ⊔ Z d.radical z) ⊔ Z d.radical (act d.radical x⁻¹ z)=stabilizer d.radical a := by
      simpa only [Z_act,inv_inv] using hgen₁
    obtain ⟨hkI,next,hnext,hrest⟩ := complete v w g⁻¹ x⁻¹ ((Ltilde d.radical a).inv_mem hg) hk
      rfl rfl haw hvw hkN hn₁ hmove₁ hg' hO₁'
    exact ⟨v,g⁻¹,(Ltilde d.radical a).inv_mem hg,x⁻¹,hk,Or.inl ⟨rfl,rfl⟩,rfl,
      hkN,hkP,hkI,next,hnext,hrest⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
