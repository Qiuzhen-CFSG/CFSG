module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.PointRootPaths
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.EqualRootPaths

/-!
# Simultaneous backward selection for every critical-root configuration

Split on the original small-mover fixed index and then on equality of the two
neighboring movers. The full point branch uses its individual generator; the
unequal branch uses the already constructed individual residual generator;
the equal branch uses the same two three-generator identities. Their trapped
cases have all been excluded before the branches are assembled here.

The output keeps the actual selectors, both B-relative indices, individual
smaller movers and full-Z fixed clauses together with the backward path. The
paired case retains its original field and quotient marking and full kernel.
No mover equality, small fixed index or preselected configuration is an input.
Source: MS93 (5.5)--(5.7), pp.915--919, the field-sized critical-image case.
The large contained-image branch and the terminal distance bound remain open.
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
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The critical-root branch of (5.7), with all mover cases discharged.
Single generators and paired generators retain their different source
fixed clauses at the same actual choices used by the backward path. -/
theorem Input.replacement_root_backward_selection
    {geometry : Geometry d.radical} {a z t c : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hat : Adjacent d.radical a t) (hfirst : path.walk.getVert 1 = t)
    (hct : Adjacent d.radical c t)
    (hmove : Nat.card F < (B d.radical a (geometry.Z_normal a)).relIndex (U d.radical c))
    (hsmall : (Q d.radical a).relIndex (Z d.radical z) < Nat.card F^2) :
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
  by_cases hJm : (centralizer (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2) : Set (FreeAmalgam d.radical))).relIndex
        (U d.radical a) ≤ Nat.card F^2
  · by_cases hequal : Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
        (Q d.radical t) (Nat.card F^2) =
      Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical t) (Nat.card F^2)
    · obtain ⟨E,hE,f,hf,hfQ,hTf,hidx,g,hg,x,hx,ha₁,hc₁,ha₂,hc₂,hi₁,hi₂,
        hcenter₁,hcenter₂,hcomm₁,hcomm₂,hcenters,hinter,hgen₁,hgen₂,hfixed,
        hmove₁,hmove₂,hxn,hxp,hback⟩ :=
        h.replacement_equal_root_backward_path d path hb hat hfirst hct hmove hequal hsmall hJm
      exact ⟨g,hg,x,hx,ha₁,hc₁,ha₂,hc₂,hi₁,hi₂,
        Or.inr ⟨E,hE,f,hf,hfQ,hTf,hidx,hgen₁,hgen₂,hfixed,hxn,hxp⟩,hback⟩
    · obtain ⟨g,hg,haw,hvw,hidx,htransport,hgen,hres,hfixed,hindividual,
        hquadA,hquadC,hcube,hnot,hlarge,hn,hback⟩ :=
        h.replacement_unequal_root_backward_path d path hb hat hfirst hct hsmall hmove hequal
      refine ⟨g,hg,1,(Ltilde d.radical a).one_mem,?_⟩
      dsimp only
      simp only [act_one]
      refine ⟨haw,hvw,haw,hvw,hidx,hidx,Or.inl ⟨True.intro,hres,?_,Or.inl hindividual⟩,?_⟩
      · rwa [htransport] at hgen
      · exact ⟨act d.radical g⁻¹ c,by simp,act d.radical g⁻¹ t,
          Or.inl ⟨rfl,rfl⟩,haw,hvw,hback⟩
  · obtain ⟨g,hg,haw,hvw,hidx,htransport,hgen,hfixed,hn,hback⟩ :=
      h.replacement_large_movement_root_backward_path d path hb hat hfirst hct hmove hsmall
        (lt_of_not_ge hJm)
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
        Or.inl ⟨rfl,rfl⟩,haw,hvw,hback⟩

/-- The geometric consumer of the complete root selector retains the
original neighbor orbit, B-relative moving index and every path overlap.
The stronger selection theorem above supplies its same-choice generation
and fixed-subgroup certificates. -/
theorem Input.replacement_root_backward_step
    {geometry : Geometry d.radical} {a z t c : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hat : Adjacent d.radical a t) (hfirst : path.walk.getVert 1 = t)
    (hct : Adjacent d.radical c t)
    (hmove : Nat.card F < (B d.radical a (geometry.Z_normal a)).relIndex (U d.radical c))
    (hsmall : (Q d.radical a).relIndex (Z d.radical z) < Nat.card F^2) :
    ∃ y ∈ Ltilde d.radical a,
      let v := act d.radical y c
      let w := act d.radical y t
      Adjacent d.radical a w ∧ Adjacent d.radical v w ∧
      (B d.radical a (geometry.Z_normal a)).relIndex (U d.radical v) =
        (B d.radical a (geometry.Z_normal a)).relIndex (U d.radical c) ∧
      ∃ back : CriticalPath d.radical geometry v (path.walk.getVert (path.walk.length-2)),
        back.walk.getVert 1 = w ∧
        ∀ i ≤ path.walk.length-2, back.walk.getVert (i+2) = path.walk.getVert i := by
  obtain ⟨g,hg,x,hx,ha₁,hc₁,ha₂,hc₂,hi₁,hi₂,hsource,v,hv,w,hvw,haw,hvw',hback⟩ :=
    h.replacement_root_backward_selection d path hb hat hfirst hct hmove hsmall
  rcases hvw with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact ⟨g⁻¹,(Ltilde d.radical a).inv_mem hg,haw,hvw',hi₁,hback⟩
  · refine ⟨g⁻¹*x,(Ltilde d.radical a).mul_mem ((Ltilde d.radical a).inv_mem hg) hx,?_⟩
    dsimp only
    rw [act_mul,act_mul]
    exact ⟨haw,hvw',hi₂,hback⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
