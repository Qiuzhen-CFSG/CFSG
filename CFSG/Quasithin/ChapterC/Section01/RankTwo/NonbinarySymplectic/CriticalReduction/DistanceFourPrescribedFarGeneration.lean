module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourPrescribedRootPair
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.PrescribedFarSelector
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourEqualRootComparison
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourNormalSpans

/-!
# The retained distance-four root pair generates with its actual far mover

The complete prescribed configuration remains unchanged. Its own mover index
is transported using the actual residual selector and the common initial
edge, then the far-selector construction uses both retained full endpoints.
The original marking, backward and companion paths, and directed kernel
noncontainment are retained along with the selected opposite-plane positions.

Source: MS93 (5.12)(3), printed p.927, using (5.6)(a), printed p.917.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource CentralRootGeometry.SmallMovers

private theorem prescribed_own_index_transport {M : Type*} [Group M] [Finite M]
    {R : Subgroup M} (q : ℕ) {a e t v w : Vertex R}
    (hat : Adjacent R a t) (het : Adjacent R e t)
    (hsmall : (centralizer (Subgroup.SmallMover.join (U R a) (Q R a)
      (Q R t) q : Set (FreeAmalgam R))).relIndex (U R a) ≤ q)
    (r : FreeAmalgam R) (hrv : act R r e=v) (hrw : act R r t=w) :
    (centralizer (Subgroup.SmallMover.join (U R v) (Q R v)
      (Q R w) q : Set (FreeAmalgam R))).relIndex (U R v) ≤ q := by
  rw [←hrv,←hrw,own_index_act,own_index_neighbors q hat het]
  exact hsmall

variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The original prescribed pair, directed kernels and markings survive the
actual far-selector construction; both unchanged full endpoints generate. -/
theorem Input.replacement_distance_four_prescribed_far_generation
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (hfixed : ⁅V d.radical a,Q d.radical a⁆ ≤ fixedCore d.radical a)
    (hmove : Nat.card F < (B d.radical a (geometry.Z_normal a)).relIndex
      (U d.radical (path.walk.getVert 2)))
    (hequal : Subgroup.SmallMover.join (U d.radical (path.walk.getVert 2)) (Q d.radical (path.walk.getVert 2))
        (Q d.radical (path.walk.getVert 1)) (Nat.card F^2) =
      Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical (path.walk.getVert 1)) (Nat.card F^2))
    (hJm : (centralizer (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical (path.walk.getVert 1)) (Nat.card F^2) : Set (FreeAmalgam d.radical))).relIndex
        (U d.radical a) ≤ Nat.card F^2) :
    ∃ B : BinaryField, B.degree = n ∧
      ∃ f : stabilizer d.radical a →* Sp B.Carrier,
        Function.Surjective f ∧ f.ker.map (stabilizer d.radical a).subtype = Q d.radical a ∧
        ((Q d.radical (path.walk.getVert 1)).subgroupOf (stabilizer d.radical a)).map f ≤ unipotent ∧
        (∀ A : Subgroup (stabilizer d.radical a),
          (centralizer (A : Set (stabilizer d.radical a))).relIndex
            ((U d.radical a).subgroupOf (stabilizer d.radical a)) =
            2 ^ BinaryOffender.fixedCodim (restrictScalars (k := ZMod 2)
              (symplecticNatural (k := B.Carrier) 2)) (A.map f)) ∧
    ∃ g ∈ Ltilde d.radical a, ∃ x ∈ Ltilde d.radical a,
      let t₁ := act d.radical g⁻¹ (path.walk.getVert 1)
      let c₁ := act d.radical g⁻¹ (path.walk.getVert 2)
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
        ∃ back : CriticalPath d.radical geometry v (path.walk.getVert 2),
          back.walk.getVert 1 = w ∧
          (∀ i ≤ path.walk.length-2, back.walk.getVert (i+2) = path.walk.getVert i) ∧
          ∃ r ∈ Ltilde d.radical a, ∃ k ∈ Ltilde d.radical a,
            act d.radical r (path.walk.getVert 2)=v ∧
            ((v=c₁ ∧ w=t₁ ∧ r=g⁻¹ ∧ k=x⁻¹) ∨
              (v=c₂ ∧ w=t₂ ∧ r=g⁻¹*x ∧ k=x)) ∧
            ((Subgroup.SmallMover.join (U d.radical v) (Q d.radical v)
              (Q d.radical w) (Nat.card F^2) ⊔ Z d.radical z) ⊔
                Z d.radical (act d.radical k z)=stabilizer d.radical a) ∧
            (¬ Z d.radical v ⊓ Q d.radical (path.walk.getVert 2) ≤
              Z d.radical v ⊓ Q d.radical (act d.radical k (path.walk.getVert 2))) ∧
            ∃ companion : CriticalPath d.radical geometry v
                (act d.radical k (path.walk.getVert 2)),
              companion.walk.getVert 1=w ∧
              (∀ i≤2, companion.walk.getVert (i+2)=act d.radical k (path.walk.getVert i)) ∧
              (Q d.radical (act d.radical k (path.walk.getVert 2))).relIndex (Z d.radical v)=Nat.card F ∧
              (Q d.radical v).relIndex
                (Z d.radical (act d.radical k (path.walk.getVert 2)))=Nat.card F ∧
              Z d.radical (path.walk.getVert 2)≤Q d.radical w ∧
              Z d.radical (act d.radical k (path.walk.getVert 2))≤Q d.radical w ∧
              (Q d.radical v).relIndex (Z d.radical (path.walk.getVert 2))=Nat.card F ∧
              (centralizer (Z d.radical (path.walk.getVert 2) : Set (FreeAmalgam d.radical))).relIndex
                (U d.radical v)=Nat.card F ∧
              (centralizer (Z d.radical (act d.radical k (path.walk.getVert 2)) : Set (FreeAmalgam d.radical))).relIndex
                (U d.radical v)=Nat.card F ∧
              Z d.radical v ⊓ centralizer (Z d.radical (path.walk.getVert 2) : Set (FreeAmalgam d.radical)) ≠
                Z d.radical v ⊓ centralizer
                  (Z d.radical (act d.radical k (path.walk.getVert 2)) : Set (FreeAmalgam d.radical)) ∧
              ∃ E : BinaryField, E.degree=n ∧
                ∃ fv : stabilizer d.radical v →* Sp E.Carrier,
                  Function.Surjective fv ∧ fv.ker.map (stabilizer d.radical v).subtype=Q d.radical v ∧
                  ((Q d.radical w).subgroupOf (stabilizer d.radical v)).map fv ≤ unipotent ∧
                  (∀ A : Subgroup (stabilizer d.radical v),
                    (centralizer (A : Set (stabilizer d.radical v))).relIndex
                      ((U d.radical v).subgroupOf (stabilizer d.radical v)) =
                        2 ^ BinaryOffender.fixedCodim (restrictScalars (k := ZMod 2)
                          (symplecticNatural (k := E.Carrier) 2)) (A.map fv)) ∧
                  ∃ s₁ s₂ : Option E.Carrier, s₁ ≠ s₂ ∧
                    ((Z d.radical (path.walk.getVert 2)).subgroupOf (stabilizer d.radical v)).map fv=rootImage s₁ ∧
                    ((Z d.radical (act d.radical k (path.walk.getVert 2))).subgroupOf
                      (stabilizer d.radical v)).map fv=rootImage s₂ ∧
                    Nat.card (rootImage s₁ ⊔ rootImage s₂ : Subgroup (Sp E.Carrier))=Nat.card F^2 ∧
                    (Q d.radical v).relIndex (Z d.radical (path.walk.getVert 2) ⊔
                      Z d.radical (act d.radical k (path.walk.getVert 2)))=Nat.card F^2 ∧
                    Nat.card F^2 < (Q d.radical v).relIndex
                      (Subgroup.SmallMover.join (U d.radical v) (Q d.radical v)
                        (Q d.radical w) (Nat.card F^2)) ∧
                    back.walk.getVert 2=a ∧
                    (
                      ∃ C : BinaryField, C.degree=n ∧
                        ∃ fFar : stabilizer d.radical v →* Sp C.Carrier,
                          Function.Surjective fFar ∧ fFar.ker.map (stabilizer d.radical v).subtype=Q d.radical v ∧
                          ((Q d.radical w).subgroupOf (stabilizer d.radical v)).map fFar ≤ unipotent ∧
                          (∀ A : Subgroup (stabilizer d.radical v),
                            (centralizer (A : Set (stabilizer d.radical v))).relIndex
                              ((U d.radical v).subgroupOf (stabilizer d.radical v)) =
                              2 ^ BinaryOffender.fixedCodim (restrictScalars (k := ZMod 2)
                                (symplecticNatural (k := C.Carrier) 2)) (A.map fFar)) ∧
                      let P := (CentralRootGeometry.wing (F := C.Carrier) true).map unipotent.subtype
                      let D := (P.comap fFar).map (stabilizer d.radical v).subtype
                      let J := Subgroup.SmallMover.join (U d.radical v) (Q d.radical v)
                        (Q d.radical w) (Nat.card F^2)
                      J ≤ D ∧ Z d.radical (path.walk.getVert 2) ≤ D ∧ Z d.radical (act d.radical k (path.walk.getVert 2)) ≤ D ∧
                      ∃ gFar ∈ Ltilde d.radical v, ∃ xFar ∈ Ltilde d.radical v, ∃ cFar : Sp C.Carrier,
                        ((J.map (MulAut.conj gFar).toMonoidHom ⊔ Z d.radical (path.walk.getVert 2)) ⊔
                          (Z d.radical (path.walk.getVert 2)).map (MulAut.conj xFar).toMonoidHom = stabilizer d.radical v) ∧
                        (D.map (MulAut.conj gFar).toMonoidHom ⊔
                          (D.map (MulAut.conj gFar).toMonoidHom).map (MulAut.conj xFar⁻¹).toMonoidHom = stabilizer d.radical v) ∧
                        ((Z d.radical v ⊓ centralizer (J.map (MulAut.conj gFar).toMonoidHom : Set (FreeAmalgam d.radical))) ⊓
                          centralizer ((J.map (MulAut.conj gFar).toMonoidHom).map
                            (MulAut.conj xFar⁻¹).toMonoidHom : Set (FreeAmalgam d.radical)) =
                            Z d.radical v ⊓ centralizer (stabilizer d.radical v : Set (FreeAmalgam d.radical))) ∧
                        xFar ∈ normalizer (D : Set (FreeAmalgam d.radical)) ∧
                        xFar ∈ (planeParabolic.comap fFar).map (stabilizer d.radical v).subtype ∧
                        ((J.map (MulAut.conj gFar).toMonoidHom ⊔ Z d.radical (path.walk.getVert 2)) ⊔ Z d.radical (act d.radical k (path.walk.getVert 2)) =
                          stabilizer d.radical v) ∧
                        (((J.map (MulAut.conj gFar).toMonoidHom).map (MulAut.conj xFar⁻¹).toMonoidHom ⊔
                          Z d.radical (path.walk.getVert 2)) ⊔ Z d.radical (act d.radical k (path.walk.getVert 2)) = stabilizer d.radical v) ∧
                        (((D.subgroupOf (stabilizer d.radical v)).map fFar).map (MulAut.conj cFar).toMonoidHom =
                          P.map (MulAut.conj (TwoConjugate.opposition (F := C.Carrier))).toMonoidHom) ∧
                        ((((D.map (MulAut.conj gFar).toMonoidHom).subgroupOf (stabilizer d.radical v)).map fFar).map
                          (MulAut.conj cFar).toMonoidHom = P) ∧
                        ((((Z d.radical (path.walk.getVert 2)).subgroupOf (stabilizer d.radical v)).map fFar).map
                          (MulAut.conj cFar).toMonoidHom = RootSubgroup.group 1) ∧
                        (((((Z d.radical (path.walk.getVert 2)).map (MulAut.conj xFar).toMonoidHom).subgroupOf
                          (stabilizer d.radical v)).map fFar).map (MulAut.conj cFar).toMonoidHom = RootSubgroup.group 3) ∧
                        ∃ rFar ∈ Ltilde d.radical v, ∃ cFar' : Sp C.Carrier,
                          ((rFar=gFar⁻¹ ∧ cFar'=cFar) ∨ ∃ xsFar : stabilizer d.radical v,
                            xsFar.val=xFar ∧ rFar=gFar⁻¹*xFar ∧ cFar'=cFar*fFar xsFar) ∧
                          let a' := act d.radical rFar (back.walk.getVert 2)
                          let s := act d.radical rFar w
                          Adjacent d.radical v s ∧ Adjacent d.radical a' s ∧
                          (¬ Z d.radical (path.walk.getVert 2) ≤ normalizer
                            ((Z d.radical a' ⊔ Z d.radical v : Subgroup (FreeAmalgam d.radical)) : Set _)) ∧
                          ((Subgroup.SmallMover.join (U d.radical v) (Q d.radical v)
                            (Q d.radical s) (Nat.card F^2) ⊔ Z d.radical (path.walk.getVert 2)) ⊔ Z d.radical (act d.radical k (path.walk.getVert 2)) = stabilizer d.radical v) ∧
                          (((D.subgroupOf (stabilizer d.radical v)).map fFar).map (MulAut.conj cFar').toMonoidHom =
                            P.map (MulAut.conj (TwoConjugate.opposition (F := C.Carrier))).toMonoidHom) ∧
                          ((((D.map (MulAut.conj rFar⁻¹).toMonoidHom).subgroupOf (stabilizer d.radical v)).map fFar).map
                            (MulAut.conj cFar').toMonoidHom = P) ∧
                          ((((Z d.radical (path.walk.getVert 2)).subgroupOf (stabilizer d.radical v)).map fFar).map
                            (MulAut.conj cFar').toMonoidHom ≤ P.map
                              (MulAut.conj (TwoConjugate.opposition (F := C.Carrier))).toMonoidHom) ∧
                          ((((Z d.radical (act d.radical k (path.walk.getVert 2))).subgroupOf (stabilizer d.radical v)).map fFar).map
                            (MulAut.conj cFar').toMonoidHom ≤ P.map
                              (MulAut.conj (TwoConjugate.opposition (F := C.Carrier))).toMonoidHom) ∧
                          ∃ farther : CriticalPath d.radical geometry a' (back.walk.getVert 2),
                            farther.walk.getVert 1=s ∧
                            ∀ i ≤ back.walk.length-2, farther.walk.getVert (i+2)=back.walk.getVert i) := by
  obtain ⟨B,hB,f,hf,hfQ,hTf,hindex,g,hg,x,hx,hat1,hct1,hat2,hct2,
      hgen1,hgen2,hfix,hmove1,hmove2,hxn,hxp,v,hv,w,hwhich,haw,hvw,hn,back,hfirst,hover,
      r,hr,k,hk,hrv,horiented,hgen,hnot,companion,hcfirst,hcover,hcrit,hcrit',hE₁,hE₂,
      hc₁,hi₁,hi₂,hne,E,hE,fv,hfv,hfvQ,hTv,hiv,s₁,s₂,hst,hs₁,hs₂,hsp,hpair,hlarge⟩ :=
    h.replacement_distance_four_prescribed_root_pair d path hb hfixed hmove hequal hJm
  have hmid : back.walk.getVert 2=a := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using hover 0 (Nat.zero_le _)
  refine ⟨B,hB,f,hf,hfQ,hTf,hindex,g,hg,x,hx,hat1,hct1,hat2,hct2,
    hgen1,hgen2,hfix,hmove1,hmove2,hxn,hxp,v,hv,w,hwhich,haw,hvw,hn,back,hfirst,hover,
    r,hr,k,hk,hrv,horiented,hgen,hnot,companion,hcfirst,hcover,hcrit,hcrit',hE₁,hE₂,
    hc₁,hi₁,hi₂,hne,E,hE,fv,hfv,hfvQ,hTv,hiv,s₁,s₂,hst,hs₁,hs₂,hsp,hpair,hlarge,hmid,?_⟩
  have hl : path.walk.length=4 := path.length_eq_b.trans hb
  have hat : Adjacent d.radical a (path.walk.getVert 1) := by
    simpa only [SimpleGraph.Walk.getVert_zero] using (cosetGraph_adj d.radical _ _).mp
      (path.walk.adj_getVert_succ (by omega : 0<path.walk.length))
  have het : Adjacent d.radical (path.walk.getVert 2) (path.walk.getVert 1) :=
    adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (path.walk.adj_getVert_succ (by omega : 1<path.walk.length)))
  have hrw : act d.radical r (path.walk.getVert 1)=w := by
    rcases horiented with ⟨_,hw',hr',_⟩ | ⟨_,hw',hr',_⟩
    · rw [hr',hw']
    · rw [hr',hw',act_mul]
  have hown := prescribed_own_index_transport (Nat.card F^2) hat het hJm r hrv hrw
  have hfixedv := radius_fixed_at d path.start_color back.start_color hfixed
  exact h.replacement_prescribed_far_selector d back companion hb hfirst hcfirst
    hfixedv hown hlarge hne

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
