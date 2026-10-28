module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourCommonEdgeRootActors
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourRootPairCoordinates

/-!
# The actual prescribed root pair excludes a square-order mover

The complete equal/small selector and both genuine backward paths are retained.
Their two full endpoint actors lie in the same actual edge. One natural
quotient marking at the selected vertex identifies both with distinct full
roots, and their literal joined image has order q². The original root-product
exclusion then forces the complete smaller-mover image above q².
No product containment, common-edge positioning, or root marking is supplied
as an additional premise. The larger-image continuation remains separate.
Source: MS93 (5.12)(3), printed p.927.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource CentralRootGeometry.SmallMovers
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The actual prescribed configuration supplies a marked full root pair
and rules out a square-order smaller-mover image at the selected vertex. -/
theorem Input.replacement_distance_four_prescribed_root_pair
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
                        (Q d.radical w) (Nat.card F^2)) := by
  obtain ⟨E,hE,f,hf,hfQ,hTf,hindex,g,hg,x,hx,hat1,hct1,hat2,hct2,
      hgen1,hgen2,hfix,hmove1,hmove2,hxn,hxp,v,hv,w,hwhich,haw,hvw,hn,back,hfirst,hover,
      r,hr,k,hk,hrv,horiented,hgen,hnot,companion,hcfirst,hcover,hcrit,hcrit',hE₁,hE₂,
      hc₁,hi₁,hi₂,hne⟩ :=
    h.replacement_distance_four_prescribed_common_edge_root_actors d path hb hfixed hmove hequal hJm
  refine ⟨E,hE,f,hf,hfQ,hTf,hindex,g,hg,x,hx,hat1,hct1,hat2,hct2,
    hgen1,hgen2,hfix,hmove1,hmove2,hxn,hxp,v,hv,w,hwhich,haw,hvw,hn,back,hfirst,hover,
    r,hr,k,hk,hrv,horiented,hgen,hnot,companion,hcfirst,hcover,hcrit,hcrit',hE₁,hE₂,
    hc₁,hi₁,hi₂,hne,?_⟩
  exact h.replacement_distinct_root_actor_coordinates d geometry (by omega) back.start_color hvw
    (Z d.radical (path.walk.getVert 2)) (Z d.radical (act d.radical k (path.walk.getVert 2)))
    hE₁ hE₂ hc₁ hcrit' hi₁ hi₂ hne

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
