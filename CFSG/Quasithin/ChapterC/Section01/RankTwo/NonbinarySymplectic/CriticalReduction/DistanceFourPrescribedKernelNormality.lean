module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourPrescribedFarGeneration
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourFullKernelNormality

/-!
# Full kernel normalization by the same prescribed far root pair

Transport the original equality of neighboring movers through both actual
selectors. This identifies the far vertex mover with the own far-edge mover
in the prescribed generation theorem. The original and k-translated paths
then normalize the same full kernel join under both unchanged full endpoints.
No kernel or fixed attachment is removed.
Source: MS93 (5.12)(3), printed p.927.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource CentralRootGeometry.SmallMovers

private theorem prescribed_mover_transport {M : Type*} [Group M] [Finite M]
    (R : Subgroup M) (q : ℕ) (y : FreeAmalgam R) (v w : Vertex R) :
    Subgroup.SmallMover.join (U R (act R y v)) (Q R (act R y v))
      (Q R (act R y w)) q =
      (Subgroup.SmallMover.join (U R v) (Q R v) (Q R w) q).map
        (MulAut.conj y⁻¹).toMonoidHom := by
  rw [U_act,Q_act,Q_act,←Subgroup.SmallMover.join_map _ (MulAut.conj y⁻¹).injective]

variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

private theorem prescribed_pair_full_kernel_normalized
    {geometry : Geometry d.radical} {a z v u s : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (back : CriticalPath d.radical geometry v (path.walk.getVert 2))
    (hmid : back.walk.getVert 2=a)
    (k : FreeAmalgam d.radical) (hk : k ∈ stabilizer d.radical a)
    (companion : CriticalPath d.radical geometry v (act d.radical k (path.walk.getVert 2)))
    (hcmid : companion.walk.getVert 2=a)
    (hvs : Adjacent d.radical v s) (hus : Adjacent d.radical u s)
    (y : FreeAmalgam d.radical) (hy : y ∈ stabilizer d.radical v)
    (hya : act d.radical y a=u)
    (hfixed : ⁅V d.radical a,Q d.radical a⁆ ≤ fixedCore d.radical a)
    (next : CriticalPath d.radical geometry u a) (hfirst : next.walk.getVert 1=s)
    (hJ : Subgroup.SmallMover.join (U d.radical u) (Q d.radical u)
        (Q d.radical s) (Nat.card F^2) =
      Subgroup.SmallMover.join (U d.radical v) (Q d.radical v)
        (Q d.radical s) (Nat.card F^2))
    (hgen : (Subgroup.SmallMover.join (U d.radical v) (Q d.radical v)
      (Q d.radical s) (Nat.card F^2) ⊔ Z d.radical (path.walk.getVert 2)) ⊔
        Z d.radical (act d.radical k (path.walk.getVert 2))=stabilizer d.radical v) :
    stabilizer d.radical v ≤ normalizer
      (((Z d.radical u ⊓ Q d.radical a) ⊔ Z d.radical v :
        Subgroup (FreeAmalgam d.radical)) : Set _) := by
  have hfirsttwo := h.replacement_distance_four_fixed_full_kernel_normalized d path hb
    back hmid hvs hus y hy hya hfixed next hfirst
  rw [hJ] at hfirsttwo
  have hka : act d.radical k a=a := hk
  let p₀ := path.act k
  let p : CriticalPath d.radical geometry a (act d.radical k z) := {
    start_color := path.start_color
    walk := p₀.walk.copy hka rfl
    shortest := by
      rw [SimpleGraph.Walk.length_copy]
      exact p₀.shortest.trans (congrArg
        (fun b => (cosetGraph d.radical).dist b (act d.radical k z)) hka)
    critical := by simpa only [hka] using p₀.critical }
  have hp : p.walk.getVert 2=act d.radical k (path.walk.getVert 2) := by
    change (p₀.walk.copy hka rfl).getVert 2=_
    rw [SimpleGraph.Walk.getVert_copy]
    exact actWalk_getVert d.radical k path.walk 2
  let cb : CriticalPath d.radical geometry v (p.walk.getVert 2) := {
    start_color := companion.start_color
    walk := companion.walk.copy rfl hp.symm
    shortest := by rw [SimpleGraph.Walk.length_copy,hp]; exact companion.shortest
    critical := by simpa only [hp] using companion.critical }
  have hcb : cb.walk.getVert 2=a := by
    change (companion.walk.copy rfl hp.symm).getVert 2=a
    rwa [SimpleGraph.Walk.getVert_copy]
  have hsecond := h.replacement_distance_four_full_fixed_kernel_normalized d p hb cb hcb
    hvs hus y hy hya hfixed
  rw [hp] at hsecond
  rw [←hgen]
  exact sup_le hfirsttwo hsecond

/-- The complete original prescribed configuration now supplies full kernel
normalization by the whole selected stabilizer, with every actor retained. -/
theorem Input.replacement_distance_four_prescribed_far_kernel_normality
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
                          (Subgroup.SmallMover.join (U d.radical a') (Q d.radical a')
                            (Q d.radical s) (Nat.card F^2) =
                            Subgroup.SmallMover.join (U d.radical v) (Q d.radical v)
                              (Q d.radical s) (Nat.card F^2)) ∧
                          (stabilizer d.radical v ≤ normalizer
                            (((Z d.radical a' ⊓ Q d.radical a) ⊔ Z d.radical v :
                              Subgroup (FreeAmalgam d.radical)) : Set _)) ∧
                          ∃ farther : CriticalPath d.radical geometry a' (back.walk.getVert 2),
                            farther.walk.getVert 1=s ∧
                            ∀ i ≤ back.walk.length-2, farther.walk.getVert (i+2)=back.walk.getVert i) := by
  have hcfg :=
    h.replacement_distance_four_prescribed_far_generation d path hb hfixed hmove hequal hJm
  rcases hcfg with ⟨B,hB,f,hf,hfQ,hTf,hindex,g,hcfg⟩
  rcases hcfg with ⟨hg,x,hx,hat1,hct1,hat2,hct2,hgen1,hcfg⟩
  rcases hcfg with ⟨hgen2,hfix,hmove1,hmove2,hxn,hxp,v,hv,hcfg⟩
  rcases hcfg with ⟨w,hwhich,haw,hvw,hn,back,hfirst,hover,hcfg⟩
  rcases hcfg with ⟨r,hr,k,hk,hrv,horiented,hgen,hnot,hcfg⟩
  rcases hcfg with ⟨companion,hcfirst,hcover,hcrit,hcrit',hE₁,hE₂,hc₁,hcfg⟩
  rcases hcfg with ⟨hi₁,hi₂,hne,E,hE,fv,hfv,hfvQ,hcfg⟩
  rcases hcfg with ⟨hTv,hiv,s₁,s₂,hst,hs₁,hs₂,hsp,hcfg⟩
  rcases hcfg with ⟨hpair,hlarge,hmid,C,hC,ff,hff,hffQ,hcfg⟩
  rcases hcfg with ⟨hffT,hffidx,hJD,hE₁D,hE₂D,gf,hgf,xf,hcfg⟩
  rcases hcfg with ⟨hxf,cf,hgenf,hpairf,hfixf,hxnf,hxpf,hpresf1,hcfg⟩
  rcases hcfg with ⟨hpresf2,hDc,hDgc,hEc,hExc,rf,hrf,cf',hcfg⟩
  rcases hcfg with ⟨hchoice,hvs,hus,hnf,hgenfar,hDpos,hDrpos,hE₁pos,hcfg⟩
  rcases hcfg with ⟨hE₂pos,farther,hfarfirst,hfarcover⟩
  have hra : act d.radical r a=a := Ltilde_le_stabilizer a hr
  have hrw : act d.radical r (path.walk.getVert 1)=w := by
    rcases horiented with ⟨_,hw',hr',_⟩ | ⟨_,hw',hr',_⟩
    · rw [hr',hw']
    · rw [hr',hw',act_mul]
  have hJvw : Subgroup.SmallMover.join (U d.radical v) (Q d.radical v)
      (Q d.radical w) (Nat.card F^2) =
    Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical w) (Nat.card F^2) := by
    have hh := congrArg (Subgroup.map (MulAut.conj r⁻¹).toMonoidHom) hequal
    rw [←prescribed_mover_transport,←prescribed_mover_transport,hrv,hrw,hra] at hh
    exact hh
  have hrfv : act d.radical rf v=v := Ltilde_le_stabilizer v hrf
  have hJfar : Subgroup.SmallMover.join
      (U d.radical (act d.radical rf (back.walk.getVert 2)))
      (Q d.radical (act d.radical rf (back.walk.getVert 2)))
      (Q d.radical (act d.radical rf w)) (Nat.card F^2) =
    Subgroup.SmallMover.join (U d.radical v) (Q d.radical v)
      (Q d.radical (act d.radical rf w)) (Nat.card F^2) := by
    have hh := congrArg (Subgroup.map (MulAut.conj rf⁻¹).toMonoidHom) hJvw.symm
    rw [←prescribed_mover_transport,←prescribed_mover_transport,hrfv] at hh
    simpa only [hmid] using hh
  have hka : act d.radical k a=a := Ltilde_le_stabilizer a hk
  have hcmid : companion.walk.getVert 2=a := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero,hka] using hcover 0 (by decide)
  have hnorm : stabilizer d.radical v ≤ normalizer
      (((Z d.radical (act d.radical rf (back.walk.getVert 2)) ⊓ Q d.radical a) ⊔ Z d.radical v :
        Subgroup (FreeAmalgam d.radical)) : Set _) := by
    let next : CriticalPath d.radical geometry
        (act d.radical rf (back.walk.getVert 2)) a := {
      start_color := farther.start_color
      walk := farther.walk.copy rfl hmid
      shortest := by rw [SimpleGraph.Walk.length_copy]; simpa only [hmid] using farther.shortest
      critical := by simpa only [hmid] using farther.critical }
    have hnfirst : next.walk.getVert 1=act d.radical rf w := by
      change (farther.walk.copy rfl hmid).getVert 1=_
      rwa [SimpleGraph.Walk.getVert_copy]
    exact prescribed_pair_full_kernel_normalized h d path hb back hmid k
      (Ltilde_le_stabilizer a hk) companion hcmid hvs hus rf
      (Ltilde_le_stabilizer v hrf) (by rw [hmid]) hfixed next hnfirst hJfar hgenfar
  exact ⟨B,hB,f,hf,hfQ,hTf,hindex,g,hg,x,hx,hat1,hct1,hat2,hct2,
    hgen1,hgen2,hfix,hmove1,hmove2,hxn,hxp,v,hv,w,hwhich,haw,hvw,hn,back,hfirst,hover,
    r,hr,k,hk,hrv,horiented,hgen,hnot,companion,hcfirst,hcover,hcrit,hcrit',hE₁,hE₂,
    hc₁,hi₁,hi₂,hne,E,hE,fv,hfv,hfvQ,hTv,hiv,s₁,s₂,hst,hs₁,hs₂,hsp,hpair,hlarge,hmid,
    C,hC,ff,hff,hffQ,hffT,hffidx,hJD,hE₁D,hE₂D,gf,hgf,xf,hxf,cf,
    hgenf,hpairf,hfixf,hxnf,hxpf,hpresf1,hpresf2,hDc,hDgc,hEc,hExc,
    rf,hrf,cf',hchoice,hvs,hus,hnf,hgenfar,hDpos,hDrpos,hE₁pos,hE₂pos,
    hJfar,hnorm,farther,hfarfirst,hfarcover⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
