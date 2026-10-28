module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourPrescribedKernelNormality
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourNormalizedKernelBudget

/-!
# Exact seed indices from the original prescribed far configuration

The same original selectors r and rFar and both original full endpoint actors
now give the normalized full kernel in B_v, the reciprocal full seed indices
B_v(Z_a)=B_e(Z_a)=q, and the full span and residual images modulo Q_a of size
at most q. All earlier configurations and marked planes are retained.
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

/-- Exact full seed indices and original full span and residual images,
with the entire unchanged prescribed far configuration retained. -/
theorem Input.replacement_distance_four_prescribed_far_seed_indices
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
                          ((Z d.radical a' ⊓ Q d.radical a) ⊔ Z d.radical v ≤
                            BinaryMS.MS93.B d.radical v (geometry.Z_normal v)) ∧
                          ((BinaryMS.MS93.B d.radical v (geometry.Z_normal v)).relIndex (Z d.radical a') ≤ Nat.card F) ∧
                          ((BinaryMS.MS93.B d.radical v (geometry.Z_normal v)).relIndex (Z d.radical a)=Nat.card F) ∧
                          ((BinaryMS.MS93.B d.radical (path.walk.getVert 2) (geometry.Z_normal _)).relIndex
                            (Z d.radical a)=Nat.card F) ∧
                          ((BinaryMS.MS93.B d.radical v (geometry.Z_normal v)).relIndex (U d.radical a)=Nat.card F) ∧
                          ((Q d.radical a).relIndex (localZSpan d.radical a v) ≤ Nat.card F) ∧
                          ((Q d.radical a).relIndex ⁅Q d.radical v,Ltilde d.radical v⁆ ≤ Nat.card F) ∧
                          ∃ farther : CriticalPath d.radical geometry a' (back.walk.getVert 2),
                            farther.walk.getVert 1=s ∧
                            ∀ i ≤ back.walk.length-2, farther.walk.getVert (i+2)=back.walk.getVert i) := by
  have hcfg :=
    h.replacement_distance_four_prescribed_far_kernel_normality d path hb hfixed hmove hequal hJm
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
  rcases hcfg with ⟨hE₂pos,hJfar,hnorm,farther,hfarfirst,hfarcover⟩
  let next : CriticalPath d.radical geometry
      (act d.radical rf (back.walk.getVert 2)) a := {
    start_color := farther.start_color
    walk := farther.walk.copy rfl hmid
    shortest := by rw [SimpleGraph.Walk.length_copy]; simpa only [hmid] using farther.shortest
    critical := by simpa only [hmid] using farther.critical }
  have hrS := Ltilde_le_stabilizer v hrf
  have hract : act d.radical rf a=act d.radical rf (back.walk.getVert 2) := by rw [hmid]
  have hLN := (Ltilde_le_stabilizer v).trans hnorm
  obtain ⟨hYB,hfarB,_,_⟩ :=
    h.replacement_distance_four_normalized_full_kernel_seed_budget d back hb path.start_color
      hfixed hvs hus rf hrS hract next hLN
  obtain ⟨hZa,hUa,hW⟩ :=
    h.replacement_distance_four_normalized_full_kernel_midpoint_indices d back hb hmid
      path.start_color hfixed hvs hus rf hrS hract next hLN
  have hZe := (h.replacement_distance_four_normalized_full_kernel_paired_indices d back hb hmid
    path.start_color hfixed hvs hus rf hrS hract next hLN r (Ltilde_le_stabilizer a hr) hrv).2
  have hQ₀ := h.replacement_distance_four_normalized_full_kernel_residual_image d back hb hmid
    path.start_color hfixed hvs hus rf hrS hract next hLN
  exact ⟨B,hB,f,hf,hfQ,hTf,hindex,g,hg,x,hx,hat1,hct1,hat2,hct2,
    hgen1,hgen2,hfix,hmove1,hmove2,hxn,hxp,v,hv,w,hwhich,haw,hvw,hn,back,hfirst,hover,
    r,hr,k,hk,hrv,horiented,hgen,hnot,companion,hcfirst,hcover,hcrit,hcrit',hE₁,hE₂,
    hc₁,hi₁,hi₂,hne,E,hE,fv,hfv,hfvQ,hTv,hiv,s₁,s₂,hst,hs₁,hs₂,hsp,hpair,hlarge,hmid,
    C,hC,ff,hff,hffQ,hffT,hffidx,hJD,hE₁D,hE₂D,gf,hgf,xf,hxf,cf,
    hgenf,hpairf,hfixf,hxnf,hxpf,hpresf1,hpresf2,hDc,hDgc,hEc,hExc,
    rf,hrf,cf',hchoice,hvs,hus,hnf,hgenfar,hDpos,hDrpos,hE₁pos,hE₂pos,
    hJfar,hnorm,hYB,hfarB,hZa,hZe,hUa,hW,hQ₀,farther,hfarfirst,hfarcover⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
