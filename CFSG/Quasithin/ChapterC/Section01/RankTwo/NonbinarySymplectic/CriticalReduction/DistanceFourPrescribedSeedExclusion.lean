module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourPrescribedSeedIndices
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourPrescribedSpanFixed
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.PrescribedChiefCentralization

/-!
# The original prescribed strict seed branch is impossible

The same far selector normalizes the full kernel join and gives the actual
midpoint seed index q. Both original endpoint actors fix the full span kernel
modulo Z_v. Their joined fixed-preimage index is at most q, while their retained
elementary image has order q². The chief-factor bound forces the full span
into B_v, contrary to the original critical path's moving-index lower bound.
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

/-- The concrete prescribed configuration contradicts the chief-factor
movement bound for its two unchanged full endpoint actors. -/
theorem Input.replacement_distance_four_prescribed_strict_seed_false
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
        (U d.radical a) ≤ Nat.card F^2) : False := by
  have hcfg :=
    h.replacement_distance_four_prescribed_far_seed_indices d path hb hfixed hmove hequal hJm
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
  rcases hcfg with ⟨hE₂pos,hJfar,hnorm,hYB,hfarB,hZa,hZe,hUa,hcfg⟩
  rcases hcfg with ⟨hW,hQ₀,farther,hfarfirst,hfarcover⟩
  have hka : act d.radical k a=a := Ltilde_le_stabilizer a hk
  have hcmid : companion.walk.getVert 2=a := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero,hka] using hcover 0 (by decide)
  have hidx := (h.replacement_distance_four_prescribed_span_pair_fixed_index d back hb hmid
    r k (Ltilde_le_stabilizer a hr) (Ltilde_le_stabilizer a hk) hrv companion hcmid
    hfixed (by rw [hUa])).2.2
  have hES₁ := back.endpoint_Z_le_start_stabilizer (by omega : 0 < geometry.b d.radical)
  have hES₂ := companion.endpoint_Z_le_start_stabilizer (by omega : 0 < geometry.b d.radical)
  let A := Z d.radical (path.walk.getVert 2) ⊔ Z d.radical (act d.radical k (path.walk.getVert 2))
  have hAS : A ≤ stabilizer d.radical v := sup_le hES₁ hES₂
  have hAf : (A.subgroupOf (stabilizer d.radical v)).map fv=rootImage s₁ ⊔ rootImage s₂ := by
    rw [show A=Z d.radical (path.walk.getVert 2) ⊔
      Z d.radical (act d.radical k (path.walk.getVert 2)) from rfl,
      subgroupOf_sup hES₁ hES₂,Subgroup.map_sup,hs₁,hs₂]
  have hEA : IsElementaryAbelian 2 ((A.subgroupOf (stabilizer d.radical v)).map fv) := by
    rw [hAf]
    let := CentralRootGeometry.wing_elementary (F := E.Carrier) true
    let : IsElementaryAbelian 2 ((CentralRootGeometry.wing (F := E.Carrier) true).map
        unipotent.subtype) := IsElementaryAbelian.map unipotent.subtype
    have hh : rootImage s₁ ⊔ rootImage s₂ ≤
        (CentralRootGeometry.wing (F := E.Carrier) true).map unipotent.subtype :=
      sup_le (map_mono (rootFamily_le_wing s₁)) (map_mono (rootFamily_le_wing s₂))
    exact IsElementaryAbelian.of_injective (inclusion hh) (inclusion_injective hh)
  exact h.replacement_critical_span_prescribed_fixed_index_false d back hb A hAS E hE fv
    hfv hfvQ hEA hpair.ge (by simpa only [hmid] using hidx)

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
