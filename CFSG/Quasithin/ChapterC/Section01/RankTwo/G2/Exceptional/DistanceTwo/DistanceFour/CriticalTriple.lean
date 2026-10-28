module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.G2.Exceptional.DistanceTwo.DistanceFour.LongRootAuxiliary
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.G2.Exceptional.DistanceTwo.DistanceFour.MovingSeedCover
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.G2.Exceptional.DistanceTwo.DistanceFour.NonfixedEdge

/-!
Adapted from the checked Chapter15 MarkedMS.G2Reconstruction proof to the
exceptional MS2(b) input. Only the two-group and core-containment consequences
of MS2 are used; the original SmallMSPair interface is unchanged.

# The last critical-triple contradiction of MS93 (3.8)

Simultaneous alignment preserves the critical offender and puts the first
edge image in the unipotent group. Its displacements on the offender-fixed
three-space are highest-long-root displacements on trace-zero octonions.
The original moving-seed cover transfers this equality to the literal
amalgam, placing the whole critical triple in the common auxiliary, which
is fixed at the same midpoint. Splitting the midpoint seed into its moving
part and edge center, and lifting fixation through its trace-zero cover,
then makes every displacement vanish. This discharges the final callback.

Source: Meierfrankenfeld–Stellmacher, *Pushing up weak BN-pairs of rank two*,
(3.8), printed p.879 / PDF p.56. The private import unfolds only the existing
NonfixedCriticalEdgeInput contract for final assembly. The model retains
LICENSES/ATLAS.txt attribution.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.G2Exceptional.Reconstruction.DistanceTwo.DistanceFour
open ChapterC BinaryMS.MS93 Comparison Comparison.CriticalImage
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
local notation "T" => R.subgroupOf (L ⊔ R)
variable (h : Pair KnownSimple.IsKnownSimple L R)
  (e : (L ⧸ pCore 2 L) ≃* commutator (Atlas.G2.Model (ZMod 2)))

open Atlas.G2 in
/-- The aligned unipotent displacement is a long-root displacement already
on trace-zero octonions, before passing to the natural quotient. -/
theorem traceZero_displacement (E B : Subgroup (Model (ZMod 2)))
    (g : Model (ZMod 2))
    (hE : E = (EvenTwoRank.elementary (ZMod 2)).map (MulAut.conj g).toMonoidHom)
    (hB : B ≤ unipotent.map (MulAut.conj g).toMonoidHom)
    (b : Model (ZMod 2)) (hb : b ∈ B) (v : Natural.TraceZero (ZMod 2))
    (hv : Restricted.NaturalCoordinates.projection (ZMod 2) v ∈ fixedSpace rho E) :
    ∃ w : Natural.TraceZero (ZMod 2),
      Natural.traceZeroAction (ZMod 2) b v-v =
        Natural.traceZeroAction (ZMod 2) (MulAut.conj g (rootA 1)) w-w := by
  let τ := Natural.traceZeroAction (ZMod 2)
  let p := Restricted.NaturalCoordinates.projection (ZMod 2)
  have he (a : Model (ZMod 2)) (x : Natural.TraceZero (ZMod 2)) :
      p (τ a x) = rho a (p x) :=
    (Restricted.NaturalCoordinates.repEquiv (ZMod 2)).isIntertwining a (Natural.mk (ZMod 2) x)
  let v' := τ g⁻¹ v
  have hv' : p v' ∈ fixedSpace rho (EvenTwoRank.elementary (ZMod 2)) := by
    intro a
    have ha : MulAut.conj g a.val ∈ E := by
      rw [hE]
      exact mem_map_of_mem (MulAut.conj g).toMonoidHom a.property
    have hh := congrArg (rho g⁻¹) (hv ⟨_,ha⟩)
    change rho g⁻¹ (rho (g*a.val*g⁻¹) (p v)) = rho g⁻¹ (p v) at hh
    change rho a.val (p (τ g⁻¹ v)) = p (τ g⁻¹ v)
    rw [he]
    simpa only [map_mul,Module.End.mul_apply,Representation.inv_self_apply] using hh
  have hu : p v' ∈ NaturalOffenders.upper := by
    change p v' ∈ fixedSpace (NaturalOffenders.binaryAction (F := ZMod 2))
      (EvenTwoRank.elementary (ZMod 2)) at hv'
    rwa [NaturalOffenders.fixedSpace_elementary] at hv'
  obtain ⟨b',hb',rfl⟩ := hB hb
  rw [unipotent_eq_range] at hb'
  obtain ⟨t,rfl⟩ := hb'
  obtain ⟨w,hw⟩ := LongRootModel.unipotent_displacement_upper t v' hu
  refine ⟨τ g w,?_⟩
  calc
    τ (MulAut.conj g (unipotentProduct t)) v-v = τ g (τ (unipotentProduct t) v'-v') := by
      simp only [v',MulAut.conj_apply,map_mul,Module.End.mul_apply,map_sub,Representation.self_inv_apply]
    _ = τ g (τ (rootA 1) w-w) := by rw [hw]
    _ = _ := by
      change τ g (τ (rootA 1) w-w) = τ (MulAut.conj g (rootA 1)) (τ g w)-τ g w
      simp only [MulAut.conj_apply,map_mul,Module.End.mul_apply,map_sub,Representation.inv_self_apply]

include h e in
/-- The whole original critical triple lies in the full-actor long-root
auxiliary, with no projection-kernel error. -/
theorem critical_triple_le_root_auxiliary
    (a z : Vertex T) (ha : color T a = false)
    (hc : CriticalPair T a z ((geometry h).exists_critical a ha))
    (t : Vertex T) (hat : Adjacent T a t)
    (d : EndpointModel T a) (g : Atlas.G2.Model (ZMod 2))
    (hE : image d (Z T z) = (Atlas.G2.EvenTwoRank.elementary (ZMod 2)).map
      (MulAut.conj g).toMonoidHom)
    (hB : image d (Q T t) ≤ Atlas.G2.unipotent.map (MulAut.conj g).toMonoidHom) :
    ⁅⁅Z T a,Z T z⁆,Q T t⁆ ≤ rootAuxiliary d g := by
  have hz := critical_endpoint_color T a ha _ hc
  let := Z_elementary_of_positive T (geometry h) z hz (by
    rw [(geometry h).distance_constant z hz]; exact (positive_even h e).1)
  obtain ⟨f,hf,he,hp⟩ := moving_seed_cover h e a ha d
  have hdisp (s : stabilizer T a) (v : Atlas.G2.Natural.TraceZero (ZMod 2)) :
      (f (Multiplicative.ofAdd (Atlas.G2.Natural.traceZeroAction (ZMod 2) (d.actor s) v-v)) : FreeAmalgam T) =
        ⁅s.val,(f (Multiplicative.ofAdd v) : FreeAmalgam T)⁆ := by
    have hv : Multiplicative.ofAdd (Atlas.G2.Natural.traceZeroAction (ZMod 2) (d.actor s) v-v) =
        Multiplicative.ofAdd (Atlas.G2.Natural.traceZeroAction (ZMod 2) (d.actor s) v) *
          (Multiplicative.ofAdd v)⁻¹ := congrArg Multiplicative.ofAdd (sub_eq_add_neg _ _)
    rw [hv,map_mul,map_inv]
    change (f (Multiplicative.ofAdd (Atlas.G2.Natural.traceZeroAction (ZMod 2) (d.actor s) v)) : FreeAmalgam T) *
      (f (Multiplicative.ofAdd v) : FreeAmalgam T)⁻¹ = _
    rw [he]
    rfl
  let r := MulAut.conj g (Atlas.G2.rootA (1 : ZMod 2))
  have hrE : r ∈ image d (Z T z) := by
    rw [hE]
    exact mem_map_of_mem (MulAut.conj g).toMonoidHom
      (Atlas.G2.NaturalOffenders.rootA_mem_elementary 1)
  obtain ⟨s,hs,hsr⟩ := hrE
  rw [commutator_comm]
  apply commutator_le.mpr
  intro b hb x hx
  let b' : stabilizer T a := ⟨b,CriticalCriterion.edge_le_stabilizer T ha hat hb⟩
  let x' : Z T a := ⟨x,critical_image_le_start (geometry h) a z ha hc hx⟩
  have hxfix : (d.projection x').toAdd ∈ fixedSpace rho (image d (Z T z)) := by
    rintro ⟨j,y,hy,rfl⟩
    have hxz := critical_image_le_endpoint (geometry h) a z ha hc hx
    have hcomm : y.val*x = x*y.val :=
      congrArg Subtype.val (mul_comm (⟨y.val,hy⟩ : Z T z) ⟨x,hxz⟩)
    have hye : (⟨y.val*x'*y.val⁻¹,
      (mem_normalizer_iff.mp (Z_normalized T a y.property) x'.val).mp x'.property⟩ : Z T a) = x' := by
      apply Subtype.ext
      change y.val*x*y.val⁻¹=x
      rw [hcomm,mul_inv_cancel_right]
    have hh := d.intertwines y x'
    rw [hye] at hh
    exact (congrArg Multiplicative.toAdd hh).symm
  obtain ⟨v,hv⟩ := hf ⟨x,critical_commutator_le_start_moving h e a z ha hc hx⟩
  have hpv : (d.projection x').toAdd = Atlas.G2.Restricted.NaturalCoordinates.projection (ZMod 2) v.toAdd := by
    have hh := congrArg Multiplicative.toAdd (hp v.toAdd)
    change (d.projection (inclusion (U_le_Z a) (f v))).toAdd =
      Atlas.G2.Restricted.NaturalCoordinates.projection (ZMod 2) v.toAdd at hh
    rw [hv] at hh
    exact hh
  obtain ⟨w,hw⟩ := traceZero_displacement (image d (Z T z)) (image d (Q T t)) g hE hB
    (d.actor b') (mem_map_of_mem d.actor hb) v.toAdd (hpv ▸ hxfix)
  have hcomm : ⁅b,x⁆ = ⁅s.val,(f (Multiplicative.ofAdd w) : FreeAmalgam T)⁆ := by
    have hh := congrArg (fun v => (f (Multiplicative.ofAdd v) : FreeAmalgam T)) hw
    have hsr' : d.actor s = MulAut.conj g (Atlas.G2.rootA 1) := hsr
    rw [hdisp,←hsr',hdisp] at hh
    change ⁅b,(f v).val⁆ = _ at hh
    rw [hv] at hh
    exact hh
  rw [hcomm]
  apply commutator_mem_commutator _ (U_le_Z a (f (Multiplicative.ofAdd w)).property)
  exact ⟨s,by change d.actor s ∈ zpowers r; rw [hsr]; exact mem_zpowers r,rfl⟩

include h e in
/-- The same-pair auxiliary makes the entire critical triple fixed by the
midpoint residual. -/
theorem critical_triple_le_midpoint_fixed
    (hb : (geometry h).b T = 4)
    (a z : Vertex T) (ha : color T a = false)
    (hc : CriticalPair T a z ((geometry h).exists_critical a ha))
    (t c : Vertex T) (hcColor : color T c = false)
    (hat : Adjacent T a t) (hct : Adjacent T c t)
    (hac : (cosetGraph T).dist a c = 2) (hcz : (cosetGraph T).dist c z = 2) :
    ⁅⁅Z T a,Z T z⁆,Q T t⁆ ≤ fixedCore T c := by
  obtain ⟨d⟩ := endpointModel_knownSimple h e ha
  obtain ⟨g,hE,hB,_,hA⟩ := critical_edge_root_auxiliary h e hb a z ha hc t c hcColor hat hct hac hcz d
  exact (critical_triple_le_root_auxiliary h e a z ha hc t hat d g hE hB).trans hA

include h e in
/-- An edge displacement inside the residual-fixed kernel vanishes. Split
the seed as its moving part times the edge center and lift natural fixation. -/
theorem seed_edge_fixed_displacement_eq_bot
    (a t : Vertex T) (ha : color T a = false) (hat : Adjacent T a t)
    (N : Subgroup (FreeAmalgam T)) (hNZ : N ≤ Z T a)
    (hfixed : ⁅N,Q T t⁆ ≤ fixedCore T a) : ⁅N,Q T t⁆ = ⊥ := by
  let := (geometry h).Z_elementary (positive_even h e).1 a ha
  obtain ⟨d⟩ := endpointModel_knownSimple h e ha
  have hEZ : edgeOmega T t ≤ Z T a := by
    rw [seed_eq_moving_sup_edgeOmega h a t ha hat]
    exact le_sup_right
  have hsup : (U T a).subgroupOf (Z T a) ⊔ (edgeOmega T t).subgroupOf (Z T a) = ⊤ := by
    rw [←subgroupOf_sup (U_le_Z a) hEZ,←seed_eq_moving_sup_edgeOmega h a t ha hat,subgroupOf_self]
  rw [commutator_comm]
  apply le_bot_iff.mp
  apply commutator_le.mpr
  intro b hb x hx
  let b' : stabilizer T a := ⟨b,CriticalCriterion.edge_le_stabilizer T ha hat hb⟩
  obtain ⟨u,hu,y,hy,huy⟩ := Subgroup.mem_sup.mp
    (show (⟨x,hNZ hx⟩ : Z T a) ∈ (U T a).subgroupOf (Z T a) ⊔ (edgeOmega T t).subgroupOf (Z T a) from
      hsup.symm ▸ mem_top _)
  have huy' : u.val*y.val = x := congrArg Subtype.val huy
  have hby : ⁅b,y.val⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr
    ((Q_le_centralizer_X T t hb) y.val hy).symm
  have hcomm : ⁅b,x⁆ = ⁅b,u.val⁆ := by
    rw [←huy',commutatorElement_mul_right_eq_mul_conj,hby]
    simp
  let v : Z T a := ⟨⁅b,u.val⁆,(Z T a).mul_mem
    ((mem_normalizer_iff.mp (Z_normalized T a b'.property) u.val).mp u.property)
    ((Z T a).inv_mem u.property)⟩
  have hvK : v.val ∈ d.projection.ker.map (Z T a).subtype := by
    rw [d.projection_kernel]
    refine ⟨v.property,?_⟩
    have hm : ⁅b,x⁆ ∈ ⁅N,Q T t⁆ := by
      rw [commutator_comm]
      exact commutator_mem_commutator hb hx
    change ⁅b,u.val⁆ ∈ centralizer (Ltilde T a : Set (FreeAmalgam T))
    rw [←hcomm]
    exact (hfixed hm).2
  obtain ⟨v',hv',hvv⟩ := hvK
  have hvp : d.projection v = 1 := (Subtype.ext hvv : v' = v) ▸ hv'
  let uc : Z T a := ⟨b*u.val*b⁻¹,
    (mem_normalizer_iff.mp (Z_normalized T a b'.property) u.val).mp u.property⟩
  have hvprod : v = uc*u⁻¹ := rfl
  rw [hvprod,map_mul,map_inv,show d.projection uc = _ from d.intertwines b' u] at hvp
  have hpfix : rho (d.actor b') (d.projection u).toAdd = (d.projection u).toAdd := by
    exact congrArg Multiplicative.toAdd (mul_inv_eq_one.mp hvp)
  have hufix := moving_seed_fixed_of_projection_fixed h e a ha d b' ⟨u.val,hu⟩ hpfix
  change ⁅b,x⁆ = 1
  rw [hcomm,commutatorElement_def,hufix,mul_inv_cancel]

include h e in
/-- The MS93 (3.8) critical triple vanishes on its original first edge
and midpoint. -/
theorem critical_triple_eq_bot
    (hb : (geometry h).b T = 4)
    (a z : Vertex T) (ha : color T a = false)
    (hc : CriticalPair T a z ((geometry h).exists_critical a ha))
    (t c : Vertex T) (hcColor : color T c = false)
    (hat : Adjacent T a t) (hct : Adjacent T c t)
    (hac : (cosetGraph T).dist a c = 2) (hcz : (cosetGraph T).dist c z = 2) :
    ⁅⁅Z T a,Z T z⁆,Q T t⁆ = ⊥ :=
  seed_edge_fixed_displacement_eq_bot h e c t hcColor hct _
    (critical_commutator_le_midpoint_seed h e hb a z c hcColor hac hcz)
    (critical_triple_le_midpoint_fixed h e hb a z ha hc t c hcColor hat hct hac hcz)

/-- The last nonfixed-derived input of MS93 (3.8), proved uniformly for
the original small MS-pair. -/
theorem nonfixedCriticalEdge_knownSimple : NonfixedCriticalEdgeInput.{u} := by
  unfold NonfixedCriticalEdgeInput
  intro J _ _ L R h e hb c hc _ a ha z hcrit t hat hct hac hcz
  exact critical_triple_eq_bot h e hb a z ha hcrit t c hc hat hct hac hcz

end CFSG.Quasithin.ChapterC.G2Exceptional.Reconstruction.DistanceTwo.DistanceFour
