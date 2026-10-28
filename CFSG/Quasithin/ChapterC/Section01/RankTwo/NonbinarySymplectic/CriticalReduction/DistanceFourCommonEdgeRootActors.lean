module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourDirectedRootKernels
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.StrictIndexSaturation
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.StrictIndexOrbit

/-!
# Full root actors on the same retained edge

The actual product actors are the full endpoint seeds Z_e and Z_(e^k),
acting at the selected backward start v. Their full fixed subgroups in Z_v
are the two directed kernels. An explicit companion backward path retains
the same first neighbor w and midpoint a. Since both endpoints are three
edges from w, minimum critical distance puts both full seeds in Q_w.
The literal Q_v images and full U_v fixed indices are q. No kernel is
removed, and no equality with the complete smaller-mover join is assumed.
Source: MS93 (5.12)(3), printed p.927.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

private theorem full_critical_fixed_kernel
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (_hb : 0<geometry.b d.radical) :
    Z d.radical a ⊓ centralizer (Z d.radical z : Set (FreeAmalgam d.radical)) =
      Z d.radical a ⊓ Q d.radical z := by
  have hAS : Z d.radical a ≤ stabilizer d.radical z :=
    Z_le_stabilizer_of_dist_le a (geometry.exists_critical a path.start_color) path.critical.1.le
  have hC := MSCentralOrbit.C_eq_Q d.radical (h.replacement_two_group d)
    (h.replacement_core_le d) (h.replacement_omegaOrbit_centralizer d) z path.end_color
  rw [←hC]
  ext x
  exact ⟨fun hx => ⟨hx.1,hAS hx.1,hx.2⟩,fun hx => ⟨hx.1,hx.2.2⟩⟩

private theorem full_critical_actor_field_index
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4≤geometry.b d.radical)
    (hi : (Q d.radical z).relIndex (Z d.radical a)=Nat.card F) :
    (centralizer (Z d.radical z : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical a)=Nat.card F := by
  have hZS := path.endpoint_Z_le_start_stabilizer (by omega)
  have heq := full_critical_fixed_kernel h d path (by omega)
  let := finite_Z d.radical a
  have hu : (centralizer (Z d.radical z : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical a)≤Nat.card F := by
    apply (relIndex_le_of_le_right (U_le_Z a) index_ne_zero_of_finite).trans
    rw [←inf_relIndex_left,heq,inf_relIndex_left,hi]
  have hn : ⁅Z d.radical z,U d.radical a⁆ ≠ ⊥ := by
    intro hz
    have hzero : ⁅Z d.radical a,Z d.radical z⁆=⊥ := by
      rw [h.replacement_Z_commutator_eq_U d geometry hb path.start_color _ hZS,
        commutator_comm,hz]
    have hfixed : Z d.radical a ≤ centralizer (Z d.radical z : Set _) :=
      commutator_eq_bot_iff_le_centralizer.mp hzero
    have hQ : Z d.radical a ≤ Q d.radical z := by
      have hh : Z d.radical a ⊓ Q d.radical z=Z d.radical a := by
        rw [←heq,inf_eq_left.mpr hfixed]
      exact hh ▸ inf_le_right
    exact path.critical.2 hQ
  have hbot : centralizer ((⊥ : Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) = ⊤ := by
    apply top_unique
    intro x _ y hy
    have hy1 : y=1 := mem_bot.mp hy
    rw [hy1,one_mul,mul_one]
  have hlo := h.replacement_fixed_U_moving_index_lower d geometry hb path.start_color
    (Z d.radical z) ⊥ hZS bot_le (by simpa only [hbot,inf_top_eq] using hn)
  have hlo' : Nat.card F≤(centralizer (Z d.radical z : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical a) := by simpa only [hbot,inf_top_eq] using hlo
  exact Nat.le_antisymm hu hlo'

omit [Finite H] [Field F] [Finite F] [CharP F 2] h in
private theorem critical_endpoint_le_first_core
    {geometry : Geometry d.radical} {a z w : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 0<geometry.b d.radical)
    (hfirst : path.walk.getVert 1=w) : Z d.radical z ≤ Q d.radical w := by
  rw [←hfirst]
  apply Z_le_Q_of_dist_lt _ z (geometry.exists_critical z path.end_color)
  rw [geometry.distance_constant z path.end_color,SimpleGraph.dist_comm,path.dist_end,path.length_eq_b]
  change geometry.b d.radical-1<geometry.b d.radical
  omega

private theorem directed_common_edge_actors
    {geometry : Geometry d.radical} {a z v w : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (back : CriticalPath d.radical geometry v (path.walk.getVert 2))
    (hfirst : back.walk.getVert 1=w)
    (haw : Adjacent d.radical a w) (hvw : Adjacent d.radical v w)
    (k : FreeAmalgam d.radical) (hk : k∈stabilizer d.radical a)
    (hfixed : ⁅V d.radical a,Q d.radical a⁆ ≤ fixedCore d.radical a)
    (hnot : ¬ Z d.radical v ⊓ Q d.radical (path.walk.getVert 2) ≤
      Z d.radical v ⊓ Q d.radical (act d.radical k (path.walk.getVert 2))) :
    ∃ companion : CriticalPath d.radical geometry v (act d.radical k (path.walk.getVert 2)),
      companion.walk.getVert 1=w ∧
      (∀ i≤2, companion.walk.getVert (i+2)=act d.radical k (path.walk.getVert i)) ∧
      (Q d.radical (act d.radical k (path.walk.getVert 2))).relIndex (Z d.radical v)=Nat.card F ∧
      (Q d.radical v).relIndex (Z d.radical (act d.radical k (path.walk.getVert 2)))=Nat.card F ∧
      Z d.radical (path.walk.getVert 2)≤Q d.radical w ∧
      Z d.radical (act d.radical k (path.walk.getVert 2))≤Q d.radical w ∧
      (Q d.radical v).relIndex (Z d.radical (path.walk.getVert 2))=Nat.card F ∧
      (centralizer (Z d.radical (path.walk.getVert 2) : Set (FreeAmalgam d.radical))).relIndex
        (U d.radical v)=Nat.card F ∧
      (centralizer (Z d.radical (act d.radical k (path.walk.getVert 2)) : Set (FreeAmalgam d.radical))).relIndex
        (U d.radical v)=Nat.card F ∧
      Z d.radical v ⊓ centralizer (Z d.radical (path.walk.getVert 2) : Set (FreeAmalgam d.radical)) ≠
        Z d.radical v ⊓ centralizer
          (Z d.radical (act d.radical k (path.walk.getVert 2)) : Set (FreeAmalgam d.radical)) := by
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
  have hp (i : ℕ) : p.walk.getVert i=act d.radical k (path.walk.getVert i) := by
    change (p₀.walk.copy hka rfl).getVert i=_
    rw [SimpleGraph.Walk.getVert_copy]
    exact actWalk_getVert d.radical k path.walk i
  have hl : p.walk.length=4 := p.length_eq_b.trans hb
  have hp2 : p.walk.getVert (p.walk.length-2)=act d.radical k (path.walk.getVert 2) := by
    rw [hl]
    exact hp 2
  have hescape : ¬ Z d.radical v≤Q d.radical (p.walk.getVert (p.walk.length-2)) := by
    rw [hp2]
    intro hh
    exact hnot (le_inf inf_le_left (inf_le_left.trans hh))
  obtain ⟨c,hc,hcover⟩ := exists_backward_path_of_not_le geometry (by omega) p haw hvw hescape
  let companion : CriticalPath d.radical geometry v (act d.radical k (path.walk.getVert 2)) := {
    start_color := c.start_color
    walk := c.walk.copy rfl hp2
    shortest := by rw [SimpleGraph.Walk.length_copy,←hp2]; exact c.shortest
    critical := by simpa only [hp2] using c.critical }
  have hcfirst : companion.walk.getVert 1=w := by
    change (c.walk.copy rfl hp2).getVert 1=w
    rwa [SimpleGraph.Walk.getVert_copy]
  have hcove (i : ℕ) (hi : i≤2) :
      companion.walk.getVert (i+2)=act d.radical k (path.walk.getVert i) := by
    change (c.walk.copy rfl hp2).getVert (i+2)=_
    rw [SimpleGraph.Walk.getVert_copy,hcover i (by omega),hp]
  obtain ⟨hi,hi'⟩ := h.replacement_distance_four_fixed_critical_indices d hb path.start_color hfixed companion
  obtain ⟨hb₁,hb₂⟩ := h.replacement_distance_four_fixed_critical_indices d hb path.start_color hfixed back
  refine ⟨companion,hcfirst,hcove,hi,hi',critical_endpoint_le_first_core d back (by omega) hfirst,
    critical_endpoint_le_first_core d companion (by omega) hcfirst,hb₂,
    full_critical_actor_field_index h d back (by omega) hb₁,
    full_critical_actor_field_index h d companion (by omega) hi,?_⟩
  rw [full_critical_fixed_kernel h d back (by omega),
    full_critical_fixed_kernel h d companion (by omega)]
  exact fun hh => hnot hh.le

/-- The original prescribed selector supplies two full root actors on one
actual edge, with exact indices and distinct whole-seed fixed kernels. -/
theorem Input.replacement_distance_four_prescribed_common_edge_root_actors
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
                  (Z d.radical (act d.radical k (path.walk.getVert 2)) : Set (FreeAmalgam d.radical)) := by
  obtain ⟨E,hE,f,hf,hfQ,hTf,hindex,g,hg,x,hx,hat1,hct1,hat2,hct2,
      hgen1,hgen2,hfix,hmove1,hmove2,hxn,hxp,v,hv,w,hwhich,haw,hvw,hn,back,hfirst,hover,
      r,hr,k,hk,hrv,horiented,hgen,hnot,_,_,_⟩ :=
    h.replacement_distance_four_prescribed_directed_root_kernels d path hb hfixed hmove hequal hJm
  refine ⟨E,hE,f,hf,hfQ,hTf,hindex,g,hg,x,hx,hat1,hct1,hat2,hct2,
    hgen1,hgen2,hfix,hmove1,hmove2,hxn,hxp,v,hv,w,hwhich,haw,hvw,hn,back,hfirst,hover,
    r,hr,k,hk,hrv,horiented,hgen,hnot,?_⟩
  exact directed_common_edge_actors h d path hb back hfirst haw hvw k
    (Ltilde_le_stabilizer a hk) hfixed hnot

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
