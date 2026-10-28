module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SylowCentrality
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.TripleCommutators

/-!
# Both source triples for the full saturated radical

In a natural symplectic module, the displacement space of either actor
is perpendicular to the fixed space of that actor. Thus one vanishing
mixed displacement implies the reversed vanishing displacement. Fixed-vector
lifting transfers this symmetry through the entire central cover, and the
literal inner quotient applies it to any two endpoint-stabilizer subgroups.

For an actual critical image of order q, use this symmetry on U at each
endpoint, then restore the entire common edge center in Z = U Z_t. This
reverses the Q,T₀ triples, including in the full-Sylow branch. The proved
Sylow image count supplies the order-q premise there; the existing parabolic
argument supplies the other two branches. Consequently both clauses of
MS93 (3.7)(1) hold for the full saturated radical, together with the midpoint
containment of the critical commutator.

Source: Meierfrankenfeld--Stellmacher (1993), (3.7)(1), printed p.873.
The stronger full-core movement in (2), paired fixed-kernel comparisons,
parabolic critical-pair selection and final field restriction remain separate.
-/

public noncomputable section
open Subgroup Representation Representation.OneCohomology
open Theory.SpecificGroups.SymplecticFour
open Representation.SymplecticFourOrthogonalCover
open scoped commutatorElement IsMulCommutative

private theorem natural_reverse_displacement {F : Type*} [Field F]
    (A B : Subgroup (Sp F))
    (h : displacementSpace A ≤ TwoLocalCover.fixedSpace B) :
    displacementSpace B ≤ TwoLocalCover.fixedSpace A := by
  rw [←orthogonal_displacementSpace] at h ⊢
  intro v hv w hw
  exact TwoLocalCover.form_alternating.eq_iff.mp (h hw v hv)

private theorem embedded_cover_reverse_triple
    {F W S G : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    [Group S] [Group G]
    (σ : Representation (ZMod 2) (L (K := F)) W)
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (j : Multiplicative W →* G) (hj : Function.Injective j)
    (ι : S →* G) (γ : S →* L (K := F))
    (hact : ∀ (s : S) (w : W), j (Multiplicative.ofAdd (σ (γ s) w)) =
      ι s*j (Multiplicative.ofAdd w)*(ι s)⁻¹)
    (A B : Subgroup S) (htriple : ⁅⁅j.range,A.map ι⁆,B.map ι⁆ = ⊥) :
    ⁅⁅j.range,B.map ι⁆,A.map ι⁆ = ⊥ := by
  let f := (commutator (Sp F)).subtype.comp γ
  have hval (s : S) (w : W) :
      j (Multiplicative.ofAdd (σ (γ s) w-w)) = ⁅ι s,j (Multiplicative.ofAdd w)⁆ := by
    rw [ofAdd_sub,map_div,div_eq_mul_inv,hact]
    rfl
  have hAB : displacementSpace (A.map f) ≤ TwoLocalCover.fixedSpace (B.map f) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨a,v⟩,rfl⟩ b hb
    change b • (a.val • v-v)=a.val • v-v
    obtain ⟨a,ha,he⟩ := a.property
    rw [←he]
    obtain ⟨b,hb,rfl⟩ := hb
    obtain ⟨w,rfl⟩ := hp.1 v
    have hcomm := commutator_eq_bot_iff_le_centralizer.mp htriple
    have hc : ι b*⁅ι a,j (Multiplicative.ofAdd w)⁆ =
        ⁅ι a,j (Multiplicative.ofAdd w)⁆*ι b := by
      apply hcomm
      · rw [commutator_comm]
        exact commutator_mem_commutator (mem_map_of_mem ι ha) ⟨_,rfl⟩
      · exact mem_map_of_mem ι hb
    have he : σ (γ b) (σ (γ a) w-w)=σ (γ a) w-w := by
      apply Multiplicative.ofAdd.injective
      apply hj
      rw [hact,hval,hc,mul_inv_cancel_right]
    have hh := congrArg p he
    rw [p.isIntertwining,map_sub,p.isIntertwining] at hh
    exact hh
  have hBA := natural_reverse_displacement (A.map f) (B.map f) hAB
  apply commutator_eq_bot_iff_le_centralizer.mpr
  rw [commutator_comm j.range]
  apply commutator_le.mpr
  rintro _ ⟨b,hb,rfl⟩ _ ⟨w,rfl⟩ _ ⟨a,ha,rfl⟩
  have hd : p (σ (γ b) w.toAdd-w.toAdd) ∈ displacementSpace (B.map f) := by
    rw [map_sub,p.isIntertwining]
    exact Coinvariants.sub_mem_ker
      (ρ := (symplecticNatural 2).comp (B.map f).subtype)
      ⟨f b,mem_map_of_mem f hb⟩ (p w.toAdd)
  have he := cover_fixed_of_projection_fixed p hp (γ a) (σ (γ b) w.toAdd-w.toAdd)
    (hBA hd (f a) (mem_map_of_mem f ha))
  have hh := congrArg (fun v => j (Multiplicative.ofAdd v)) he
  rw [hact,hval,mul_inv_eq_iff_eq_mul] at hh
  exact hh

open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo
open DistanceTwoRecognition ChapterB.QuasisimpleSource
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The original symplectic cover reverses vanishing triple commutators
for any two subgroups of the whole endpoint stabilizer. -/
theorem moving_reversed_triple
    (g : Geometry d.radical) (hb : 0 < g.b d.radical)
    {z : Vertex d.radical} (hz : color d.radical z = false)
    (A B : Subgroup (FreeAmalgam d.radical))
    (hA : A ≤ stabilizer d.radical z) (hB : B ≤ stabilizer d.radical z)
    (htriple : ⁅⁅U d.radical z,A⁆,B⁆ = ⊥) :
    ⁅⁅U d.radical z,B⁆,A⁆ = ⊥ := by
  let := replacementComponent_normal h d
  let s := replacementMovedSection h d
  obtain ⟨⟨E,hE,e,he,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hfaith,hsemi,hconj,hproj,hker⟩⟩ :=
    replacement_ambient_initial_cover_at_vertex h d hz
  have hCtop : replacementComponent d = ⊤ := by
    let q := QuotientGroup.mk' (pCore 2 d.overgroup)
    have hh := congrArg (fun A : Subgroup d.overgroup => A.map q)
      (replacement_inner_of_positive h d g hb)
    rw [Subgroup.map_sup,show (pCore 2 d.overgroup).map q = ⊥ from
      (Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk']),sup_bot_eq,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at hh
    exact hh
  let κC := κ.codRestrict (replacementComponent d) (fun x => hCtop ▸ mem_top (κ x))
  let γ := e.groupEquiv.toMonoidHom.comp κC
  let S := stabilizer d.radical z
  have haction (x : S) (w : s.space.toSubmodule) :
      j (Multiplicative.ofAdd (MovedSection.coverAction s e (γ x) w)) =
        x.val*j (Multiplicative.ofAdd w)*x.val⁻¹ := by
    change j (Multiplicative.ofAdd (s.space.toRepresentation
      (e.groupEquiv.symm (e.groupEquiv (κC x))) w)) = _
    rw [e.groupEquiv.symm_apply_apply]
    exact hconj x w
  have hAm : (A.subgroupOf S).map S.subtype = A := map_subgroupOf_eq_of_le hA
  have hBm : (B.subgroupOf S).map S.subtype = B := map_subgroupOf_eq_of_le hB
  have hh := embedded_cover_reverse_triple (MovedSection.coverAction s e)
    (MovedSection.coverProjection s e) he j hj S.subtype γ haction
    (A.subgroupOf S) (B.subgroupOf S) (by
      rwa [hjr,hAm,hBm])
  simpa only [hjr,hAm,hBm] using hh

omit h d in
private theorem triple_sup_of_central_factor {G : Type*} [Group G]
    (T U Z A B : Subgroup G) (hU : U ≤ T) (hZ : Z ≤ T)
    (hA : A ≤ T) (_hB : B ≤ T)
    (hTB : T ≤ normalizer (B : Set G))
    (hcentral : Z ≤ centralizer (T : Set G))
    (htriple : ⁅⁅U,A⁆,B⁆ = ⊥) : ⁅⁅U ⊔ Z,A⁆,B⁆ = ⊥ := by
  apply commutator_eq_bot_iff_le_centralizer.mpr
  apply commutator_sup_le_of_relative_normal T U Z A _
    (hTB.trans (normalizer_le_normalizer_centralizer B)) hU hZ
    (commutator_eq_bot_iff_le_centralizer.mp htriple)
  exact (commutator_eq_bot_iff_le_centralizer.mpr
    (hcentral.trans (centralizer_le hA))).le.trans bot_le

/-- Reverse both triples of MS93 (3.7)(1) when the critical image has
order q, including the full-Sylow case and the entire common edge center. -/
theorem critical_root_reversed_triples
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t)
    (hcritical : (Q d.radical z).relIndex (Z d.radical a) = 2^n) :
    ⁅⁅Z d.radical z,Q d.radical a⁆,componentRadical d a t⁆ = ⊥ ∧
      ⁅⁅Z d.radical a,Q d.radical z⁆,componentRadical d z t⁆ = ⊥ := by
  have hparts := critical_root_component_displacements h d path hb hat hzt c c' hcritical
  have hedge := MSCentralOrbit.edgeCentralizerCondition d.radical (replacement_isPGroup h d)
    (replacement_core_le h d) (replacement_omegaOrbit_centralizer h d)
  let rev : CriticalPath d.radical g z a :=
    { start_color := path.end_color
      walk := path.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
      critical := critical_reverse d.radical g hedge a path.start_color
        (by rw [g.distance_constant a path.start_color]; change 0 < g.b d.radical; omega)
        z path.end_color path.critical }
  have hcritical' := (replacement_critical_indices_eq_field_of_small h d path (by omega) (by
    rw [hcritical]
    have hq : 1 < 2^n := one_lt_pow₀ (by decide : 1 < (2:ℕ)) (by have := h.nonbinary; omega)
    nlinarith)).2
  have ht : color d.radical t = true := by
    have hn := adjacent_color_ne d.radical hat
    cases he : color d.radical t <;> simp_all [path.start_color]
  have hZt : Z d.radical t = omegaCenter (Q d.radical t) := by simp [Z,ht,edgeOmega]
  have hcentral : Z d.radical t ≤ centralizer (Q d.radical t : Set (FreeAmalgam d.radical)) := by
    rw [hZt]
    exact fun x hx => (mem_omegaCenter_iff.mp hx).2.2
  have hseed (v : Vertex d.radical) (hv : color d.radical v=false)
      (hvt : Adjacent d.radical v t) : Z d.radical v ≤ Q d.radical t := by
    apply Z_le_Q_of_dist_lt d.radical v (g.exists_critical v hv)
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj _ _ _).mpr hvt),
      g.distance_constant v hv]
    change 1<g.b d.radical
    omega
  have hz := moving_reversed_triple h d g (by omega) path.end_color
    (componentRadical d a t) (Q d.radical a)
    (inf_le_left.trans c'.edge_le) (c.core_le_edge.trans c'.edge_le)
    (le_antisymm ((commutator_mono (commutator_mono (U_le_Z z) le_rfl) le_rfl).trans
      hparts.2.1.le) bot_le)
  have ha := moving_reversed_triple h d g (by omega) path.start_color
    (componentRadical d z t) (Q d.radical z)
    (inf_le_left.trans c.edge_le) (c'.core_le_edge.trans c.edge_le)
    (le_antisymm ((commutator_mono (commutator_mono (U_le_Z a) le_rfl) le_rfl).trans
      hparts.2.2.2.1.le) bot_le)
  constructor
  · rw [Z_eq_moving_sup_edge_of_critical_index h d rev hb hzt hcritical']
    exact triple_sup_of_central_factor (Q d.radical t) (U d.radical z) (Z d.radical t)
      (Q d.radical a) (componentRadical d a t)
      ((U_le_Z z).trans (hseed z path.end_color hzt)) (hZt ▸ omegaCenter_le _)
      c.core_le_edge inf_le_left c.componentRadical_normalized hcentral hz
  · rw [Z_eq_moving_sup_edge_of_critical_index h d path hb hat hcritical]
    exact triple_sup_of_central_factor (Q d.radical t) (U d.radical a) (Z d.radical t)
      (Q d.radical z) (componentRadical d z t)
      ((U_le_Z a).trans (hseed a path.start_color hat)) (hZt ▸ omegaCenter_le _)
      c'.core_le_edge inf_le_left c'.componentRadical_normalized hcentral ha

/-- Source (3.7)(1) holds in all three saturated radical branches.
The Sylow alternative is discharged using its actual order-q critical images. -/
theorem paired_source_triples
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2 = d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t) :
    ⁅Z d.radical z,componentRadical d a t⁆ ≤ U d.radical a ∧
      ⁅⁅Z d.radical z,Q d.radical a⁆,componentRadical d a t⁆ = ⊥ ∧
      ⁅Z d.radical a,componentRadical d z t⁆ ≤ U d.radical z ∧
      ⁅⁅Z d.radical a,Q d.radical z⁆,componentRadical d z t⁆ = ⊥ ∧
      ⁅Z d.radical a,Z d.radical z⁆ ≤ Z d.radical t := by
  rcases paired_source_triples_or_sylow h d g hb hsat path hat hzt c c' with hp | ⟨S,hS⟩
  · exact hp
  have hi := (critical_indices_eq_field_of_full_sylow h d path hb hat hzt c c' S hS).1
  have hr := critical_root_reversed_triples h d path hb hat hzt c c' hi
  have hc := critical_root_component_displacements h d path hb hat hzt c c' hi
  exact ⟨hc.1,hr.1,hc.2.2.1,hr.2,hc.2.2.2.2⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo
