module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SourceThreeMovement

/-!
# Component containment and full overlap in MS93 (3.7)(3)

In the noncontained-core branch, the component radical has exactly the
critical displacement on the opposite full natural cover. Projection puts
its natural displacement inside the critical root line. Symplectic
orthogonality and the full root-fixer theorem therefore put its actor image
in that root, giving T₀ ≤ Z Q′ through the original whole-core kernel.

The opposite overlap Z′ ∩ Q consequently centralizes T₀. The existing
whole-core centralizer theorem places this overlap in U D with the entire
component-fixed core D retained. Factoring an overlap element as u d,
centrality of d on T₀ shows that u centralizes T₀ and Q, hence T. Its
involution property puts u in the actual midpoint omega-center Z_t.
Thus Z′ ∩ Q ≤ Z_t D and [Z′ ∩ Q,T] ≤ D.

These are the full-overlap comparisons preceding the final plane-radical
generator contradiction. That contradiction, paired fixed-kernel equality,
source (5)/(6) selection and the field restriction are not asserted here.
Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (3.7)(3), printed p.874.
-/

public noncomputable section
open scoped IsMulCommutative commutatorElement
open Subgroup Representation Representation.BinaryOffender Representation.OneCohomology
open Representation.SymplecticFourOrthogonalCover Theory.SpecificGroups.SymplecticFour

private theorem embedded_actor_le_root_of_commutator_le
    {F W G : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W] [Group G]
    (σ : Representation (ZMod 2) (L (K := F)) W)
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (j : Multiplicative W →* G) (hj : Function.Injective j)
    (A B : Subgroup G) (α : A →* L (K := F)) (β : B →* L (K := F))
    (hA : ∀ (a : A) (w : W), j (Multiplicative.ofAdd (σ (α a) w))=
      a.val*j (Multiplicative.ofAdd w)*a.val⁻¹)
    (hB : ∀ (b : B) (w : W), j (Multiplicative.ofAdd (σ (β b) w))=
      b.val*j (Multiplicative.ofAdd w)*b.val⁻¹)
    (hle : ⁅A,j.range⁆ ≤ ⁅B,j.range⁆)
    (hd : Module.finrank F (displacementSpace (((commutator (Sp F)).subtype.comp β).range))=1)
    (hc : Nat.card (((commutator (Sp F)).subtype.comp β).range)=Nat.card F) :
    ((commutator (Sp F)).subtype.comp α).range ≤
      ((commutator (Sp F)).subtype.comp β).range := by
  let α' := (commutator (Sp F)).subtype.comp α
  let β' := (commutator (Sp F)).subtype.comp β
  let D := displacementSpace β'.range
  let P := ((D.restrictScalars (ZMod 2)).comap p.toLinearMap).toAddSubgroup.toSubgroup.map j
  have hBP : ⁅B,j.range⁆ ≤ P := by
    apply commutator_le.mpr
    intro b hb u hu
    obtain ⟨w,rfl⟩ := hu
    refine ⟨Multiplicative.ofAdd (σ (β ⟨b,hb⟩) w.toAdd-w.toAdd),?_,?_⟩
    · change p (σ (β ⟨b,hb⟩) w.toAdd-w.toAdd) ∈ D
      rw [map_sub,p.isIntertwining]
      exact Coinvariants.sub_mem_ker
        (ρ := (symplecticNatural 2).comp β'.range.subtype) ⟨β' ⟨b,hb⟩,⟨_,rfl⟩⟩ _
    · rw [ofAdd_sub,map_div,div_eq_mul_inv,hB]
      rfl
  have hD : displacementSpace α'.range ≤ D := by
    intro v hv
    obtain ⟨w,hw,hm⟩ := natural_displacement_lifts j.range A j rfl α σ hA p hp.1 v hv
    obtain ⟨u,hu,he⟩ := hBP (hle hm)
    have he' : u=Multiplicative.ofAdd w := hj he
    change p u.toAdd ∈ D at hu
    rw [he'] at hu
    change p w ∈ D at hu
    rwa [hw] at hu
  rw [←root_fixedSpace_fixer_eq β'.range hd hc]
  intro x hx
  apply (mem_fixingSubgroup_iff _).mpr
  intro v hv
  have hv' : v ∈ TwoLocalCover.fixedSpace α'.range := by
    rw [←orthogonal_displacementSpace] at hv ⊢
    exact fun w hw => hv w (hD hw)
  exact hv' x hx

open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo
open DistanceTwoRecognition ChapterB.QuasisimpleSource
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The component radical lies in the opposite core times the actual
critical root. The same plane cover, quotient and full core kernel are used. -/
theorem source_three_noncontained_component_containment
    (g : Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t)
    (hcritical : (Q d.radical z).relIndex (Z d.radical a)=2^n)
    (hnot : ¬ Q d.radical a ≤ Z d.radical a ⊔ Q d.radical z) :
    componentRadical d a t ≤ Z d.radical a ⊔ Q d.radical z := by
  let := replacementComponent_normal h d
  obtain ⟨⟨cv⟩,_,_⟩ :=
    source_three_noncontained_plane_cover h d g hb hsat path hat hzt c c' hcritical hnot
  rcases cv with ⟨⟨E,hE,e,he,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hfaith,hsemi,hconj,hproj,hker⟩,
    hTS,β,hβmark,hact,hαker,hplane⟩
  let s := replacementMovedSection h d
  let α := (commutator (Sp E.Carrier)).subtype.comp β
  have hZaQ : Z d.radical a ≤ Q d.radical a :=
    (g.omega_bound a path.start_color (by
      rw [g.distance_constant a path.start_color]; change 0 < g.b d.radical; omega)).trans
      (omegaCenter_le _)
  have hZaT := hZaQ.trans c.core_le_edge
  have hBT : componentRadical d a t ≤ Q d.radical t := inf_le_left
  let βB := β.comp (inclusion hBT)
  let βZ := β.comp (inclusion hZaT)
  let αB := (commutator (Sp E.Carrier)).subtype.comp βB
  let αZ := (commutator (Sp E.Carrier)).subtype.comp βZ
  have hZaS := hZaT.trans hTS
  let δ := κ.comp (inclusion hZaS)
  have hFc : Nat.card E.Carrier=2^n :=
    E.card_eq.trans (congrArg (2^·) hE)
  have hother := (replacement_critical_indices_eq_field_of_small h d path (by omega) (by
    rw [hcritical]
    have hq : 1 < 2^n := one_lt_pow₀ (by decide : 1 < (2:ℕ)) (by have := h.nonbinary; omega)
    nlinarith)).2
  have hδcard : Nat.card δ.range=Nat.card E.Carrier :=
    (Sp4Four.SourceComparison.quotient_image_card _ _ _ hZaS κ hκQ).trans
      (hcritical.trans hFc.symm)
  obtain ⟨η,hηcard,hηmark,hηact,hηdim,hηquad⟩ := inner_root_actor_of_field_index path (by omega)
    (MSCentralOrbit.C_eq_Q d.radical (replacement_isPGroup h d)
      (replacement_core_le h d) (replacement_omegaOrbit_centralizer h d) a path.start_color)
    h.nonbinary hFc s e he (replacement_component_image_structure h d).2.2.2.2
    j hj hjr δ
    (fun x w => hconj (inclusion hZaS x) w) hδcard (hother.trans hFc.symm)
  have hβZ : βZ=η := by
    apply MonoidHom.ext
    intro x
    apply e.groupEquiv.symm.injective
    exact Subtype.ext ((hβmark (inclusion hZaT x)).trans (hηmark x).symm)
  have hZrange : αZ.range=η.range.map (commutator (Sp E.Carrier)).subtype := by
    rw [MonoidHom.range_comp,hβZ]
  have hdim : Module.finrank E.Carrier (displacementSpace αZ.range)=1 := by
    rw [hZrange]
    exact hηdim
  have hcard : Nat.card αZ.range=Nat.card E.Carrier := by
    rw [hZrange,card_map_of_injective (commutator (Sp E.Carrier)).subtype_injective,hηcard]
  have hmove : ⁅componentRadical d a t,U d.radical z⁆ ≤ ⁅Z d.radical a,U d.radical z⁆ := by
    apply (commutator_mono le_rfl (U_le_Z z)).trans
    rw [source_three_noncontained_component_movement h d g hb hsat path hat hzt c c' hcritical hnot,
      critical_displacement_eq_paired_moving h d path hb hat hzt]
    exact commutator_mono (U_le_Z a) le_rfl
  have hle : αB.range ≤ αZ.range :=
    embedded_actor_le_root_of_commutator_le
      (MovedSection.coverAction s e) (MovedSection.coverProjection s e) he
      j hj (componentRadical d a t) (Z d.radical a) βB βZ
      (fun x w => hact (inclusion hBT x) w)
      (fun x w => hact (inclusion hZaT x) w)
      (by rw [hjr]; exact hmove) hdim hcard
  intro x hx
  obtain ⟨y,hy⟩ := hle (show αB ⟨x,hx⟩ ∈ αB.range from ⟨⟨x,hx⟩,rfl⟩)
  let u : Q d.radical t := inclusion hBT ⟨x,hx⟩*(inclusion hZaT y)⁻¹
  have hu : u ∈ α.ker := by
    change α u=1
    dsimp only [u]
    rw [map_mul,map_inv]
    change αB ⟨x,hx⟩*(αZ y)⁻¹=1
    rw [hy,mul_inv_cancel]
  have hq : x*y.val⁻¹ ∈ Q d.radical z :=
    show u ∈ (Q d.radical z).subgroupOf (Q d.radical t) from hαker ▸ hu
  have hh := (Z d.radical a ⊔ Q d.radical z).mul_mem (mem_sup_right hq) (mem_sup_left y.property)
  simpa only [mul_assoc,inv_mul_cancel,mul_one] using hh

/-- The opposite overlap centralizes the component radical, and is contained
in the midpoint center times the complete fixed core. -/
theorem source_three_noncontained_overlap
    (g : Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t)
    (hcritical : (Q d.radical z).relIndex (Z d.radical a)=2^n)
    (hnot : ¬ Q d.radical a ≤ Z d.radical a ⊔ Q d.radical z) :
    ⁅Z d.radical z ⊓ Q d.radical a,componentRadical d a t⁆=⊥ ∧
      Z d.radical z ⊓ Q d.radical a ≤ Z d.radical t ⊔ fixedCore d.radical a := by
  have hinside := source_three_noncontained_component_containment h d g hb hsat path hat hzt c c' hcritical hnot
  have hcentral : Z d.radical z ⊓ Q d.radical a ≤
      centralizer (componentRadical d a t : Set (FreeAmalgam d.radical)) := by
    apply le_centralizer_iff.mp
    apply hinside.trans
    apply sup_le
    · exact (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q d.radical a path.start_color)).trans (centralizer_le inf_le_right)
    · exact (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q d.radical z path.end_color))).trans (centralizer_le inf_le_left)
  refine ⟨commutator_eq_bot_iff_le_centralizer.mpr hcentral,?_⟩
  have hedge := MSCentralOrbit.edgeCentralizerCondition d.radical (replacement_isPGroup h d)
    (replacement_core_le h d) (replacement_omegaOrbit_centralizer h d)
  let rev : CriticalPath d.radical g z a :=
    { start_color := path.end_color
      walk := path.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
      critical := critical_reverse d.radical g hedge a path.start_color
        (by rw [g.distance_constant a path.start_color]; change 0 < g.b d.radical; omega)
        z path.end_color path.critical }
  let := g.Z_elementary (by omega : 0 < g.b d.radical) z path.end_color
  have hprod : Z d.radical z ⊓ Q d.radical a ≤ U d.radical a ⊔ fixedCore d.radical a :=
    (le_inf inf_le_right (inf_le_left.trans (Z d.radical z).le_centralizer)).trans
      (critical_core_centralizer_le_moving_sup_fixed h d rev hb)
  have hUaC : U d.radical a ≤ centralizer (Q d.radical a : Set (FreeAmalgam d.radical)) :=
    (U_le_Z a).trans (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q d.radical a path.start_color))
  have hUD : U d.radical a ≤ normalizer (fixedCore d.radical a : Set (FreeAmalgam d.radical)) :=
    (hUaC.trans (centralizer_le inf_le_left)).trans (Subgroup.centralizer_le_normalizer _)
  have hDC : fixedCore d.radical a ≤
      centralizer (componentRadical d a t : Set (FreeAmalgam d.radical)) :=
    commutator_eq_bot_iff_le_centralizer.mp (EdgeMarking.fixedCore_centralizes_componentRadical (d := d) (a := a) (t := t))
  have hZX := g.omega_bound a path.start_color (by
    rw [g.distance_constant a path.start_color]; change 0 < g.b d.radical; omega)
  have ht : color d.radical t=true := by
    apply Bool.eq_true_of_not_eq_false
    intro he
    exact adjacent_color_ne d.radical hat (path.start_color.trans he.symm)
  have hZt : Z d.radical t=omegaCenter (Q d.radical t) := by simp [Z,ht,edgeOmega]
  intro x hx
  have hxprod := hprod hx
  rw [←SetLike.mem_coe,coe_mul_of_left_le_normalizer_right _ _ hUD] at hxprod
  obtain ⟨u,hu,v,hv,rfl⟩ := hxprod
  have huC : u ∈ centralizer (componentRadical d a t : Set (FreeAmalgam d.radical)) := by
    have hh := (centralizer (componentRadical d a t : Set (FreeAmalgam d.radical))).mul_mem
      (hcentral hx) ((centralizer _).inv_mem (hDC hv))
    simpa only [mul_inv_cancel_right] using hh
  have huT : u ∈ centralizer (Q d.radical t : Set (FreeAmalgam d.radical)) := by
    have hB : componentRadical d a t ≤ centralizer ({u} : Set (FreeAmalgam d.radical)) :=
      fun b hb => mem_centralizer_singleton_iff.mpr (huC b hb)
    have hQ : Q d.radical a ≤ centralizer ({u} : Set (FreeAmalgam d.radical)) :=
      fun q hq => mem_centralizer_singleton_iff.mpr (hUaC hu q hq)
    have hh := sup_le hB hQ
    rw [c.componentRadical_sup_core g (by omega)] at hh
    exact fun y hy => mem_centralizer_singleton_iff.mp (hh hy)
  have huZt : u ∈ Z d.radical t := by
    rw [hZt]
    exact mem_omegaCenter_iff.mpr ⟨c.core_le_edge (omegaCenter_le _ (hZX (U_le_Z a hu))),
      (mem_omegaCenter_iff.mp (hZX (U_le_Z a hu))).2.1,huT⟩
  exact mul_mem (mem_sup_left huZt) (mem_sup_right hv)

/-- The whole radical moves the opposite overlap only into the complete
fixed core. This is the bound used in the final generator contradiction
of source (3.7)(3). -/
theorem source_three_noncontained_overlap_displacement
    (g : Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t)
    (hcritical : (Q d.radical z).relIndex (Z d.radical a)=2^n)
    (hnot : ¬ Q d.radical a ≤ Z d.radical a ⊔ Q d.radical z) :
    ⁅Z d.radical z ⊓ Q d.radical a,Q d.radical t⁆ ≤ fixedCore d.radical a := by
  have hle := (source_three_noncontained_overlap h d g hb hsat path hat hzt c c' hcritical hnot).2
  have ht : color d.radical t=true := by
    apply Bool.eq_true_of_not_eq_false
    intro he
    exact adjacent_color_ne d.radical hat (path.start_color.trans he.symm)
  have hZt : Z d.radical t=omegaCenter (Q d.radical t) := by simp [Z,ht,edgeOmega]
  apply (commutator_mono hle le_rfl).trans
  apply commutator_sup_le_of_relative_normal (Q d.radical t)
    (Z d.radical t) (fixedCore d.radical a) (Q d.radical t) (fixedCore d.radical a)
    c.fixedCore_normalized (hZt ▸ omegaCenter_le _) (inf_le_left.trans c.core_le_edge)
  · rw [commutator_eq_bot_iff_le_centralizer.mpr
      (show Z d.radical t ≤ centralizer (Q d.radical t : Set (FreeAmalgam d.radical)) from by
        rw [hZt]; exact fun x hx => (mem_omegaCenter_iff.mp hx).2.2)]
    exact bot_le
  · exact le_normalizer_iff_commutator_le_left.mp c.fixedCore_normalized

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo
