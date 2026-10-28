module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SourceSixSelection
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SourceFiveEquality
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SourceFourComparison
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Backward.Products.RelativeNormalizer

/-!
# The moved critical pair in MS93 (3.7)(6)

Realize the selected normalizer's action on the entire midpoint radical
inside the actual holomorph stabilizer. Its conjugate of the opposite
vertex has the same full attachment and radical displacement. Source (5)
therefore turns the selected movement into a genuine critical pair.

The selected involutions have the same coset modulo the original endpoint
core. Their commutator is a square in that core, hence lies in its Frattini
subgroup. The common displacement and the equality of the full attachments
put it in the opposite cover kernel; fixed-vector lifting makes it trivial.

For the resulting critical pair, either the critical image has order q,
or the same conjugated element escapes the opposite core. A field-power
centralizer count, squeezed by the actual midpoint index q squared and a
noncentral commuting witness, gives both indices q for the printed X and
the reciprocal fixed index q. No fixed attachment is removed.

This proves the construction through the X-index calculation on printed
p.876. The subsequent whole-core displacement contradiction, the order-q
existence conclusion, and the field-four endgame remain to be established.
Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (3.7)(6), printed p.876.
-/

public noncomputable section
open Subgroup
open scoped Pointwise commutatorElement IsMulCommutative
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo
open DistanceTwoRecognition ChapterB.QuasisimpleSource
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.Backward.Products
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

private theorem source_six_regular_conjugate_commutes
    (g : Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t)
    (hcritical : (2^n)^2 ≤ (Q d.radical z).relIndex (Z d.radical a))
    (x y : FreeAmalgam d.radical) (hx : x ∈ Z d.radical z)
    (hyT : y ∈ normalizer (Q d.radical t : Set (FreeAmalgam d.radical)))
    (hcoset : x⁻¹*(y*x*y⁻¹) ∈ Q d.radical a) : Commute x (y*x*y⁻¹) := by
  let := finite_stabilizer d.radical a
  let : Finite (Q d.radical a) := Finite.of_injective
    (inclusion (show Q d.radical a ≤ stabilizer d.radical a from fun _ hx => hx.1))
    (inclusion_injective _)
  let : Fact (IsPGroup 2 (Q d.radical a)) := ⟨Q_isPGroup d.radical
    (replacement_isPGroup h d) (replacement_core_le h d) a path.start_color⟩
  let := g.Z_elementary (by omega) z path.end_color
  have hx2 : x^2=1 := elemPow_eq_one_of_isElementaryAbelian x hx
  have hxi : x⁻¹=x := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hx2)
  let w := y*x*y⁻¹
  have hw2 : w^2=1 := by
    change ((MulAut.conj y) x)^2=1
    rw [←map_pow,hx2,map_one]
  have hwi : w⁻¹=w := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hw2)
  have hxw : x*w ∈ Q d.radical a := by simpa only [hxi] using hcoset
  have hphi : ⁅x,w⁆ ∈ (frattini (Q d.radical a)).map (Q d.radical a).subtype := by
    rw [commutatorElement_def,hxi,hwi]
    have he : x*w*x*w=(x*w)^2 := by simp only [pow_two,mul_assoc]
    rw [he]
    exact mem_map_of_mem (Q d.radical a).subtype
      (pth_power_mem_frattini_of_isPGroup (p := 2) (⟨x*w,hxw⟩ : Q d.radical a))
  have hpos : 0<criticalDistance d.radical z (g.exists_critical z path.end_color) := by
    rw [g.distance_constant z path.end_color]
    change 0<g.b d.radical
    omega
  have hZzT : Z d.radical z ≤ Q d.radical t :=
    ((g.omega_bound z path.end_color hpos).trans (omegaCenter_le _)).trans c'.core_le_edge
  have hwT : w ∈ Q d.radical t := (mem_normalizer_iff.mp hyT x).mp (hZzT hx)
  obtain ⟨_,_,_,_,hRa,hRz,_⟩ :=
    source_four_large_paired_geometry h d g hb hsat path hat hzt c c' hcritical
  have hcR : ⁅x,w⁆ ∈ ⁅Z d.radical a,Q d.radical t⁆ :=
    (hRz.trans hRa.symm) ▸ commutator_mem_commutator hx hwT
  have hcA : ⁅x,w⁆ ∈ U d.radical a ⊓
      centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) :=
    ⟨full_radical_Z_displacement_le_moving h d g (by omega) path.start_color c hcR,
      (frattini_le_fixedCore h d g hb path.start_color hphi).2⟩
  have hcAz : ⁅x,w⁆ ∈ U d.radical z ⊓
      centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical)) :=
    source_four_fixed_attachments h d g hb hsat path hat hzt c c' ▸ hcA
  have ht : color d.radical t=true := by
    apply Bool.eq_true_of_not_eq_false
    intro he
    exact adjacent_color_ne d.radical hzt (path.end_color.trans he.symm)
  have hZt : Z d.radical t=omegaCenter (Q d.radical t) := by simp [Z,ht,edgeOmega]
  have hcent : Z d.radical t ≤ centralizer (Q d.radical t : Set (FreeAmalgam d.radical)) := by
    rw [hZt]
    exact fun v hv => (mem_omegaCenter_iff.mp hv).2.2
  have hn : Z d.radical t ≤ normalizer (U d.radical z : Set (FreeAmalgam d.radical)) :=
    ((Sp4Four.edge_Z_le_endpoint d.radical path.end_color hzt).trans
      ((Z d.radical z).le_centralizer.trans (centralizer_le (U_le_Z z)))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hsplit := hx
  rw [Z_eq_moving_sup_edge_of_distance_two h d g hb path.end_color hzt,
    ←SetLike.mem_coe,coe_mul_of_right_le_normalizer_left _ _ hn] at hsplit
  obtain ⟨u,hu,v,hv,rfl⟩ := hsplit
  have hvalue : ⁅w,u*v⁆=⁅w,u⁆ := by
    rw [commutatorElement_mul_right_eq_mul_conj,
      commutatorElement_eq_one_iff_commute.mpr (hcent hv w hwT)]
    simp
  have hfix : ⁅w,u⁆ ∈ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical)) := by
    rw [←hvalue,←commutatorElement_inv]
    exact (centralizer _).inv_mem hcAz.2
  have hone := stabilizer_value_in_fixed_eq_one h d g (by omega) path.end_color c'
    w (c'.edge_le hwT) u hu hfix
  exact (commutatorElement_eq_one_iff_commute.mp (hvalue.trans hone)).symm

private theorem source_six_exists_moved_critical_pair
    (g : Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t)
    (hcritical : (2^n)^2 ≤ (Q d.radical z).relIndex (Z d.radical a)) :
    ∃ x ∈ Z d.radical z, x ∉ Q d.radical a ∧
      Z d.radical a ⊓ centralizer ({x} : Set (FreeAmalgam d.radical))=Z d.radical t ∧
      ∃ y ∈ stabilizer d.radical a, ∃ k ∈ stabilizer d.radical t,
        (∀ u ∈ Q d.radical t, (MulAut.conj k) u=(MulAut.conj y) u) ∧
        x⁻¹*(y*x*y⁻¹) ∈ Q d.radical a ∧
        Commute x (y*x*y⁻¹) ∧
        y ∉ normalizer (((Z d.radical z ⊔ Q d.radical a) : Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) ∧
        Nonempty (CriticalPath d.radical g (act d.radical k⁻¹ z) z) := by
  obtain ⟨x,hx,hxQ,hreg,y,hy,hyT,_,hcoset,hmove⟩ :=
    source_six_exists_moving_regular_element h d g hb hsat path hat hzt c c' hcritical
  obtain ⟨k,hk,he⟩ := holomorph_realizes t a path.start_color hat y hyT
  let v := act d.radical k⁻¹ z
  have hv : color d.radical v=false := (action_preserves_color _ _ _).trans path.end_color
  have hkt : act d.radical k⁻¹ t=t := (stabilizer d.radical t).inv_mem hk
  have hvt : Adjacent d.radical v t := by
    simpa only [hkt] using (adjacent_act_iff d.radical k⁻¹ z t).mpr hzt
  have hZQ (b : Vertex d.radical) (hbcol : color d.radical b=false) :
      Z d.radical b ≤ Q d.radical b :=
    (g.omega_bound b hbcol (by rw [g.distance_constant b hbcol]; change 0<g.b d.radical; omega)).trans
      (omegaCenter_le _)
  have hZaT := (hZQ a path.start_color).trans c.core_le_edge
  have hZzT := (hZQ z path.end_color).trans c'.core_le_edge
  have hZmap : Z d.radical v=(Z d.radical z).map (MulAut.conj y).toMonoidHom := by
    rw [Z_act,inv_inv]
    exact map_conj_eq_of_agree hZzT he
  have hne : Z d.radical v≠Z d.radical z := by
    intro hh
    apply hmove
    rw [mem_normalizer_iff_map_conj_eq]
    change (Z d.radical z ⊔ Q d.radical a).map (MulAut.conj y).toMonoidHom=_
    rw [Subgroup.map_sup,←hZmap,hh]
    congr 1
    exact mem_normalizer_iff_map_conj_eq.mp (Q_normalized d.radical a hy)
  let A := fun b : Vertex d.radical =>
    U d.radical b ⊓ centralizer (Ltilde d.radical b : Set (FreeAmalgam d.radical))
  have hAact (b : Vertex d.radical) (r : FreeAmalgam d.radical) :
      A (act d.radical r⁻¹ b)=(A b).map (MulAut.conj r).toMonoidHom := by
    dsimp only [A]
    rw [U_act,Ltilde_act,inv_inv,
      ←map_inf_centralizer_of_injective _ (MulAut.conj r).injective]
  have hAeq : A a=A z := source_four_fixed_attachments h d g hb hsat path hat hzt c c'
  have hAya : (A a).map (MulAut.conj y).toMonoidHom=A a := by
    rw [←hAact]
    have hya : act d.radical y⁻¹ a=a := (stabilizer d.radical a).inv_mem hy
    rw [hya]
  have hAv : A v=A z := by
    have hm : (A z).map (MulAut.conj k).toMonoidHom=(A z).map (MulAut.conj y).toMonoidHom :=
      map_conj_eq_of_agree ((inf_le_left.trans (U_le_Z z)).trans hZzT) he
    rw [hAact,hm,←hAeq,hAya]
  obtain ⟨_,_,_,_,hRa,hRz,_⟩ :=
    source_four_large_paired_geometry h d g hb hsat path hat hzt c c' hcritical
  have hR : ⁅Z d.radical z,Q d.radical t⁆=⁅Z d.radical a,Q d.radical t⁆ := hRz.trans hRa.symm
  have hdisplace : ⁅Z d.radical v,Q d.radical t⁆=⁅Z d.radical z,Q d.radical t⁆ := by
    have hTy : (Q d.radical t).map (MulAut.conj y).toMonoidHom=Q d.radical t :=
      mem_normalizer_iff_map_conj_eq.mp hyT
    have hZay : (Z d.radical a).map (MulAut.conj y).toMonoidHom=Z d.radical a :=
      mem_normalizer_iff_map_conj_eq.mp (Z_normalized d.radical a hy)
    calc
      _ = (⁅Z d.radical z,Q d.radical t⁆).map (MulAut.conj y).toMonoidHom := by
        rw [map_commutator,hTy,hZmap]
      _ = (⁅Z d.radical a,Q d.radical t⁆).map (MulAut.conj y).toMonoidHom := by rw [hR]
      _ = ⁅Z d.radical a,Q d.radical t⁆ := by rw [map_commutator,hTy,hZay]
      _ = _ := hR.symm
  have hedge := MSCentralOrbit.edgeCentralizerCondition d.radical (replacement_isPGroup h d)
    (replacement_core_le h d) (replacement_omegaOrbit_centralizer h d)
  let rev : CriticalPath d.radical g z a :=
    { start_color := path.end_color
      walk := path.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
      critical := critical_reverse d.radical g hedge a path.start_color
        (by rw [g.distance_constant a path.start_color]; change 0<g.b d.radical; omega)
        z path.end_color path.critical }
  obtain ⟨cv⟩ := exists_edgeMarking h d g (by omega) hv hvt
  have hnot : ¬ Z d.radical v ≤ Q d.radical z := by
    intro hin
    exact hne (source_five_Z_equality h d g hb hsat rev hzt hat hvt hv c' c cv
      hAv.symm hdisplace hin)
  have hd : (cosetGraph d.radical).dist v z=2 :=
    Escape.Propagation.neighbor_distance_two hv hvt hzt (by
      intro hvz
      exact hnot (hvz.symm ▸ hZQ z path.end_color))
  refine ⟨x,hx,hxQ,hreg,y,hy,k,hk,he,hcoset,
    source_six_regular_conjugate_commutes h d g hb hsat path hat hzt c c' hcritical x y hx hyT hcoset,hmove,
    ⟨CriticalPath.ofPair hv ⟨?_,hnot⟩⟩⟩
  rw [hd,g.distance_constant v hv]
  exact hb.symm

private theorem large_pair_centralizer_indices
    (g : Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t)
    (hcritical : (2^n)^2 ≤ (Q d.radical z).relIndex (Z d.radical a))
    (A : Subgroup (FreeAmalgam d.radical)) (hAZ : A ≤ Z d.radical z)
    (hAnot : ¬ A ≤ Q d.radical a)
    (x : FreeAmalgam d.radical) (hx : x ∈ Z d.radical a)
    (hxt : x ∉ Z d.radical t) (hxA : x ∈ centralizer (A : Set (FreeAmalgam d.radical))) :
    (Z d.radical a ⊓ centralizer (A : Set (FreeAmalgam d.radical))).relIndex (Z d.radical a)=2^n ∧
      (Q d.radical z).relIndex (Z d.radical a ⊓ centralizer (A : Set (FreeAmalgam d.radical)))=2^n := by
  let := finite_Z d.radical a
  have hZQ (b : Vertex d.radical) (hc : color d.radical b=false) : Z d.radical b ≤ Q d.radical b :=
    (g.omega_bound b hc (by rw [g.distance_constant b hc]; change 0<g.b d.radical; omega)).trans
      (omegaCenter_le _)
  have hAT := hAZ.trans ((hZQ z path.end_color).trans c'.core_le_edge)
  obtain ⟨⟨cv⟩,_,hai,_,_⟩ := source_four_large_paired_geometry h d g hb hsat path hat hzt c c' hcritical
  obtain ⟨hak,_,_,_⟩ := source_four_large_midpoint_kernels h d g hb hsat path hat hzt c c' hcritical
  let X := Z d.radical a ⊓ centralizer (A : Set (FreeAmalgam d.radical))
  let : Finite X := Finite.of_injective
    (inclusion (show X ≤ Z d.radical a from inf_le_left)) (inclusion_injective _)
  let r := Module.finrank cv.field.Carrier (Theory.SpecificGroups.SymplecticFour.displacementSpace
    (((commutator (Theory.SpecificGroups.SymplecticFour.Sp cv.field.Carrier)).subtype.comp cv.actor).comp
      (inclusion hAT)).range)
  have hindex : X.relIndex (Z d.radical a)=(2^n)^r := by
    rw [inf_relIndex_left]
    exact plane_cover_full_fixed_index h d g hb path.start_color hat cv A hAT
  have ht : color d.radical t=true := by
    apply Bool.eq_true_of_not_eq_false
    intro he
    exact adjacent_color_ne d.radical hat (path.start_color.trans he.symm)
  have hCt : Z d.radical t ≤ centralizer (Q d.radical t : Set (FreeAmalgam d.radical)) := by
    rw [show Z d.radical t=omegaCenter (Q d.radical t) by simp [Z,ht,edgeOmega]]
    exact fun y hy => (mem_omegaCenter_iff.mp hy).2.2
  have htX : Z d.radical t ≤ X := le_inf
    (Sp4Four.edge_Z_le_endpoint d.radical path.start_color hat) (hCt.trans (centralizer_le hAT))
  have hm := relIndex_mul_relIndex (Z d.radical t) X (Z d.radical a) htX inf_le_left
  rw [hai,hindex] at hm
  have hr0 : r≠0 := by
    intro hr
    have hZC : Z d.radical a ≤ centralizer (A : Set (FreeAmalgam d.radical)) := by
      have hi : X.relIndex (Z d.radical a)=1 := by rw [hindex,hr,pow_zero]
      exact (relIndex_eq_one.mp hi).trans inf_le_right
    apply hAnot
    intro y hy
    rw [←stabilizer_centralizer_moving_eq_core h d path.start_color]
    exact ⟨c.edge_le (hAT hy),fun u hu => (hZC (U_le_Z a hu) y hy).symm⟩
  have hstep : 2 ≤ (Z d.radical t).relIndex X := by
    have hn : (Z d.radical t).relIndex X≠1 := by
      intro he
      exact hxt (relIndex_eq_one.mp he ⟨hx,hxA⟩)
    have hp : 0<(Z d.radical t).relIndex X := Nat.pos_of_ne_zero index_ne_zero_of_finite
    omega
  have hq : 1<2^n := one_lt_pow₀ (by decide : 1<(2:ℕ)) (by have := h.nonbinary; omega)
  have hr : r=1 := by
    by_contra hn
    have hh := Nat.pow_le_pow_right (by omega : 0<2^n) (show 2≤r by omega)
    nlinarith only [hm,hstep,hh,sq_pos_of_pos (show 0<2^n by omega)]
  have hXi : X.relIndex (Z d.radical a)=2^n := by rw [hindex,hr,pow_one]
  have hk : X ⊓ Q d.radical z=Z d.radical t := by
    apply le_antisymm
    · exact (inf_le_inf_right _ (show X ≤ Z d.radical a from inf_le_left)).trans_eq hak
    · exact le_inf htX ((Sp4Four.edge_Z_le_endpoint d.radical path.end_color hzt).trans
        (hZQ z path.end_color))
  refine ⟨hXi,?_⟩
  rw [←inf_relIndex_left,hk]
  rw [hr,pow_one] at hm
  nlinarith only [hm,hq]

/-- The literal source-(6) critical pair and its centralizer alternative.
The same regular element, conjugator and induced midpoint action are retained. -/
theorem source_six_field_pair_or_centralizer_configuration
    (g : Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t)
    (hcritical : (2^n)^2 ≤ (Q d.radical z).relIndex (Z d.radical a)) :
    ∃ x ∈ Z d.radical z, x ∉ Q d.radical a ∧
      Z d.radical a ⊓ centralizer ({x} : Set (FreeAmalgam d.radical))=Z d.radical t ∧
      ∃ y ∈ stabilizer d.radical a, ∃ k ∈ stabilizer d.radical t,
        (∀ u ∈ Q d.radical t, (MulAut.conj k) u=(MulAut.conj y) u) ∧
        x⁻¹*(y*x*y⁻¹) ∈ Q d.radical a ∧ Commute x (y*x*y⁻¹) ∧
        y ∉ normalizer (((Z d.radical z ⊔ Q d.radical a) : Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) ∧
        Nonempty (CriticalPath d.radical g (act d.radical k⁻¹ z) z) ∧
        ((Q d.radical z).relIndex (Z d.radical (act d.radical k⁻¹ z))=2^n ∨
          (y*x*y⁻¹ ∉ Q d.radical z ∧
            (Z d.radical z ⊓ centralizer ({y*x*y⁻¹} : Set (FreeAmalgam d.radical))).relIndex
              (Z d.radical z)=2^n ∧
            (Q d.radical (act d.radical k⁻¹ z)).relIndex
              (Z d.radical z ⊓ centralizer ({y*x*y⁻¹} : Set (FreeAmalgam d.radical)))=2^n ∧
            (centralizer ((Z d.radical z ⊓ centralizer ({y*x*y⁻¹} : Set (FreeAmalgam d.radical))) :
              Set (FreeAmalgam d.radical))).relIndex (Z d.radical (act d.radical k⁻¹ z))=2^n)) := by
  obtain ⟨x,hx,hxQ,hreg,y,hy,k,hk,he,hcoset,hcomm,hmove,⟨p⟩⟩ :=
    source_six_exists_moved_critical_pair h d g hb hsat path hat hzt c c' hcritical
  refine ⟨x,hx,hxQ,hreg,y,hy,k,hk,he,hcoset,hcomm,hmove,⟨p⟩,?_⟩
  by_cases hc : (2^n)^2 ≤ (Q d.radical z).relIndex (Z d.radical (act d.radical k⁻¹ z))
  swap
  · exact Or.inl (replacement_critical_indices_eq_field_of_small h d p (by omega) (lt_of_not_ge hc)).1
  apply Or.inr
  let v := act d.radical k⁻¹ z
  let w := y*x*y⁻¹
  have hv : color d.radical v=false := p.start_color
  have hkt : act d.radical k⁻¹ t=t := (stabilizer d.radical t).inv_mem hk
  have hvt : Adjacent d.radical v t := by
    simpa only [hkt] using (adjacent_act_iff d.radical k⁻¹ z t).mpr hzt
  obtain ⟨cv⟩ := exists_edgeMarking h d g (by omega) hv hvt
  have hZQ (b : Vertex d.radical) (hcol : color d.radical b=false) : Z d.radical b ≤ Q d.radical b :=
    (g.omega_bound b hcol (by rw [g.distance_constant b hcol]; change 0<g.b d.radical; omega)).trans
      (omegaCenter_le _)
  have hxT := c'.core_le_edge (hZQ z path.end_color hx)
  have hxt : x ∉ Z d.radical t := fun ht => hxQ (hZQ a path.start_color
    (Sp4Four.edge_Z_le_endpoint d.radical path.start_color hat ht))
  have hw : w=(MulAut.conj k) x := (he x hxT).symm
  have hwZ : w ∈ Z d.radical v := by
    rw [Z_act,inv_inv,hw]
    exact mem_map_of_mem (MulAut.conj k).toMonoidHom hx
  have hwt : w ∉ Z d.radical t := by
    intro hwt
    apply hxt
    rw [hw] at hwt
    exact (mem_normalizer_iff.mp (Z_normalized d.radical t hk) x).mpr hwt
  obtain ⟨hvk,hzk,_,hzi⟩ := source_four_large_midpoint_kernels h d g hb hsat p hvt hzt cv c' hc
  have hwQ : w ∉ Q d.radical z := fun hq => hwt (hvk ▸ (show w ∈ Z d.radical v ⊓ Q d.radical z from ⟨hwZ,hq⟩))
  have hedge := MSCentralOrbit.edgeCentralizerCondition d.radical (replacement_isPGroup h d)
    (replacement_core_le h d) (replacement_omegaOrbit_centralizer h d)
  let rev : CriticalPath d.radical g z v :=
    { start_color := path.end_color
      walk := p.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,p.shortest,SimpleGraph.dist_comm]
      critical := critical_reverse d.radical g hedge v hv
        (by rw [g.distance_constant v hv]; change 0<g.b d.radical; omega)
        z path.end_color p.critical }
  have hC : centralizer (zpowers w : Set (FreeAmalgam d.radical))=
      centralizer ({w} : Set (FreeAmalgam d.radical)) := by
    rw [zpowers_eq_closure,centralizer_closure]
  have hi := large_pair_centralizer_indices h d g hb hsat rev hzt hvt c' cv hzi.ge
    (zpowers w) (zpowers_le.mpr hwZ) (fun hn => hwQ (hn (mem_zpowers w)))
    x hx hxt (by rw [hC]; exact mem_centralizer_singleton_iff.mpr hcomm.eq)
  rw [hC] at hi
  let X := Z d.radical z ⊓ centralizer ({w} : Set (FreeAmalgam d.radical))
  have hXnot : ¬ X ≤ Q d.radical v := by
    intro hh
    have hh' := relIndex_eq_one.mpr hh
    have hq : 1<2^n := one_lt_pow₀ (by decide : 1<(2:ℕ)) (by have := h.nonbinary; omega)
    have hh'' : (Q d.radical v).relIndex X=2^n := hi.2
    omega
  have hwX : w ∈ centralizer (X : Set (FreeAmalgam d.radical)) := by
    intro u hu
    exact (mem_centralizer_singleton_iff.mp hu.2)
  have hi' := (large_pair_centralizer_indices h d g hb hsat p hvt hzt cv c' hc
    X inf_le_left hXnot w hwZ hwt hwX).1
  rw [inf_relIndex_left] at hi'
  exact ⟨hwQ,hi.1,hi.2,hi'⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo
