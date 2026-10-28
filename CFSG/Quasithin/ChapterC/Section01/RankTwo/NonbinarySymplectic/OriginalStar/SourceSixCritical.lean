module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceSixSelection
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceFourComparison
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Backward.Products.RelativeNormalizer
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceFiveCore
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceFourEscape

/-!
# Original source-(6) moved critical pair

The moving normalizer acts through the actual midpoint holomorph. Source (5)
forces its moved neighboring vertex into a critical pair, with both full
attachments retained. The same regular element gives the field-sized
centralizer indices in the large branch.

Source: MS93 (3.7)(6), printed p.876. Private imports are intentional reuse
of the original core and plane-cover calculations within this proof chain.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
open scoped Pointwise commutatorElement IsMulCommutative
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar
open DistanceTwoRecognition ChapterB.QuasisimpleSource
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.Backward.Products
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (hshort : IsShort K) (hinner : K ⊔ pCore 2 H = ⊤)
variable (hnsyl : ¬ ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
  (R.subgroupOf K).map (componentProjection h))
include h hshort hinner hnsyl

private theorem original_source_six_regular_conjugate_commutes
    (g : Geometry R) (hb : g.b R=2)
    {a z t : Vertex R} (path : CriticalPath R g a z)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (hcritical : (2^n)^2 ≤ (Q R z).relIndex (Z R a))
    (x y : FreeAmalgam R) (hx : x ∈ Z R z)
    (hyT : y ∈ normalizer (Q R t : Set (FreeAmalgam R)))
    (hcoset : x⁻¹*(y*x*y⁻¹) ∈ Q R a) : Commute x (y*x*y⁻¹) := by
  let := finite_stabilizer R a
  let : Finite (Q R a) := Finite.of_injective
    (inclusion (show Q R a ≤ stabilizer R a from fun _ hx => hx.1))
    (inclusion_injective _)
  let : Fact (IsPGroup 2 (Q R a)) := ⟨Q_isPGroup R
    h.radical.isPGroup h.radical.twoCore_le a path.start_color⟩
  let := g.Z_elementary (by omega) z path.end_color
  have hx2 : x^2=1 := elemPow_eq_one_of_isElementaryAbelian x hx
  have hxi : x⁻¹=x := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hx2)
  let w := y*x*y⁻¹
  have hw2 : w^2=1 := by
    change ((MulAut.conj y) x)^2=1
    rw [←map_pow,hx2,map_one]
  have hwi : w⁻¹=w := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hw2)
  have hxw : x*w ∈ Q R a := by simpa only [hxi] using hcoset
  have hphi : ⁅x,w⁆ ∈ (frattini (Q R a)).map (Q R a).subtype := by
    rw [commutatorElement_def,hxi,hwi]
    have he : x*w*x*w=(x*w)^2 := by simp only [pow_two,mul_assoc]
    rw [he]
    exact mem_map_of_mem (Q R a).subtype
      (pth_power_mem_frattini_of_isPGroup (p := 2) (⟨x*w,hxw⟩ : Q R a))
  have hpos : 0<criticalDistance R z (g.exists_critical z path.end_color) := by
    rw [g.distance_constant z path.end_color]
    change 0<g.b R
    omega
  have hZzT : Z R z ≤ Q R t :=
    ((g.omega_bound z path.end_color hpos).trans (omegaCenter_le _)).trans (original_core_le_edge R path.end_color hzt)
  have hwT : w ∈ Q R t := (mem_normalizer_iff.mp hyT x).mp (hZzT hx)
  obtain ⟨_,_,_,_,hRa,hRz,_⟩ :=
    original_source_four_large_paired_geometry h hshort hinner hnsyl g hb path hat hzt hcritical
  have hcR : ⁅x,w⁆ ∈ ⁅Z R a,Q R t⁆ :=
    (hRz.trans hRa.symm) ▸ commutator_mem_commutator hx hwT
  have hcA : ⁅x,w⁆ ∈ U R a ⊓
      centralizer (Ltilde R a : Set (FreeAmalgam R)) :=
    ⟨original_full_radical_Z_displacement_le_moving h hinner path.start_color hat hcR,
      (original_short_frattini_le_fixedCore h hshort path.start_color hphi).2⟩
  have hcAz : ⁅x,w⁆ ∈ U R z ⊓
      centralizer (Ltilde R z : Set (FreeAmalgam R)) :=
    original_source_four_fixed_attachments h hshort hinner hnsyl g hb path hat hzt ▸ hcA
  have ht : color R t=true := by
    apply Bool.eq_true_of_not_eq_false
    intro he
    exact adjacent_color_ne R hzt (path.end_color.trans he.symm)
  have hZt : Z R t=omegaCenter (Q R t) := by simp [Z,ht,edgeOmega]
  have hcent : Z R t ≤ centralizer (Q R t : Set (FreeAmalgam R)) := by
    rw [hZt]
    exact fun v hv => (mem_omegaCenter_iff.mp hv).2.2
  have hn : Z R t ≤ normalizer (U R z : Set (FreeAmalgam R)) :=
    ((Sp4Four.edge_Z_le_endpoint R path.end_color hzt).trans
      ((Z R z).le_centralizer.trans (centralizer_le (U_le_Z z)))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hsplit := hx
  rw [original_Z_eq_moving_sup_edge h hshort hinner g hb path.end_color hzt,
    ←SetLike.mem_coe,coe_mul_of_right_le_normalizer_left _ _ hn] at hsplit
  obtain ⟨u,hu,v,hv,rfl⟩ := hsplit
  have hvalue : ⁅w,u*v⁆=⁅w,u⁆ := by
    rw [commutatorElement_mul_right_eq_mul_conj,
      commutatorElement_eq_one_iff_commute.mpr (hcent hv w hwT)]
    simp
  have hfix : ⁅w,u⁆ ∈ centralizer (Ltilde R z : Set (FreeAmalgam R)) := by
    rw [←hvalue,←commutatorElement_inv]
    exact (centralizer _).inv_mem hcAz.2
  have hone := original_stabilizer_value_in_fixed_eq_one h hinner path.end_color
    w ((original_edge_le_stabilizer R hzt) hwT) u hu hfix
  exact (commutatorElement_eq_one_iff_commute.mp (hvalue.trans hone)).symm

private theorem original_source_six_exists_moved_critical_pair
    (g : Geometry R) (hb : g.b R=2)
    {a z t : Vertex R} (path : CriticalPath R g a z)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (hcritical : (2^n)^2 ≤ (Q R z).relIndex (Z R a)) :
    ∃ x ∈ Z R z, x ∉ Q R a ∧
      Z R a ⊓ centralizer ({x} : Set (FreeAmalgam R))=Z R t ∧
      ∃ y ∈ stabilizer R a, ∃ k ∈ stabilizer R t,
        (∀ u ∈ Q R t, (MulAut.conj k) u=(MulAut.conj y) u) ∧
        x⁻¹*(y*x*y⁻¹) ∈ Q R a ∧
        Commute x (y*x*y⁻¹) ∧
        y ∉ normalizer (((Z R z ⊔ Q R a) : Subgroup (FreeAmalgam R)) : Set (FreeAmalgam R)) ∧
        Nonempty (CriticalPath R g (act R k⁻¹ z) z) := by
  obtain ⟨x,hx,hxQ,hreg,y,hy,hyT,_,hcoset,hmove⟩ :=
    original_source_six_exists_moving_regular_element h hshort hinner hnsyl g hb path hat hzt hcritical
  obtain ⟨k,hk,he⟩ := holomorph_realizes t a path.start_color hat y hyT
  let v := act R k⁻¹ z
  have hv : color R v=false := (action_preserves_color _ _ _).trans path.end_color
  have hkt : act R k⁻¹ t=t := (stabilizer R t).inv_mem hk
  have hvt : Adjacent R v t := by
    simpa only [hkt] using (adjacent_act_iff R k⁻¹ z t).mpr hzt
  have hZQ (b : Vertex R) (hbcol : color R b=false) :
      Z R b ≤ Q R b :=
    (g.omega_bound b hbcol (by rw [g.distance_constant b hbcol]; change 0<g.b R; omega)).trans
      (omegaCenter_le _)
  have hZaT := (hZQ a path.start_color).trans (original_core_le_edge R path.start_color hat)
  have hZzT := (hZQ z path.end_color).trans (original_core_le_edge R path.end_color hzt)
  have hZmap : Z R v=(Z R z).map (MulAut.conj y).toMonoidHom := by
    rw [Z_act,inv_inv]
    exact map_conj_eq_of_agree hZzT he
  have hne : Z R v≠Z R z := by
    intro hh
    apply hmove
    rw [mem_normalizer_iff_map_conj_eq]
    change (Z R z ⊔ Q R a).map (MulAut.conj y).toMonoidHom=_
    rw [Subgroup.map_sup,←hZmap,hh]
    congr 1
    exact mem_normalizer_iff_map_conj_eq.mp (Q_normalized R a hy)
  let A := fun b : Vertex R =>
    U R b ⊓ centralizer (Ltilde R b : Set (FreeAmalgam R))
  have hAact (b : Vertex R) (r : FreeAmalgam R) :
      A (act R r⁻¹ b)=(A b).map (MulAut.conj r).toMonoidHom := by
    dsimp only [A]
    rw [U_act,Ltilde_act,inv_inv,
      ←map_inf_centralizer_of_injective _ (MulAut.conj r).injective]
  have hAeq : A a=A z := original_source_four_fixed_attachments h hshort hinner hnsyl g hb path hat hzt
  have hAya : (A a).map (MulAut.conj y).toMonoidHom=A a := by
    rw [←hAact]
    have hya : act R y⁻¹ a=a := (stabilizer R a).inv_mem hy
    rw [hya]
  have hAv : A v=A z := by
    have hm : (A z).map (MulAut.conj k).toMonoidHom=(A z).map (MulAut.conj y).toMonoidHom :=
      map_conj_eq_of_agree ((inf_le_left.trans (U_le_Z z)).trans hZzT) he
    rw [hAact,hm,←hAeq,hAya]
  obtain ⟨_,_,_,_,hRa,hRz,_⟩ :=
    original_source_four_large_paired_geometry h hshort hinner hnsyl g hb path hat hzt hcritical
  have hR : ⁅Z R z,Q R t⁆=⁅Z R a,Q R t⁆ := hRz.trans hRa.symm
  have hdisplace : ⁅Z R v,Q R t⁆=⁅Z R z,Q R t⁆ := by
    have hTy : (Q R t).map (MulAut.conj y).toMonoidHom=Q R t :=
      mem_normalizer_iff_map_conj_eq.mp hyT
    have hZay : (Z R a).map (MulAut.conj y).toMonoidHom=Z R a :=
      mem_normalizer_iff_map_conj_eq.mp (Z_normalized R a hy)
    calc
      _ = (⁅Z R z,Q R t⁆).map (MulAut.conj y).toMonoidHom := by
        rw [map_commutator,hTy,hZmap]
      _ = (⁅Z R a,Q R t⁆).map (MulAut.conj y).toMonoidHom := by rw [hR]
      _ = ⁅Z R a,Q R t⁆ := by rw [map_commutator,hTy,hZay]
      _ = _ := hR.symm
  have hedge := MSCentralOrbit.edgeCentralizerCondition R h.radical.isPGroup
    h.radical.twoCore_le h.omegaOrbit_centralizer
  let rev : CriticalPath R g z a :=
    { start_color := path.end_color
      walk := path.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
      critical := critical_reverse R g hedge a path.start_color
        (by rw [g.distance_constant a path.start_color]; change 0<g.b R; omega)
        z path.end_color path.critical }
  have hnot : ¬ Z R v ≤ Q R z := by
    intro hin
    exact hne (original_source_five_Z_equality h hshort hinner hnsyl g hb rev hzt hat hvt hv
      hAv.symm hdisplace hin)
  have hd : (cosetGraph R).dist v z=2 :=
    Escape.Propagation.neighbor_distance_two hv hvt hzt (by
      intro hvz
      exact hnot (hvz.symm ▸ hZQ z path.end_color))
  refine ⟨x,hx,hxQ,hreg,y,hy,k,hk,he,hcoset,
    original_source_six_regular_conjugate_commutes h hshort hinner hnsyl g hb path hat hzt hcritical x y hx hyT hcoset,hmove,
    ⟨CriticalPath.ofPair hv ⟨?_,hnot⟩⟩⟩
  rw [hd,g.distance_constant v hv]
  exact hb.symm

private theorem large_pair_centralizer_indices
    (g : Geometry R) (hb : g.b R=2)
    {a z t : Vertex R} (path : CriticalPath R g a z)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (hcritical : (2^n)^2 ≤ (Q R z).relIndex (Z R a))
    (A : Subgroup (FreeAmalgam R)) (hAZ : A ≤ Z R z)
    (hAnot : ¬ A ≤ Q R a)
    (x : FreeAmalgam R) (hx : x ∈ Z R a)
    (hxt : x ∉ Z R t) (hxA : x ∈ centralizer (A : Set (FreeAmalgam R))) :
    (Z R a ⊓ centralizer (A : Set (FreeAmalgam R))).relIndex (Z R a)=2^n ∧
      (Q R z).relIndex (Z R a ⊓ centralizer (A : Set (FreeAmalgam R)))=2^n := by
  let := finite_Z R a
  have hZQ (b : Vertex R) (hc : color R b=false) : Z R b ≤ Q R b :=
    (g.omega_bound b hc (by rw [g.distance_constant b hc]; change 0<g.b R; omega)).trans
      (omegaCenter_le _)
  have hAT := hAZ.trans ((hZQ z path.end_color).trans (original_core_le_edge R path.end_color hzt))
  obtain ⟨⟨cv⟩,_,hai,_,_⟩ := original_source_four_large_paired_geometry h hshort hinner hnsyl g hb path hat hzt hcritical
  obtain ⟨hak,_,_,_⟩ := original_source_four_large_midpoint_kernels h hshort hinner hnsyl g hb path hat hzt hcritical
  let X := Z R a ⊓ centralizer (A : Set (FreeAmalgam R))
  let : Finite X := Finite.of_injective
    (inclusion (show X ≤ Z R a from inf_le_left)) (inclusion_injective _)
  let r := Module.finrank cv.field.Carrier (Theory.SpecificGroups.SymplecticFour.displacementSpace
    (((commutator (Theory.SpecificGroups.SymplecticFour.Sp cv.field.Carrier)).subtype.comp cv.actor).comp
      (inclusion hAT)).range)
  have hindex : X.relIndex (Z R a)=(2^n)^r := by
    rw [inf_relIndex_left]
    exact plane_cover_full_fixed_index h hshort hinner g hb path.start_color hat cv A hAT
  have ht : color R t=true := by
    apply Bool.eq_true_of_not_eq_false
    intro he
    exact adjacent_color_ne R hat (path.start_color.trans he.symm)
  have hCt : Z R t ≤ centralizer (Q R t : Set (FreeAmalgam R)) := by
    rw [show Z R t=omegaCenter (Q R t) by simp [Z,ht,edgeOmega]]
    exact fun y hy => (mem_omegaCenter_iff.mp hy).2.2
  have htX : Z R t ≤ X := le_inf
    (Sp4Four.edge_Z_le_endpoint R path.start_color hat) (hCt.trans (centralizer_le hAT))
  have hm := relIndex_mul_relIndex (Z R t) X (Z R a) htX inf_le_left
  rw [hai,hindex] at hm
  have hr0 : r≠0 := by
    intro hr
    have hZC : Z R a ≤ centralizer (A : Set (FreeAmalgam R)) := by
      have hi : X.relIndex (Z R a)=1 := by rw [hindex,hr,pow_zero]
      exact (relIndex_eq_one.mp hi).trans inf_le_right
    apply hAnot
    intro y hy
    rw [←original_stabilizer_centralizer_moving_eq_core h path.start_color]
    exact ⟨(original_edge_le_stabilizer R hat) (hAT hy),fun u hu => (hZC (U_le_Z a hu) y hy).symm⟩
  have hstep : 2 ≤ (Z R t).relIndex X := by
    have hn : (Z R t).relIndex X≠1 := by
      intro he
      exact hxt (relIndex_eq_one.mp he ⟨hx,hxA⟩)
    have hp : 0<(Z R t).relIndex X := Nat.pos_of_ne_zero index_ne_zero_of_finite
    omega
  have hq : 1<2^n := one_lt_pow₀ (by decide : 1<(2:ℕ)) (by have := h.nonbinary; omega)
  have hr : r=1 := by
    by_contra hn
    have hh := Nat.pow_le_pow_right (by omega : 0<2^n) (show 2≤r by omega)
    nlinarith only [hm,hstep,hh,sq_pos_of_pos (show 0<2^n by omega)]
  have hXi : X.relIndex (Z R a)=2^n := by rw [hindex,hr,pow_one]
  have hk : X ⊓ Q R z=Z R t := by
    apply le_antisymm
    · exact (inf_le_inf_right _ (show X ≤ Z R a from inf_le_left)).trans_eq hak
    · exact le_inf htX ((Sp4Four.edge_Z_le_endpoint R path.end_color hzt).trans
        (hZQ z path.end_color))
  refine ⟨hXi,?_⟩
  rw [←inf_relIndex_left,hk]
  rw [hr,pow_one] at hm
  nlinarith only [hm,hq]

/-- The literal source-(6) critical pair and its centralizer alternative.
The same regular element, conjugator and induced midpoint action are retained. -/
theorem original_source_six_field_pair_or_centralizer_configuration
    (g : Geometry R) (hb : g.b R=2)
    {a z t : Vertex R} (path : CriticalPath R g a z)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (hcritical : (2^n)^2 ≤ (Q R z).relIndex (Z R a)) :
    ∃ x ∈ Z R z, x ∉ Q R a ∧
      Z R a ⊓ centralizer ({x} : Set (FreeAmalgam R))=Z R t ∧
      ∃ y ∈ stabilizer R a, ∃ k ∈ stabilizer R t,
        (∀ u ∈ Q R t, (MulAut.conj k) u=(MulAut.conj y) u) ∧
        x⁻¹*(y*x*y⁻¹) ∈ Q R a ∧ Commute x (y*x*y⁻¹) ∧
        y ∉ normalizer (((Z R z ⊔ Q R a) : Subgroup (FreeAmalgam R)) : Set (FreeAmalgam R)) ∧
        Nonempty (CriticalPath R g (act R k⁻¹ z) z) ∧
        ((Q R z).relIndex (Z R (act R k⁻¹ z))=2^n ∨
          (y*x*y⁻¹ ∉ Q R z ∧
            (Z R z ⊓ centralizer ({y*x*y⁻¹} : Set (FreeAmalgam R))).relIndex
              (Z R z)=2^n ∧
            (Q R (act R k⁻¹ z)).relIndex
              (Z R z ⊓ centralizer ({y*x*y⁻¹} : Set (FreeAmalgam R)))=2^n ∧
            (centralizer ((Z R z ⊓ centralizer ({y*x*y⁻¹} : Set (FreeAmalgam R))) :
              Set (FreeAmalgam R))).relIndex (Z R (act R k⁻¹ z))=2^n)) := by
  obtain ⟨x,hx,hxQ,hreg,y,hy,k,hk,he,hcoset,hcomm,hmove,⟨p⟩⟩ :=
    original_source_six_exists_moved_critical_pair h hshort hinner hnsyl g hb path hat hzt hcritical
  refine ⟨x,hx,hxQ,hreg,y,hy,k,hk,he,hcoset,hcomm,hmove,⟨p⟩,?_⟩
  by_cases hc : (2^n)^2 ≤ (Q R z).relIndex (Z R (act R k⁻¹ z))
  swap
  · exact Or.inl (by
      simpa only [h.field_card] using (h.original_small_critical_indices_eq_field p (by omega)
        (by simpa only [h.field_card] using lt_of_not_ge hc)).1)
  apply Or.inr
  let v := act R k⁻¹ z
  let w := y*x*y⁻¹
  have hv : color R v=false := p.start_color
  have hkt : act R k⁻¹ t=t := (stabilizer R t).inv_mem hk
  have hvt : Adjacent R v t := by
    simpa only [hkt] using (adjacent_act_iff R k⁻¹ z t).mpr hzt
  have hZQ (b : Vertex R) (hcol : color R b=false) : Z R b ≤ Q R b :=
    (g.omega_bound b hcol (by rw [g.distance_constant b hcol]; change 0<g.b R; omega)).trans
      (omegaCenter_le _)
  have hxT := (original_core_le_edge R path.end_color hzt) (hZQ z path.end_color hx)
  have hxt : x ∉ Z R t := fun ht => hxQ (hZQ a path.start_color
    (Sp4Four.edge_Z_le_endpoint R path.start_color hat ht))
  have hw : w=(MulAut.conj k) x := (he x hxT).symm
  have hwZ : w ∈ Z R v := by
    rw [Z_act,inv_inv,hw]
    exact mem_map_of_mem (MulAut.conj k).toMonoidHom hx
  have hwt : w ∉ Z R t := by
    intro hwt
    apply hxt
    rw [hw] at hwt
    exact (mem_normalizer_iff.mp (Z_normalized R t hk) x).mpr hwt
  obtain ⟨hvk,hzk,_,hzi⟩ := original_source_four_large_midpoint_kernels h hshort hinner hnsyl g hb p hvt hzt hc
  have hwQ : w ∉ Q R z := fun hq => hwt (hvk ▸ (show w ∈ Z R v ⊓ Q R z from ⟨hwZ,hq⟩))
  have hedge := MSCentralOrbit.edgeCentralizerCondition R h.radical.isPGroup
    h.radical.twoCore_le h.omegaOrbit_centralizer
  let rev : CriticalPath R g z v :=
    { start_color := path.end_color
      walk := p.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,p.shortest,SimpleGraph.dist_comm]
      critical := critical_reverse R g hedge v hv
        (by rw [g.distance_constant v hv]; change 0<g.b R; omega)
        z path.end_color p.critical }
  have hC : centralizer (zpowers w : Set (FreeAmalgam R))=
      centralizer ({w} : Set (FreeAmalgam R)) := by
    rw [zpowers_eq_closure,centralizer_closure]
  have hi := large_pair_centralizer_indices h hshort hinner hnsyl g hb rev hzt hvt hzi.ge
    (zpowers w) (zpowers_le.mpr hwZ) (fun hn => hwQ (hn (mem_zpowers w)))
    x hx hxt (by rw [hC]; exact mem_centralizer_singleton_iff.mpr hcomm.eq)
  rw [hC] at hi
  let X := Z R z ⊓ centralizer ({w} : Set (FreeAmalgam R))
  have hXnot : ¬ X ≤ Q R v := by
    intro hh
    have hh' := relIndex_eq_one.mpr hh
    have hq : 1<2^n := one_lt_pow₀ (by decide : 1<(2:ℕ)) (by have := h.nonbinary; omega)
    have hh'' : (Q R v).relIndex X=2^n := hi.2
    omega
  have hwX : w ∈ centralizer (X : Set (FreeAmalgam R)) := by
    intro u hu
    exact (mem_centralizer_singleton_iff.mp hu.2)
  have hi' := (large_pair_centralizer_indices h hshort hinner hnsyl g hb p hvt hzt hc
    X inf_le_left hXnot w hwZ hwt hwX).1
  rw [inf_relIndex_left] at hi'
  exact ⟨hwQ,hi.1,hi.2,hi'⟩


end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar
