module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceSixDisplacement
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SourceSixCentralizer
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceFourEscape
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceTwoFixedCoreQuadratic
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceFiveCore

/-!
# The whole-core contradiction on the original nonsylow star

The fixed hyperplane centralizer has index q on the entire opposite core.
Four conjugates of its root image generate the original component, forcing
that core to be its moving layer times its full component-fixed core.
Paired attachment equality and regularity then put the selected escaping
conjugate in the opposite core, a contradiction.

Thus the original star has a critical pair of field-sized image, and every
component vertex has the whole-core decomposition Q = U D. All radicals,
centers, attachments and quotient markings remain those of the original
input; no characteristic replacement or minimum saturation is introduced.

Source: Meierfrankenfeld--Stellmacher (1993), (3.7)(6), printed p.876.
-/

public noncomputable section
open scoped IsMulCommutative commutatorElement
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.OneCohomology Representation.SymplecticFourOrthogonalCover
open Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar
open DistanceTwoRecognition ChapterB.QuasisimpleSource
open SaturatedDistanceTwo (RadicalPlaneCover whole_core_index_bound_of_conjugates)
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (hshort : IsShort K) (hinner : K ⊔ pCore 2 H = ⊤)
include h hshort hinner

/-- Evaluation on the full fixed hyperplane bounds an arbitrary subgroup of
its radical. The denominator retains the complete cover attachment. -/
theorem original_plane_cover_hyperplane_centralizer_bound
    (g : Geometry R) (hb : g.b R=2)
    {z t : Vertex R} (hz : color R z=false)
    (hzt : Adjacent R z t)
    (cv : RadicalPlaneCover R (originalMovedSection h) n z t)
    (Y B : Subgroup (FreeAmalgam R)) (hY : Y ≤ Q R t) (hB : B ≤ Q R t)
    (hi : (centralizer (Y : Set (FreeAmalgam R))).relIndex (Z R z)=2^n) :
    (centralizer ((Z R z ⊓ centralizer (Y : Set (FreeAmalgam R))) :
      Set (FreeAmalgam R))).relIndex B ≤
        (U R z ⊓ centralizer (Ltilde R z : Set (FreeAmalgam R))).relIndex
          ⁅B,Z R z ⊓ centralizer (Y : Set (FreeAmalgam R))⁆ := by
  have hm := plane_cover_full_fixed_index h hshort hinner g hb hz hzt cv Y hY
  have hdim : Module.finrank cv.field.Carrier (displacementSpace
      (((commutator (Sp cv.field.Carrier)).subtype.comp cv.actor).comp (inclusion hY)).range)=1 :=
    Nat.pow_right_injective
      (one_lt_pow₀ (by decide : 1<(2:ℕ)) (by have := h.nonbinary; omega))
      (hm.symm.trans (hi.trans (pow_one _).symm))
  have ht : color R t=true := by
    apply Bool.eq_true_of_not_eq_false
    intro he
    exact adjacent_color_ne R hzt (hz.trans he.symm)
  have hCT : Z R t ≤ centralizer (Q R t : Set (FreeAmalgam R)) := by
    rw [show Z R t=omegaCenter (Q R t) by simp [Z,ht,edgeOmega]]
    exact fun _ hx => (mem_omegaCenter_iff.mp hx).2.2
  let := g.Z_elementary (by omega) z hz
  let := finite_stabilizer R z
  let : Finite B := Finite.of_injective (inclusion (hB.trans cv.edge_le)) (inclusion_injective _)
  obtain ⟨k,hk⟩ := cv.plane_image
  exact fixed_hyperplane_bound
    (MovedSection.coverAction (originalMovedSection h) cv.equiv)
    (MovedSection.coverProjection (originalMovedSection h) cv.equiv) cv.cover
    (U R z) (Z R z) (Z R t) (Q R t) Y B
    (U R z ⊓ centralizer (Ltilde R z : Set (FreeAmalgam R)))
    (U_le_Z z) (Sp4Four.edge_Z_le_endpoint R hz hzt)
    (original_Z_eq_moving_sup_edge h hshort hinner g hb hz hzt) hCT hY hB
    (cv.edge_le.trans (U_normalized z)) cv.embedding cv.injective cv.range_eq cv.actor
    cv.actor_conjugation k hk hdim (fun w => (cv.kernel w).trans
      ⟨fun hc => ⟨cv.range_eq ▸ ⟨_,rfl⟩,hc⟩,fun hc => hc.2⟩)

private theorem plane_root_generating_conjugates
    (g : Geometry R) (hb : g.b R=2)
    {a t : Vertex R} (ha : color R a=false)
    (hat : Adjacent R a t)
    (cv : RadicalPlaneCover R (originalMovedSection h) n a t)
    (B : Subgroup (FreeAmalgam R)) (hBT : B ≤ Q R t)
    (hcard : (Q R a).relIndex B=2^n)
    (hfixed : (centralizer (B : Set (FreeAmalgam R))).relIndex (Z R a)=2^n) :
    ∃ f : Fin 4 → L (K := cv.field.Carrier),
      (⨆ i, (cv.actor.comp (inclusion hBT)).range.map (MulAut.conj (f i)).toMonoidHom)=⊤ := by
  have hm := plane_cover_full_fixed_index h hshort hinner g hb ha hat cv B hBT
  let E := cv.field
  let e := cv.equiv
  let κ := cv.quotient
  let β := cv.actor
  have hTS := cv.edge_le
  have hαker := cv.actor_kernel
  let k : Sp E.Carrier := Classical.choose cv.plane_image
  have hk := Classical.choose_spec cv.plane_image
  let βB := β.comp (inclusion hBT)
  let α := (commutator (Sp E.Carrier)).subtype.comp β
  let αB := α.comp (inclusion hBT)
  have hEc : Nat.card E.Carrier=2^n := E.card_eq.trans (congrArg (2^·) cv.degree)
  have hq : 1<2^n := one_lt_pow₀ (by decide : 1<(2:ℕ)) (by have := h.nonbinary; omega)
  have hαcard : Nat.card αB.range=2^n := by
    rw [←index_ker,←MonoidHom.comap_ker,hαker,comap_inclusion_subgroupOf]
    exact hcard
  have hβcard : Nat.card βB.range=Nat.card E.Carrier := by
    have hr : αB.range=βB.range.map (commutator (Sp E.Carrier)).subtype :=
      MonoidHom.range_comp (commutator (Sp E.Carrier)).subtype βB
    rw [hr,card_map_of_injective (commutator (Sp E.Carrier)).subtype_injective] at hαcard
    exact hαcard.trans hEc.symm
  have hdim : Module.finrank E.Carrier (displacementSpace αB.range)=1 := by
    exact Nat.pow_right_injective hq (hm.symm.trans (hfixed.trans (pow_one _).symm))
  have hαmap : βB.range.map (commutator (Sp E.Carrier)).subtype=αB.range :=
    (MonoidHom.range_comp (commutator (Sp E.Carrier)).subtype βB).symm
  let P := Classical.choose (conjugate_plane_geometry (F := E.Carrier) α.range k hk)
  have hfix := (Classical.choose_spec (conjugate_plane_geometry (F := E.Carrier) α.range k hk)).2.1
  have hmove := (Classical.choose_spec (conjugate_plane_geometry (F := E.Carrier) α.range k hk)).2.2
  have hquad : ∀ x ∈ αB.range, ∀ y ∈ αB.range, ∀ v : Vector E.Carrier,
      x • (y • v-v)=y • v-v := by
    rintro _ ⟨x,rfl⟩ _ ⟨y,rfl⟩ v
    exact hfix _ ⟨inclusion hBT x,rfl⟩ _ (hmove _ ⟨inclusion hBT y,rfl⟩ v)
  have hlarge : 2<Nat.card E.Carrier := by
    rw [hEc]
    exact lt_of_lt_of_le (by decide : 2<2^2) (Nat.pow_le_pow_right (by decide) h.nonbinary)
  exact derived_four_conjugates_of_displacement_one (F := E.Carrier) hlarge βB.range hβcard
    (by rw [hαmap]; exact hdim) (by rw [hαmap]; exact hquad)

/-- The four-conjugate source argument applies to the actual field-sized
subgroup of a plane radical, with its centralizer measured on the whole core. -/
theorem original_core_eq_moving_sup_fixed_of_plane_root
    (g : Geometry R) (hb : g.b R=2)
    {a t : Vertex R} (ha : color R a=false)
    (hat : Adjacent R a t)
    (cv : RadicalPlaneCover R (originalMovedSection h) n a t)
    (B : Subgroup (FreeAmalgam R)) (hBT : B ≤ Q R t)
    (hcard : (Q R a).relIndex B=2^n)
    (hfixed : (centralizer (B : Set (FreeAmalgam R))).relIndex (Z R a)=2^n)
    (hindex : (centralizer (B : Set (FreeAmalgam R))).relIndex (Q R a) ≤ 2^n) :
    Q R a=U R a ⊔ fixedCore R a := by
  let E := cv.field
  let e := cv.equiv
  let κ := cv.quotient
  let β := cv.actor
  let βB := β.comp (inclusion hBT)
  have hTS := cv.edge_le
  have hq : 1<2^n := one_lt_pow₀ (by decide : 1<(2:ℕ)) (by have := h.nonbinary; omega)
  let f := Classical.choose (plane_root_generating_conjugates h hshort hinner g hb ha hat cv B hBT hcard hfixed)
  have hf := Classical.choose_spec (plane_root_generating_conjugates h hshort hinner g hb ha hat cv B hBT hcard hfixed)
  let s := Classical.choose (short_original_wholeKernelQuotient_over h hshort ha κ cv.onto cv.kernel_Q)
  have hs := Classical.choose_spec (short_original_wholeKernelQuotient_over h hshort ha κ cv.onto cv.kernel_Q)
  let γ := (K.map (QuotientGroup.mk' (pCore 2 H))).subtype.comp e.groupEquiv.symm.toMonoidHom
  let σ := s.action.comp γ
  have hBS : B ≤ stabilizer R a := hBT.trans hTS
  have hmap : (B.subgroupOf (stabilizer R a)).map κ=βB.range.map γ := by
    rw [←MonoidHom.range_comp]
    apply le_antisymm
    · rintro u ⟨b,hb,rfl⟩
      refine ⟨⟨b.val,hb⟩,?_⟩
      exact cv.actor_marking (inclusion hBT ⟨b.val,hb⟩)
    · rintro u ⟨b,rfl⟩
      exact ⟨inclusion hBS b,b.property,(cv.actor_marking (inclusion hBT b)).symm⟩
  have hSN : stabilizer R a ≤ normalizer
      (fixedCore R a : Set (FreeAmalgam R)) := by
    have hSL : stabilizer R a ≤ normalizer (Ltilde R a : Set (FreeAmalgam R)) := by
      have ht := le_normalizer_map (H := pResidual 2 (stabilizer R a))
        (stabilizer R a).subtype
      rw [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] at ht
      exact ht
    exact (le_inf (Q_normalized R a)
      (hSL.trans (normalizer_le_normalizer_centralizer _))).trans inf_normalizer_le_normalizer_inf
  let := finite_stabilizer R a
  let : Finite (Q R a) := Finite.of_injective
    (inclusion (show Q R a ≤ stabilizer R a from fun _ hx => hx.1))
    (inclusion_injective _)
  have hfullfixed : fixedSpace σ ⊤=⊥ := by
    apply bot_unique
    intro v hv
    apply s.fixed_eq_bot.le
    rintro ⟨x,hx⟩
    rw [hs,cv.component] at hx
    obtain ⟨b,hb⟩ := e.groupEquiv.symm.surjective ⟨x,hx⟩
    have he : γ b=x := congrArg Subtype.val hb
    change s.action x v=v
    rw [←he]
    exact hv ⟨b,mem_top _⟩
  have hsmall := whole_core_index_bound_of_conjugates R a s (2^n) n rfl
    B hBS hSN γ βB.range f hf (by rw [hs]; exact hmap) hfullfixed hindex
  rw [short_original_core_fixed_index_eq_natural_mul h hshort ha] at hsmall
  have hrel : (U R a ⊔ fixedCore R a).relIndex (Q R a)=1 := by
    have hp : 0<(2^n)^4 := pow_pos (by omega) _
    have hlo : 0<(U R a ⊔ fixedCore R a).relIndex (Q R a) :=
      Nat.pos_of_ne_zero index_ne_zero_of_finite
    nlinarith only [hp,hlo,hsmall]
  apply le_antisymm (relIndex_eq_one.mp hrel)
  exact sup_le ((U_le_Z a).trans
    ((g.omega_bound a ha (by rw [g.distance_constant a ha]; change 0<g.b R; omega)).trans
      (omegaCenter_le _))) inf_le_left


variable (hnsyl : ¬ ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
  (R.subgroupOf K).map (componentProjection h))
include hnsyl

/-- The actual source-(6) selection, now with index q for the centralizer
in the entire moved endpoint core. All selected elements and full attachments
remain those of the preceding construction. -/
theorem original_source_six_field_pair_or_whole_core_centralizer
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
              Set (FreeAmalgam R))).relIndex (Z R (act R k⁻¹ z))=2^n ∧
            (U R z ⊓ centralizer (Ltilde R z : Set (FreeAmalgam R))).relIndex
              ⁅Q R (act R k⁻¹ z),
                Z R z ⊓ centralizer ({y*x*y⁻¹} : Set (FreeAmalgam R))⁆ = 2^n ∧
            ⁅Q R (act R k⁻¹ z),
                Z R z ⊓ centralizer ({y*x*y⁻¹} : Set (FreeAmalgam R))⁆ ⊔
              (U R z ⊓ centralizer (Ltilde R z : Set (FreeAmalgam R))) ≠
                ⁅Z R z,Q R t⁆ ∧
            (centralizer ((Z R z ⊓ centralizer ({y*x*y⁻¹} : Set (FreeAmalgam R))) :
              Set (FreeAmalgam R))).relIndex (Q R (act R k⁻¹ z))=2^n)) := by
  obtain ⟨x,hx,hxQ,hreg,y,hy,k,hk,he,hcoset,hcomm,hmove,⟨p⟩,halt⟩ :=
    original_source_six_field_pair_or_small_whole_core_movement h hshort hinner hnsyl g hb path hat hzt hcritical
  refine ⟨x,hx,hxQ,hreg,y,hy,k,hk,he,hcoset,hcomm,hmove,⟨p⟩,?_⟩
  rcases halt with hsmall | ⟨hwQ,hi,hQi,hCi,hMi,hne⟩
  · exact Or.inl hsmall
  apply Or.inr
  refine ⟨hwQ,hi,hQi,hCi,hMi,hne,?_⟩
  let v := act R k⁻¹ z
  have hkt : act R k⁻¹ t=t := (stabilizer R t).inv_mem hk
  have hvt : Adjacent R v t := by
    simpa only [hkt] using (adjacent_act_iff R k⁻¹ z t).mpr hzt
  obtain ⟨_,⟨cz⟩,_⟩ := original_source_four_large_paired_geometry h hshort hinner hnsyl g hb path hat hzt hcritical
  have hZQ (b : Vertex R) (hc : color R b=false) : Z R b ≤ Q R b :=
    (g.omega_bound b hc (by rw [g.distance_constant b hc]; change 0<g.b R; omega)).trans
      (omegaCenter_le _)
  have hxT : x ∈ Q R t := (original_core_le_edge R path.end_color hzt) (hZQ z path.end_color hx)
  have hwT : y*x*y⁻¹ ∈ Q R t := by
    have hconj : (MulAut.conj k) x ∈ Q R t :=
      (mem_normalizer_iff.mp (Q_normalized R t hk) x).mp hxT
    rw [he x hxT] at hconj
    exact hconj
  have hcent : centralizer (zpowers (y*x*y⁻¹) : Set (FreeAmalgam R))=
      centralizer ({y*x*y⁻¹} : Set (FreeAmalgam R)) := by
    rw [zpowers_eq_closure,centralizer_closure]
  have hu := original_plane_cover_hyperplane_centralizer_bound h hshort hinner g hb path.end_color hzt cz
    (zpowers (y*x*y⁻¹)) (Q R v) (zpowers_le.mpr hwT) (original_core_le_edge R p.start_color hvt)
    (by rw [hcent,←inf_relIndex_left]; exact hi)
  rw [hcent,hMi] at hu
  apply le_antisymm hu
  let := finite_stabilizer R v
  let : Finite (Q R v) := Finite.of_injective
    (inclusion (show Q R v ≤ stabilizer R v from fun _ hv => hv.1))
    (inclusion_injective _)
  rw [←hCi]
  exact relIndex_le_of_le_right (hZQ v p.start_color) index_ne_zero_of_finite

private theorem fixedCore_le_opposite_of_large_pair
    (g : Geometry R) (hb : g.b R=2)
    {a z t : Vertex R} (path : CriticalPath R g a z)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (hcritical : (2^n)^2 ≤ (Q R z).relIndex (Z R a)) :
    fixedCore R a ≤ Q R z := by
  obtain ⟨_,_,_,_,hRa,hRz,_⟩ :=
    original_source_four_large_paired_geometry h hshort hinner hnsyl g hb path hat hzt hcritical
  have hA := original_source_four_fixed_attachments h hshort hinner hnsyl g hb path hat hzt
  let D := fixedCore R a
  have hDQ : D ≤ Q R a := inf_le_left
  have hZT : Z R z ≤ Q R t :=
    ((g.omega_bound z path.end_color (by
      rw [g.distance_constant z path.end_color]; change 0<g.b R; omega)).trans
      (omegaCenter_le _)).trans (original_core_le_edge R path.end_color hzt)
  have hmove : ⁅D,U R z⁆ ≤
      U R z ⊓ centralizer (Ltilde R z : Set (FreeAmalgam R)) := by
    rw [←hA]
    apply le_inf
    · apply (commutator_mono (hDQ.trans (original_core_le_edge R path.start_color hat)) (U_le_Z z)).trans
      rw [commutator_comm,hRz,←hRa]
      exact original_full_radical_Z_displacement_le_moving h hinner path.start_color hat
    · apply le_trans ?_ (show D ≤ centralizer (Ltilde R a : Set (FreeAmalgam R)) from inf_le_right)
      exact le_normalizer_iff_commutator_le_left.mp
        (((U_le_Z z).trans hZT).trans (original_fixedCore_normalized hat))
  have hc : D ≤ centralizer (U R z : Set (FreeAmalgam R)) := by
    intro b hbD u hu
    exact (commutatorElement_eq_one_iff_commute.mp
      (original_stabilizer_value_in_fixed_eq_one h hinner path.end_color b
        ((original_edge_le_stabilizer R hzt) ((original_core_le_edge R path.start_color hat) (hDQ hbD))) u hu
        (hmove (commutator_mem_commutator hbD hu)).2)).eq.symm
  rw [←original_stabilizer_centralizer_moving_eq_core h path.end_color]
  exact le_inf ((hDQ.trans (original_core_le_edge R path.start_color hat)).trans (original_edge_le_stabilizer R hzt)) hc

omit h hshort hinner hnsyl [Finite H] [Field F] [Finite F] [CharP F 2] in
private theorem core_decomposition_at (R : Subgroup H)
    {a b : Vertex R} (ha : color R a=false) (hb : color R b=false)
    (hcore : Q R a=U R a ⊔ fixedCore R a) :
    Q R b=U R b ⊔ fixedCore R b := by
  obtain ⟨x,hx⟩ := exists_mVertex_of_color R ha
  obtain ⟨y,hy⟩ := exists_mVertex_of_color R hb
  have hab : act R (x⁻¹*y) a=b := by
    rw [hx,hy,act_mVertex,mul_inv_cancel_left]
  have hD (k : FreeAmalgam R) : fixedCore R (act R k a)=
      (fixedCore R a).map (MulAut.conj k⁻¹).toMonoidHom := by
    have hc : (centralizer (Ltilde R a : Set (FreeAmalgam R))).map
        (MulAut.conj k⁻¹).toMonoidHom =
        centralizer ((Ltilde R a).map (MulAut.conj k⁻¹).toMonoidHom : Set (FreeAmalgam R)) := by
      apply le_antisymm
      · exact map_centralizer_le_centralizer_image _ _
      · intro z hz
        let e := MulAut.conj k⁻¹
        refine ⟨e.symm z,?_,e.apply_symm_apply z⟩
        intro w hw
        apply e.injective
        simpa only [map_mul,e.apply_symm_apply] using hz (e w) (mem_map_of_mem _ hw)
    rw [fixedCore,Q_act,Ltilde_act,fixedCore,map_inf _ _ _ (MulAut.conj k⁻¹).injective,hc]
  rw [←hab,Q_act,U_act,hD,←Subgroup.map_sup,←hcore]

/-- The commuting-coset contradiction at the end of source (6), with the
regular element and the full component-fixed core retained. -/
private theorem large_regular_conjugate_mem_core
    (g : Geometry R) (hb : g.b R=2)
    {a z t : Vertex R} (path : CriticalPath R g a z)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (hcritical : (2^n)^2 ≤ (Q R z).relIndex (Z R a))
    (hcore : Q R a=U R a ⊔ fixedCore R a)
    (x w : FreeAmalgam R) (hx : x ∈ Z R z)
    (hreg : Z R a ⊓ centralizer ({x} : Set (FreeAmalgam R))=Z R t)
    (hcoset : x⁻¹*w ∈ Q R a) (hcomm : Commute x w) : w ∈ Q R z := by
  have hD := fixedCore_le_opposite_of_large_pair h hshort hinner hnsyl g hb path hat hzt hcritical
  have hUD : U R a ≤ centralizer (fixedCore R a : Set (FreeAmalgam R)) :=
    ((U_le_Z a).trans (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q R a path.start_color))).trans (centralizer_le inf_le_left)
  rw [hcore,←SetLike.mem_coe,coe_mul_of_left_le_normalizer_right _ _
    (hUD.trans (Subgroup.centralizer_le_normalizer _))] at hcoset
  obtain ⟨u,hu,v,hv,he⟩ := hcoset
  change u*v=x⁻¹*w at he
  have hvx : Commute v x := (commutator_eq_bot_iff_le_centralizer.mp
    (Z_centralizes_Q R z path.end_color)) hx v (hD hv)
  have hux : Commute u x := by
    have hprod : Commute (u*v) x := by
      rw [he]
      exact (Commute.refl x).inv_left.mul_left hcomm.symm
    change u*x=x*u
    apply mul_right_cancel (b := v)
    calc
      u*x*v=u*(v*x) := by rw [mul_assoc,hvx.eq]
      _ = (u*v)*x := (mul_assoc _ _ _).symm
      _ = x*(u*v) := hprod.eq
      _ = x*u*v := (mul_assoc _ _ _).symm
  have hut : u ∈ Z R t := hreg ▸
    (show u ∈ Z R a ⊓ centralizer ({x} : Set (FreeAmalgam R)) from
      ⟨U_le_Z a hu,mem_centralizer_singleton_iff.mpr hux.eq⟩)
  have hZQ : Z R z ≤ Q R z :=
    (g.omega_bound z path.end_color (by
      rw [g.distance_constant z path.end_color]; change 0<g.b R; omega)).trans (omegaCenter_le _)
  have hq : x⁻¹*w ∈ Q R z := he ▸ (Q R z).mul_mem
    (hZQ (Sp4Four.edge_Z_le_endpoint R path.end_color hzt hut)) (hD hv)
  have hh := (Q R z).mul_mem (hZQ hx) hq
  simpa only [mul_inv_cancel_left] using hh


/-- MS93 (3.7)(6): a genuine critical pair with image of field order exists.
The critical pair belongs to the literal original nonsylow star. -/
theorem original_source_six_exists_field_critical_pair
    (g : Geometry R) (hb : g.b R=2) :
    ∃ a z : Vertex R, Nonempty (CriticalPath R g a z) ∧
      (Q R z).relIndex (Z R a)=2^n := by
  let a := mVertex R 1
  obtain ⟨z,⟨path⟩⟩ := CriticalPath.exists_from (R := R) (geometry := g)
    (a := a) (show color R a=false from rfl)
  by_cases hcritical : (2^n)^2 ≤ (Q R z).relIndex (Z R a)
  swap
  · exact ⟨a,z,⟨path⟩,((h.original_small_critical_indices_eq_field path (by omega)
      (by rw [h.field_card]; exact lt_of_not_ge hcritical)).1.trans h.field_card)⟩
  have hd : (cosetGraph R).dist a z=2 :=
    path.critical.1.trans ((g.distance_constant a path.start_color).trans hb)
  obtain ⟨t,hat,hzt⟩ := exists_common_neighbor_of_dist_two R a z hd
  obtain ⟨x,hx,hxQ,hreg,y,hy,k,hk,he,hcoset,hcomm,hmove,⟨p⟩,halt⟩ :=
    original_source_six_field_pair_or_whole_core_centralizer h hshort hinner hnsyl g hb path hat hzt hcritical
  rcases halt with hsmall | ⟨hwQ,hi,hQi,hCi,hMi,hne,hwhole⟩
  · exact ⟨act R k⁻¹ z,z,⟨p⟩,hsmall⟩
  let v := act R k⁻¹ z
  by_cases hc : (2^n)^2 ≤ (Q R z).relIndex (Z R v)
  swap
  · exact ⟨v,z,⟨p⟩,((h.original_small_critical_indices_eq_field p (by omega)
      (by rw [h.field_card]; exact lt_of_not_ge hc)).1.trans h.field_card)⟩
  have hkt : act R k⁻¹ t=t := (stabilizer R t).inv_mem hk
  have hvt : Adjacent R v t := by
    simpa only [hkt] using (adjacent_act_iff R k⁻¹ z t).mpr hzt
  obtain ⟨⟨pv⟩,_⟩ := original_source_four_large_paired_geometry h hshort hinner hnsyl g hb p hvt hzt hc
  let X := Z R z ⊓ centralizer ({y*x*y⁻¹} : Set (FreeAmalgam R))
  have hZT : Z R z ≤ Q R t :=
    ((g.omega_bound z path.end_color (by
      rw [g.distance_constant z path.end_color]
      change 0<g.b R
      omega)).trans (omegaCenter_le _)).trans (original_core_le_edge R path.end_color hzt)
  have hXT : X ≤ Q R t := inf_le_left.trans hZT
  have hvcore := original_core_eq_moving_sup_fixed_of_plane_root h hshort hinner g hb p.start_color hvt pv X hXT
    hQi hCi hwhole.le
  have hacore := core_decomposition_at R p.start_color path.start_color hvcore
  exact (hwQ (large_regular_conjugate_mem_core h hshort hinner hnsyl g hb path hat hzt hcritical
    hacore x (y*x*y⁻¹) hx hreg hcoset hcomm)).elim

/-- The immediate whole-core consequence of source (6) and source (3),
for every vertex of the original component color. This supplies the whole-core
premise of the subsequent source endgame without assuming a critical image. -/
theorem original_source_six_core_decomposition
    (g : Geometry R) (hb : g.b R=2)
    {a : Vertex R} (ha : color R a=false) :
    Q R a=U R a ⊔ fixedCore R a := by
  obtain ⟨b,z,⟨path⟩,hcritical⟩ := original_source_six_exists_field_critical_pair h hshort hinner hnsyl g hb
  have hd : (cosetGraph R).dist b z=2 :=
    path.critical.1.trans ((g.distance_constant b path.start_color).trans hb)
  obtain ⟨t,hbt,hzt⟩ := exists_common_neighbor_of_dist_two R b z hd
  have hcore := (original_source_three_of_field_critical h hshort hinner hnsyl g hb path hbt hzt hcritical).2.1
  exact core_decomposition_at R path.start_color ha hcore

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar
