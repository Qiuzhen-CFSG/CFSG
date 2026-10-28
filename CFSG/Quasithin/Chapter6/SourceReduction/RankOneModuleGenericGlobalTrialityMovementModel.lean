module
public import Theory.SpecificGroups.Triality.ArmsOrbit
public import Theory.SpecificGroups.Triality.FullParabolicActions
public import Theory.SpecificGroups.Triality.ArmsLocalCoreCenter

/-!
# Intrinsic short-root orbit separation in the triality arms factor

On the arms core modulo its center, vectors fixed by the unipotent group
have only the penultimate long-root coordinate. The Borel preserves this
fixed space. Its nonzero orbit has size at most q-1, and the Borel index
bounds the full local-factor orbit by (q-1)(q³+1).

The genuine arms torus scales the highest short root by t F(t)/F²(t).
This character is bijective in characteristic two: an element in its
kernel has F(t)²=1, hence t=1. Together with the short-root trace shear,
this produces q(q³-1) distinct quotient vectors, strictly more than the
fixed-vector bound. Automorphisms of the actual local factor preserve
these intrinsic orbit sizes, so every automorphic image of the marked
short root is moved modulo the center by the original unipotent group.

The companion TrialityNonfusion module transports this through the literal
right-factor map and the original S. No root-class preservation or equality
between S and its conjugate is assumed.
Source: Aschbacher–Smith F.4.35, printed p.292 (`refs/quasithin.pdf`).
The coordinate formulas reuse the licensed ATLAS port; see LICENSES/ATLAS.txt
and LICENSES/ATLAS-CITATION.cff. No further ATLAS code is copied here.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.TrialityMovement
open _root_.Triality.Standard _root_.Triality.Standard.Parabolics
open _root_.Triality.Standard.RadicalCoordinates
open _root_.Triality.Standard.RadicalCoordinates.Centers
open _root_.Triality.Standard.RadicalCoordinates.LeviCommutators
open _root_.Triality.Standard.EvenInvolutionGeometry.ArmsNormalization
variable (P : Parameters) (hp : P.prime = 2)

include hp in
private theorem local_center :
    (center (localFactor P .arms)).map (localFactor P .arms).subtype = highestRoot P := by
  apply le_antisymm
  · rintro _ ⟨a,ha,rfl⟩
    have hc : a.val ∈ centralizer (radical P .arms : Set (Carrier P)) := by
      apply mem_centralizer_iff.mpr
      intro r hr
      exact congrArg Subtype.val
        (mem_center_iff.mp ha ⟨r,radical_le_localFactor P hp .arms hr⟩)
    have har := parabolic_centralizer_radical_le P hp .arms
      ⟨localFactor_le_parabolic P .arms a.property,hc⟩
    rw [←embedded_center_radical_arms P hp]
    refine ⟨⟨a.val,har⟩,mem_center_iff.mpr (fun r => ?_),rfl⟩
    apply Subtype.ext
    exact congrArg (fun x : localFactor P .arms => x.val)
      (mem_center_iff.mp ha ⟨r,radical_le_localFactor P hp .arms r.property⟩)
  · intro z hz
    have hzR : z ∈ radical P .arms := by
      rw [←embedded_center_radical_arms P hp] at hz
      exact map_subtype_le _ hz
    refine ⟨⟨z,radical_le_localFactor P hp .arms hzR⟩,mem_center_iff.mpr (fun x => ?_),rfl⟩
    apply Subtype.ext
    have hh := localFactor_arms_le_centralizer_center_unipotent P hp x.property
    rw [embedded_center_unipotent P hp] at hh
    exact (mem_centralizer_iff.mp hh z hz).symm

private abbrev K := localFactor P .arms
private abbrev Space := K P ⧸ center (K P)
private def point : K P →* Space P := QuotientGroup.mk' (center (K P))
private def action : K P →* MulAut (Space P) := MulAut.conj.comp (point P)
private def points (v : Space P) : Set (Space P) := Set.range fun h : K P => action P h v
private def qpoint (v : radical P .arms) : Space P := point P ⟨v.val,radical_le_localFactor P hp .arms v.property⟩

private theorem action_point (h v : K P) :
    action P h (point P v)=point P (h*v*h⁻¹) := by
  simp only [action,MonoidHom.comp_apply,MulAut.conj_apply,map_mul,map_inv]

include hp in
private theorem point_eq_iff (v w : K P) :
    point P v=point P w ↔ v.val*w.val⁻¹∈highestRoot P := by
  change (v : K P ⧸ center (K P))=(w : K P ⧸ center (K P)) ↔ _
  rw [QuotientGroup.eq_iff_div_mem,div_eq_mul_inv,←local_center P hp]
  constructor
  · intro h; exact ⟨v*w⁻¹,h,rfl⟩
  · rintro ⟨z,hz,he⟩
    exact (show z=v*w⁻¹ from Subtype.ext he) ▸ hz

include hp in
private theorem action_point_fixed (h v : K P) :
    action P h (point P v)=point P v ↔ ⁅h.val,v.val⁆∈highestRoot P := by
  rw [action_point,point_eq_iff P hp]
  rfl

private theorem coordinate_eq (v w : ArmsParameters P)
    (he : qpoint P hp (armsCoordinates P hp v)=qpoint P hp (armsCoordinates P hp w)) :
    v.1=w.1 ∧ v.2 0=w.2 0 ∧ v.2 1=w.2 1 :=
  coordinates_eq_of_central_difference P hp w v ((point_eq_iff P hp _ _).mp he)

private theorem long_mem_core (i : Fin 3) (a : fixedField P) : long P hp i a∈radical P .arms := by
  rw [radical_eq_descendedRootSubgroup P hp .arms]
  exact long_mem P hp .arms i trivial a

private theorem short_mem_core (d : ExtensionField P) : short P hp 2 d∈radical P .arms := by
  rw [radical_eq_descendedRootSubgroup P hp .arms]
  exact short_mem P hp .arms 2 (by change (2 : Fin 3)≠0; decide) d

private theorem short_mem_unipotent (d : ExtensionField P) : short P hp 0 d∈unipotent P :=
  descendSubgroup_mono P (rootSubgroup_le_positiveSubgroup P hp .central)
    (short_mem P hp .central 0 trivial d)

include hp in
private theorem unipotent_mem_factor : unipotent P ≤ K P :=
  unipotent_le_localFactor P .arms (hp.symm ▸ unipotent_isPGroup_binary P hp)

private def longPoint (e : fixedField P) : Space P :=
  qpoint P hp ⟨long P hp 1 e,long_mem_core P hp 1 e⟩

private theorem long_two_point (f : fixedField P) :
    qpoint P hp ⟨long P hp 2 f,long_mem_core P hp 2 f⟩=1 := by
  apply (QuotientGroup.eq_one_iff _).mpr
  have hz : long P hp 2 f∈highestRoot P := by
    refine ⟨longElementary P hp 2 f,?_,rfl⟩
    change elementaryInclusion P (longElementary P hp 2 f)∈splitHighestRoot P
    rw [longElementary_val]
    exact ⟨Multiplicative.ofAdd f.val,rfl⟩
  rw [←local_center P hp] at hz
  obtain ⟨x,hx,he⟩ := hz
  exact (show x=⟨long P hp 2 f,radical_le_localFactor P hp .arms (long_mem_core P hp 2 f)⟩ from
    Subtype.ext he) ▸ hx

include hp in
private theorem fixed_point_support (v : K P) (hv : v.val∈radical P .arms)
    (hfix : ∀ h : K P, h.val∈unipotent P → action P h (point P v)=point P v) :
    ∃ e : fixedField P, point P v=longPoint P hp e := by
  have hh (a : ExtensionField P) : ⁅short P hp 0 a,v.val⁆∈highestRoot P :=
    (action_point_fixed P hp _ _).mp
      (hfix ⟨_,unipotent_mem_factor P hp (short_mem_unipotent P hp a)⟩ (short_mem_unipotent P hp a))
  obtain ⟨e,f,he⟩ := fixed_mod_center_long_support P hp ⟨v.val,hv⟩ hh
  refine ⟨e,?_⟩
  have hv' : v=⟨long P hp 1 e,radical_le_localFactor P hp .arms (long_mem_core P hp 1 e)⟩ *
      ⟨long P hp 2 f,radical_le_localFactor P hp .arms (long_mem_core P hp 2 f)⟩ := Subtype.ext he
  rw [hv',map_mul]
  change longPoint P hp e*qpoint P hp ⟨_,long_mem_core P hp 2 f⟩=longPoint P hp e
  rw [long_two_point,mul_one]

private theorem longPoint_zero : longPoint P hp 0=1 := by
  unfold longPoint qpoint
  have hz : (⟨long P hp 1 0,radical_le_localFactor P hp .arms (long_mem_core P hp 1 0)⟩ : K P)=1 :=
    Subtype.ext (long_zero P hp 1)
  rw [hz,map_one]

private theorem conjugate_core (k : K P) {v : K P} (hv : v.val∈radical P .arms) :
    (k*v*k⁻¹).val∈radical P .arms := by
  have hn := (normal_subgroupOf_iff_le_normalizer (radical_le_parabolic P .arms)).mp
    (radical_normal P .arms)
  exact (mem_normalizer_iff.mp (hn (localFactor_le_parabolic P .arms k.property)) v.val).mp hv

include hp in
private theorem borel_conjugate_fixed (b : K P) (hb : b.val∈borel P) (v : Space P)
    (hv : ∀ h : K P, h.val∈unipotent P → action P h v=v) :
    ∀ h : K P, h.val∈unipotent P → action P h (action P b v)=action P b v := by
  intro h hh
  have hn := (normal_subgroupOf_iff_le_normalizer (unipotent_le_borel P)).mp
    (ConcreteBruhat.unipotent_normal_in_borel P hp)
  have hm : b.val⁻¹*h.val*b.val∈unipotent P := by
    simpa only [inv_inv] using
      (mem_normalizer_iff.mp (hn ((borel P).inv_mem hb)) h.val).mp hh
  have he := congrArg (action P b) (hv (b⁻¹*h*b) hm)
  simpa only [map_mul,map_inv,MulAut.mul_apply,MulAut.inv_apply,
    MulEquiv.apply_symm_apply] using he

include hp in
private theorem small_borel_orbit (v : K P) (hv : v.val∈radical P .arms)
    (hv1 : point P v≠1)
    (hfix : ∀ h : K P, h.val∈unipotent P → action P h (point P v)=point P v) :
    (Set.range fun b : (borel P).subgroupOf (K P) => action P b.val (point P v)).ncard ≤ P.q-1 := by
  let O := Set.range fun b : (borel P).subgroupOf (K P) => action P b.val (point P v)
  have hs (x : O) : ∃ e : (fixedField P)ˣ, x.val=longPoint P hp e.val := by
    obtain ⟨b,hb⟩ := x.property
    have hf := borel_conjugate_fixed P hp b.val b.property (point P v) hfix
    change action P b.val (point P v)=x.val at hb
    rw [action_point] at hf hb
    obtain ⟨e,he⟩ := fixed_point_support P hp (b.val*v*b.val⁻¹) (conjugate_core P b.val hv) hf
    have he0 : e≠0 := by
      intro hh
      have hz : action P b.val (point P v)=1 := by rw [action_point,he,hh,longPoint_zero]
      exact hv1 ((action P b.val).injective (hz.trans (map_one _).symm))
    exact ⟨Units.mk0 e he0,hb.symm.trans he⟩
  choose e he using hs
  have hi : Function.Injective e := by
    intro x y hh
    apply Subtype.ext
    rw [he x,he y,hh]
  have hc := Nat.card_le_card_of_injective e hi
  change Nat.card O≤P.q-1
  simpa only [Nat.card_units,card_fixedField] using hc

private theorem orbit_index_bound {A X : Type*} [Group A] [Finite A] [Group X]
    (f : A →* MulAut X) (B : Subgroup A) (v : X) :
    (Set.range fun a : A => f a v).ncard ≤
      (Set.range fun b : B => f b.val v).ncard * B.index := by
  let : MulAction A X := MulAction.compHom X f
  let : MulAction B X := MulAction.compHom X (f.comp B.subtype)
  let C := MulAction.stabilizer A v
  have he : MulAction.stabilizer B v = C.subgroupOf B := by rfl
  change (MulAction.orbit A v).ncard ≤ (MulAction.orbit B v).ncard * B.index
  rw [←MulAction.index_stabilizer,←MulAction.index_stabilizer,he]
  change C.index≤C.relIndex B*B.index
  rw [←inf_relIndex_left B C,relIndex_mul_index inf_le_left]
  exact index_antitone inf_le_right

private theorem fixed_orbit_bound (m : ℕ) (hm : 0<m)
    (v : K (binaryParameters m hm)) (hv : v.val∈radical (binaryParameters m hm) .arms)
    (hv1 : point (binaryParameters m hm) v≠1)
    (hfix : ∀ h : K (binaryParameters m hm), h.val∈unipotent (binaryParameters m hm) →
      action (binaryParameters m hm) h (point (binaryParameters m hm) v)=point (binaryParameters m hm) v) :
    (points (binaryParameters m hm) (point (binaryParameters m hm) v)).ncard ≤
      ((binaryParameters m hm).q-1)*((binaryParameters m hm).q^3+1) := by
  let R := binaryParameters m hm
  have hb := small_borel_orbit R rfl v hv hv1 hfix
  have hi : ((borel R).subgroupOf (K R)).index ≤ R.q^3+1 := by
    have hh := relIndex_le_of_le_right (H := borel R) (localFactor_le_parabolic R .arms)
      (by rw [OuterOdd.Coverage.RootGeometry.SimpleRecognition.borel_relIndex_parabolic m hm .arms]; omega)
    exact hh.trans_eq (OuterOdd.Coverage.RootGeometry.SimpleRecognition.borel_relIndex_parabolic m hm .arms)
  exact (orbit_index_bound (action R) ((borel R).subgroupOf (K R)) (point R v)).trans
    (Nat.mul_le_mul hb hi)


private def scale : (ExtensionField P)ˣ →* (ExtensionField P)ˣ :=
  (MonoidHom.id _ * Units.map (fieldFrobenius P).toMonoidHom) *
    (Units.map ((fieldFrobenius P).trans (fieldFrobenius P)).toMonoidHom)⁻¹

private theorem scale_val (t : (ExtensionField P)ˣ) :
    (scale P t).val=t.val*fieldFrobenius P t.val/fieldFrobenius P (fieldFrobenius P t.val) := by
  simp only [scale,MonoidHom.mul_apply,MonoidHom.id_apply,MonoidHom.inv_apply,
    Units.val_mul,Units.val_inv_eq_inv_val,Units.coe_map,div_eq_mul_inv]
  rfl

include hp in
private theorem scale_surjective : Function.Surjective (scale P) := by
  let : CharP (ExtensionField P) 2 := hp ▸ inferInstanceAs (CharP (ExtensionField P) P.prime)
  apply Finite.surjective_of_injective
  apply (injective_iff_map_eq_one (scale P)).mpr
  intro t ht
  have hn : fieldFrobenius P (fieldFrobenius P t.val)≠0 :=
    (map_ne_zero _).mpr ((map_ne_zero _).mpr t.ne_zero)
  have hh : t.val*fieldFrobenius P t.val=fieldFrobenius P (fieldFrobenius P t.val) := by
    have he := congrArg Units.val ht
    rw [scale_val,Units.val_one] at he
    exact (div_eq_one_iff_eq hn).mp he
  have hf := congrArg (fieldFrobenius P) hh
  rw [map_mul,fieldFrobenius_three,←hh] at hf
  have hs : (fieldFrobenius P t.val)^2=1 := by
    apply mul_left_cancel₀ t.ne_zero
    simpa only [pow_two,mul_one,mul_left_comm,mul_assoc] using hf
  have he : fieldFrobenius P t.val=1 := by
    simpa only [CharTwo.neg_eq,or_self] using (sq_eq_one_iff.mp hs)
  exact Units.ext ((fieldFrobenius P).injective (he.trans (map_one _).symm))

private theorem short_conjugation_transport (g : elementarySubgroup P) (d z : ExtensionField P)
    (h : elementaryInclusion P g*shortSplit P 2 d*(elementaryInclusion P g)⁻¹=shortSplit P 2 z) :
    toCarrier P g*short P hp 2 d*(toCarrier P g)⁻¹=short P hp 2 z := by
  have he : g*shortElementary P hp 2 d*g⁻¹=shortElementary P hp 2 z := by
    apply elementaryInclusion_injective P
    simpa only [map_mul,map_inv,shortElementary_val] using h
  simpa only [short,map_mul,map_inv] using congrArg (toCarrier P) he

private theorem torus_short_two (t : (ExtensionField P)ˣ) (d : ExtensionField P) :
    torusActor P hp .arms t*short P hp 2 d*(torusActor P hp .arms t)⁻¹ =
      short P hp 2 ((scale P t).val*d) := by
  exact short_conjugation_transport P hp (torusElementary P hp .arms t) d _
    ((torus_arms_short_two_conjugate P hp t d).trans
      (congrArg (fun z : ExtensionField P => shortSplit P 2 (z*d)) (scale_val P t).symm))

private theorem short_coordinates (d : ExtensionField P) :
    (armsCoordinates P hp (![0,d],![0,0,0])).val=short P hp 2 d := by
  rw [armsCoordinates_factorization]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.head_cons,Matrix.tail_cons,long_zero,short_zero,one_mul,mul_one]

private theorem short_coordinate_orbit (d₀ : ExtensionField P) (hd₀ : d₀≠0)
    (d : (ExtensionField P)ˣ) (e : fixedField P) :
    qpoint P hp (armsCoordinates P hp (![0,d.val],![0,e,0]))∈
      points P (qpoint P hp ⟨short P hp 2 d₀,short_mem_core P hp d₀⟩) := by
  obtain ⟨t,ht⟩ := scale_surjective P hp (Units.mk0 (d.val/d₀) (div_ne_zero d.ne_zero hd₀))
  have ht' : (scale P t).val*d₀=d.val := by rw [ht]; exact div_mul_cancel₀ _ hd₀
  obtain ⟨a,ha⟩ := armsPairing_surjective_left P hp d.val d.ne_zero e
  have hs : short P hp 0 a∈K P := unipotent_mem_factor P hp (short_mem_unipotent P hp a)
  have htor : torusActor P hp .arms t∈K P :=
    levi_le_localFactor P hp .arms (torusActor_mem_levi P hp .arms t)
  refine ⟨⟨short P hp 0 a*torusActor P hp .arms t,(K P).mul_mem hs htor⟩,?_⟩
  change action P _ (point P _)=point P _
  rw [action_point]
  apply congrArg (point P)
  apply Subtype.ext
  change (short P hp 0 a*torusActor P hp .arms t)*short P hp 2 d₀*
    (short P hp 0 a*torusActor P hp .arms t)⁻¹ = _
  rw [show (short P hp 0 a*torusActor P hp .arms t)*short P hp 2 d₀*
      (short P hp 0 a*torusActor P hp .arms t)⁻¹ =
      short P hp 0 a*(torusActor P hp .arms t*short P hp 2 d₀*
      (torusActor P hp .arms t)⁻¹)*(short P hp 0 a)⁻¹ by group,
    torus_short_two,ht',←short_coordinates,short_shear]
  congr 2
  simp [shearParameters,higherCoefficient,ha,-fieldFrobenius_apply]

private theorem short_orbit_lower (d : ExtensionField P) (hd : d≠0) :
    (P.q^3-1)*P.q ≤ (points P (qpoint P hp ⟨short P hp 2 d,short_mem_core P hp d⟩)).ncard := by
  let f : ((ExtensionField P)ˣ × fixedField P) →
      points P (qpoint P hp ⟨short P hp 2 d,short_mem_core P hp d⟩) := fun x =>
    ⟨qpoint P hp (armsCoordinates P hp (![0,x.1.val],![0,x.2,0])),
      short_coordinate_orbit P hp d hd x.1 x.2⟩
  have hf : Function.Injective f := by
    intro x y he
    have hh := coordinate_eq P hp _ _ (congrArg Subtype.val he)
    apply Prod.ext
    · exact Units.ext (congrFun hh.1 1)
    · exact hh.2.2
  change (P.q^3-1)*P.q ≤ Nat.card (points P (qpoint P hp ⟨short P hp 2 d,short_mem_core P hp d⟩))
  simpa only [Nat.card_prod,Nat.card_units,card_extensionField,card_fixedField] using
    Nat.card_le_card_of_injective f hf


private theorem short_point_ne_one (d : ExtensionField P) (hd : d≠0) :
    qpoint P hp ⟨short P hp 2 d,short_mem_core P hp d⟩ ≠ 1 := by
  intro he
  have hz : qpoint P hp (armsCoordinates P hp (![0,0],![0,0,0]))=1 := by
    have h0 : armsCoordinates P hp (![0,0],![0,0,0])=1 := by
      apply Subtype.ext
      rw [short_coordinates,short_zero]
      rfl
    rw [h0]
    exact map_one (point P)
  have hs : qpoint P hp (armsCoordinates P hp (![0,d],![0,0,0])) =
      qpoint P hp ⟨short P hp 2 d,short_mem_core P hp d⟩ := by
    exact congrArg (qpoint P hp) (Subtype.ext (short_coordinates P hp d))
  have hh := congrFun (coordinate_eq P hp _ _ (hs.trans (he.trans hz.symm))).1 1
  exact hd hh

private theorem orbit_card_automorphism (a : MulAut (K P)) (v : K P) :
    (points P (point P (a v))).ncard=(points P (point P v)).ncard := by
  let b := quotientAut (center (K P)) a
  have he (v : K P) : b (point P v)=point P (a v) := quotientAut_apply_mk _ _ _
  have hab (h : K P) (q : Space P) : b (action P h q)=action P (a h) (b q) := by
    change b (point P h*q*(point P h)⁻¹)=point P (a h)*b q*(point P (a h))⁻¹
    rw [map_mul,map_mul,map_inv,he]
  have horbit : b '' points P (point P v)=points P (point P (a v)) := by
    ext x
    constructor
    · rintro ⟨_,⟨h,rfl⟩,rfl⟩
      refine ⟨a h,?_⟩
      simpa only [he] using (hab h (point P v)).symm
    · rintro ⟨h,rfl⟩
      refine ⟨action P (a.symm h) (point P v),⟨_,rfl⟩,?_⟩
      rw [hab,a.apply_symm_apply,he]
  rw [←horbit,Set.ncard_image_of_injective _ b.injective]

include hp in
private theorem automorphism_core (a : MulAut (K P)) (v : K P)
    (hv : v.val∈radical P .arms) : (a v).val∈radical P .arms := by
  rw [←localFactor_twoCore_map P hp .arms] at hv ⊢
  obtain ⟨w,hw,he⟩ := hv
  have hwv : w=v := Subtype.ext he
  have hm := mem_map_of_mem a.toMonoidHom (hwv ▸ hw)
  rw [pCore_map_iso] at hm
  exact mem_map_of_mem (K P).subtype hm

/-- Every automorphic image of the marked short root is moved modulo the
highest root by the original unipotent subgroup. The proof compares intrinsic
orbits under the actual arms factor, and assumes no preservation of root classes. -/
theorem short_root_automorphism_moved (m : ℕ) (hm : 0<m)
    (a : MulAut (localFactor (binaryParameters m hm) .arms))
    (w : localFactor (binaryParameters m hm) .arms)
    (hw : w.val=short (binaryParameters m hm) rfl 2 1) :
    ∃ x : localFactor (binaryParameters m hm) .arms,
      x.val∈unipotent (binaryParameters m hm) ∧
        ⁅x,a w⁆∉center (localFactor (binaryParameters m hm) .arms) := by
  let R := binaryParameters m hm
  by_contra! hfix
  have hcore : w.val∈radical R .arms := hw ▸ short_mem_core R rfl 1
  have hnon : point R w≠1 := by
    have he : w=⟨short R rfl 2 1,radical_le_localFactor R rfl .arms (short_mem_core R rfl 1)⟩ :=
      Subtype.ext hw
    rw [he]
    exact short_point_ne_one R rfl 1 one_ne_zero
  have hnon' : point R (a w)≠1 := by
    change QuotientGroup.mk' (center (K R)) (a w)≠1
    rw [←quotientAut_apply_mk (center (K R)) a w]
    exact fun he => hnon ((quotientAut (center (K R)) a).injective (he.trans (map_one _).symm))
  have hu := fixed_orbit_bound m hm (a w) (automorphism_core R rfl a w hcore) hnon'
    (fun x hx => (action_point_fixed R rfl x (a w)).mpr (by
      rw [←local_center R rfl]
      exact mem_map_of_mem (K R).subtype (hfix x hx)))
  rw [orbit_card_automorphism] at hu
  have he : point R w=qpoint R rfl ⟨short R rfl 2 1,short_mem_core R rfl 1⟩ := by
    apply congrArg (point R)
    exact Subtype.ext hw
  rw [he] at hu
  have hl := short_orbit_lower R rfl 1 one_ne_zero
  have hle := hl.trans hu
  have hq := R.q_ge_two
  have hq3 : 1≤R.q^3 := one_le_pow₀ (by omega)
  have hs1 := Nat.sub_add_cancel (by omega : 1≤R.q)
  have hs3 := Nat.sub_add_cancel hq3
  have hsq : R.q^2≥2*R.q := by nlinarith
  have hcube : R.q^3≥4*R.q := by nlinarith [Nat.mul_le_mul_right R.q hsq]
  nlinarith

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.TrialityMovement
