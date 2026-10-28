module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.ThirdCommutator

/-!
# Full centers of the source Suzuki radical and unipotent group

Write V=U_s₂, D=Φ(V)=[V,V], E=U₂^(s₁s₂s₁). The faithful Suzuki
module V/D has order q⁵ and the fixed image of E has order q. Joining
that image to the image of Z(V) gives a proper invariant subgroup:
otherwise the Frattini nongenerating property would give V=Z(V)E,
contradicting the known noncentral commutator of E with U₁^s₂.
The invariant-layer bound therefore puts Z(V) in ED. The same mixed
commutator and [V,D]=Ω₁(E) give (Z(V)D)∩E≤Ω₁(E), so Z(V)≤D.
Applying the invariant-layer bound in D identifies Z(V)=Ω₁(E).
Local characteristic two puts Z(U) in V, yielding the same center.

This argument retains q=2 and avoids inferring product support from
individual root intersections. OriginalCenters and Section10Centers
apply it to the literal original quotient and every N-conjugate.
Source: Fong--Seitz I (1973), (6H)(g), printed p.55;
II (1974), (10.3)(iii), printed p.221.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory
open scoped Pointwise
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open BenderSuzuki.MatrixGroups BenderSuzuki.PFAppendixIII
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (n : ℕ) (hn : Odd n) (m : ℕ)
  (ν : (Endpoint Q 0 ⧸ panelKernel Q 0) ≃* PSL2BinaryMatrixGroup n)
  (T : Sylow 2 (PSL2BinaryMatrixGroup n))
  (hC : (quotientBorel Q 0).map ν.toMonoidHom = normalizer (T : Set _))
  (μ : (Endpoint Q 1 ⧸ panelKernel Q 1) ≃* SuzukiMatrixGroup m)
  (hB : (quotientBorel Q 1).map μ.toMonoidHom = normalizer (SuzukiRootSubgroup m : Set _))

private theorem center_image_centralizes (V : Subgroup (X ⧸ Q.D)) :
    (center V).map V.subtype ≤ centralizer (V : Set (X ⧸ Q.D)) := by
  rintro z ⟨x,hx,rfl⟩
  exact mem_centralizer_iff.mpr (fun v hv => congrArg Subtype.val
    (mem_center_iff.mp hx ⟨v,hv⟩))

include μ hB in
private theorem omega_card (w : Weyl Q) :
    Nat.card (omegaOneAmbient (rootAt Q split 1 w)) = 2^(2*m+1) := by
  let e := (MulAut.conj (representative w : X ⧸ Q.D)).symm
  have he : (simpleRoot Q split 1).map e.toMonoidHom = rootAt Q split 1 w := by
    simp only [rootAt,rightConjugate,comap_equiv_eq_map_symm']; rfl
  rw [←he,←map_omegaOneAmbient_injective e.toMonoidHom e.injective,
    card_map_of_injective e.injective]
  exact suzukiOmega_card Q split 1 m μ hB

include ν hC μ hB hn in
private theorem center_supplement_bounds
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥)
    (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤ pCore 2 (Endpoint Q 1)) :
    let V := simpleRemainder Q split 1
    let Z := (center V).map V.subtype
    let E := rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)
    Z ⊔ E ≠ V ∧ (Z ⊔ ⁅V,V⁆) ⊓ E ≤ omegaOneAmbient E := by
  let V := simpleRemainder Q split 1
  let Z := (center V).map V.subtype
  let E := rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)
  let B := rootAt Q split 0 (Q.simple 1)
  let C := rootAt Q split 1 (Q.simple 0*Q.simple 1)
  let O := omegaOneAmbient E
  have hBV : B ≤ V := (octagon_three_roots_le_remainder Q split hm 1 0 (by decide)).1
  have hEV : E ≤ V := (octagon_three_roots_le_remainder Q split hm 1 0 (by decide)).2.2
  have hZV : Z ≤ V := map_subtype_le _
  have hCZ := center_image_centralizes Q V
  have hEB : ⁅E,B⁆ = omegaOneAmbient C := by
    have hh := congrArg (fun A => rightConjugate A
      (representative (Q.simple 0*Q.simple 1*Q.simple 0) : X ⧸ Q.D))
      (source_six_four_eq Q split n hn m ν T hC μ hB hm hcore hc)
    have hmap (A : Subgroup (X ⧸ Q.D)) :
        rightConjugate (omegaOneAmbient A)
          (representative (Q.simple 0*Q.simple 1*Q.simple 0) : X ⧸ Q.D) =
        omegaOneAmbient (rightConjugate A
          (representative (Q.simple 0*Q.simple 1*Q.simple 0) : X ⧸ Q.D)) := by
      simp only [rightConjugate,comap_equiv_eq_map_symm']
      exact map_omegaOneAmbient_injective _ (MulEquiv.injective _) _
    have hcomm (A D : Subgroup (X ⧸ Q.D)) (w : Weyl Q) :
        rightConjugate ⁅A,D⁆ (representative w : X ⧸ Q.D) =
          ⁅rightConjugate A (representative w : X ⧸ Q.D),
            rightConjugate D (representative w : X ⧸ Q.D)⁆ := by
      simp only [rightConjugate,comap_equiv_eq_map_symm',map_commutator]
    rw [hcomm,
      hmap,(four_interval_reflection Q split hm 1 0 (by decide) _ (representative_spec _)).2.2,
      (four_interval_reflection Q split hm 1 0 (by decide) _ (representative_spec _)).2.1] at hh
    exact hh
  have hCE : Disjoint C E := by
    have hs (k : Fin 2) : Q.simple k*Q.simple k = 1 := by
      simpa only [pow_two] using (Q.tits.involutions _ (Q.simple_mem k)).2
    have hi (k : Fin 2) : (Q.simple k)⁻¹ = Q.simple k := inv_eq_of_mul_eq_one_right (hs k)
    have h7 := wordLength_alternatingWord Q true (n := 7) (by omega)
    have h6 := wordLength_alternatingWord Q true (n := 6) (by omega)
    simp only [alternatingWord,Bool.false_eq_true,↓reduceIte,Bool.not_false,Bool.not_true,mul_one,←mul_assoc] at h7 h6
    apply rootAt_disjoint Q split 1 (Q.simple 0*Q.simple 1) (Q.simple 0*Q.simple 1*Q.simple 0)
    simp only [mul_inv_rev,hi,←mul_assoc,h7,h6]
  have hnot : ¬ omegaOneAmbient C ≤ E := by
    intro hh
    have hz : omegaOneAmbient C = ⊥ := bot_unique ((le_inf (omegaOneAmbient_le C) hh).trans hCE.le_bot)
    have hhcard := omega_card Q split m μ hB (Q.simple 0*Q.simple 1)
    rw [hz,Subgroup.card_bot] at hhcard
    exact (Nat.one_lt_pow (by omega : 2*m+1 ≠ 0) (by decide : 1 < 2)).ne hhcard
  have hON : V ≤ normalizer (O : Set (X ⧸ Q.D)) :=
    (le_centralizer_iff.mp ((source_perpendicular_omega_le_centers Q split n hn m ν T hC μ hB hm hcore hc).2.trans hCZ)).trans
      (_root_.centralizer_le_normalizer _)
  have hZB : ⁅Z,B⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
    (hCZ.trans (centralizer_le hBV))
  have hDB : ⁅⁅V,V⁆,B⁆ ≤ O := by
    apply (commutator_mono le_rfl hBV).trans
    rw [commutator_comm,source_radical_third_eq_omega Q split n hn m ν T hC μ hB hm hcore hc]
  have hJ : ⁅Z ⊔ ⁅V,V⁆,B⁆ ≤ O :=
    commutator_sup_le_of_relative_normal V Z ⁅V,V⁆ B O hON hZV
      (commutator_le_self V) (by rw [hZB]; exact bot_le) hDB
  constructor
  · intro he
    change Z ⊔ E = V at he
    have hnE : V ≤ normalizer (E : Set (X ⧸ Q.D)) := by
      rw [←he]
      exact sup_le ((hCZ.trans (centralizer_le hEV)).trans (_root_.centralizer_le_normalizer _)) E.le_normalizer
    apply hnot
    rw [←hEB]
    exact le_normalizer_iff_commutator_le_left.mp (hBV.trans hnE)
  · apply suzuki_rootAt_intersection_le_omega_of_not_le Q split 1 m μ hB
    · have hNV : Q.tits.B ⊓ Q.tits.N ≤ normalizer (V : Set (X ⧸ Q.D)) :=
        fun h hh => remainder_parabolic_normalizes Q split 1
          (marked_suzuki_remainder_le_kernel Q split 1 m μ hB)
          (Q.tits.B_le_standardParabolic _ hh.1)
      apply le_trans (le_inf
        (hNV.trans (normalizer_le_normalizer_characteristic_image V (center V)))
        (show Q.tits.B ⊓ Q.tits.N ≤ normalizer ((⁅V,V⁆ : Subgroup (X ⧸ Q.D)) : Set (X ⧸ Q.D)) from ?_))
        (normalizer_inf_normalizer_le_normalizer_sup _ _)
      intro h hh
      rw [mem_normalizer_iff_map_conj_eq,map_commutator,
        mem_normalizer_iff_map_conj_eq.mp (hNV hh)]
    · intro he
      apply hnot
      rw [←hEB]
      exact ((commutator_mono he le_rfl).trans hJ).trans (omegaOneAmbient_le E)




include ν hC μ hB hn in
/-- The actual radical center lies in its Frattini subgroup. -/
theorem source_radical_center_le_frattini
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥)
    (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤ pCore 2 (Endpoint Q 1)) :
    center (simpleRemainder Q split 1) ≤ frattini (simpleRemainder Q split 1) := by
  let V := simpleRemainder Q split 1
  let E := rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)
  let Z := (center V).map V.subtype
  let hV := marked_suzuki_remainder_le_kernel Q split 1 m μ hB
  let d := radicalSection Q split 1 hV
  have hd : d.effectiveDenominator = frattini V := by
    rw [d.effectiveDenominator_eq]
    exact sup_bot_eq _
  let : (d.effectiveDenominator : Subgroup V).Normal := d.effectiveDenominator_normal
  let π := QuotientGroup.mk' d.effectiveDenominator
  have hEV : E ≤ V := (octagon_three_roots_le_remainder Q split hm 1 0 (by decide)).2.2
  let πE : E →* d.EffectiveCarrier := π.comp (inclusion hEV)
  let L := πE.range
  let K := (center V).map π ⊔ L
  have hker : πE.ker = (omegaOneAmbient E).subgroupOf E := by
    ext x
    have hmem : πE x = 1 ↔ inclusion hEV x ∈ frattini V := by
      change QuotientGroup.mk (inclusion hEV x) = 1 ↔ _
      rw [QuotientGroup.eq_one_iff,hd]
    rw [MonoidHom.mem_ker,hmem]
    change inclusion hEV x ∈ frattini V ↔ (x : X ⧸ Q.D) ∈ omegaOneAmbient E
    have hI := source_derived_inf_perpendicular_eq_omega Q split n hn m ν T hC μ hB hm hcore hc
    rw [source_radical_derived_eq_frattini Q split n hn m ν T hC μ hB hm hcore hc] at hI
    constructor
    · intro hx
      exact hI.le ⟨⟨inclusion hEV x,hx,rfl⟩,x.property⟩
    · intro hx
      obtain ⟨y,hy,he⟩ := (hI.ge hx).1
      exact (show y = inclusion hEV x from Subtype.ext he) ▸ hy
  have hkcard : Nat.card πE.ker = 2^(2*m+1) := by
    rw [hker,Nat.card_congr (subgroupOfEquivOfLe (omegaOneAmbient_le E)).toEquiv]
    exact omega_card Q split m μ hB _
  have hEcard : Nat.card E = (2^(2*m+1))^2 := by
    change Nat.card (rightConjugate (simpleRoot Q split 1)
      (representative (Q.simple 0*Q.simple 1*Q.simple 0) : X ⧸ Q.D)) = _
    rw [Nat.card_congr (RootAction.conjugateEquiv (simpleRoot Q split 1)
      (representative (Q.simple 0*Q.simple 1*Q.simple 0))).toEquiv,
      Nat.card_congr (suzukiRootEquiv Q split 1 m μ hB).toEquiv,matrixRoot_card]
  have hLcard : Nat.card L = 2^(2*m+1) := by
    have h := πE.ker.card_mul_index
    rw [index_ker,hkcard,hEcard] at h
    apply Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 2^(2*m+1))
    simpa only [pow_two] using h
  let e := suzukiActorEquiv Q split 1 m μ hB
  let f : SuzukiMatrixGroup m →* MulAut d.EffectiveCarrier := d.effectiveAction.comp e.symm.toMonoidHom
  have hf : Function.Injective f :=
    (radical_effectiveAction_injective Q split 1 hV hc).comp e.symm.injective
  have hfix (g : SuzukiMatrixGroup m) : L ≤ (f g).fixedSubgroup := by
    rintro z ⟨x,rfl⟩
    apply (MulAut.mem_fixedSubgroup _ _).mpr
    change d.effectiveAction (e.symm g) (QuotientGroup.mk (inclusion hEV x)) =
      QuotientGroup.mk (inclusion hEV x)
    rw [d.effectiveAction_mk]
    congr 1
    apply Subtype.ext
    rw [d.numeratorAction_apply]
    have hx := (source_suzuki_actor_radical_centralizer Q split n hn m ν T hC μ hB hm hcore hc).ge x.property
    have hcomm := mem_centralizer_iff.mp hx.2 (e.symm g : X ⧸ Q.D) (e.symm g).property
    change (e.symm g : X ⧸ Q.D)*(x : X ⧸ Q.D)*(e.symm g : X ⧸ Q.D)⁻¹ = x
    rw [hcomm,mul_inv_cancel_right]
  have hLinv (g : SuzukiMatrixGroup m) : L.map (f g).toMonoidHom = L := by
    apply le_antisymm
    · rintro z ⟨x,hx,rfl⟩
      change (f g) x ∈ L
      rwa [(MulAut.mem_fixedSubgroup _ _).mp (hfix g hx)]
    · intro z hz
      exact ⟨z,hz,(MulAut.mem_fixedSubgroup _ _).mp (hfix g hz)⟩
  have hKinv (g : SuzukiMatrixGroup m) : K.map (f g).toMonoidHom = K := by
    have heq : (f g).toMonoidHom.comp π = π.comp (d.numeratorAction (e.symm g)).toMonoidHom := by
      ext x
      exact d.effectiveAction_mk (e.symm g) x
    dsimp only [K]
    rw [Subgroup.map_sup,hLinv,map_map,heq,←map_map]
    have hcenter : (center V).map (d.numeratorAction (e.symm g)).toMonoidHom = center V :=
      center_map_equiv (d.numeratorAction (e.symm g))
    rw [hcenter]
  have hLeq : (E.subgroupOf V).map π = L := by
    apply le_antisymm
    · rintro y ⟨x,hx,rfl⟩
      exact ⟨⟨x,hx⟩,rfl⟩
    · rintro y ⟨x,rfl⟩
      exact ⟨inclusion hEV x,x.property,rfl⟩
  have hKt : K ≠ ⊤ := by
    intro ht
    have he : ((center V ⊔ E.subgroupOf V) ⊔ frattini V) = ⊤ := by
      have hh := congrArg (Subgroup.comap π) ht
      dsimp only [K] at hh
      rw [←hLeq,←Subgroup.map_sup,comap_map_eq,QuotientGroup.ker_mk',comap_top] at hh
      rw [hd] at hh
      exact hh
    have hh := frattini_nongenerating he
    have hh' := congrArg (Subgroup.map V.subtype) hh
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hEV,←MonoidHom.range_eq_map,V.range_subtype] at hh'
    exact (center_supplement_bounds Q split n hn m ν T hC μ hB hm hcore hc).1 hh'
  have hWcard : Nat.card d.EffectiveCarrier = (2^(2*m+1))^5 := by
    have hDcard : Nat.card (frattini V) = (2^(2*m+1))^5 := by
      rw [←card_map_of_injective (K := frattini V) V.subtype_injective,
        ←source_radical_derived_eq_frattini Q split n hn m ν T hC μ hB hm hcore hc]
      exact (source_radical_derived_data Q split n hn m ν T hC μ hB hm hcore hc).2
    have hVcard : Nat.card V = (2^(2*m+1))^10 := by
      rw [suzuki_octagon_radical_card Q split 1 0 m μ hB hm (by decide),
        ←rootAt_one Q split 0,linear_rootAt_card Q split 0 n ν T hC hn.pos,
        ree_common_field_exponent Q split hm n hn m ν T hC μ hB (UnitarySource.actorReflection Q split) hcore]
      ring
    have hh := (frattini V).card_mul_index
    rw [hDcard,hVcard] at hh
    change Nat.card (V ⧸ d.effectiveDenominator) = _
    rw [hd]
    apply Nat.eq_of_mul_eq_mul_left (by positivity : 0 < (2^(2*m+1))^5)
    exact hh.trans (by ring)
  have hKL := suzuki_proper_invariant_eq_fixed_layer
    (d.isTwo.to_quotient d.effectiveDenominator) m f hf L K le_sup_right hKt hfix hKinv hWcard hLcard
  intro z hz
  have hzL : π z ∈ L := hKL ▸ (show π z ∈ K from (show (center V).map π ≤ K from le_sup_left) (mem_map_of_mem π hz))
  obtain ⟨a,ha⟩ := hzL
  have hza : π (z*(inclusion hEV a)⁻¹) = 1 := by
    rw [map_mul,map_inv,show π (inclusion hEV a) = π z from ha,mul_inv_cancel]
  have hzaF : z*(inclusion hEV a)⁻¹ ∈ frattini V := by
    rw [←hd]
    exact (QuotientGroup.eq_one_iff _).mp hza
  have hzaD : (z : X ⧸ Q.D)*(a : X ⧸ Q.D)⁻¹ ∈ ⁅V,V⁆ := by
    rw [source_radical_derived_eq_frattini Q split n hn m ν T hC μ hB hm hcore hc]
    exact mem_map_of_mem V.subtype hzaF
  have haJ : (a : X ⧸ Q.D) ∈ Z ⊔ ⁅V,V⁆ := by
    have hh := (Z ⊔ ⁅V,V⁆).mul_mem
      ((Z ⊔ ⁅V,V⁆).inv_mem ((show ⁅V,V⁆ ≤ Z ⊔ ⁅V,V⁆ from le_sup_right) hzaD)) ((show Z ≤ Z ⊔ ⁅V,V⁆ from le_sup_left) (mem_map_of_mem V.subtype hz))
    simpa only [mul_inv_rev,inv_inv,Subgroup.subtype_apply,inv_mul_cancel_right] using hh
  have haO := (center_supplement_bounds Q split n hn m ν T hC μ hB hm hcore hc).2 ⟨haJ,a.property⟩
  have haF : inclusion hEV a ∈ frattini V := by
    have hI := source_derived_inf_perpendicular_eq_omega Q split n hn m ν T hC μ hB hm hcore hc
    have haD := (hI.ge haO).1
    rw [source_radical_derived_eq_frattini Q split n hn m ν T hC μ hB hm hcore hc] at haD
    obtain ⟨y,hy,he⟩ := haD
    exact (show y = inclusion hEV a from Subtype.ext he) ▸ hy
  simpa only [inv_mul_cancel_right] using (frattini V).mul_mem hzaF haF



include ν hC μ hB hn in
/-- The full center of the source Suzuki radical, including q=2. -/
theorem source_radical_center_eq_omega
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥)
    (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤ pCore 2 (Endpoint Q 1)) :
    (center (simpleRemainder Q split 1)).map (simpleRemainder Q split 1).subtype =
      omegaOneAmbient (rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)) := by
  let V := simpleRemainder Q split 1
  let hV := marked_suzuki_remainder_le_kernel Q split 1 m μ hB
  let d := frattiniRadicalSection Q split 1 hV
  let D := d.numerator
  let E := rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)
  let Z := omegaOneAmbient E
  let K := (center V).map V.subtype
  have hD : D = ⁅V,V⁆ := (source_radical_derived_eq_frattini Q split n hn m ν T hC μ hB hm hcore hc).symm
  have hKD : K ≤ D := map_mono
    (source_radical_center_le_frattini Q split n hn m ν T hC μ hB hm hcore hc)
  have hZK : Z ≤ K :=
    (source_perpendicular_omega_le_centers Q split n hn m ν T hC μ hB hm hcore hc).2
  have hKne : K ≠ D := by
    intro he
    have hh : ⁅D,V⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
      (he ▸ center_image_centralizes Q V)
    rw [hD,commutator_comm,source_radical_third_eq_omega Q split n hn m ν T hC μ hB hm hcore hc] at hh
    have hcZ := omega_card Q split m μ hB (Q.simple 0*Q.simple 1*Q.simple 0)
    rw [hh,Subgroup.card_bot] at hcZ
    exact (Nat.one_lt_pow (by omega : 2*m+1 ≠ 0) (by decide : 1 < 2)).ne hcZ
  let e := suzukiActorEquiv Q split 1 m μ hB
  let f : SuzukiMatrixGroup m →* MulAut D := d.numeratorAction.comp e.symm.toMonoidHom
  have hfaith := frattiniRadical_effectiveAction_injective Q split 1 hV m μ hB hm 0 (by decide)
    (source_six_three Q split 1 0 m μ hB ν T hC hm (by decide)).2
  have hf : Function.Injective f := by
    intro a b hab
    apply e.symm.injective
    apply hfaith
    apply MulEquiv.ext
    intro z
    induction z using QuotientGroup.induction_on with
    | H z =>
      rw [d.effectiveAction_mk,d.effectiveAction_mk]
      exact congrArg QuotientGroup.mk (congrArg (fun t : MulAut D => t z) hab)
  have hKN : rankOne Q split 1 ≤ normalizer (K : Set (X ⧸ Q.D)) := by
    intro r hr
    exact normalizer_le_normalizer_characteristic_image V (center V)
      (remainder_parabolic_normalizes Q split 1 hV (rankOne_le_parabolic Q split 1 hr))
  have hKinv (g : SuzukiMatrixGroup m) : (K.subgroupOf D).map (f g).toMonoidHom = K.subgroupOf D := by
    apply map_injective D.subtype_injective
    have heq : D.subtype.comp (f g).toMonoidHom =
        (MulAut.conj (e.symm g : X ⧸ Q.D)).toMonoidHom.comp D.subtype := by
      ext x
      exact d.numeratorAction_apply (e.symm g) x
    rw [map_map,heq,←map_map,map_subgroupOf_eq_of_le hKD]
    exact mem_normalizer_iff_map_conj_eq.mp (hKN (e.symm g).property)
  have hfix (g : SuzukiMatrixGroup m) : Z.subgroupOf D ≤ (f g).fixedSubgroup := by
    intro x hx
    apply (MulAut.mem_fixedSubgroup _ _).mpr
    apply Subtype.ext
    change (e.symm g : X ⧸ Q.D)*(x : X ⧸ Q.D)*(e.symm g : X ⧸ Q.D)⁻¹ = x
    have hcentral := (source_suzuki_actor_radical_centralizer Q split n hn m ν T hC μ hB hm hcore hc).ge
      (omegaOneAmbient_le E hx)
    have hh := mem_centralizer_iff.mp hcentral.2 (e.symm g : X ⧸ Q.D) (e.symm g).property
    change (e.symm g : X ⧸ Q.D)*(x : X ⧸ Q.D) = (x : X ⧸ Q.D)*(e.symm g : X ⧸ Q.D) at hh
    rw [hh,mul_inv_cancel_right]
  have hDcard : Nat.card D = (2^(2*m+1))^5 := by
    rw [hD]
    exact (source_radical_derived_data Q split n hn m ν T hC μ hB hm hcore hc).2
  have hZcard : Nat.card (Z.subgroupOf D) = 2^(2*m+1) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (hZK.trans hKD)).toEquiv]
    exact omega_card Q split m μ hB _
  have hKtop : K.subgroupOf D ≠ ⊤ := by
    intro he
    have hh := congrArg (fun R : Subgroup D => R.map D.subtype) he
    rw [map_subgroupOf_eq_of_le hKD,←MonoidHom.range_eq_map,D.range_subtype] at hh
    exact hKne hh
  have he := suzuki_proper_invariant_eq_fixed_layer d.isTwo m f hf (Z.subgroupOf D) (K.subgroupOf D)
    (subgroupOf_mono D hZK) hKtop hfix hKinv hDcard hZcard
  have hh := congrArg (fun R : Subgroup D => R.map D.subtype) he
  rw [map_subgroupOf_eq_of_le hKD,map_subgroupOf_eq_of_le (hZK.trans hKD)] at hh
  exact hh



include ν hC μ hB hn in
/-- The full unipotent center is the same perpendicular Omega root. -/
theorem source_unipotent_center_eq_omega
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥)
    (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤ pCore 2 (Endpoint Q 1)) :
    (center split.U).map split.U.subtype =
      omegaOneAmbient (rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)) := by
  apply le_antisymm
  · rw [←source_radical_center_eq_omega Q split n hn m ν T hC μ hB hm hcore hc]
    let V := simpleRemainder Q split 1
    have hVU : V ≤ split.U := inf_le_left
    have hVP : V = (Endpoint Q 1).pCoreIn 2 := remainder_eq_endpoint_core Q split 1
      (marked_suzuki_remainder_le_kernel Q split 1 m μ hB)
    rintro z ⟨u,hu,rfl⟩
    let a : Endpoint Q 1 := ⟨u, Q.tits.B_le_standardParabolic _ (split.U_le u.property)⟩
    have ha : a ∈ centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) := by
      apply mem_centralizer_iff.mpr
      intro b hb
      apply Subtype.ext
      have hbV : (b : X ⧸ Q.D) ∈ V := hVP ▸ mem_map_of_mem (Endpoint Q 1).subtype hb
      exact congrArg (fun x : split.U => (x : X ⧸ Q.D)) (mem_center_iff.mp hu ⟨b,hVU hbV⟩)
    have huV : (u : X ⧸ Q.D) ∈ V := by
      rw [hVP]
      exact mem_map_of_mem (Endpoint Q 1).subtype (hc ha)
    refine ⟨⟨u,huV⟩,mem_center_iff.mpr (fun v => ?_),rfl⟩
    exact Subtype.ext (congrArg (fun x : split.U => (x : X ⧸ Q.D)) (mem_center_iff.mp hu ⟨v,hVU v.property⟩))
  · exact (source_perpendicular_omega_le_centers Q split n hn m ν T hC μ hB hm hcore hc).1

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
