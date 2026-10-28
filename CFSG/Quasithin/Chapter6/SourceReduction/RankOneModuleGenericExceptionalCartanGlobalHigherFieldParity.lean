module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalHigherFieldOmega
public import Theory.Representation.OrthogonalFourMinusRankOne.AmbientActions.Elementary
public import Theory.FieldTheory.FiniteAutomorphismOrder

/-!
# Divisibility by four in the original Hermitian Cartan branch

A Sylow element acts on the actual Hermitian omega-span through the literal
quotient L/O₂(L). Its coefficient action on the half-field is a two-element.
At odd half-degree that coefficient is trivial; the scalar-commutant theorem
then makes its module lift linear over the half-field. The fixed space of
T ∩ L is one-dimensional over that field and contains a nonzero omega-point.
Since T fixes this point, it fixes the whole line, identifying that line with
the original omega-center. The local Borel therefore normalizes omega.

When the original field degree exceeds two, the proved Hermitian non-FF
argument makes H centralize omega. A zero-core Cartan join is consequently
impossible at odd half-degree, giving 4 ∣ n for the original exponent. With
universal local control, the actual minus torus normalizes O²(H) and the
plus torus has a zero-core join with H. This proves the parity and factor
premises of 5.1.6(4); the numerical bound from 3.1.6 and the selection of the
Hermitian model remain separate obligations.

Source: Aschbacher--Smith 5.1.6(4) and 5.2.2, printed pp.632--633,647
(`refs/quasithin.pdf`).
-/

set_option backward.isDefEq.respectTransparency false

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation
open scoped MatrixGroups
open Representation.OrthogonalFourMinus
open Representation.OrthogonalFourMinus.FiniteModel
open Representation.OrthogonalFourMinus.RankOne
open Representation.OrthogonalFourMinus.RankOne.AmbientActions
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
local instance (s : ℕ) : Algebra (ZMod 2) (fixedField s) := ZMod.algebra _ 2
local instance (s : ℕ) [NeZero s] : Module (ZMod 2) (Space s) :=
  Module.compHom (Space s) (algebraMap (ZMod 2) (fixedField s))

private theorem odd_half_intertwiner_linear (s : ℕ) [NeZero s] (hs : Odd s)
    (α : MulAut SL(2,Field s)) (hα : ∃ k : ℕ, α^(2^k)=1)
    (E : Space s ≃ₗ[ZMod 2] Space s)
    (hE : ∀ g w, E (SL2.BinarySmall.hermitian s g w) =
      SL2.BinarySmall.hermitian s (α g) (E w)) :
    ∀ (c : fixedField s) w, E (c • w) = c • E w := by
  let p := SL2AutomorphismNatural.parameterEquiv.symm α
  let g := p.left
  let σ := p.right
  have heα : α = MulAut.conj g * BenderSuzuki.ZD.Linear.sl2FieldAut σ :=
    (SL2AutomorphismNatural.parameterEquiv.apply_symm_apply α).symm
  let res : (Field s ≃+* Field s) →* (fixedField s ≃+* fixedField s) :=
    { toFun := fieldRestriction s
      map_one' := by ext x; rfl
      map_mul' := by intros; ext x; rfl }
  have hr : res σ = 1 := by
    let : Finite (fixedField s ≃+* fixedField s) := Finite.of_injective
      (fun f : fixedField s ≃+* fixedField s => (f : fixedField s → fixedField s))
      DFunLike.coe_injective
    have hd : orderOf (res σ) ∣ s := (_root_.orderOf_dvd_natCard _).trans
      (dvd_of_eq (FiniteField.card_ringAut_of_card_prime_pow Nat.prime_two (card_fixedField s)))
    obtain ⟨k,hk⟩ := hα
    have hp : (res σ)^(2^k)=1 := by
      change res (SL2AutomorphismNatural.fieldAction α) ^ (2^k) = 1
      rw [←map_pow,←map_pow,hk,map_one,map_one]
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
      (hs.coprime_two_right.pow_right k) hd (orderOf_dvd_of_pow_eq_one hp))
  let e₀ : Space s ≃+ Space s := (fieldLift s σ).trans
    (LinearMap.GeneralLinearGroup.toLinearEquiv ((action s).asGroupHom g)).toAddEquiv
  have he₀ (b : SL(2,Field s)) (w : Space s) :
      e₀ (action s b w) = action s (α b) (e₀ w) := by
    change action s g (fieldLift s σ (action s b w)) =
      action s (α b) (action s g (fieldLift s σ w))
    rw [heα]
    change action s g (fieldLift s σ (action s b w)) =
      action s (g * BenderSuzuki.ZD.Linear.sl2FieldAut σ b * g⁻¹)
        (action s g (fieldLift s σ w))
    rw [fieldLift_action]
    simp only [←Module.End.mul_apply,←map_mul,inv_mul_cancel_right]
  let f := e₀.symm.toAddMonoidHom.comp E.toAddMonoidHom
  obtain ⟨c,hc⟩ := commuting_addHom_eq_scalar s f (by
    intro b w
    apply e₀.injective
    change e₀ (e₀.symm (E (action s b w))) = e₀ (action s b (e₀.symm (E w)))
    rw [e₀.apply_symm_apply,he₀,e₀.apply_symm_apply]
    exact hE b w)
  have hform (w : Space s) : E w = e₀ (c • w) := by
    have hh := congrArg e₀ (hc w)
    change e₀ (e₀.symm (E w)) = _ at hh
    rwa [e₀.apply_symm_apply] at hh
  have hσfix (d : fixedField s) : fieldRestriction s σ d = d :=
    DFunLike.congr_fun hr d
  intro d w
  rw [hform,hform]
  change action s g (fieldLift s σ (c • d • w)) = d • action s g (fieldLift s σ (c • w))
  rw [smul_comm c d,fieldLift_smul,hσfix,map_smul]

private theorem sylow_fixed_line (s : ℕ) [NeZero s]
    (S : Sylow 2 SL(2,Field s)) (z x : Space s)
    (hz : z ∈ BinaryOffender.fixedSpace (SL2.BinarySmall.hermitian s) S)
    (hx : x ∈ BinaryOffender.fixedSpace (SL2.BinarySmall.hermitian s) S)
    (hz0 : z ≠ 0) : ∃ c : fixedField s, x = c • z := by
  obtain ⟨a,_,ha,_⟩ := Matrix.SpecialLinearGroup.sylow_odd_subgroup_diagonal_coordinates
    S ⊥ bot_le (by simp)
  have hfixed (w : Space s)
      (hw : w ∈ BinaryOffender.fixedSpace (SL2.BinarySmall.hermitian s) S) :
      action s a w ∈ invariants
        ((action s).comp (Matrix.SpecialLinearGroup.upperUnipotent (Field s)).subtype) := by
    rw [←ha]
    intro b
    obtain ⟨b₀,hb₀,he⟩ := b.property
    change action s (b : SL(2,Field s)) (action s a w) = action s a w
    rw [←he]
    change action s (a*b₀*a⁻¹) (action s a w) = _
    simp only [←Module.End.mul_apply,←map_mul,inv_mul_cancel_right]
    rw [map_mul,Module.End.mul_apply]
    exact congrArg (action s a) (hw ⟨b₀,hb₀⟩)
  let z' : invariants ((action s).comp (Matrix.SpecialLinearGroup.upperUnipotent (Field s)).subtype) :=
    ⟨action s a z,hfixed z hz⟩
  let x' : invariants ((action s).comp (Matrix.SpecialLinearGroup.upperUnipotent (Field s)).subtype) :=
    ⟨action s a x,hfixed x hx⟩
  have hzne : upperFixedEquivK s z' ≠ 0 := by
    intro he
    have he' : z' = 0 := (upperFixedEquivK s).injective (he.trans (map_zero _).symm)
    exact hz0 ((action s).apply_bijective a |>.injective
      ((congrArg Subtype.val he').trans (map_zero _).symm))
  let c : fixedField s := upperFixedEquivK s x' / upperFixedEquivK s z'
  let y' : invariants ((action s).comp (Matrix.SpecialLinearGroup.upperUnipotent (Field s)).subtype) :=
    ⟨c • z'.val, (invariants ((action s).comp
      (Matrix.SpecialLinearGroup.upperUnipotent (Field s)).subtype)).smul_mem c z'.property⟩
  have he : x' = y' := by
    apply (upperFixedEquivK s).injective
    change upperFixedEquivK s x' = c * upperFixedEquivK s z'
    exact (div_mul_cancel₀ _ hzne).symm
  refine ⟨c,(action s).apply_bijective a |>.injective ?_⟩
  exact (congrArg Subtype.val he).trans (map_smul _ _ _).symm


variable {G : Type*} [Group G] [Finite G]

/-- At odd half-degree the original Borel normalizes the whole Sylow omega-center. -/
theorem Input.hermitian_odd_half_borel_normalizes_omega
    {T : Sylow 2 G} {L W : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (s : ℕ) [NeZero s] (hs : Odd s)
    (hm : IsConjugationModel L
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L)
      (SL2.BinarySmall.hermitian s)) :
    localBorel T L ≤ normalizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) := by
  let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L
  have hu := LocalOmega.span_elementary_le_sylow T L (h.qtke.evenCharacteristic T)
    h.maximal_local.1 h.sylow_normalizes
  have hr := LocalOmega.span_reduced T L (h.qtke.evenCharacteristic T)
    h.maximal_local.1 h.sylow_normalizes
  let : IsElementaryAbelian 2 U := hu.1
  have hred : U ∈ reducedFamily (L ⊔ (T : Subgroup G)) :=
    ⟨hu.2.trans le_sup_right,hu.1,hr.normal,hr.quotient_pCore_eq_bot⟩
  have hTU : (T : Subgroup G) ≤ normalizer (U : Set G) :=
    le_sup_right.trans (reduced_normalizes hred)
  have hZU : omegaOneCenterAmbient (T : Subgroup G) ≤ U := le_conjugateSpanBy _ _
  obtain ⟨e,f,hf⟩ := hm
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let ρ := SL2.BinarySmall.hermitian s
  have hact (l : L) (v : Space s) :
      (f.symm (Multiplicative.ofAdd (ρ (q l) v)) : G) =
        (l : G)*(f.symm (Multiplicative.ofAdd v) : G)*(l : G)⁻¹ := by
    have he := hf l (f.symm (Multiplicative.ofAdd v))
    change (f.symm (Multiplicative.ofAdd
      (ρ (q l) (f (f.symm (Multiplicative.ofAdd v))).toAdd)) : G) = _ at he
    simpa only [f.apply_symm_apply,toAdd_ofAdd] using he
  obtain ⟨P,hP⟩ := NormalSylowQuotientAction.intersection_sylow T L h.sylow_normalizes
  let S := P.mapSurjective hq
  have hfixed (u : U) (huZ : (u : G) ∈ omegaOneCenterAmbient (T : Subgroup G)) :
      (f u).toAdd ∈ BinaryOffender.fixedSpace ρ S := by
    intro g
    obtain ⟨l,hl,he⟩ := g.property
    change ρ g.val (f u).toAdd = _
    rw [←he]
    apply Multiplicative.ofAdd.injective
    apply f.symm.injective
    apply U.subtype_injective
    change (f.symm (Multiplicative.ofAdd (ρ (q l) (f u).toAdd)) : G) = (f.symm (f u) : G)
    rw [f.symm_apply_apply,hact,ofAdd_toAdd,f.symm_apply_apply]
    change l ∈ (P : Subgroup L) at hl
    have hlT : (l : G) ∈ (T : Subgroup G) := by rwa [hP] at hl
    have hc := ((mem_omegaOneCenterAmbient_iff _ _).mp huZ).2.2 l hlT
    rw [hc,mul_inv_cancel_right]
  have hW0 : W ≠ ⊥ := fun he => h.noncentral (by rw [he,commutator_bot_left])
  obtain ⟨z,hz1⟩ := ne_bot_iff_exists_ne_one.mp
    (inf_centerIn_ne_bot T.isPGroup' hW0 h.reduced_le_sylow
      (le_sup_right.trans (reduced_normalizes h.reduced)))
  have hzZ : (z : G) ∈ omegaOneCenterAmbient (T : Subgroup G) := by
    let := h.reduced.2.1
    exact (mem_omegaOneCenterAmbient_iff _ _).mpr
      ⟨h.reduced_le_sylow z.property.1,
        elemPow_eq_one_of_isElementaryAbelian (p:=2) (z:G) z.property.1,z.property.2.2⟩
  let zU : U := ⟨z,hZU hzZ⟩
  have hz0 : (f zU).toAdd ≠ 0 := by
    intro he
    have hh : zU = 1 := f.injective (he.trans f.map_one.symm)
    exact hz1 (Subtype.ext (congrArg (fun u : U => (u : G)) hh))
  have hline (v : Space s) (hv : v ∈ BinaryOffender.fixedSpace ρ S) :
      (f.symm (Multiplicative.ofAdd v) : G) ∈ omegaOneCenterAmbient (T : Subgroup G) := by
    obtain ⟨c,hc⟩ := sylow_fixed_line s S (f zU).toAdd v (hfixed zU hzZ) hv hz0
    let u : U := f.symm (Multiplicative.ofAdd v)
    apply (mem_omegaOneCenterAmbient_iff _ _).mpr
    refine ⟨hu.2 u.property,elemPow_eq_one_of_isElementaryAbelian (p:=2) (u:G) u.property,?_⟩
    intro t ht
    let β := U.normalizerMonoidHom ⟨t,hTU ht⟩
    let ea : Space s ≃+ Space s :=
      f.toAdditiveLeft.symm.trans (β.toAdditive.trans f.toAdditiveLeft)
    let E : Space s ≃ₗ[ZMod 2] Space s :=
      { __ := ea
        map_smul' := ZMod.map_smul ea }
    have hEv (w : Space s) :
        (f.symm (Multiplicative.ofAdd (E w)) : G) =
          t * (f.symm (Multiplicative.ofAdd w) : G) * t⁻¹ := by
      change (f.symm (f (β (f.symm (Multiplicative.ofAdd w)))) : G) = _
      rw [f.symm_apply_apply]
      rfl
    let αhom : T →* MulAut SL(2,Field s) :=
      (MulAut.congr e).toMonoidHom.comp
        ((pCoreJoinAction 2 h.sylow_normalizes).comp (inclusion le_sup_right))
    let α := αhom ⟨t,ht⟩
    have hαq (l : L) : α (q l) = q (L.normalizerMonoidHom ⟨t,h.sylow_normalizes ht⟩ l) := by
      change e (pCoreJoinAction 2 h.sylow_normalizes (inclusion le_sup_right ⟨t,ht⟩)
        (e.symm (e (QuotientGroup.mk' (pCore 2 L) l)))) = _
      rw [e.symm_apply_apply,pCoreJoinAction_mk]
      rfl
    have hE (g : SL(2,Field s)) (w : Space s) : E (ρ g w) = ρ (α g) (E w) := by
      obtain ⟨l,rfl⟩ := hq g
      apply Multiplicative.ofAdd.injective
      apply f.symm.injective
      apply U.subtype_injective
      change (f.symm (Multiplicative.ofAdd (E (ρ (q l) w))) : G) =
        (f.symm (Multiplicative.ofAdd (ρ (α (q l)) (E w))) : G)
      rw [hEv,hact,hαq,hact,hEv]
      change t * ((l:G) * _ * (l:G)⁻¹) * t⁻¹ =
        (t*(l:G)*t⁻¹) * (t * _ * t⁻¹) * (t*(l:G)*t⁻¹)⁻¹
      group
    have hαpow : ∃ k : ℕ, α^(2^k)=1 := by
      obtain ⟨k,hk⟩ := T.isPGroup'.exists_pow_pow_eq_one ⟨t,ht⟩
      exact ⟨k,by change αhom ⟨t,ht⟩ ^ (2^k)=1; rw [←map_pow,hk,map_one]⟩
    have hlin := odd_half_intertwiner_linear s hs α hαpow E hE
    have hEz : E (f zU).toAdd = (f zU).toAdd := by
      apply Multiplicative.ofAdd.injective
      apply f.symm.injective
      apply U.subtype_injective
      change (f.symm (Multiplicative.ofAdd (E (f zU).toAdd)) : G) = (f.symm (f zU) : G)
      rw [hEv,ofAdd_toAdd,f.symm_apply_apply]
      have hzcomm := ((mem_omegaOneCenterAmbient_iff _ _).mp hzZ).2.2 t ht
      change t * (z : G) * t⁻¹ = (z : G)
      rw [hzcomm,mul_inv_cancel_right]
    have hEvfix : E v = v := by rw [hc,hlin,hEz]
    have he := hEv v
    rw [hEvfix] at he
    exact mul_inv_eq_iff_eq_mul.mp he.symm
  have hnorm (l : L) (hl : (l : G) ∈ localBorel T L) :
      q l ∈ normalizer (S : Set SL(2,Field s)) := by
    have hN : l ∈ normalizer (P : Set L) := by
      have hh : (l : G) ∈ (normalizer ((T : Subgroup G).subgroupOf L : Set L)).map L.subtype := by
        rwa [←localBorel_eq_map]
      have hh' := (mem_map_iff_mem L.subtype_injective).mp hh
      change l ∈ normalizer ((P : Subgroup L) : Set L)
      rw [hP]
      exact hh'
    exact (Subgroup.le_normalizer_map (H := (P : Subgroup L)) q) (mem_map_of_mem q hN)
  have hstable (a : G) (ha : a ∈ localBorel T L) (x : G)
      (hx : x ∈ omegaOneCenterAmbient (T : Subgroup G)) :
      a*x*a⁻¹ ∈ omegaOneCenterAmbient (T : Subgroup G) := by
    let aL : L := ⟨a,ha.1⟩
    let xU : U := ⟨x,hZU hx⟩
    have hxfix := hfixed xU hx
    have haxfix : ρ (q aL) (f xU).toAdd ∈ BinaryOffender.fixedSpace ρ S :=
      (BinaryOffender.fixedSpace_stable_of_normalizes ρ (le_refl (normalizer (S : Set SL(2,Field s))))
        (hnorm aL ha) (f xU).toAdd).2 hxfix
    have hh := hline _ haxfix
    rw [hact,ofAdd_toAdd,f.symm_apply_apply] at hh
    exact hh
  intro a ha
  apply mem_normalizer_iff.mpr
  intro x
  constructor
  · exact hstable a ha x
  · intro hx
    have hh := hstable a⁻¹ ((localBorel T L).inv_mem ha) _ hx
    simpa only [inv_inv,inv_mul_cancel_left,mul_assoc,mul_inv_cancel_right,inv_mul_cancel,mul_one] using hh


/-- The zero-core Hermitian branch has original degree divisible by four.
The Borel would normalize omega at odd half-degree, contradicting zero core. -/
theorem Input.hermitian_four_dvd_of_zero_core
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hn : 2 < n)
    (hzero : (A ⊔ H).pCoreIn 2 = ⊥) (s : ℕ) [NeZero s]
    (hm : IsConjugationModel L
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L)
      (SL2.BinarySmall.hermitian s)) : 4 ∣ n := by
  have hn' := h.exponent_of_hermitian_model s hm
  have hs : 1 < s := by omega
  have he : Even s := by
    by_contra hodd
    have hBN := h.hermitian_odd_half_borel_normalizes_omega s
      (Nat.not_even_iff_odd.mp hodd) hm
    have hHC := h.hermitian_omega_span_centralizes hH s hs hm
    have hnorm : A ⊔ H ≤ normalizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) :=
      sup_le (c.left_le.trans hBN) (hHC.trans (Subgroup.centralizer_le_normalizer _))
    have hZT : omegaOneCenterAmbient (T : Subgroup G) ≤ (T : Subgroup G) :=
      fun x hx => ((mem_omegaOneCenterAmbient_iff _ _).mp hx).1
    have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
    have hZcore := le_pCoreIn_of_normalizes (T.isPGroup'.to_le hZT)
      (hZT.trans (hTH.trans le_sup_right)) hnorm
    have hW0 : W ≠ ⊥ := fun he => h.noncentral (by rw [he,commutator_bot_left])
    have hT0 : (T : Subgroup G) ≠ ⊥ := fun he => hW0 (bot_unique (he ▸ h.reduced_le_sylow))
    let : Nontrivial T := (nontrivial_iff_ne_bot _).mpr hT0
    have hZ0 : omegaOneCenterAmbient (T : Subgroup G) ≠ ⊥ := by
      intro he
      exact omega_center_ne_bot T.isPGroup'
        ((Subgroup.map_eq_bot_iff_of_injective _ (f := (T : Subgroup G).subtype)
          (T : Subgroup G).subtype_injective).mp he)
    exact hZ0 (bot_unique (hzero ▸ hZcore))
  obtain ⟨k,hk⟩ := he
  exact ⟨k,by omega⟩

/-- Under universal local control and failure of normalization, the actual
Hermitian torus has a normalizing minus factor and a zero-core plus join.
Only the later numerical bound, not parity or these factor premises, remains. -/
theorem Input.hermitian_torus_of_escape
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hn : 2 < n)
    (hcontrol : CartanLocalControl A H)
    (hescape : ¬ A ≤ normalizer (residual H : Set G)) (s : ℕ) [NeZero s]
    (hm : IsConjugationModel L
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L)
      (SL2.BinarySmall.hermitian s)) :
    4 ∣ n ∧ ∃ Dminus Dplus : Subgroup G,
      Dminus ⊔ Dplus = A ∧ Nat.card Dminus = 2^(n/2)+1 ∧
      Nat.card Dplus = 2^(n/2)-1 ∧
      Dminus ⊔ H ≤ omegaCentralizer T ∧
      (Dminus ⊔ H).pCoreIn 2 ≠ ⊥ ∧
      Dminus ≤ normalizer (residual H : Set G) ∧
      (Dplus ⊔ H).pCoreIn 2 = ⊥ := by
  have hzero := hcontrol.core_eq_bot_of_not_normalizes le_rfl hescape
  have hfour := h.hermitian_four_dvd_of_zero_core hH c hn hzero s hm
  obtain ⟨he,Dm,Dp,hjoin,hmc,hpc,hmfix⟩ := c.hermitian_torus_factors h s hm
    (le_conjugateSpanBy _ _)
  have hs : 1 < s := by omega
  have hh : n/2 = s := by omega
  have hcentral := sup_le hmfix (h.hermitian_omega_span_centralizes hH s hs hm)
  have hcore := core_ne_bot_of_omega_centralizes hH.1.1.2 hH.1.1.1 hcentral
  have hmN := hcontrol Dm (hjoin ▸ le_sup_left) hcore
  refine ⟨hfour,Dm,Dp,hjoin,hh ▸ hmc,hh ▸ hpc,hcentral,hcore,hmN,?_⟩
  by_contra hp
  exact hescape (hjoin ▸ sup_le hmN (hcontrol Dp (hjoin ▸ le_sup_right) hp))

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
