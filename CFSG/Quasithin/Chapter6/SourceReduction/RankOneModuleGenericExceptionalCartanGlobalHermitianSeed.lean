module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalHigherFieldDegree
public import Theory.GroupTheory.ReducedNormal.SylowCentralSeed
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalSubmodule
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalHigherFieldTorus
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalHigherFieldSpan
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalHigherFieldParity
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalHigherFieldQrc
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalHigherFieldDegree

/-!
# The higher-field Cartan bound from one Hermitian constituent

Use the actual intersection of a Sylow-invariant Hermitian constituent U
with Ω₁Z(T). This seed is nontrivial, and the original minus torus fixes
it pointwise. At odd half-degree the entire Borel normalizes it, giving a
nontrivial normal two-subgroup of AH. Thus zero core forces even half-degree.

The plus-torus orbit fills the Hermitian Sylow-fixed line. Its reducedness,
faithful torus action and compatible Hall normalization give the literal
qrc hypotheses. Zero core of the plus join excludes common normal subgroups,
and the regular cyclic action bounds the half-degree by four. Universal
local control applies to the minus join's actual nonzero core, forcing
zero core of the plus join under escape. This yields n = 4 or 8 and the
required small Cartan generation, including the order-seventeen factor.

All actions use L/O₂(L) and the same original Cartan. No model of the whole
omega-span, splitting, or equality of the original and residual degrees is
assumed. The stationary selection consumer supplies U and its coordinates.
The internal imports continue the existing torus and qrc calculations.

Source: Aschbacher--Smith 5.1.6(4) and 5.2.2, pp.632--633,647,
using B.2.14 and 3.1.5--6 (`refs/quasithin.pdf`).
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation
open CFSG.Quasithin.ChapterD CFSG.Quasithin.ChapterD.UniqueFactor
open scoped IsMulCommutative MatrixGroups
open Representation.OrthogonalFourMinus Representation.BinaryOffender
open Representation.OrthogonalFourMinus.FiniteModel
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
local instance cartanGlobalHermitianSeedFixedFieldAlgebra (s : ℕ) : Algebra (ZMod 2) (fixedField s) := ZMod.algebra _ 2
local instance cartanGlobalHermitianSeedBinarySpace (s : ℕ) [NeZero s] : Module (ZMod 2) (Space s) :=
  Module.compHom (Space s) (algebraMap (ZMod 2) (fixedField s))
private theorem hermitian_seed_plus_span
    {T : Sylow 2 G} {L W H A B D U₀ : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    [IsElementaryAbelian 2 U₀]
    (hUT : U₀ ≤ (T : Subgroup G)) (hTU : (T : Subgroup G) ≤ normalizer (U₀ : Set G))
    (hU0 : U₀ ≠ ⊥)
    (c : CartanPair T L H A B) (s : ℕ) [NeZero s]
    (hm : IsConjugationModel L
      U₀
      (SL2.BinarySmall.hermitian s))
    (hDA : D ≤ A) (hDc : Nat.card D = 2^s-1) :
    let V := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G) ⊓ U₀) D
    V = U₀ ⊓ centralizer (((T : Subgroup G) ⊓ L : Subgroup G) : Set G) ∧
    Nat.card V = 2^s ∧
    A ⊔ (T : Subgroup G) ≤ normalizer (V : Set G) ∧
    D ⊓ centralizer (V : Set G) = ⊥ := by
  let Z := omegaOneCenterAmbient (T : Subgroup G) ⊓ U₀
  let V := conjugateSpanBy Z D
  let C := U₀ ⊓ centralizer (((T : Subgroup G) ⊓ L : Subgroup G) : Set G)
  obtain ⟨hCc,hfix⟩ := hermitian_fixed_geometry s h.sylow_normalizes hm
  change Nat.card C = 2^s at hCc
  have hZT : Z ≤ (T : Subgroup G) := fun _ hx => ((mem_omegaOneCenterAmbient_iff _ _).mp hx.1).1
  have hZC : Z ≤ C := by
    intro z hz
    exact ⟨hz.2,fun t ht =>
      ((mem_omegaOneCenterAmbient_iff _ _).mp hz.1).2.2 t ht.1⟩
  have hLU : L ≤ normalizer (U₀ : Set G) := hm.normalizes
  have hTinter : (T : Subgroup G) ≤ normalizer (((T : Subgroup G) ⊓ L : Subgroup G) : Set G) :=
    (le_inf (T : Subgroup G).le_normalizer h.sylow_normalizes).trans inf_normalizer_le_normalizer_inf
  have hnorm : A ⊔ (T : Subgroup G) ≤ normalizer (C : Set G) := by
    apply (le_inf (sup_le ((c.left_le.trans inf_le_left).trans
      hLU) hTU)
      (sup_le (c.left_le.trans inf_le_right) hTinter |>.trans
        (normalizer_le_normalizer_centralizer _))).trans inf_normalizer_le_normalizer_inf
  have hVC : V ≤ C := conjugateSpanBy_le hZC (hDA.trans (le_sup_left.trans hnorm))
  obtain ⟨z,hz1⟩ := ne_bot_iff_exists_ne_one.mp
    (inf_centerIn_ne_bot T.isPGroup' hU0 hUT hTU)
  have hzZ : (z:G) ∈ Z :=
    ⟨(mem_omegaOneCenterAmbient_iff _ _).mpr
      ⟨hUT z.property.1,elemPow_eq_one_of_isElementaryAbelian (p:=2) (z:G) z.property.1,
        z.property.2.2⟩,z.property.1⟩
  have hz0 : (z:G) ≠ 1 := fun he => hz1 (Subtype.ext he)
  have hodd : Odd (2^s-1) := by
    have hh := (even_two : Even (2:ℕ)).pow_of_ne_zero (NeZero.ne s)
    have hp : 0 < (2:ℕ)^s := pow_pos (by decide) _
    exact Nat.odd_iff.mpr (by have := Nat.even_iff.mp hh; omega)
  have hcop : (2^s+1).Coprime (2^s-1) := by
    have hp : 0 < (2:ℕ)^s := pow_pos (by decide) _
    rw [show 2^s+1 = (2^s-1)+2 by omega,Nat.coprime_self_add_left]
    exact hodd.coprime_two_left
  have hfree (x : G) (hx : x ∈ D) (he : x*(z:G)*x⁻¹=(z:G)) : x=1 := by
    have hd : orderOf x ∣ 2^s-1 := by
      rw [←hDc,←Subgroup.orderOf_mk x hx]
      exact _root_.orderOf_dvd_natCard _
    have hn := (hfix x (c.left_le (hDA hx)) (hodd.of_dvd_nat hd)
      z (hZC hzZ) hz0).mp he
    exact orderOf_eq_one_iff.mp
      (Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hn) hd)
  let orb : D → V := fun d =>
    ⟨(d:G)*(z:G)*(d:G)⁻¹,subset_closure ⟨d,d.property,z,hzZ,rfl⟩⟩
  have horb0 (d : D) : orb d ≠ 1 := by
    intro he
    apply hz0
    have hh := congrArg Subtype.val he
    change (MulAut.conj (d:G)) (z:G) = 1 at hh
    exact (MulAut.conj (d:G)).map_eq_one_iff.mp hh
  have hi : Function.Injective orb := by
    intro a b he
    have hh : (b:G)*(z:G)*(b:G)⁻¹=(a:G)*(z:G)*(a:G)⁻¹ :=
      (congrArg Subtype.val he).symm
    have hf := hfree ((a:G)⁻¹*(b:G)) (D.mul_mem (D.inv_mem a.property) b.property) (by
      calc
        (a:G)⁻¹*(b:G)*(z:G)*((a:G)⁻¹*(b:G))⁻¹ =
            (a:G)⁻¹*((b:G)*(z:G)*(b:G)⁻¹)*(a:G) := by group
        _ = (z:G) := by rw [hh]; group)
    exact Subtype.ext (inv_mul_eq_one.mp hf)
  let f : Option D → V := fun d => d.elim 1 orb
  have hfi : Function.Injective f := by
    intro a b he
    cases a with
    | none =>
      cases b with
      | none => rfl
      | some b => exact (horb0 b he.symm).elim
    | some a =>
      cases b with
      | none => exact (horb0 a he).elim
      | some b => exact congrArg some (hi he)
  have hlow := Nat.card_le_card_of_injective f hfi
  have hopt : Nat.card (Option D) = Nat.card D+1 := by
    let : Fintype D := Fintype.ofFinite D
    simp only [Nat.card_eq_fintype_card,Fintype.card_option]
  rw [hopt,hDc] at hlow
  have hp : 0 < (2:ℕ)^s := pow_pos (by decide) _
  have he : V = C := eq_of_le_of_card_ge hVC (by omega)
  change V = C ∧ Nat.card V = 2^s ∧ A ⊔ (T : Subgroup G) ≤ normalizer (V : Set G) ∧ _
  refine ⟨he,by rw [he]; exact hCc,by rw [he]; exact hnorm,?_⟩
  apply _root_.eq_bot_iff.mpr
  intro x hx
  apply mem_bot.mpr
  apply hfree x hx.1
  exact mul_inv_eq_iff_eq_mul.mpr ((hx.2 z (le_conjugateSpanBy Z D hzZ)).symm)


private theorem hermitian_seed_plus_reduced
    {T : Sylow 2 G} {L W H A B D U₀ : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    [IsElementaryAbelian 2 U₀]
    (hUT : U₀ ≤ (T : Subgroup G)) (hTU : (T : Subgroup G) ≤ normalizer (U₀ : Set G))
    (hU0 : U₀ ≠ ⊥)
    (c : CartanPair T L H A B) (s : ℕ) [NeZero s]
    (hm : IsConjugationModel L U₀ (SL2.BinarySmall.hermitian s))
    (hDA : D ≤ A) (hDc : Nat.card D = 2^s-1) :
    let Z := omegaOneCenterAmbient (T : Subgroup G) ⊓ U₀
    conjugateSpanBy Z D = conjugateSpanBy Z A ∧
    conjugateSpanBy Z D ∈ reducedFamily (D ⊔ (T : Subgroup G)) := by
  let Z := omegaOneCenterAmbient (T : Subgroup G) ⊓ U₀
  let X := conjugateSpanBy Z D
  let J := D ⊔ (T : Subgroup G)
  have hg := hermitian_seed_plus_span h hUT hTU hU0 c s hm hDA hDc
  have hXU : X ≤ U₀ := hg.1.le.trans inf_le_left
  let : IsElementaryAbelian 2 X := IsElementaryAbelian.of_le hXU
  have hXJ : X ≤ J := hXU.trans (hUT.trans le_sup_right)
  have hn : J ≤ normalizer (X : Set G) := (sup_le_sup_right hDA _).trans hg.2.2.1
  have hspan : X = conjugateSpanBy Z J := le_antisymm
    (conjugateSpanBy_mono le_rfl le_sup_left)
    (conjugateSpanBy_le (le_conjugateSpanBy Z D) hn)
  have hr := reduced_of_sylow_central_seed T J X Z le_sup_right hXJ hn
    (le_conjugateSpanBy Z D)
    (fun _ hz => ((mem_omegaOneCenterAmbient_iff _ _).mp hz.1).2.2) hspan
  refine ⟨le_antisymm (conjugateSpanBy_mono le_rfl hDA)
    (conjugateSpanBy_le (le_conjugateSpanBy Z D) (le_sup_left.trans hg.2.2.1)),
    hXJ,inferInstance,hr.normal,hr.quotient_pCore_eq_bot⟩
private theorem hermitian_seed_odd_half
    {T : Sylow 2 G} {L W U₀ : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    [IsElementaryAbelian 2 U₀]
    (hUT : U₀ ≤ (T : Subgroup G)) (hTU : (T : Subgroup G) ≤ normalizer (U₀ : Set G))
    (hU0 : U₀ ≠ ⊥)
    (s : ℕ) [NeZero s] (hs : Odd s)
    (hm : IsConjugationModel L
      U₀
      (SL2.BinarySmall.hermitian s)) :
    localBorel T L ≤ normalizer ((omegaOneCenterAmbient (T : Subgroup G) ⊓ U₀ : Subgroup G) : Set G) := by
  have hLU : L ≤ normalizer (U₀ : Set G) := hm.normalizes
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
  have hfixed (u : U₀) (huZ : (u : G) ∈ omegaOneCenterAmbient (T : Subgroup G)) :
      (f u).toAdd ∈ BinaryOffender.fixedSpace ρ S := by
    intro g
    obtain ⟨l,hl,he⟩ := g.property
    change ρ g.val (f u).toAdd = _
    rw [←he]
    apply Multiplicative.ofAdd.injective
    apply f.symm.injective
    apply U₀.subtype_injective
    change (f.symm (Multiplicative.ofAdd (ρ (q l) (f u).toAdd)) : G) = (f.symm (f u) : G)
    rw [f.symm_apply_apply,hact,ofAdd_toAdd,f.symm_apply_apply]
    change l ∈ (P : Subgroup L) at hl
    have hlT : (l : G) ∈ (T : Subgroup G) := by rwa [hP] at hl
    have hc := ((mem_omegaOneCenterAmbient_iff _ _).mp huZ).2.2 l hlT
    rw [hc,mul_inv_cancel_right]
  obtain ⟨z,hz1⟩ := ne_bot_iff_exists_ne_one.mp
    (inf_centerIn_ne_bot T.isPGroup' hU0 hUT hTU)
  have hzZ : (z:G) ∈ omegaOneCenterAmbient (T : Subgroup G) :=
    (mem_omegaOneCenterAmbient_iff _ _).mpr
      ⟨hUT z.property.1,elemPow_eq_one_of_isElementaryAbelian (p:=2) (z:G) z.property.1,
        z.property.2.2⟩
  let zU : U₀ := ⟨z,z.property.1⟩
  have hz0 : (f zU).toAdd ≠ 0 := by
    intro he
    have hh : zU = 1 := f.injective (he.trans f.map_one.symm)
    exact hz1 (Subtype.ext (congrArg (fun u : U₀ => (u : G)) hh))
  have hline (v : Space s) (hv : v ∈ BinaryOffender.fixedSpace ρ S) :
      (f.symm (Multiplicative.ofAdd v) : G) ∈ omegaOneCenterAmbient (T : Subgroup G) := by
    obtain ⟨c,hc⟩ := sylow_fixed_line s S (f zU).toAdd v (hfixed zU hzZ) hv hz0
    let u : U₀ := f.symm (Multiplicative.ofAdd v)
    apply (mem_omegaOneCenterAmbient_iff _ _).mpr
    refine ⟨hUT u.property,elemPow_eq_one_of_isElementaryAbelian (p:=2) (u:G) u.property,?_⟩
    intro t ht
    let β := U₀.normalizerMonoidHom ⟨t,hTU ht⟩
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
      apply U₀.subtype_injective
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
      apply U₀.subtype_injective
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
      (hx : x ∈ omegaOneCenterAmbient (T : Subgroup G) ⊓ U₀) :
      a*x*a⁻¹ ∈ omegaOneCenterAmbient (T : Subgroup G) ⊓ U₀ := by
    let aL : L := ⟨a,ha.1⟩
    let xU : U₀ := ⟨x,hx.2⟩
    have hxfix := hfixed xU hx.1
    have haxfix : ρ (q aL) (f xU).toAdd ∈ BinaryOffender.fixedSpace ρ S :=
      (BinaryOffender.fixedSpace_stable_of_normalizes ρ (le_refl (normalizer (S : Set SL(2,Field s))))
        (hnorm aL ha) (f xU).toAdd).2 hxfix
    have hh := hline _ haxfix
    rw [hact,ofAdd_toAdd,f.symm_apply_apply] at hh
    exact ⟨hh,(mem_normalizer_iff.mp (hLU ha.1) x).mp hx.2⟩
  intro a ha
  apply mem_normalizer_iff.mpr
  intro x
  constructor
  · exact hstable a ha x
  · intro hx
    have hh := hstable a⁻¹ ((localBorel T L).inv_mem ha) _ hx
    simpa only [inv_inv,inv_mul_cancel_left,mul_assoc,mul_inv_cancel_right,inv_mul_cancel,mul_one] using hh


private theorem hermitian_seed_qrc
    {T : Sylow 2 G} {L W H A B D U₀ : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    [IsElementaryAbelian 2 U₀]
    (hUT : U₀ ≤ (T : Subgroup G)) (hTU : (T : Subgroup G) ≤ normalizer (U₀ : Set G))
    (hU0 : U₀ ≠ ⊥)
    (c : CartanPair T L H A B) (s : ℕ) [NeZero s] (_hs : 1 < s)
    (hm : IsConjugationModel L
      U₀
      (SL2.BinarySmall.hermitian s))
    (hHC : H ≤ omegaCentralizer T)
    (hDA : D ≤ A) (hDc : Nat.card D = 2^s-1) :
    Chapter3.QrcHypotheses T (normalizer (L : Set G))
      (D ⊔ (T : Subgroup G)) H
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G) ⊓ U₀) D) := by
  let Z := omegaOneCenterAmbient (T : Subgroup G) ⊓ U₀
  let X := conjugateSpanBy Z D
  let J := D ⊔ (T : Subgroup G)
  have hg := hermitian_seed_plus_span h hUT hTU hU0 c s hm hDA hDc
  obtain ⟨hspan,hr⟩ := hermitian_seed_plus_reduced h hUT hTU hU0 c s hm hDA hDc
  let := hr.2.1
  have hJN : J ≤ normalizer (X : Set G) := reduced_normalizes hr
  have hcore := reduced_torus_centralizer hr
    (torus_join_card c h.sylow_normalizes h.linear hDA) hg.2.2.2
  have hBN : B ≤ normalizer (X : Set G) := by
    rw [show X = conjugateSpanBy Z A from hspan]
    exact normalizes_conjugateSpanBy Z A B
      ((c.right_le.trans inf_le_right).trans
        (hHC.trans ((centralizer_le inf_le_left).trans (Subgroup.centralizer_le_normalizer _)))) c.right_normalizes_left
  refine ⟨le_sup_right,
    sup_le (hDA.trans (c.left_le.trans (inf_le_left.trans L.le_normalizer))) h.sylow_normalizes,
    hH,hr.1,hJN,hr.2.1,?_,hcore,Or.inr ?_⟩
  · exact Chapter3.Section02.internalActionImage_core_of_reduced J X hr.1 hJN
      (show IsPReduced 2 (X.subgroupOf J) from ⟨hr.2.2.choose,IsElementaryAbelian.subgroupOf hr.1,hr.2.2.choose_spec⟩)
  · rw [inf_comm,←c.sylow_sup_right h.sylow_normalizes hH.1.1.2]
    exact sup_le (le_sup_right.trans hJN) hBN

/-- Zero core of the literal plus-torus/H join eliminates common normal
subgroups directly. No uniqueness over the smaller torus join is assumed. -/
private theorem hermitian_seed_configuration
    {T : Sylow 2 G} {L W H A B D U₀ : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    [IsElementaryAbelian 2 U₀]
    (hUT : U₀ ≤ (T : Subgroup G)) (hTU : (T : Subgroup G) ≤ normalizer (U₀ : Set G))
    (hU0 : U₀ ≠ ⊥)
    (c : CartanPair T L H A B) (s : ℕ) [NeZero s] (hs : 1 < s)
    (hm : IsConjugationModel L
      U₀
      (SL2.BinarySmall.hermitian s))
    (hHC : H ≤ omegaCentralizer T)
    (hDA : D ≤ A) (hDc : Nat.card D = 2^s-1)
    (hz : (D ⊔ H).pCoreIn 2 = ⊥) :
    ChapterD.QRCConfiguration (D ⊔ (T : Subgroup G)) H (T : Subgroup G)
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G) ⊓ U₀) D) := by
  have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
  have hq := hermitian_seed_qrc h hH hUT hTU hU0 c s hs hm hHC hDA hDc
  apply hq.toQRCConfiguration
  rintro ⟨N,hNc,hN,hn⟩
  have hNT : N ≤ (T : Subgroup G) := hNc.trans (hq.core_eq_centralizer ▸ inf_le_left)
  have hgen : Chapter3.generated (D ⊔ (T : Subgroup G)) H = D ⊔ H := by
    rw [Chapter3.generated_eq_sup,sup_assoc,sup_eq_right.mpr hTH]
  have hnorm : D ⊔ H ≤ normalizer (N : Set G) := by
    simpa only [hgen] using (Chapter3.normalIn_iff_le_normalizer.mp hn).2
  have hcore := le_pCoreIn_of_normalizes (T.isPGroup'.to_le hNT)
    (hNT.trans (hTH.trans le_sup_right)) hnorm
  exact hN (bot_unique (hz ▸ hcore))

private theorem hermitian_seed_cubic
    {T : Sylow 2 G} {L W H A B D U₀ : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    [IsElementaryAbelian 2 U₀]
    (hUT : U₀ ≤ (T : Subgroup G)) (hTU : (T : Subgroup G) ≤ normalizer (U₀ : Set G))
    (hU0 : U₀ ≠ ⊥)
    (c : CartanPair T L H A B) (s : ℕ) [NeZero s] (hs : 1 < s)
    (hm : IsConjugationModel L
      U₀
      (SL2.BinarySmall.hermitian s))
    (hHC : H ≤ omegaCentralizer T)
    (hDA : D ≤ A) (hDc : Nat.card D = 2^s-1)
    (hz : (D ⊔ H).pCoreIn 2 = ⊥) :
    let X := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G) ⊓ U₀) D
    let hq := hermitian_seed_qrc h hH hUT hTU hU0 c s hs hm hHC hDA hDc
    letI := hq.module_elementary
    cubicRatio (imageRepresentation (D ⊔ (T : Subgroup G)) X hq.module_normalized) ≤ 2 := by
  let Z := omegaOneCenterAmbient (T : Subgroup G) ⊓ U₀
  let X := conjugateSpanBy Z D
  let hq := hermitian_seed_qrc h hH hUT hTU hU0 c s hs hm hHC hDA hDc
  let d := hermitian_seed_configuration h hH hUT hTU hU0 c s hs hm hHC hDA hDc hz
  have hg := hermitian_seed_plus_span h hUT hTU hU0 c s hm hDA hDc
  have hne : X ≠ ⊥ := by
    intro he
    have hh := hg.2.1
    change Nat.card X = 2^s at hh
    rw [he,Subgroup.card_bot] at hh
    have hp : 1 < (2:ℕ)^s := Nat.one_lt_pow (NeZero.ne s) (by decide)
    omega
  have hBV : H ⊓ normalizer (L : Set G) ≤ normalizer (X : Set G) := by
    rw [inf_comm,←c.sylow_sup_right h.sylow_normalizes hH.1.1.2]
    apply sup_le (le_sup_right.trans hq.module_normalized)
    have hspan := (hermitian_seed_plus_reduced h hUT hTU hU0 c s hm hDA hDc).1
    change B ≤ normalizer (conjugateSpanBy Z D : Set G)
    rw [hspan]
    exact normalizes_conjugateSpanBy Z A B
      ((c.right_le.trans inf_le_right).trans
        (hHC.trans ((centralizer_le inf_le_left).trans
          (Subgroup.centralizer_le_normalizer _)))) c.right_normalizes_left
  exact normalized_cubicRatio_le_two hq h.qtke h.maximal d hne hBV

private theorem hermitian_seed_degree_le_eight
    {T : Sylow 2 G} {L W H A B D U₀ : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    [IsElementaryAbelian 2 U₀]
    (hUT : U₀ ≤ (T : Subgroup G)) (hTU : (T : Subgroup G) ≤ normalizer (U₀ : Set G))
    (hU0 : U₀ ≠ ⊥)
    (c : CartanPair T L H A B) (s : ℕ) [NeZero s] (hs : 1 < s)
    (hm : IsConjugationModel L
      U₀
      (SL2.BinarySmall.hermitian s))
    (hHC : H ≤ omegaCentralizer T)
    (hDA : D ≤ A) (hDc : Nat.card D = 2^s-1)
    (hz : (D ⊔ H).pCoreIn 2 = ⊥) : n ≤ 8 := by
  let X := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G) ⊓ U₀) D
  let J := D ⊔ (T : Subgroup G)
  let U := (T : Subgroup G) ⊓ L
  let hq := hermitian_seed_qrc h hH hUT hTU hU0 c s hs hm hHC hDA hDc
  let := hq.module_elementary
  have hg := hermitian_seed_plus_span h hUT hTU hU0 c s hm hDA hDc
  have hJ : J ≤ normalizer (X : Set G) := hq.module_normalized
  let f := actionHom D X (le_sup_left.trans hJ)
  let C := internalActionImage D X (le_sup_left.trans hJ)
  obtain ⟨F,_,_,_,_,⟨e⟩⟩ := c.left_equiv_units h.linear h.sylow_normalizes
  let : IsCyclic A := isCyclic_of_injective e.toMonoidHom e.injective
  let : IsCyclic D := isCyclic_of_injective (inclusion hDA) (inclusion_injective hDA)
  let : IsCyclic C := isCyclic_of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hfi : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    rw [actionHom_ker]
    apply _root_.eq_bot_iff.mpr
    intro d hd
    apply mem_bot.mpr
    apply Subtype.ext
    exact mem_bot.mp (hg.2.2.2 ▸ (show (d:G) ∈ D ⊓ centralizer (X : Set G) from
      ⟨d.property,hd⟩))
  have hregD := Theory.GroupAction.faithful_cyclic_binary_singer_regular f hfi hs hDc hg.2.1
  have hreg : ∀ v w : X, v ≠ 1 → w ≠ 1 → ∃! a : C, a.val v = w := by
    intro v w hv hw
    obtain ⟨d,hd,hu⟩ := hregD v w hv hw
    refine ⟨f.rangeRestrict d,hd,?_⟩
    intro a ha
    obtain ⟨b,hb⟩ := f.rangeRestrict_surjective a
    rw [←hb] at ha ⊢
    exact congrArg f.rangeRestrict (hu b ha)
  have hTB : (T : Subgroup G) ≤ normalizer (localBorel T L : Set G) :=
    (le_inf h.sylow_normalizes
      ((le_inf (T : Subgroup G).le_normalizer h.sylow_normalizes).trans
        inf_normalizer_le_normalizer_inf |>.trans (normalizer (U : Set G)).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  have hTN : (T : Subgroup G) ≤ normalizer ((U ⊔ D : Subgroup G) : Set G) :=
    hTB.trans (Prime.cartan_subgroup_preimage_normalized c h.sylow_normalizes h.linear hDA)
  have hUC : U ≤ centralizer (X : Set G) := by
    apply le_centralizer_iff.mp
    change conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G) ⊓ U₀) D ≤ _
    rw [hg.1]
    exact inf_le_right
  have hN : internalActionImage J X hJ ≤ normalizer (C : Set (MulAut X)) :=
    image_normalizes_torus hJ (inf_le_left.trans le_sup_right) le_sup_left hUC
      (sup_le (le_sup_right.trans (U ⊔ D).le_normalizer) hTN)
  have hc := regular_cyclic_normalizer_cubic_card_le C (internalActionImage J X hJ)
    hreg hN (imageRepresentation J X hJ) (fun _ _ => rfl)
      (hermitian_seed_cubic h hH hUT hTU hU0 c s hs hm hHC hDA hDc hz)
  rw [hg.2.1] at hc
  have hs4 : s ≤ 4 := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hc
  have he := h.exponent_of_hermitian_model s hm
  omega


private theorem hermitian_seed_torus_factors
    {T : Sylow 2 G} {L W H A B U : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (c : CartanPair T L H A B) (s : ℕ) [NeZero s]
    (hm : IsConjugationModel L U (Representation.SL2.BinarySmall.hermitian s)) :
    n = 2*s ∧ ∃ Dminus Dplus : Subgroup G,
      Dminus ⊔ Dplus = A ∧ Nat.card Dminus = 2^s+1 ∧
        Nat.card Dplus = 2^s-1 ∧ Dminus ≤ centralizer ((omegaOneCenterAmbient (T : Subgroup G) ⊓ U : Subgroup G) : Set G) := by
  have hn := h.exponent_of_hermitian_model s hm
  obtain ⟨F,_,_,_,hF,⟨e⟩⟩ := c.left_equiv_units h.linear h.sylow_normalizes
  let : IsCyclic A := isCyclic_of_injective e.toMonoidHom e.injective
  have hc : Nat.card A = (2^s+1)*(2^s-1) := by
    rw [c.left_card h.linear h.sylow_normalizes,hn,pow_mul']
    have hp : 0 < (2:ℕ)^s := pow_pos (by decide) _
    have he : 2^s - 1 + 1 = 2^s := Nat.sub_add_cancel hp
    have he2 := Nat.sub_add_cancel (show 1 ≤ ((2 : ℕ)^s)^2 from pow_pos hp 2)
    nlinarith
  have hcop : (2^s+1).Coprime (2^s-1) := by
    have hp : 0 < (2:ℕ)^s := pow_pos (by decide) _
    have he : 2^s+1 = (2^s-1)+2 := by omega
    rw [he,Nat.coprime_self_add_left]
    apply Nat.prime_two.coprime_iff_not_dvd.mpr
    have hv := (even_two : Even (2 : ℕ)).pow_of_ne_zero (NeZero.ne s)
    have hmod := Nat.even_iff.mp hv
    intro hd
    have := Nat.mod_eq_zero_of_dvd hd
    omega
  obtain ⟨Dm,Dp,hs,hmcard,hpcard⟩ := cyclic_split A (2^s+1) (2^s-1) hc hcop
  refine ⟨hn,Dm,Dp,hs,hmcard,hpcard,?_⟩
  intro x hx z hz
  have hp : x^(2^s+1)=1 := by
    have hh := congrArg Subtype.val (pow_card_eq_one' (x := (⟨x,hx⟩ : Dm)))
    simpa only [hmcard,Subgroup.coe_pow,Subgroup.coe_one] using hh
  exact (mem_centralizer_singleton_iff.mp
    (hermitian_minus_root_fixes_omega_intersection s h.sylow_normalizes hm
      (c.left_le (hs ▸ (mem_sup_left hx))) hp hz.2 hz.1)).symm


private theorem elementary_seed_ne_bot
    {T : Sylow 2 G} {U : Subgroup G} [IsElementaryAbelian 2 U]
    (hUT : U ≤ (T : Subgroup G)) (hTU : (T : Subgroup G) ≤ normalizer (U : Set G))
    (hU0 : U ≠ ⊥) : omegaOneCenterAmbient (T : Subgroup G) ⊓ U ≠ ⊥ := by
  obtain ⟨z,hz1⟩ := ne_bot_iff_exists_ne_one.mp
    (inf_centerIn_ne_bot T.isPGroup' hU0 hUT hTU)
  have hz : (z:G) ∈ omegaOneCenterAmbient (T : Subgroup G) ⊓ U :=
    ⟨(mem_omegaOneCenterAmbient_iff _ _).mpr
      ⟨hUT z.property.1,elemPow_eq_one_of_isElementaryAbelian (p:=2) (z:G) z.property.1,
        z.property.2.2⟩,z.property.1⟩
  intro he
  exact hz1 (Subtype.ext (mem_bot.mp (he ▸ hz)))

/-- The actual Hermitian constituent suffices for the higher-field Cartan
reduction. Its central Sylow points supply the nontrivial minus-join core;
the same plus-join line gives the numerical bound. -/
theorem Input.hermitian_seed_degree_and_smallGeneration
    {T : Sylow 2 G} {L W H A B U : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) [IsElementaryAbelian 2 U]
    (hUT : U ≤ (T : Subgroup G)) (hTU : (T : Subgroup G) ≤ normalizer (U : Set G))
    (hU0 : U ≠ ⊥) (s : ℕ) [NeZero s] (hs : 1 < s)
    (hm : IsConjugationModel L U (SL2.BinarySmall.hermitian s))
    (hHC : H ≤ omegaCentralizer T) (hcontrol : CartanLocalControl A H)
    (hescape : ¬ A ≤ normalizer (residual H : Set G)) :
    (n = 4 ∨ n = 8) ∧ CartanSmallGeneration A H n := by
  let Z := omegaOneCenterAmbient (T : Subgroup G) ⊓ U
  have hZ0 : Z ≠ ⊥ := elementary_seed_ne_bot hUT hTU hU0
  have hZT : Z ≤ (T : Subgroup G) := inf_le_right.trans hUT
  have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
  have hHZ : H ≤ centralizer (Z : Set G) := hHC.trans (centralizer_le inf_le_left)
  have hz := hcontrol.core_eq_bot_of_not_normalizes le_rfl hescape
  have he := h.exponent_of_hermitian_model s hm
  have heven : Even s := by
    by_contra hodd
    have hBN := hermitian_seed_odd_half h hUT hTU hU0 s
      (Nat.not_even_iff_odd.mp hodd) hm
    have hnorm : A ⊔ H ≤ normalizer (Z : Set G) :=
      sup_le (c.left_le.trans hBN) (hHZ.trans (Subgroup.centralizer_le_normalizer _))
    have hcore := le_pCoreIn_of_normalizes (T.isPGroup'.to_le hZT)
      (hZT.trans (hTH.trans le_sup_right)) hnorm
    exact hZ0 (bot_unique (hz ▸ hcore))
  obtain ⟨_,Dm,Dp,hjoin,hmc,hpc,hmfix⟩ := hermitian_seed_torus_factors h c s hm
  have hDmA : Dm ≤ A := hjoin ▸ le_sup_left
  have hDpA : Dp ≤ A := hjoin ▸ le_sup_right
  have hcore : (Dm ⊔ H).pCoreIn 2 ≠ ⊥ := by
    intro hzero
    have hn : Dm ⊔ H ≤ normalizer (Z : Set G) :=
      (sup_le hmfix hHZ).trans (Subgroup.centralizer_le_normalizer _)
    have hc := le_pCoreIn_of_normalizes (T.isPGroup'.to_le hZT)
      (hZT.trans (hTH.trans le_sup_right)) hn
    exact hZ0 (bot_unique (hzero ▸ hc))
  have hmN := hcontrol Dm hDmA hcore
  have hpzero : (Dp ⊔ H).pCoreIn 2 = ⊥ := by
    by_contra hp
    exact hescape (hjoin ▸ sup_le hmN (hcontrol Dp hDpA hp))
  have hb := hermitian_seed_degree_le_eight h hH hUT hTU hU0 c s hs hm hHC hDpA hpc hpzero
  obtain ⟨k,hk⟩ := heven
  have hn : n = 4 ∨ n = 8 := by omega
  refine ⟨hn,?_⟩
  rcases hn with hn | hn
  · exact h.cartanSmallGeneration_of_degree_two_or_four hH c (Or.inr hn)
  · have hs4 : s = 4 := by omega
    have h15 : Nat.card Dp = 15 := by simpa [hs4] using hpc
    obtain ⟨F,_,_,_,_,⟨e⟩⟩ := c.left_equiv_units h.linear h.sylow_normalizes
    let : IsCyclic A := isCyclic_of_injective e.toMonoidHom e.injective
    let : IsCyclic Dp := isCyclic_of_injective (inclusion hDpA) (inclusion_injective hDpA)
    obtain ⟨D3,D5,h35,h3,h5⟩ := cyclic_split Dp 3 5 h15 (by decide)
    exact ⟨Or.inr (Or.inr hn),Dm,D3,D5,
      by rw [sup_assoc,h35,hjoin],hcore,Or.inr h3,Or.inr h5⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
