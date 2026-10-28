module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixCentralClosureFixedGroups
public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixScalarLayerConjugationAt
public import Theory.Representation.HexacodeAction.FullSignCharacters
public import Theory.Representation.ElementaryCubicEqualFixed

/-!
# The original scalar residual centralizes the exact pair layer

The selected transverse double and triple transpositions have the same fixed
group on P+. The actual scalar operator has order dividing three; the even
lift commutes with it and the odd lift inverts it. The binary fixed-space
obstruction kills that operator and hence the entire literal scalar residual.

Source: Aschbacher--Smith12.7.19, printed p.846.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterE ChapterB.QuasisimpleSource Atlas.Codes
open Theory.SpecificGroups.SymmetricSix MatchingEightGeneration
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- The actual scalar residual centralizes P modulo the original denominator. -/
theorem original_tripleSix_central_closure_scalar
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U) (a : ActionEquiv D.quotientAction Hexacode.evenAction)
    (z : U) (hz : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({(z : G)} : Set G))
    (hnot : ¬ U ≤ (centralizer ({(z : G)} : Set G)).pCoreIn 2)
    (houter : ¬ inducedAutomizer U (conjugateSpanBy (tripleSixPoint D a z)
      (conjugateSpanBy U (centralizer ({(z : G)} : Set G)))) ≤ inducedAutomizer U K) :
    let W := conjugateSpanBy (tripleSixPoint D a z)
      (conjugateSpanBy U (centralizer ({(z : G)} : Set G)))
    ∃ g : K,
      let Wg := W.map (MulAut.conj (g : G)).toMonoidHom
      let I := W ⊔ Wg
      K ≤ I ∧ I=K ⊔ W ∧
        ⁅⁅I.pCoreIn 2,I⁆,tripleSixScalarResidual K⁆ ≤ (W ⊓ Wg) ⊔ U := by
  let W := conjugateSpanBy (tripleSixPoint D a z)
    (conjugateSpanBy U (centralizer ({(z : G)} : Set G)))
  obtain ⟨q,g,hq,_,_,hWg,hKI,hIe,_,_,_,hn,hPmap,_,_,_,helem,_,hfixed⟩ :=
    original_tripleSix_central_closure_fixed_groups h structural D a z hz hzT hnot houter
  let Wg := W.map (MulAut.conj (g : G)).toMonoidHom
  let I := W ⊔ Wg
  let P := ⁅pCore 2 I,(⊤ : Subgroup I)⁆
  let N := ((W ⊓ Wg) ⊔ U).subgroupOf I
  let X := tripleSixScalarResidual K
  let := hn
  let π := QuotientGroup.mk' N
  let V := P.map π
  let : V.Normal := (inferInstance : P.Normal).map π (QuotientGroup.mk'_surjective N)
  let : IsElementaryAbelian 2 V := helem
  let ρ : I →* MulAut V := (MulAut.conjNormal : (I ⧸ N) →* MulAut V).comp π
  have hP : P ≤ ρ.ker := by
    intro p hp
    apply MulEquiv.ext
    intro v
    apply Subtype.ext
    change π p * v.val * (π p)⁻¹=v.val
    rw [← mem_centralizer_iff.mp (V.le_centralizer (mem_map_of_mem π hp)) v.val v.property,
      mul_inv_cancel_right]
  obtain ⟨hWT,f0,hf0,hfk,_,_,_⟩ :=
    original_tripleSix_central_closure_matching h structural D a z hz hzT hnot houter
  have hIM : I ≤ K ⊔ (T : Subgroup G) := hIe.le.trans
    (sup_le le_sup_left (hWT.trans le_sup_right))
  have hIN : I ≤ normalizer (U : Set G) := hIM.trans
    (sup_le D.normalizes (((structural K h).2.2 U D).1))
  let α := U.normalizerMonoidHom.rangeRestrict.comp (inclusion hIN)
  let f := f0.comp α
  have hfk' (k : K) : f (inclusion hKI k)=
      (a.groupEquiv (QuotientGroup.mk' (pCore 2 K) k)).val := hfk k
  obtain ⟨hXI,c,hfc,hc,hce,hco,hgenX⟩ :=
    original_tripleSix_scalar_layer_conjugation_at D a I hKI hIM ρ hP f hfk'
  let E := MulEquiv.ofBijective f0 hf0
  have hsign (b : Automizer U) : (q b).sign=hexSign (f0 b) := by
    have hh := Hexacode.six_quotient_sign (q.comp E.symm.toMonoidHom)
      (hq.comp E.symm.surjective) (E b)
    have hh' : (q b).sign=hexSign (E b) := by
      simpa only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,MulEquiv.symm_apply_apply] using hh
    exact hh'.trans (congrArg hexSign (show E b=f0 b from rfl))
  let d : Equiv.Perm (Fin 6) := Equiv.swap 0 5 * Equiv.swap 1 2
  let e : Equiv.Perm (Fin 6) := d * Equiv.swap 3 4
  have hd : d ∈ shiftedMatchingEight :=
    mul_mem (subset_closure (by simp)) (subset_closure (by simp))
  have he : e ∈ shiftedMatchingEight := mul_mem hd (subset_closure (by simp))
  have hdn : d≠1 := by decide
  have hen : e≠1 := by decide
  have hds : ¬d.IsSwap := by unfold Equiv.Perm.IsSwap; decide
  have hes : ¬e.IsSwap := by unfold Equiv.Perm.IsSwap; decide
  obtain ⟨_,⟨t0,htW,rfl⟩,htq⟩ := (hWg.symm ▸ hd : d ∈ (inducedAutomizer U Wg).map q)
  obtain ⟨_,⟨s0,hsW,rfl⟩,hsq⟩ := (hWg.symm ▸ he : e ∈ (inducedAutomizer U Wg).map q)
  let t : I := ⟨t0.val,mem_sup_right htW⟩
  let s : I := ⟨s0.val,mem_sup_right hsW⟩
  have hte : hexSign (f t)=1 := by
    change hexSign (f0 (α t))=1
    rw [←hsign,show q (α t)=d from htq]
    decide
  have hso : hexSign (f s)=-1 := by
    change hexSign (f0 (α s))=-1
    rw [←hsign,show q (α s)=e from hsq]
    decide
  have hW2 : IsPGroup 2 W := T.isPGroup'.to_le hWT
  have hphi := (original_tripleSix_central_closure_configuration h structural D a z hz hzT hnot).2.2.2.1
  have hZU : zpowers (z : G) ≤ U := zpowers_le.mpr z.property
  have hUconj : U.map (MulAut.conj g.val).toMonoidHom=U :=
    mem_normalizer_iff_map_conj_eq.mp (D.normalizes g.property)
  have hw2 (x : I) (hx : x.val ∈ Wg) : π x * π x=1 := by
    obtain ⟨w,hw,heq⟩ := hx
    let : Fact (IsPGroup 2 W) := ⟨hW2⟩
    have hpow : w^2 ∈ U := hZU (hphi (mem_map_of_mem W.subtype
      (pth_power_mem_frattini_of_isPGroup (p := 2) (⟨w,hw⟩ : W))))
    have hxpow : x.val^2 ∈ U := by
      rw [←heq,←map_pow]
      exact hUconj ▸ mem_map_of_mem (MulAut.conj g.val).toMonoidHom hpow
    have hxN : x*x ∈ N := mem_sup_right (show x.val*x.val ∈ U from by simpa only [pow_two] using hxpow)
    rw [←map_mul]
    exact (QuotientGroup.eq_one_iff _).mpr hxN
  have ht : ρ t * ρ t=1 := by
    change MulAut.conjNormal (π t) * MulAut.conjNormal (π t)=1
    rw [←map_mul,hw2 t htW,map_one]
  have htsfix (v : V) (hv : ρ t v=v) : ρ s v=v := by
    have htv : v.val ∈ V ⊓ centralizer ({π t} : Set (I ⧸ N)) := by
      refine ⟨v.property,mem_centralizer_singleton_iff.mpr ?_⟩
      have hh := congrArg Subtype.val hv
      change π t * v.val * (π t)⁻¹=v.val at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    have htB := hfixed t (hIN t.property) htW (htq.symm ▸ hdn) (htq.symm ▸ hds)
    have hsB := hfixed s (hIN s.property) hsW (hsq.symm ▸ hen) (hsq.symm ▸ hes)
    have hsv : v.val ∈ V ⊓ centralizer ({π s} : Set (I ⧸ N)) :=
      hsB.symm ▸ (htB ▸ htv)
    apply Subtype.ext
    change π s * v.val * (π s)⁻¹=v.val
    rw [← mem_centralizer_singleton_iff.mp hsv.2,mul_inv_cancel_right]
  have hci : (ρ (inclusion hXI c))⁻¹=ρ (inclusion hXI c)^2 := by
    apply inv_eq_of_mul_eq_one_left
    simpa only [←pow_succ] using hc
  have hsc : ρ s * ρ (inclusion hXI c)=ρ (inclusion hXI c)^2 * ρ s := by
    have hh := hco s hso
    rw [hci] at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  have hc1 := MulAut.cubic_eq_one_of_fixed_containment
    (ρ (inclusion hXI c)) (ρ t) (ρ s) hc ht (hce t hte) hsc htsfix
  have hXone := hgenX hc1
  have hcomm : ⁅P,X.subgroupOf I⁆ ≤ N := by
    apply commutator_le.mpr
    intro p hp x hx
    apply (QuotientGroup.eq_one_iff _).mp
    change π ⁅p,x⁆=1
    rw [map_commutatorElement]
    apply commutatorElement_eq_one_iff_mul_comm.mpr
    have hh := congrArg (fun a : MulAut V => (a ⟨π p,mem_map_of_mem π hp⟩).val)
      (hXone (⟨x.val,hx⟩ : X))
    change π x * π p * (π x)⁻¹=π p at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  have hmap := map_mono (f := I.subtype) hcomm
  rw [map_commutator,hPmap,map_subgroupOf_eq_of_le hXI] at hmap
  have hUI : U ≤ I := D.le_component.trans hKI
  rw [map_subgroupOf_eq_of_le (sup_le (inf_le_left.trans le_sup_left) hUI)] at hmap
  exact ⟨g,hKI,hIe,hmap⟩

end CFSG.Quasithin.Chapter12.Section07
