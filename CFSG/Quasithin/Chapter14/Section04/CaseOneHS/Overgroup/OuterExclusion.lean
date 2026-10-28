module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Overgroup.OuterPointCentralizer
public import Theory.GroupTheory.CentralizerOrbitTransfer

/-!
# Excluding the order-eight shadow in original 14.3.33

Ambient simplicity and extremal Thompson transfer produce an inner
conjugate of the original outer involution, carrying its whole Sylow
centralizer. The point-centralizer placement keeps that transport when
moving the involution to PU. The source centralizer bounds force equality
of the transported centralizers, contradicting their characteristic-point
obstruction. This proves U=O₂(H) on the actual source subgroups.

Source: Aschbacher--Smith, 14.3.33(3), printed p.1005.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Overgroup
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Extremal transfer and the original characteristic point exclude the
order-eight cubic centralizer, including the shadow of Aut(HS). -/
theorem cubic_centralizer_card_ne_eight
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (s : LocalStructure L F) (hne : ¬ IsMulCommutative F.U)
    (x : G) (hx : x ∈ F.Li L 1) (hx3 : orderOf x = 3) :
    Nat.card (F.H.pCoreIn 2 ⊓ centralizer (zpowers x : Set G) : Subgroup G) ≠ 8 := by
  intro hcard
  let := h.chosen.elementary
  let := h.source.simpleQTKE.simple
  obtain ⟨r,hr,hrL,hr2,hd⟩ := exists_outer_involution h structural alternatives F s hne x hx hx3 hcard
  have hrT := point_core_le_sylow F hr.1
  let rT : T := ⟨r,hrT⟩
  have hrT2 : orderOf rT = 2 := (Subgroup.orderOf_coe rT).symm.trans hr2
  obtain ⟨y,g,hg,hyL,hCg,_⟩ := T.exists_isConj_mem_with_saturated_centralizer_transport
    (index_ne_two_of_nonabelian_simple h.source.simpleQTKE.nonabelian)
    (L.subgroupOf (T : Subgroup G))
    (inner_sylow_index_two h structural alternatives F s hne x hx hx3 hcard) rT hrT2
  have hconj : IsConj r (y : G) := isConj_iff.mpr ⟨g,hg⟩
  have hy2 : orderOf (y : G) = 2 :=
    (congrArg orderOf hg).symm.trans (((MulAut.conj g).orderOf_eq r).trans hr2)
  have hyP : (y : G) ∉ L.pCoreIn 2 := by
    intro hyP
    have hyPow : (y : G)^2 = 1 := by simpa only [hy2] using pow_orderOf_eq_one (y : G)
    have hyV := (centerSpan_square_kernel_and_card h structural alternatives F s hne).1 (y : G)
      ((centerSpan_eq_core h structural alternatives F s hne).symm ▸ hyP) |>.mp hyPow
    exact outer_involution_not_fused_into_seed h structural alternatives F s hne x hx hx3 hcard
      r hr hrL hr2 hd y hyV hconj
  let C := (T : Subgroup G) ⊓ centralizer ({r} : Set G)
  let R := C.map (MulAut.conj g).toMonoidHom
  have hpC : IsPGroup 2 C := T.isPGroup'.of_injective (inclusion inf_le_left) (inclusion_injective _)
  have hRM : R ≤ L ⊔ (T : Subgroup G) := (hCg.trans inf_le_left).trans le_sup_right
  obtain ⟨k,_,hkPU,hkT⟩ := actor_involution_core_closure_centralizer_placement h structural alternatives
    F s hne y hyL hy2 hyP R (hpC.map _) hRM (hCg.trans inf_le_right)
  let a := k*g
  have hay : MulAut.conj a r = k*(y:G)*k⁻¹ := by
    change (k*g)*r*(k*g)⁻¹ = _
    rw [← hg]
    simp only [rT,MulAut.conj_apply,mul_inv_rev,mul_assoc]
  have haPU : MulAut.conj a r ∈ L.pCoreIn 2 ⊔ F.U := hay.symm ▸ hkPU
  have haT : C.map (MulAut.conj a).toMonoidHom ≤ (T : Subgroup G) := by
    have he : (MulAut.conj a).toMonoidHom =
        (MulAut.conj k).toMonoidHom.comp (MulAut.conj g).toMonoidHom := by
      ext v
      simp only [a,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,MulAut.conj_apply,mul_inv_rev,mul_assoc]
    rw [he,← map_map]
    exact hkT
  have haConj : IsConj r (MulAut.conj a r) := isConj_iff.mpr ⟨a,rfl⟩
  have haU : MulAut.conj a r ∉ F.U := fun hh =>
    outer_involution_not_fused_into_closure h structural alternatives F s hne x hx hx3 hcard
      r hr hrL hr2 hd _ hh haConj
  have haP : MulAut.conj a r ∉ L.pCoreIn 2 := by
    intro hp
    have hpow : (MulAut.conj a r)^2 = 1 := by
      rw [←map_pow]
      have he : r^2=1 := hr2 ▸ pow_orderOf_eq_one r
      rw [he,map_one]
    have hv := (centerSpan_square_kernel_and_card h structural alternatives F s hne).1 _
      ((centerSpan_eq_core h structural alternatives F s hne).symm ▸ hp) |>.mp hpow
    exact outer_involution_not_fused_into_seed h structural alternatives F s hne x hx hx3 hcard
      r hr hrL hr2 hd _ hv haConj
  let D := (T : Subgroup G) ⊓ centralizer ({MulAut.conj a r} : Set G)
  have hCD : C.map (MulAut.conj a).toMonoidHom ≤ D := by
    refine le_inf haT ?_
    rintro _ ⟨c,hc,rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    change MulAut.conj a c * MulAut.conj a r = MulAut.conj a r * MulAut.conj a c
    simpa only [map_mul] using congrArg (MulAut.conj a) (mem_centralizer_singleton_iff.mp hc.2)
  have hCc : Nat.card C = 128 := outer_involution_sylow_centralizer_card h structural alternatives
    F s hne x hx hx3 hcard r hr hrL hr2 hd
  have hQ : Nat.card (F.H.pCoreIn 2) = 128 := by
    rw [point_core_card_eq_sixteen_mul_cubic_centralizer h structural alternatives F s hne x hx hx3,hcard]
  have hb := core_closure_nonclosure_sylow_centralizer_bound h structural alternatives F s hne
    _ haPU haP haU
  rw [sylow_card_of_point_core_card F s hQ] at hb
  have heq : C.map (MulAut.conj a).toMonoidHom = D := eq_of_le_of_card_ge hCD (by
    rw [card_map_of_injective (MulAut.conj a).injective,hCc]
    change 8*Nat.card D ≤ 1024 at hb
    omega)
  have hright : (a⁻¹)⁻¹*r*a⁻¹ = MulAut.conj a r := by simp only [inv_inv,MulAut.conj_apply]
  apply outer_involution_no_centralizer_conjugate h structural alternatives F s hne
    x hx hx3 hcard r hr hrL hr2 hd a⁻¹ (hright.symm ▸ haPU) (hright.symm ▸ haU)
  change C.map (MulAut.conj (a⁻¹)⁻¹).toMonoidHom = _
  simpa only [D,inv_inv,MulAut.conj_apply] using heq

/-- Original 14.3.33(3): the point two-core is exactly the original U. -/
theorem source_closure_core
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (s : LocalStructure L F) (hne : ¬ IsMulCommutative F.U) :
    F.U = F.H.pCoreIn 2 := by
  obtain ⟨x,hx,hx3⟩ := exists_point_cubic h structural alternatives F s hne
  rcases closure_core_or_outer_cubic h structural alternatives F s hne x hx hx3 with he | he
  · exact he
  · exact (cubic_centralizer_card_ne_eight h structural alternatives F s hne x hx hx3 he.2.1).elim

end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Overgroup
