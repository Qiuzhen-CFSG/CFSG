module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.LinearEndpoints.NormalizerCubicCentralizer
public import Theory.SpecificGroups.Alternating.FiveLocalGeometry.CubicCentralizer

/-!
# The original natural endpoint has self-centralizing cubics

The quotient is the retained natural SL2(4), whose cubic centralizer has
order three. The actual radical has no fixed points, making the restricted
quotient injective. Thus the whole endpoint centralizer is the original
cyclic subgroup, with no coordinate change.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G] {A : Subgroup G} [IsElementaryAbelian 2 A]

/-- Every specified original cubic is self-centralizing inside its natural endpoint. -/
theorem NaturalEndpointData.cubic_endpoint_centralizer (d : NaturalEndpointData A)
    (t : G) (ht : t∈d.carrier) (ht3 : orderOf t=3) :
    d.carrier⊓centralizer ({t}:Set G)=zpowers t := by
  let E := d.carrier⊓centralizer ({t}:Set G)
  let T : d.carrier := ⟨t,ht⟩
  have hT : orderOf T=3 := (orderOf_coe T).symm.trans ht3
  have hk : IsPGroup 2 d.quotient.ker := by
    rw [d.quotient_kernel]
    exact (IsElementaryAbelian.isPGroup (p := 2) (G := A)).comap_subtype
  have hqT : orderOf (d.quotient T)=3 :=
    (d.quotient.orderOf_map_eq_of_coprime_of_isPGroup_ker hk T
      (by rw [hT]; decide)).trans hT
  let C := centralizer ({d.quotient T}:Set Representation.SL2FourNatural.SL)
  have hc : Nat.card C=3 := by
    have hh := alternatingGroup.FiveLocalGeometry.cubic_centralizer_card
      Representation.SL2FourNatural.alternatingFiveEquiv (zpowers (d.quotient T))
      (by rw [Nat.card_zpowers,hqT])
    simpa only [zpowers_eq_closure,centralizer_closure] using hh
  let f : E→*C := (d.quotient.comp (inclusion (show E≤d.carrier from inf_le_left))).codRestrict C (by
    intro x
    apply mem_centralizer_singleton_iff.mpr
    have he : (⟨(x:G),x.property.1⟩:d.carrier)*T=T*⟨(x:G),x.property.1⟩ :=
      Subtype.ext (mem_centralizer_singleton_iff.mp x.property.2)
    change d.quotient ⟨(x:G),x.property.1⟩ * d.quotient T =
      d.quotient T * d.quotient ⟨(x:G),x.property.1⟩
    simpa only [map_mul] using congrArg d.quotient he)
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rw [eq_bot_iff_forall]
    intro x hx
    have hq : d.quotient (inclusion (show E≤d.carrier from inf_le_left) x)=1 :=
      congrArg Subtype.val hx
    have ha : (x:G)∈A := by
      have hh : inclusion (show E≤d.carrier from inf_le_left) x ∈ d.quotient.ker := hq
      rwa [d.quotient_kernel] at hh
    apply Subtype.ext
    exact show (x:G)=1 from
      (show (x:G)∈(⊥:Subgroup G) from d.cubic_radical_centralizer t ht ht3 ▸ ⟨ha,x.property.2⟩)
  have hEC : Nat.card E≤3 := by
    have : Finite C := Nat.finite_of_card_ne_zero (by rw [hc]; decide)
    exact hc ▸ Nat.card_le_card_of_injective f hf
  let : Finite C := Nat.finite_of_card_ne_zero (by rw [hc]; decide)
  let : Finite E := Finite.of_injective f hf
  have hZE : zpowers t≤E := zpowers_le.mpr ⟨ht,mem_centralizer_singleton_iff.mpr rfl⟩
  exact (eq_of_le_of_card_ge hZE (by rw [Nat.card_zpowers,ht3]; exact hEC)).symm

end CFSG.Quasithin.HigmanSims
