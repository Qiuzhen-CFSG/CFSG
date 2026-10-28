module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.TwoCentral.MarkedLocal.Factors
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.LocalActionFusion
public import Theory.GroupTheory.CComponent.QuasisimpleFactors

/-!
# Fixed points of the marked five-line in the extraspecial core

An order-five subgroup of the marked component fixes exactly the inverter's
central involution line in its extraspecial core. The complement meets the
core trivially, so its five-line acts faithfully on the literal Frattini
quotient of order sixteen. That action has no nonidentity fixed points.
Consequently every fixed core element lies in the Frattini subgroup, whose
ambient image is the marked involution line.

The core's structure is transported from the seed through conjugation of
its actual involution centralizer. All kernels, complements and Frattini
quotients remain relative to that centralizer. The final application uses
Y = P ∩ fiveComponent E and discharges the core premise in
`MarkedLocal.localData_of_core_and_component`.

Source: Aschbacher, *Sporadic Groups* (1994), 47.2, printed p.261,
the core calculation in the paragraph beginning with Y = P ∩ E(M).
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.TwoCentral.MarkedLocal.CoreFixed
variable {G : Type*} [Group G] [Finite G] {D : Seed G} {E : Subgroup G}

omit [Finite G] in
private theorem centralizer_map_equiv (e : G ≃* G) (t : G) :
    (involutionCentralizer t).map e.toMonoidHom = involutionCentralizer (e t) := by
  apply le_antisymm
  · simpa only [Set.image_singleton, MulEquiv.coe_toMonoidHom] using
      map_centralizer_le_centralizer_image ({t} : Set G) e.toMonoidHom
  · intro x hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    apply mem_centralizer_singleton_iff.mpr
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using mem_centralizer_singleton_iff.mp hx

private theorem core_equiv (W : RootFiveWitness D E) :
    Nonempty (localCore W.inverter ≃* MinusExtraspecial.Model) := by
  obtain ⟨g, hg⟩ := isConj_iff.mp W.inverter_conj
  let e := MulAut.conj g
  have he : e D.z = W.inverter := hg
  let c : involutionCentralizer D.z ≃* involutionCentralizer W.inverter :=
    (e.subgroupMap _).trans
      (MulEquiv.subgroupCongr ((centralizer_map_equiv e D.z).trans (congrArg involutionCentralizer he)))
  let q : localCore D.z ≃* localCore W.inverter :=
    (c.subgroupMap _).trans (MulEquiv.subgroupCongr (map_generalizedFitting_equiv c))
  exact ⟨q.symm.trans D.localType.core_equiv.some⟩

private theorem frattini_action_kernel (Q : Subgroup G) [Q.Normal]
    (hQ : Q = pCore 2 G) (hc : centralizer (Q : Set G) ≤ Q) :
    ((quotientAut (frattini Q)).comp (MulAut.conjNormal : G →* MulAut Q)).ker = Q := by
  subst Q
  exact pCore_frattini_action_kernel 2 hc

private theorem core_action_kernel (W : RootFiveWitness D E) :
    (coreFrattiniAction W.inverter).ker = localCore W.inverter := by
  have hc : Nat.card (localCore W.inverter) = 32 :=
    (Nat.card_congr (core_equiv W).some.toEquiv).trans MinusExtraspecial.card_model
  have hp : IsPGroup 2 (localCore W.inverter) := IsPGroup.of_card (n := 5) hc
  have he : localCore W.inverter = pCore 2 (involutionCentralizer W.inverter) :=
    le_antisymm (le_sSup ⟨inferInstance, hp⟩)
      ((pCore_le_fitting _ 2).trans (fitting_le_generalizedFitting _))
  exact frattini_action_kernel _ he (centralizer_generalizedFitting_le _)

private theorem frattini_image (W : RootFiveWitness D E) :
    (frattini (localCore W.inverter)).map
      ((involutionCentralizer W.inverter).subtype.comp (localCore W.inverter).subtype) =
        zpowers W.inverter := by
  let H := involutionCentralizer W.inverter
  let Q := localCore W.inverter
  let k : Q →* G := H.subtype.comp Q.subtype
  let : IsExtraspecial 2 Q := IsExtraspecial.of_mulEquiv (core_equiv W).some.symm inferInstance
  rw [IsExtraspecial.frattini_eq_center_two]
  have hzH : W.inverter ∈ H := mem_centralizer_singleton_iff.mpr rfl
  have hzZH : (⟨W.inverter, hzH⟩ : H) ∈ center H :=
    mem_center_iff.mpr fun a => Subtype.ext (mem_centralizer_singleton_iff.mp a.property)
  have hzQ : (⟨W.inverter, hzH⟩ : H) ∈ Q := HTypeAt.center_le_core hzZH
  have hzZ : (⟨⟨W.inverter, hzH⟩, hzQ⟩ : Q) ∈ center Q :=
    mem_center_iff.mpr fun q => Subtype.ext (mem_center_iff.mp hzZH q)
  apply (eq_of_le_of_card_ge (zpowers_le.mpr (mem_map_of_mem k hzZ)) ?_).symm
  have hk : Function.Injective k := H.subtype_injective.comp Q.subtype_injective
  change Nat.card ((center Q).map k) ≤ Nat.card (zpowers W.inverter)
  rw [card_map_of_injective hk,
    IsExtraspecial.center_order_p 2 Q, Nat.card_zpowers, inverter_order W]

/-- The order-five component subgroup fixes exactly the marked involution line in the core. -/
theorem core_fixed (W : RootFiveWitness D E) (Y : Subgroup G)
    (hYL : Y ≤ fiveComponent E) (hY : Nat.card Y = 5) :
    ambientCore W.inverter ⊓ centralizer (Y : Set G) = zpowers W.inverter := by
  let H := involutionCentralizer W.inverter
  let Q := localCore W.inverter
  let V := Q ⧸ frattini Q
  let k : Q →* G := H.subtype.comp Q.subtype
  let q : Q →* V := QuotientGroup.mk' (frattini Q)
  let : IsExtraspecial 2 Q := IsExtraspecial.of_mulEquiv (core_equiv W).some.symm inferInstance
  have hQcard : Nat.card Q = 32 :=
    (Nat.card_congr (core_equiv W).some.toEquiv).trans MinusExtraspecial.card_model
  have hV : Nat.card V = 16 := by
    dsimp only [V]
    rw [IsExtraspecial.frattini_eq_center_two]
    have hc := card_eq_card_quotient_mul_card_subgroup (center Q)
    rw [hQcard, IsExtraspecial.center_order_p 2 Q] at hc
    omega
  have hYH : Y ≤ H := hYL.trans W.component_le
  let f : Y →* MulAut V := (coreFrattiniAction W.inverter).comp (inclusion hYH)
  have hinj : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply bot_unique
    intro y hy
    apply mem_bot.mpr
    apply Subtype.ext
    have hyQ : inclusion hYH y ∈ Q := by
      change inclusion hYH y ∈ localCore W.inverter
      rw [← core_action_kernel W]
      exact hy
    have hd := W.complement.disjoint
    rw [ambientCore_subgroupOf] at hd
    have he : inclusion hYH y = 1 :=
      disjoint_def.mp hd (hYL y.property) hyQ
    exact congrArg (fun a : H => (a : G)) he
  have hA : Nat.card f.range = 5 :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm.trans hY
  have hfixed := SmallNonabelianTwoGroup.order_five_actor_fixed_subgroup_eq_bot hV f.range hA
  apply le_antisymm
  · rintro x ⟨hxQ, hxC⟩
    obtain ⟨a, ha, rfl⟩ := hxQ
    let x : Q := ⟨a, ha⟩
    have hxfix : q x ∈ FixedPoints.subgroup f.range V := by
      apply (FixedPoints.mem_subgroup (M := f.range) (a := q x)).mpr
      rintro ⟨aut, y, rfl⟩
      change coreFrattiniAction W.inverter (inclusion hYH y) (q x) = q x
      change quotientAut (frattini Q) (MulAut.conjNormal (inclusion hYH y)) (q x) = q x
      rw [quotientAut_apply_mk]
      apply congrArg q
      apply Subtype.ext
      apply Subtype.ext
      change (y : G) * (a : G) * (y : G)⁻¹ = (a : G)
      exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_iff.mp hxC y y.property)
    have hxone : q x = 1 := mem_bot.mp (hfixed ▸ hxfix)
    have hxPhi : x ∈ frattini Q := (QuotientGroup.eq_one_iff _).mp hxone
    rw [← frattini_image W]
    exact mem_map_of_mem k hxPhi
  · apply zpowers_le.mpr
    refine ⟨HTypeAt.involution_mem_core, ?_⟩
    apply mem_centralizer_iff.mpr
    intro y hy
    exact mem_centralizer_singleton_iff.mp (hYH hy)

/-- The literal Sylow intersection supplies the core premise of marked-local assembly. -/
theorem intersection_core_fixed (hG : Nat.card G = 604800) (W : RootFiveWitness D E)
    (P : Sylow 5 G) (hEP : E ≤ (P : Subgroup G)) :
    ambientCore W.inverter ⊓
      centralizer (((P : Subgroup G) ⊓ fiveComponent E : Subgroup G) : Set G) =
        zpowers W.inverter :=
  core_fixed W _ inf_le_right (intersection_card hG W P hEP)

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.TwoCentral.MarkedLocal.CoreFixed
