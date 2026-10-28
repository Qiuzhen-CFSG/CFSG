module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Selection.Inside.Dual.Action
public import Theory.GroupTheory.PResidual.SubnormalCoreAction

/-!
# Residual action on the point quotient

The local two-residual maps onto SL3(2), and its commutators with the point
extension lie in Z_c. Thus the quotient by the natural Z_c-image is trivial.
A fixed vector lifts to a point of Q_c whose residual commutators lie in
D_c. Residual commutator idempotence removes that central error, putting
the lift in D_c. Consequently the fixed space of the extension is zero.
All normality and finiteness arguments use the relative vertex stabilizer.

Adapted from Reduction/Escape/EdgeTransfer/Extension/Residual.
Source: MS93 (1993), the dual application of (1.5)(i) in (4.4.1)(2), p.891.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Inside.Dual

/-- Residual commutator idempotence removes a central error in a finite two-group. -/
private theorem centralizes_of_central_error {G : Type*} [Group G] [Finite G]
    (P E D : Subgroup G) [D.Normal] (hp : IsPGroup 2 P)
    (he : IsPPerfect 2 E) (hDP : D ≤ P) (hDE : ⁅D,E⁆ = ⊥)
    (x : G) (hx : x ∈ P) (hcomm : ∀ y ∈ E, ⁅x,y⁆ ∈ D) :
    x ∈ centralizer (E : Set G) := by
  let N := commutatorPreimage P E D
  have hDN : D ≤ N := le_commutatorPreimage hDP (hDE.le.trans bot_le)
  have hNE : ⁅N,E⁆ ≤ D := commutator_commutatorPreimage_le P E D le_normalizer_of_normal
  have hn : E ≤ normalizer N :=
    le_normalizer_iff_commutator_le_left.mpr (hNE.trans hDN)
  have hz : ⁅N,E⁆ = ⊥ := by
    rw [← commutator_isPPerfect_idempotent E N he
      (hp.to_le (commutatorPreimage_le P E D)) hn]
    exact le_bot_iff.mp ((commutator_mono hNE le_rfl).trans hDE.le)
  apply commutator_eq_bot_iff_le_centralizer.mp hz
  change x ∈ commutatorPreimage P E D
  rw [commutatorPreimage_eq_inf_comap_centralizer]
  refine ⟨hx, ?_⟩
  rintro _ ⟨y,hy,rfl⟩
  have hc : ⁅QuotientGroup.mk' D x, QuotientGroup.mk' D y⁆ = 1 := by
    rw [← map_commutatorElement]
    exact (QuotientGroup.eq_one_iff _).mpr (hcomm y hy)
  exact (commutatorElement_eq_one_iff_mul_comm.mp hc).symm

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
    {source : LocalSource L R} {geometry : Geometry R}

private theorem residual_projection_surjective {c : Vertex R} {point : FreeAmalgam R} (A : Action c point)
    (g : SL) : ∃ l : stabilizer R c, l ∈ pResidual 2 (stabilizer R c) ∧ A.projection l = g := by
  let : Finite (stabilizer R c) := finite_stabilizer R c
  have hp : IsPPerfect 2 SL := by
    let : Group.IsPerfect SL := Atlas.sl_perfect 3 (by decide)
    intro N hN hq
    let := hN
    have hs : Subsingleton (SL ⧸ N) := by
      by_contra! hn
      exact Group.IsPerfect.not_isNilpotent (SL ⧸ N) hq.isNilpotent
    apply eq_top_iff.mpr
    intro x _
    exact (QuotientGroup.eq_one_iff x).mp (Subsingleton.elim _ _)
  have hm : (pResidual 2 (stabilizer R c)).map A.projection = ⊤ := by
    rw [map_pResidual_of_surjective 2 A.projection A.projection_surjective,
      (pResidual_eq_top_iff 2 SL).mpr hp]
  exact mem_map.mp (hm ▸ (show g ∈ (⊤ : Subgroup SL) from mem_top g))

/-- The residual commutator bound makes the quotient by the actual Z-image trivial. -/
theorem action_hasTrivialQuotient (modules : ModuleFacts source geometry)
    {c : Vertex R} {point : FreeAmalgam R} (hc : color R c = false)
    (data : PointData c point) (A : Action c point) :
    letI := A.normal
    letI := A.elementary
    Representation.OneCohomology.HasTrivialQuotient A.natural := by
  let := A.normal
  let := A.elementary
  change Representation.OneCohomology.HasTrivialQuotient A.natural
  intro g w
  obtain ⟨l,hl,rfl⟩ := residual_projection_surjective A g
  obtain ⟨x,hx⟩ := QuotientGroup.mk'_surjective
    ((fixedCore R c).subgroupOf (carrier c point)) w.toMul
  have hwx : Additive.ofMul (QuotientGroup.mk' _ x) = w := congrArg Additive.ofMul hx
  subst w
  let y : carrier c point := ⟨(l : FreeAmalgam R) * (x : FreeAmalgam R) * (l : FreeAmalgam R)⁻¹,
    le_normalizer_iff.mp (carrier_normalized modules hc data) l l.property x x.property⟩
  have hy := A.conjugation l x y rfl
  have hc : ((y / x : carrier c point) : FreeAmalgam R) ∈ Z R c := by
    have hc := carrier_residual_commutator_le modules hc data
      (show ⁅(l : FreeAmalgam R), (x : FreeAmalgam R)⁆ ∈ ⁅carrier c point,Ltilde R c⁆ by
        rw [commutator_comm]
        exact commutator_mem_commutator (mem_map_of_mem (stabilizer R c).subtype hl) x.property)
    simpa only [y, coe_div, div_eq_mul_inv, coe_mul, coe_inv, Subtype.coe_mk, commutatorElement_def, mul_assoc] using hc
  change Additive.ofMul (A.action (A.projection l) (QuotientGroup.mk' _ x) /
    QuotientGroup.mk' _ x) ∈ A.natural.toSubmodule
  rw [hy, ← map_div]
  exact (A.mem_natural_iff (y / x)).mpr ((show Z R c ≤ Z R c ⊔ fixedCore R c from le_sup_left) hc)

/-- Every fixed quotient vector lifts to the literal fixed core, hence is zero. -/
theorem action_fixed_eq_bot (modules : ModuleFacts source geometry)
    {c : Vertex R} {point : FreeAmalgam R} (hc : color R c = false)
    (data : PointData c point) (A : Action c point) :
    letI := A.normal
    letI := A.elementary
    Representation.OneCohomology.fixed A.representation = ⊥ := by
  let := A.normal
  let := A.elementary
  apply le_bot_iff.mp
  intro w hw
  change w = 0
  obtain ⟨x,hx⟩ := QuotientGroup.mk'_surjective
    ((fixedCore R c).subgroupOf (carrier c point)) w.toMul
  have hwx : Additive.ofMul (QuotientGroup.mk' _ x) = w := congrArg Additive.ofMul hx
  subst w
  let S := stabilizer R c
  let P := (Q R c).subgroupOf S
  let E := pResidual 2 S
  let D := (fixedCore R c).subgroupOf S
  let : Finite S := finite_stabilizer R c
  let : D.Normal := normal_subgroupOf_of_le_normalizer
    (PathCentrality.fixedCore_normalized R c)
  let xS : S := ⟨x, ((carrier_le_Q modules hc data) x.property).1⟩
  have hDE : ⁅D,E⁆ = ⊥ := by
    apply commutator_eq_bot_iff_le_centralizer.mpr
    intro z hz l hl
    apply Subtype.ext
    exact hz.2 l (mem_map_of_mem S.subtype hl)
  have hxcomm : ∀ l ∈ E, ⁅xS,l⁆ ∈ D := by
    intro l hl
    let y : carrier c point := ⟨(l : FreeAmalgam R) * (x : FreeAmalgam R) * (l : FreeAmalgam R)⁻¹,
      le_normalizer_iff.mp (carrier_normalized modules hc data) l l.property x x.property⟩
    have hy := A.conjugation l x y rfl
    have hf := hw (A.projection l)
    change Additive.ofMul (A.action (A.projection l) (QuotientGroup.mk' _ x)) =
      Additive.ofMul (QuotientGroup.mk' _ x) at hf
    have heq : QuotientGroup.mk' ((fixedCore R c).subgroupOf (carrier c point)) y =
        QuotientGroup.mk' ((fixedCore R c).subgroupOf (carrier c point)) x := by
      rw [← hy]
      exact congrArg Additive.toMul hf
    have hc := QuotientGroup.eq_iff_div_mem.mp heq
    have hc' : ⁅(l : FreeAmalgam R), (x : FreeAmalgam R)⁆ ∈ fixedCore R c := by
      simpa only [y, mem_subgroupOf, coe_div, div_eq_mul_inv, coe_mul, coe_inv, Subtype.coe_mk, commutatorElement_def, mul_assoc] using hc
    change ⁅(x : FreeAmalgam R), (l : FreeAmalgam R)⁆ ∈ fixedCore R c
    rw [← commutatorElement_inv]
    exact (fixedCore R c).inv_mem hc'
  have hxc := centralizes_of_central_error P E D
    (Q_isPGroup R source.two_group source.core_le c hc).comap_subtype
    (isPPerfect_pResidual 2) (fun _ hz => hz.1) hDE xS
    (carrier_le_Q modules hc data x.property) hxcomm
  have hxD : (x : FreeAmalgam R) ∈ fixedCore R c := by
    refine ⟨carrier_le_Q modules hc data x.property, ?_⟩
    rintro _ ⟨l,hl,rfl⟩
    exact congrArg Subtype.val (hxc l hl)
  change Additive.ofMul (QuotientGroup.mk' _ x) = 0
  change QuotientGroup.mk' _ x = 1
  exact (QuotientGroup.eq_one_iff x).mpr hxD

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Inside.Dual
