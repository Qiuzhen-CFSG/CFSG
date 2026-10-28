module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.EdgeTransfer.Extension.Action

public import Theory.GroupTheory.PResidual.SubnormalCoreAction

/-!
# Residual action on the neighboring extension quotient

Let H = ([Z_delta,Q_beta] Z_alpha) D_alpha, with
D_alpha = Q_alpha ∩ C(Ltilde_alpha). The local two-residual surjects onto
the perfect SL3(2) quotient. Its commutators with H lie in Z_alpha, so the
action on the quotient of H/D_alpha by the image of Z_alpha is trivial.

A fixed vector in H/D_alpha initially gives only commutators in D_alpha.
Inside the finite vertex stabilizer, the commutator preimage of D_alpha in
Q_alpha is a two-group normalized by the two-residual. Commutator idempotence,
together with centrality of D_alpha under the residual, makes those
commutators trivial. Thus the lift belongs to D_alpha and the vector is zero.
All normality and finiteness arguments take place in the local stabilizer.

These are the two residual-action inputs to the extension argument. The
natural-module marking is separate. Adapted from the checked marked-extension proof in
`DistanceFour/Early/EdgeStructure/Containment/Transfer/SpanBound/Extension`.
The general construction uses the source and module data and b > 2.

Source: Meierfrankenfeld--Stellmacher,
*Pushing up weak BN-pairs of rank two* (1993), proof of (4.2)(i), printed
p.882, applying (1.5)(i), printed p.843.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.EdgeTransfer.Extension

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

private theorem residual_projection_surjective {a b d : Vertex R} (A : Action a b d)
    (g : SL) : ∃ l : stabilizer R a, l ∈ pResidual 2 (stabilizer R a) ∧ A.projection l = g := by
  let : Finite (stabilizer R a) := finite_stabilizer R a
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
  have hm : (pResidual 2 (stabilizer R a)).map A.projection = ⊤ := by
    rw [map_pResidual_of_surjective 2 A.projection A.projection_surjective,
      (pResidual_eq_top_iff 2 SL).mpr hp]
  exact mem_map.mp (hm ▸ (show g ∈ (⊤ : Subgroup SL) from mem_top g))

private theorem carrier_residual_commutator_le
    (hlarge : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (a b d : Vertex R) (ha : color R a = false)
    (hB : ⁅Z R d,Q R b⁆ ≤ B R a (geometry.Z_normal a)) :
    ⁅carrier a b d,Ltilde R a⁆ ≤ Z R a := by
  have hpre : carrier a b d ≤ commutatorPreimage (carrier a b d) (Ltilde R a) (Z R a) := by
    refine sup_le (sup_le ?_ ?_) ?_
    · exact le_commutatorPreimage (le_sup_left.trans le_sup_left)
        (neighbor_displacement_local hlarge a b d ha hB).2
    · exact le_commutatorPreimage (le_sup_right.trans le_sup_left)
        (le_normalizer_iff_commutator_le_left.mp
          ((Ltilde_le_stabilizer a).trans (Z_normalized R a)))
    · exact le_commutatorPreimage le_sup_right
        ((commutator_eq_bot_iff_le_centralizer.mpr (show fixedCore R a ≤
          centralizer (Ltilde R a : Set (FreeAmalgam R)) from inf_le_right)).le.trans bot_le)
  exact (commutator_mono hpre le_rfl).trans
    (commutator_commutatorPreimage_le _ _ _
      (((carrier_le_Q hlarge modules a b d ha hB).trans (fun _ hx => hx.1)).trans (Z_normalized R a)))

/-- The residual commutator bound makes the quotient by the actual Z-image trivial. -/
theorem action_hasTrivialQuotient (hlarge : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (a b d : Vertex R) (ha : color R a = false) (hab : Adjacent R a b)
    (hB : ⁅Z R d,Q R b⁆ ≤ B R a (geometry.Z_normal a)) (A : Action a b d) :
    letI := A.normal
    letI := A.elementary
    Representation.OneCohomology.HasTrivialQuotient A.natural := by
  let := A.normal
  let := A.elementary
  change Representation.OneCohomology.HasTrivialQuotient A.natural
  intro g w
  obtain ⟨l,hl,rfl⟩ := residual_projection_surjective A g
  obtain ⟨x,hx⟩ := QuotientGroup.mk'_surjective
    ((fixedCore R a).subgroupOf (carrier a b d)) w.toMul
  have hwx : Additive.ofMul (QuotientGroup.mk' _ x) = w := congrArg Additive.ofMul hx
  subst w
  let y : carrier a b d := ⟨(l : FreeAmalgam R) * (x : FreeAmalgam R) * (l : FreeAmalgam R)⁻¹,
    le_normalizer_iff.mp (carrier_normalized (source := source) hlarge a b d ha hab hB) l l.property x x.property⟩
  have hy := A.conjugation l x y rfl
  have hc : ((y / x : carrier a b d) : FreeAmalgam R) ∈ Z R a := by
    have hc := carrier_residual_commutator_le hlarge modules a b d ha hB
      (show ⁅(l : FreeAmalgam R), (x : FreeAmalgam R)⁆ ∈ ⁅carrier a b d,Ltilde R a⁆ by
        rw [commutator_comm]
        exact commutator_mem_commutator (mem_map_of_mem (stabilizer R a).subtype hl) x.property)
    simpa only [y, coe_div, div_eq_mul_inv, coe_mul, coe_inv, Subtype.coe_mk, commutatorElement_def, mul_assoc] using hc
  change Additive.ofMul (A.action (A.projection l) (QuotientGroup.mk' _ x) /
    QuotientGroup.mk' _ x) ∈ A.natural.toSubmodule
  rw [hy, ← map_div]
  exact (A.mem_natural_iff (y / x)).mpr ((show Z R a ≤ Z R a ⊔ fixedCore R a from le_sup_left) hc)

/-- Every fixed quotient vector lifts to the literal fixed core, hence is zero. -/
theorem action_fixed_eq_bot (hlarge : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (a b d : Vertex R) (ha : color R a = false) (hab : Adjacent R a b)
    (hB : ⁅Z R d,Q R b⁆ ≤ B R a (geometry.Z_normal a)) (A : Action a b d) :
    letI := A.normal
    letI := A.elementary
    Representation.OneCohomology.fixed A.representation = ⊥ := by
  let := A.normal
  let := A.elementary
  apply le_bot_iff.mp
  intro w hw
  change w = 0
  obtain ⟨x,hx⟩ := QuotientGroup.mk'_surjective
    ((fixedCore R a).subgroupOf (carrier a b d)) w.toMul
  have hwx : Additive.ofMul (QuotientGroup.mk' _ x) = w := congrArg Additive.ofMul hx
  subst w
  let S := stabilizer R a
  let P := (Q R a).subgroupOf S
  let E := pResidual 2 S
  let D := (fixedCore R a).subgroupOf S
  let : Finite S := finite_stabilizer R a
  let : D.Normal := normal_subgroupOf_of_le_normalizer
    (fixedCore_normalized R a)
  let xS : S := ⟨x, ((carrier_le_Q hlarge modules a b d ha hB) x.property).1⟩
  have hDE : ⁅D,E⁆ = ⊥ := by
    apply commutator_eq_bot_iff_le_centralizer.mpr
    intro z hz l hl
    apply Subtype.ext
    exact hz.2 l (mem_map_of_mem S.subtype hl)
  have hxcomm : ∀ l ∈ E, ⁅xS,l⁆ ∈ D := by
    intro l hl
    let y : carrier a b d := ⟨(l : FreeAmalgam R) * (x : FreeAmalgam R) * (l : FreeAmalgam R)⁻¹,
      le_normalizer_iff.mp (carrier_normalized (source := source) hlarge a b d ha hab hB) l l.property x x.property⟩
    have hy := A.conjugation l x y rfl
    have hf := hw (A.projection l)
    change Additive.ofMul (A.action (A.projection l) (QuotientGroup.mk' _ x)) =
      Additive.ofMul (QuotientGroup.mk' _ x) at hf
    have heq : QuotientGroup.mk' ((fixedCore R a).subgroupOf (carrier a b d)) y =
        QuotientGroup.mk' ((fixedCore R a).subgroupOf (carrier a b d)) x := by
      rw [← hy]
      exact congrArg Additive.toMul hf
    have hc := QuotientGroup.eq_iff_div_mem.mp heq
    have hc' : ⁅(l : FreeAmalgam R), (x : FreeAmalgam R)⁆ ∈ fixedCore R a := by
      simpa only [y, mem_subgroupOf, coe_div, div_eq_mul_inv, coe_mul, coe_inv, Subtype.coe_mk, commutatorElement_def, mul_assoc] using hc
    change ⁅(x : FreeAmalgam R), (l : FreeAmalgam R)⁆ ∈ fixedCore R a
    rw [← commutatorElement_inv]
    exact (fixedCore R a).inv_mem hc'
  have hxc := centralizes_of_central_error P E D
    (Q_isPGroup R source.two_group source.core_le a ha).comap_subtype
    (isPPerfect_pResidual 2) (fun _ hz => hz.1) hDE xS
    (carrier_le_Q hlarge modules a b d ha hB x.property) hxcomm
  have hxD : (x : FreeAmalgam R) ∈ fixedCore R a := by
    refine ⟨carrier_le_Q hlarge modules a b d ha hB x.property, ?_⟩
    rintro _ ⟨l,hl,rfl⟩
    exact congrArg Subtype.val (hxc l hl)
  change Additive.ofMul (QuotientGroup.mk' _ x) = 0
  change QuotientGroup.mk' _ x = 1
  exact (QuotientGroup.eq_one_iff x).mpr hxD

/-- The two quotient-action facts required by the conditional extension assembly. -/
theorem action_quotient_facts (hlarge : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (a b d : Vertex R) (ha : color R a = false) (hab : Adjacent R a b)
    (hB : ⁅Z R d,Q R b⁆ ≤ B R a (geometry.Z_normal a)) (A : Action a b d) :
    letI := A.normal
    letI := A.elementary
    Representation.OneCohomology.HasTrivialQuotient A.natural ∧
      Representation.OneCohomology.fixed A.representation = ⊥ :=
  ⟨action_hasTrivialQuotient hlarge modules a b d ha hab hB A,
    action_fixed_eq_bot hlarge modules a b d ha hab hB A⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.EdgeTransfer.Extension
