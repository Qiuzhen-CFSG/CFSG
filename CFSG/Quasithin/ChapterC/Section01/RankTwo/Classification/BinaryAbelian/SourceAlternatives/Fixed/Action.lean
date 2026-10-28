module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.AbelianCore.QuotientRecognition.CoreAction.CentralizerQuotient
public import Theory.Representation.SLThreeCentralExtension.Normalizer

/-!
# The actual ambient action on a one-copy binary MS cover

The natural quotient of the abelian core D=[O₂(J),L] gives a central module
cover, since [D,L]=D. Every ambient conjugation normalizes the component
and preserves C_D(L). The normalizer theorem for a natural central cover
therefore makes that conjugation an actual SL₃(2) action on the whole D.
The resulting epimorphism retains both its component marking and the exact
projection formula. It applies to the nonsplit order-sixteen case without
replacing D by its order-eight quotient.

Source: Aschbacher–Smith C.1.34(5), printed p.137; Meierfrankenfeld–Stellmacher,
“Pushing up weak BN-pairs of rank two” (1993), Main Theorem (8), p.830.
-/

@[expose] public section
open Subgroup Representation Representation.OneCohomology
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS
universe u
variable {J : Type u} [Group J] [Finite J] {κ : GroupClass.{u}} {L R : Subgroup J}
variable (h : Input κ L R) [IsElementaryAbelian 2 (commutatorCore L)]

namespace AbelianCore.NaturalQuotient
variable (q : NaturalQuotient h 1)

/-- The whole-core representation descending literal component conjugation. -/
noncomputable def oneRepresentation : Representation (ZMod 2) BinaryLinearThree.Group
    (Additive (commutatorCore L)) where
  toFun g := (q.action h inferInstance g).toMonoidHom.toAdditive.toZModLinearMap 2
  map_one' := by
    ext d : 1
    change Additive.ofMul (q.action h inferInstance 1 d.toMul) = d
    rw [map_one]
    rfl
  map_mul' g k := by
    ext d : 1
    change Additive.ofMul (q.action h inferInstance (g * k) d.toMul) = _
    rw [map_mul]
    rfl

@[simp] theorem oneRepresentation_component (l : L) (d : Additive (commutatorCore L)) :
    q.oneRepresentation h (q.quotientEquiv (QuotientGroup.mk' (pCore 2 L) l)) d =
      Additive.ofMul (h.coreConjugate l d.toMul) :=
  congrArg Additive.ofMul (q.action_component h inferInstance l d.toMul)

/-- The given group projection as a natural covering map. -/
noncomputable def oneProjection : (q.oneRepresentation h).IntertwiningMap BinaryLinearThree.W where
  toLinearMap := (LinearMap.proj (0 : Fin 1)).comp
    (q.projection.toAdditiveLeft.toZModLinearMap 2)
  isIntertwining' g := by
    ext d : 1
    exact q.action_equivariant h inferInstance g d.toMul 0

theorem oneProjection_kernel (d : Additive (commutatorCore L)) :
    q.oneProjection h d = 0 ↔ d.toMul ∈ coreFixed L := by
  rw [← q.kernel]
  change (q.projection d.toMul).toAdd 0 = 0 ↔ q.projection d.toMul = 1
  constructor
  · intro hd
    apply Multiplicative.toAdd.injective
    funext i
    change (q.projection d.toMul).toAdd i = 0
    simpa only [Subsingleton.elim i 0] using hd
  · intro hd
    rw [hd]
    rfl

/-- No complement is assumed: the projection is a central commutator-generated cover. -/
theorem oneProjection_isCover : IsCover (q.oneProjection h) := by
  refine ⟨?_, ?_, ?_⟩
  · intro v
    obtain ⟨d, hd⟩ := q.surjective (Multiplicative.ofAdd (fun _ => v))
    exact ⟨Additive.ofMul d, congrArg (fun x => x.toAdd 0) hd⟩
  · intro d hd g
    obtain ⟨l, hl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) (q.quotientEquiv.symm g)
    have he : q.quotientEquiv (QuotientGroup.mk' (pCore 2 L) l) = g := by
      rw [hl, MulEquiv.apply_symm_apply]
    rw [← he, q.oneRepresentation_component]
    apply Additive.toMul.injective
    apply Subtype.ext
    change (h.coreConjugate l d.toMul : J) = (d.toMul : J)
    have hc : (l : J) * (d.toMul : J) = (d.toMul : J) * (l : J) :=
      (q.oneProjection_kernel h d).mp hd l l.property
    rw [h.coreConjugate_val, hc, mul_inv_cancel_right]
  · let C : Subgroup (commutatorCore L) :=
      (Coinvariants.ker (q.oneRepresentation h)).toAddSubgroup.toSubgroup'
    have hDC : commutatorCore L ≤ C.map (commutatorCore L).subtype := by
      conv_lhs => rw [← h.commutatorCore_idempotent, commutator_comm]
      apply commutator_le.mpr
      intro l hl d hd
      let d' : Additive (commutatorCore L) := Additive.ofMul ⟨d,hd⟩
      let g := q.quotientEquiv (QuotientGroup.mk' (pCore 2 L) ⟨l,hl⟩)
      refine ⟨((q.oneRepresentation h) g d' - d').toMul,
        Coinvariants.sub_mem_ker g d', ?_⟩
      change (((q.oneRepresentation h) g d').toMul : J) / d = ⁅l,d⁆
      rw [q.oneRepresentation_component]
      change (h.coreConjugate ⟨l,hl⟩ ⟨d,hd⟩ : J) / d = ⁅l,d⁆
      rw [h.coreConjugate_val, div_eq_mul_inv]
      rfl
    apply top_unique
    intro d _
    obtain ⟨w, hw, he⟩ := hDC d.toMul.property
    have heq : w = d.toMul := Subtype.ext he
    change d.toMul ∈ C
    exact heq ▸ hw

/-- Every ambient conjugation is the action of a matrix in the same marking. -/
theorem ambient_action_mem_range (j : J) :
    h.coreAmbientConjugation j ∈ (q.action h inferInstance).range := by
  let a := h.coreAmbientConjugation j
  let e : Additive (commutatorCore L) ≃ₗ[ZMod 2] Additive (commutatorCore L) :=
    LinearEquiv.ofBijective (a.toMonoidHom.toAdditive.toZModLinearMap 2) a.bijective
  have he (d : Additive (commutatorCore L)) :
      ((e d).toMul : J) = j * (d.toMul : J) * j⁻¹ :=
    h.coreAmbientConjugation_apply j d.toMul
  let := h.component_normal
  have hn : j ∈ normalizer (L : Set J) := by rw [normalizer_eq_top]; trivial
  have hk (d : Additive (commutatorCore L)) (hd : q.oneProjection h d = 0) :
      q.oneProjection h (e d) = 0 := by
    apply (q.oneProjection_kernel h _).mpr
    have hdC := (q.oneProjection_kernel h d).mp hd
    change ((e d).toMul : J) ∈ centralizer (L : Set J)
    rw [he]
    exact (normalizer_le_normalizer_centralizer L hn _).mp hdC
  have hnormal (g : BinaryLinearThree.Group) :
      ∃ k, ∀ d, e (q.oneRepresentation h g d) = q.oneRepresentation h k (e d) := by
    obtain ⟨l, hl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) (q.quotientEquiv.symm g)
    have heq : q.quotientEquiv (QuotientGroup.mk' (pCore 2 L) l) = g := by
      rw [hl, MulEquiv.apply_symm_apply]
    let k : L := ⟨j * (l : J) * j⁻¹, h.component_normal.conj_mem l l.property j⟩
    refine ⟨q.quotientEquiv (QuotientGroup.mk' (pCore 2 L) k), fun d => ?_⟩
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [he, ← heq, q.oneRepresentation_component, q.oneRepresentation_component]
    change j * (h.coreConjugate l d.toMul : J) * j⁻¹ =
      (h.coreConjugate k (e d).toMul : J)
    rw [h.coreConjugate_val, h.coreConjugate_val, he]
    change j * ((l : J) * (d.toMul : J) * (l : J)⁻¹) * j⁻¹ =
      (j * (l : J) * j⁻¹) * (j * (d.toMul : J) * j⁻¹) * (j * (l : J) * j⁻¹)⁻¹
    group
  obtain ⟨g, hg⟩ := SLThreeCentralExtension.normalizing_equiv_eq_action
    (q.oneProjection h) (q.oneProjection_isCover h) e hk hnormal
  refine ⟨g, ?_⟩
  apply MulEquiv.ext
  intro d
  exact (congrArg Additive.toMul (hg (Additive.ofMul d))).symm

/-- The natural head makes the action on its cover faithful. -/
theorem action_injective : Function.Injective (q.action h inferInstance) := by
  intro g k hgk
  apply Matrix.SpecialLinearGroup.toLin'_injective
  apply LinearEquiv.ext
  intro v
  obtain ⟨d, hd⟩ := q.surjective (Multiplicative.ofAdd (fun _ => v))
  have he := congrArg (fun a : MulAut (commutatorCore L) =>
    (q.projection (a d)).toAdd 0) hgk
  rw [q.action_equivariant, q.action_equivariant, hd] at he
  exact he

/-- The full ambient action, expressed in the quotient's original matrix marking. -/
noncomputable def ambientActor : J →* BinaryLinearThree.Group :=
  (MonoidHom.ofInjective (q.action_injective h)).symm.toMonoidHom.comp
    (h.coreAmbientConjugation.codRestrict _ (q.ambient_action_mem_range h))

theorem ambientActor_action (j : J) :
    q.action h inferInstance (q.ambientActor h j) = h.coreAmbientConjugation j :=
  congrArg Subtype.val ((MonoidHom.ofInjective (q.action_injective h)).apply_symm_apply
    ⟨h.coreAmbientConjugation j, q.ambient_action_mem_range h j⟩)

theorem ambientActor_component (l : L) :
    q.ambientActor h l = q.quotientEquiv (QuotientGroup.mk' (pCore 2 L) l) := by
  apply q.action_injective h
  rw [q.ambientActor_action]
  ext d
  rw [q.action_component, h.coreAmbientConjugation_apply, h.coreConjugate_val]

theorem ambientActor_surjective : Function.Surjective (q.ambientActor h) := by
  intro g
  obtain ⟨l, hl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) (q.quotientEquiv.symm g)
  refine ⟨l, ?_⟩
  rw [q.ambientActor_component, hl, MulEquiv.apply_symm_apply]

/-- Projection coordinates commute with every actual ambient conjugation. -/
theorem ambientActor_equivariant (j : J) (d : commutatorCore L) :
    (q.projection (h.coreAmbientConjugation j d)).toAdd 0 =
      BinaryLinearThree.W (q.ambientActor h j) ((q.projection d).toAdd 0) := by
  rw [← q.ambientActor_action]
  exact q.action_equivariant h inferInstance _ d 0

/-- The exact kernel is the centralizer of the whole commutator core. -/
theorem ambientActor_ker_centralizer :
    (q.ambientActor h).ker = centralizer (commutatorCore L : Set J) := by
  rw [← h.coreAmbientConjugation_kernel]
  ext j
  change q.ambientActor h j = 1 ↔ h.coreAmbientConjugation j = 1
  rw [← q.ambientActor_action]
  constructor
  · intro he
    rw [he, map_one]
  · intro he
    apply q.action_injective h
    rw [map_one]
    exact he

/-- The ambient two-core acts trivially on the whole natural cover. -/
theorem ambientActor_kernel : (q.ambientActor h).ker = pCore 2 J := by
  apply le_antisymm
  · rw [q.ambientActor_ker_centralizer]
    exact h.core_centralizer_le
  · intro n hn
    have hc := commutator_eq_bot_iff_le_centralizer.mp
      (h.abelianCore_ambient_image_commutator inferInstance)
      (mem_map_of_mem h.coreAmbientConjugation hn)
    have hz : q.ambientActor h n ∈ center BinaryLinearThree.Group := by
      apply mem_center_iff.mpr
      intro g
      obtain ⟨l,hl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) (q.quotientEquiv.symm g)
      have he : q.ambientActor h l = g := by
        rw [q.ambientActor_component, hl, MulEquiv.apply_symm_apply]
      apply q.action_injective h
      rw [map_mul, map_mul, ← he, q.ambientActor_action, q.ambientActor_action]
      exact hc _ (mem_map_of_mem h.coreAmbientConjugation l.property)
    exact Matrix.PSL3Two.center_eq_bot.le hz

/-- The same action identifies the actual ambient core quotient with SL₃(2). -/
noncomputable def ambientQuotientEquiv : (J ⧸ pCore 2 J) ≃* BinaryLinearThree.Group :=
  (QuotientGroup.quotientMulEquivOfEq (q.ambientActor_kernel h).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (q.ambientActor h)
      (q.ambientActor_surjective h))

omit [IsElementaryAbelian 2 (commutatorCore L)] in
include h in
/-- The fixed subgroup of order two is central in the whole ambient group. -/
theorem fixed_le_center (hc : Nat.card (coreFixed L) = 2) :
    commutatorCore L ⊓ centralizer (L : Set J) ≤ center J := by
  let := h.component_normal
  let C := commutatorCore L ⊓ centralizer (L : Set J)
  let e : coreFixed L ≃* C :=
    ((coreFixed L).equivMapOfInjective (commutatorCore L).subtype
      (commutatorCore L).subtype_injective).trans
      (MulEquiv.subgroupCongr (by
        change ((centralizer (L : Set J)).comap (commutatorCore L).subtype).map _ = _
        rw [map_comap_eq, range_subtype]))
  have he : Nat.card C = 2 := (Nat.card_congr e.toEquiv).symm.trans hc
  exact central_of_normal_card_two C he

end AbelianCore.NaturalQuotient
end CFSG.Quasithin.ChapterC.BinaryMS
