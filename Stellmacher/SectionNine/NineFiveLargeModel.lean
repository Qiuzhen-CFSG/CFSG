module

public import Stellmacher.SectionNine.NineFiveCanonicalPair
public import Stellmacher.SectionNine.NineFiveRecognitionReduction
public import Stellmacher.SectionNine.NineFiveSupportGeometry

/-!
# The large terminal quotient from the canonical support in (9.5)

The two distinct lifted supports in the terminal neighbor module identify
its stabilizer modulo the two-core with the regular wreath product
SL2(2) ≀ C2. The actual quotient action, its exact core kernel, a canonical
Section One factor, and the equality of its commutator module with the
lifted support's quotient image are explicit producer inputs. No abstract
pair of factors or quotient model is assumed.

The supplied penultimate-core conjugator lies in the terminal stabilizer.
Its inverse acts on V/Z by the recorded literal conjugation formula, which
transports the second lifted support to the corresponding quotient support.
Both lifts contain Z, so equal quotient images would make the lifts equal.
Their ambient span gives full quotient span. The canonical-factor theorem
therefore supplies two commuting disjoint SL2(2) factors, a normal join
with trivial centralizer, factor permutation, and an element swapping them.
The wreath recognizer identifies the action range. Composing the range
isomorphism with the original action proves the model with exact QAt kernel.

This is the recognition half of Stellmacher (9.5)(b), printed pp.52–53 in
`refs/files/stellmacher-n-group.pdf`. The source-correct large model is
`SL2TwoWreathC2`. Constructing the support and its canonical-factor witness
remains the independent support producer's responsibility.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext
universe u

/-- The actual canonical support identifies the large terminal core quotient. -/
public theorem nine_five_large_model_of_canonical_support
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (prev : ctx.Γ.Vertex) (actor : G)
    (data : NineFiveSupportData ctx.toLocalContext prev actor)
    (hne : data.support ≠ data.support.map
      (MulAut.conj data.conjugator⁻¹).toMonoidHom)
    (hN : ((ZAt ctx.Γ ctx.criticalPath.a').subgroupOf
      (VAt ctx.Γ ctx.criticalPath.a')).Normal) :
    let _ := hN
    let P := GAt ctx.Γ ctx.criticalPath.a'
    let U := VAt ctx.Γ ctx.criticalPath.a'
    let Z := ZAt ctx.Γ ctx.criticalPath.a'
    ∀ hW : IsElementaryAbelian 2 (U ⧸ Z.subgroupOf U),
      let _ := hW
      ∀ action : P →* MulAut (U ⧸ Z.subgroupOf U),
        (∀ mover : P, ∀ point : U,
          action mover (QuotientGroup.mk' (Z.subgroupOf U) point) =
            QuotientGroup.mk' (Z.subgroupOf U)
              ⟨(mover : G) * (point : G) * (mover : G)⁻¹,
                (Subgroup.mem_normalizer_iff.mp
                  (stabilizer_le_normalizer_v ctx.Γ ctx.criticalPath.a' mover.property) point).mp
                    point.property⟩) →
        action.ker = pCore 2 P →
        SectionOne.Hypotheses action.range (U ⧸ Z.subgroupOf U) →
        ∀ factor : Subgroup action.range,
          SectionOne.IsOneSevenFactor (V := U ⧸ Z.subgroupOf U) factor →
          (data.support.subgroupOf U).map (QuotientGroup.mk' (Z.subgroupOf U)) =
            commutatorAction factor (U ⧸ Z.subgroupOf U) →
          QuotientIsModel P (QAt ctx.Γ ctx.criticalPath.a') SL2TwoWreathC2 := by
  let _ := hN
  let P := GAt ctx.Γ ctx.criticalPath.a'
  let U := VAt ctx.Γ ctx.criticalPath.a'
  let Z := ZAt ctx.Γ ctx.criticalPath.a'
  dsimp only
  intro hW
  let _ := hW
  intro action haction hkernel hyp factor hfactor hsupport
  let W := U ⧸ Z.subgroupOf U
  let q : U →* W := QuotientGroup.mk' (Z.subgroupOf U)
  let other := data.support.map (MulAut.conj data.conjugator⁻¹).toMonoidHom
  have hfirst : data.support ≤ U := le_sup_left.trans_eq data.span.symm
  have hother : other ≤ U := le_sup_right.trans_eq data.span.symm
  have hconjugator : data.conjugator ∈ P :=
    nine_five_support_conjugator_mem_terminal ctx.toLocalContext hb prev actor data
  let mover : P := ⟨data.conjugator⁻¹, P.inv_mem hconjugator⟩
  let moved : action.range := action.rangeRestrict mover
  have hZother : Z ≤ other := by
    intro point hpoint
    refine ⟨data.conjugator * point * data.conjugator⁻¹, ?_, ?_⟩
    · exact data.center_le ((Subgroup.mem_normalizer_iff.mp
        (stabilizer_le_normalizer_z ctx.Γ ctx.criticalPath.a' hconjugator) point).mp hpoint)
    · change data.conjugator⁻¹ * (data.conjugator * point * data.conjugator⁻¹) *
        (data.conjugator⁻¹)⁻¹ = point
      simp only [inv_inv, mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]
  have hcovariance : (other.subgroupOf U).map q =
      ((data.support.subgroupOf U).map q).map (action mover).toMonoidHom := by
    ext point
    constructor
    · rintro ⟨value, hvalue, rfl⟩
      obtain ⟨original, horiginal, heq⟩ := hvalue
      refine ⟨q ⟨original, hfirst horiginal⟩,
        ⟨⟨original, hfirst horiginal⟩, horiginal, rfl⟩, ?_⟩
      change action mover (QuotientGroup.mk' (Z.subgroupOf U)
        ⟨original, hfirst horiginal⟩) = q value
      rw [haction]
      congr 1
      apply Subtype.ext
      exact heq
    · rintro ⟨value, ⟨original, horiginal, rfl⟩, rfl⟩
      change action mover (QuotientGroup.mk' (Z.subgroupOf U) original) ∈
        (other.subgroupOf U).map q
      rw [haction]
      refine ⟨_, ?_, rfl⟩
      exact ⟨(original : G), horiginal, rfl⟩
  have hactionMap : (action mover).toMonoidHom =
      (MulDistribMulAction.toMulAut action.range W moved).toMonoidHom := rfl
  have hmove : commutatorAction factor W ≠
      (commutatorAction factor W).map
        (MulDistribMulAction.toMulAut action.range W moved).toMonoidHom := by
    intro heq
    apply hne
    have hmap : (data.support.subgroupOf U).map q = (other.subgroupOf U).map q := by
      rw [hcovariance, hactionMap]
      exact hsupport.trans (heq.trans (congrArg
        (fun subgroup : Subgroup W => subgroup.map
          (MulDistribMulAction.toMulAut action.range W moved).toMonoidHom) hsupport.symm))
    have hsubgroup : data.support.subgroupOf U = other.subgroupOf U := by
      apply Subgroup.map_injective_of_ker_le q ?_ ?_ hmap
      · rw [QuotientGroup.ker_mk']
        exact Subgroup.subgroupOf_mono U data.center_le
      · rw [QuotientGroup.ker_mk']
        exact Subgroup.subgroupOf_mono U hZother
    have hambient := congrArg (fun subgroup : Subgroup U => subgroup.map U.subtype) hsubgroup
    simpa only [Subgroup.map_subgroupOf_eq_of_le hfirst,
      Subgroup.map_subgroupOf_eq_of_le hother] using hambient
  have hspan : commutatorAction factor W ⊔
      (commutatorAction factor W).map
        (MulDistribMulAction.toMulAut action.range W moved).toMonoidHom = ⊤ := by
    rw [← hsupport, ← hactionMap, ← hcovariance, ← Subgroup.map_sup,
      ← Subgroup.subgroupOf_sup hfirst hother, ← data.span]
    change (U.subgroupOf U).map q = ⊤
    rw [Subgroup.subgroupOf_self]
    exact Subgroup.map_top_of_surjective q (QuotientGroup.mk'_surjective (Z.subgroupOf U))
  obtain ⟨first, second, hfirstSL, hsecondSL, hcomm, hdisjoint,
      hnormal, hcentralizer, hpermute, hswap⟩ :=
    nine_five_two_factors_of_canonical_support hyp factor hfactor moved hmove hspan
  let _ := hnormal
  obtain ⟨equiv⟩ := wreath_of_two_sl2_factors first second hfirstSL hsecondSL
    hcomm hdisjoint hcentralizer hpermute hswap
  refine ⟨equiv.toMonoidHom.comp action.rangeRestrict,
    equiv.surjective.comp action.rangeRestrict_surjective, ?_⟩
  rw [MonoidHom.ker_comp_of_injective _ _ equiv.injective,
    MonoidHom.ker_rangeRestrict, hkernel]
  change pCore 2 P = (ctx.Γ.twoCoreAt ctx.criticalPath.a').subgroupOf P
  rw [ctx.Γ.twoCoreAt_def]
  exact (Subgroup.comap_map_eq_self_of_injective P.subtype_injective _).symm

end Stellmacher.SectionNine
