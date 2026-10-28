module
public import Theory.GroupTheory.OddSylowNormalCenterless
public import Theory.Alternating.FivePairOuterTwo
public import Theory.Alternating.PrimeRank
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalComponentPreparation
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalProductResidual

/-!
# The cubic Sylows and central-cover reduction in source 12.3.13

The normal A₅ section in the actual point-centralizer and its local
three-rank bound force abelian cubic Sylows. A cubic Sylow of the original
L fixes a word in the 35-element weight-four orbit. Transport through the
original projection conjugates it into the selected point-centralizer.
Its image in L/O₂(L) is therefore abelian, removing the central cover.

The resulting A₇ marking agrees with the original projection. It supplies
L=O^{3′}(N_G(L)) and the ambient residual identity for the literal L₁.
ComponentAnalysis remains the allowed premise, discharged by the final
terminal assembly owner qt-d-1231-terminal. No product data are assumed.
Source: Aschbacher--Smith, 12.3.12--13 and completion of 12.3.1, p.811.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
open Section02 BinarySevenCode
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}
variable {S : Setup T L V} {D : S.LocalAnalysis}
namespace TerminalPoint
variable (P : TerminalPoint S D)

/-- The actual point-centralizer has abelian Sylow three-subgroups. -/
theorem pointCentralizer_threeSylow_commutative (C : P.ComponentAnalysis)
    (R : Sylow 3 P.pointCentralizer) : IsMulCommutative R := by
  let B := P.K.subgroupOf P.pointCentralizer
  let : B.Normal := normal_subgroupOf_of_le_normalizer C.normalizes
  let eB := subgroupOfEquivOfLe P.residual_le_pointCentralizer
  let e : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5) :=
    (QuotientGroup.congr _ _ eB (pCore_map_iso 2 eB)).trans C.quotient
  have hz : center (B ⧸ pCore 2 B) = ⊥ := by
    apply le_bot_iff.mp
    intro b hb
    have h : e b ∈ center (alternatingGroup (Fin 5)) := (centerCongr e ⟨b,hb⟩).property
    rw [alternatingGroup.center_eq_bot (by simp),mem_bot] at h
    exact e.map_eq_one_iff.mp h
  have hr : primeRank 3 (B ⧸ pCore 2 B) = 1 := by
    rw [primeRank_congr 3 e,
      GLS3.Chapter5.PRank.alternating_primeRank_of_odd_prime 5 3 Nat.prime_three (by decide)]
  have ho : IsPGroup 2 (MulAut.Outer (B ⧸ pCore 2 B)) :=
    Theory.AlternatingFive.outer_isPGroup_two.of_equiv (MulAut.outerCongr e).symm
  exact sylow_commutative_of_normal_twoCore_quotient_rank_one (by decide) B hz hr
    (P.pointCentralizer_sqtk.stronglyQuasithin 3 Nat.prime_three (by decide)) ho R

/-- A cubic Sylow fixes a weight-four word; conjugation carries that word
onto the original selected point, without changing its centralizer. -/
theorem threeSylow_embeds_pointCentralizer (R : Sylow 3 L) :
    ∃ f : R →* P.pointCentralizer, Function.Injective f := by
  let a : R →* Equiv.Perm (Fin 7) :=
    (alternatingGroup (Fin 7)).subtype.comp (S.projection.comp (R : Subgroup L).subtype)
  let : MulAction R WeightFourWord := MulAction.compHom _ a
  obtain ⟨w,hw⟩ := R.isPGroup'.nonempty_fixed_point_of_prime_not_dvd_card WeightFourWord
    (by rw [card_weightFourWord]; decide)
  have hfix (r : R) : evenRepresentation (S.projection (r : L)).val w.val = w.val :=
    congrArg Subtype.val (hw r)
  obtain ⟨b,hb⟩ := weight_four_transitive w.val (D.model.coordinates P.point).toAdd
    w.property P.weight_four
  obtain ⟨l,hl⟩ := S.projection_surjective b
  let f : R →* L := (MulAut.conj l).toMonoidHom.comp (R : Subgroup L).subtype
  have hf : Function.Injective f := (MulAut.conj l).injective.comp (R : Subgroup L).subtype_injective
  have hc (r : R) : (f r : G) ∈ P.pointCentralizer := by
    have hrep : evenRepresentation (S.projection (f r)).val
        (D.model.coordinates P.point).toAdd = (D.model.coordinates P.point).toAdd := by
      change evenRepresentation (S.projection (l * (r : L) * l⁻¹)).val _ = _
      rw [map_mul,map_mul,map_inv]
      change evenRepresentation ((S.projection l).val * (S.projection (r : L)).val *
        (S.projection l).val⁻¹) _ = _
      rw [hl,← hb]
      rw [← Module.End.mul_apply,← map_mul]
      simp only [inv_mul_cancel_right]
      rw [map_mul,Module.End.mul_apply,hfix]
    have he := D.model.equivariant ⟨f r,S.chosen.normalizes (f r).property⟩ P.point
    rw [D.component_action,hrep] at he
    have h := congrArg Subtype.val
      (D.model.coordinates.injective (Multiplicative.toAdd.injective he))
    exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp h)
  let j : R →* P.pointCentralizer := (L.subtype.comp f).codRestrict _ hc
  refine ⟨j,fun x y h => hf (Subtype.ext ?_)⟩
  exact congrArg (fun z : P.pointCentralizer => (z : G)) h

/-- The normal A₅ section forces abelian cubic Sylows in the original L. -/
theorem threeSylow_commutative (C : P.ComponentAnalysis) (R : Sylow 3 L) :
    IsMulCommutative R := by
  obtain ⟨f,hf⟩ := P.threeSylow_embeds_pointCentralizer R
  obtain ⟨Q,hQ⟩ :=
    (R.isPGroup'.of_surjective f.rangeRestrict f.rangeRestrict_surjective).exists_le_sylow
  let : IsMulCommutative Q := P.pointCentralizer_threeSylow_commutative C Q
  let j := (inclusion hQ).comp f.rangeRestrict
  have hj : Function.Injective j := (inclusion_injective hQ).comp
    (fun x y h => hf (congrArg Subtype.val h))
  let : CommGroup R := MonoidHom.commGroupOfInjective j hj
  exact ⟨inferInstance⟩

/-- The abelian-Sylow premise of the cover reduction is now discharged. -/
theorem quotient_threeSylow_commutative (C : P.ComponentAnalysis)
    (R : Sylow 3 (L ⧸ pCore 2 L)) : IsMulCommutative R := by
  let q := QuotientGroup.mk' (pCore 2 L)
  obtain ⟨Q,rfl⟩ := Sylow.mapSurjective_surjective (f := q)
    (QuotientGroup.mk'_surjective _) 3 R
  let : IsMulCommutative Q := P.threeSylow_commutative C Q
  let : CommGroup (Q.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 L))) :=
    MonoidHom.commGroupOfSurjective (q.subgroupMap (Q : Subgroup L))
      (q.subgroupMap_surjective _)
  exact ⟨inferInstance⟩

theorem exists_abelian_threeSylow (C : P.ComponentAnalysis) :
    ∃ R : Sylow 3 (L ⧸ pCore 2 L), IsMulCommutative R :=
  ⟨Classical.choice inferInstance,P.quotient_threeSylow_commutative C _⟩

/-- Source 12.3.13: the full central kernel is the original two-core. -/
theorem central_kernel_eq_twoCore (C : P.ComponentAnalysis) :
    (center (L ⧸ pCore 2 L)).comap (QuotientGroup.mk' (pCore 2 L)) = pCore 2 L := by
  obtain ⟨R,hR⟩ := P.exists_abelian_threeSylow C
  exact central_kernel_eq_twoCore_of_abelian_threeSylow S R hR

/-- The genuine A₇ quotient marking retains the original projection. -/
def twoCoreQuotientEquiv (C : P.ComponentAnalysis) :
    (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 7) :=
  (QuotientGroup.quotientMulEquivOfEq (P.central_kernel_eq_twoCore C).symm).trans S.quotient

theorem twoCoreQuotientEquiv_apply (C : P.ComponentAnalysis) (l : L) :
    P.twoCoreQuotientEquiv C (QuotientGroup.mk' (pCore 2 L) l) = S.projection l := rfl

/-- The second assertion of source 12.3.13 with the original normalizer. -/
theorem normalizer_residual (C : P.ComponentAnalysis) :
    (primeToResidual 3 (normalizer (L : Set G))).map
      (normalizer (L : Set G)).subtype = L :=
  S.normalizer_residual_of_twoCore_quotient (P.twoCoreQuotientEquiv C)

/-- The literal L₁ is the ambient prime-to-three centralizer residual. -/
theorem L1_eq_ambient_residual_of_component (C : P.ComponentAnalysis)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u}) :
    P.L1 = (primeToResidual 3 (centralizer (P.Z : Set G))).map
      (centralizer (P.Z : Set G)).subtype :=
  P.L1_eq_ambient_residual structural (P.normalizer_residual C)

end TerminalPoint
end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
