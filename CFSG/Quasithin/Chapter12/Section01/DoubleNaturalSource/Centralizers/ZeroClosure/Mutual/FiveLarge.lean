module

public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.ZeroClosure.Mutual.FiveSmall

/-!
# The large-rank mutually normalizing branch of 12.1.3

Mutual normalization of elementary abelian groups makes their conjugation
actions quadratic: the moved space lies in the fixed space. H.9.2 puts a
rank-at-least-five actor inside the layer. The natural/dual displacement
bound and quadraticity then force total fixed codimension five, with
factor codimensions two and three. The reverse actor has rank five and
is also inner. Choosing the marked summand with moved dimension two
contradicts the same reverse-action obstruction used in the small branch.

This treats every rank at least five without a radical-conjugator choice
or a symmetric-rank premise. The last theorem assembles both rank cases
on the actual pair; `ZeroClosure.Assembly` supplies the chosen-orbit consumer.
Source: Aschbacher--Smith, 12.1.3, printed p.790 (PDF807), using H.9.2(2).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender Module
open scoped IsMulCommutative commutatorElement
open CFSG.Quasithin.ChapterH.NaturalDual CFSG.Quasithin.ChapterE
open CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.WeakClosure.LowRank
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.ZeroClosure.Mutual
variable {M E : Type*} [Group M] [AddCommGroup E] [Module (ZMod 2) E]

/-- Self-duality bounds the fixed codimension of a quadratic inner actor. -/
theorem inner_quadratic_budget {n : ℕ} (S : SourceSetup n M E) (I : Subgroup M)
    (hi : I ≤ componentLayer M)
    (hq : subspaceCommutator S.representation ⊤ I ≤ S.fixed I) :
    fixedCodim S.representation I ≤ n := by
  let : FiniteDimensional (ZMod 2) E := S.model.coordinates.symm.finiteDimensional
  let J := I ⊓ componentLayer M
  let ρ := innerNatural S I
  have hj : J = I := inf_eq_left.mpr hi
  have hm := moved_finrank_equivariant (S.representation.comp J.subtype)
    (ρ.prod ρ.dual) (MonoidHom.id J) S.model.coordinates
    (innerNatural_equivariant S I) ⊤
  rw [subspaceCommutator_comp_map,←MonoidHom.range_eq_map,range_subtype,
    Subgroup.map_id] at hm
  have hm' := (congrArg (fun A => finrank (ZMod 2)
    (subspaceCommutator S.representation ⊤ A)) hj).symm.trans hm
  have hd : fixedCodim ρ ⊤ = finrank (ZMod 2) (subspaceCommutator ρ.dual ⊤ ⊤) := by
    rw [subspaceCommutator_top_eq_coinvariants]
    exact Representation.finrank_quotient_invariants_eq_dual_commutator (ρ.comp (⊤ : Subgroup J).subtype)
  rw [moved_finrank_prod,←fixedCodim_dual_eq_moved_finrank ρ ⊤,←hd] at hm'
  have hc := (inner_fixedCodim_eq S I).trans (congrArg (fixedCodim S.representation) hj)
  rw [fixedCodim_prod] at hc
  change fixedCodim ρ ⊤ + fixedCodim ρ.dual ⊤ = _ at hc
  have hle := Submodule.finrank_mono hq
  have htotal := fixedCodim_add_finrank S.representation I
  have hdim : finrank (ZMod 2) E = 2 * n := by
    rw [S.model.coordinates.finrank_eq]
    simp [BinaryNaturalDual.CoordinateSpace, BinaryLinear.OuterCyclic.Space,
      Module.finrank_prod, two_mul]
  change _ ≤ finrank (ZMod 2) (fixedSpace S.representation I) at hle
  omega

/-- The corresponding dimensions on the original dual summand. -/
theorem inner_dual_dimensions {n : ℕ} (S : SourceSetup n M E) (I : Subgroup M)
    (hi : I ≤ componentLayer M) :
    finrank (ZMod 2) S.dual - finrank (ZMod 2) ↥(S.dual ⊓ S.fixed I) =
        fixedCodim (innerNatural S I).dual ⊤ ∧
      finrank (ZMod 2) (subspaceCommutator S.representation S.dual I) =
        fixedCodim (innerNatural S I) ⊤ := by
  let : FiniteDimensional (ZMod 2) E := S.model.coordinates.symm.finiteDimensional
  let J := I ⊓ componentLayer M
  let ρ := innerNatural S I
  let e := S.dualEmbedding
  have hinj : Function.Injective e :=
    S.dual.injective_subtype.comp S.model.dualCoordinates.symm.injective
  have hj : J = I := inf_eq_left.mpr hi
  have ha (a : J) (x : Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n)) :
      S.representation a (e x) = e (ρ.dual a x) := by
    apply S.model.coordinates.injective
    rw [innerNatural_equivariant S I, S.dualEmbedding_coordinates,
      S.dualEmbedding_coordinates]
    change (ρ a 0, ρ.dual a x) = (0,ρ.dual a x)
    rw [map_zero]
  have hf : fixedSpace (S.representation.comp J.subtype) ⊤ = S.fixed I := by
    rw [fixedSpace_comp_map,←MonoidHom.range_eq_map,range_subtype,hj]
    rfl
  have hcomap : (S.fixed I).comap e = fixedSpace ρ.dual ⊤ := by
    ext x
    change e x ∈ S.fixed I ↔ x ∈ fixedSpace ρ.dual ⊤
    rw [←hf]
    simpa only [Subgroup.map_id] using embedding_mem_fixedSpace_iff
      (S.representation.comp J.subtype) ρ.dual (MonoidHom.id J) e hinj ha ⊤ x
  have hfixed : (fixedSpace ρ.dual ⊤).map e = S.dual ⊓ S.fixed I := by
    rw [←hcomap,Submodule.map_comap_eq,S.dualEmbedding_range,inf_comm]
  have hcomm : subspaceCommutator S.representation S.dual I =
      (subspaceCommutator ρ.dual ⊤ ⊤).map e := by
    have hh := subspaceCommutator_map_embedding (S.representation.comp J.subtype)
      ρ.dual (MonoidHom.id J) e ha ⊤ ⊤
    rw [Submodule.map_top,S.dualEmbedding_range,Subgroup.map_id,
      subspaceCommutator_comp_map,←MonoidHom.range_eq_map,range_subtype] at hh
    exact (congrArg (subspaceCommutator S.representation S.dual) hj).symm.trans hh
  have hfn : finrank (ZMod 2) ↥(S.dual ⊓ S.fixed I) =
      finrank (ZMod 2) (fixedSpace ρ.dual ⊤) := by
    rw [←hfixed]
    exact (Submodule.equivMapOfInjective e hinj _).finrank_eq.symm
  constructor
  · have hd := S.model.dualCoordinates.finrank_eq
    have hc := fixedCodim_add_finrank ρ.dual ⊤
    rw [hfn]
    change finrank (ZMod 2) S.dual - finrank (ZMod 2) (fixedSpace ρ.dual ⊤) =
      fixedCodim ρ.dual ⊤
    omega
  · rw [hcomm]
    have hd : fixedCodim ρ ⊤ = finrank (ZMod 2) (subspaceCommutator ρ.dual ⊤ ⊤) := by
      rw [subspaceCommutator_top_eq_coinvariants]
      exact Representation.finrank_quotient_invariants_eq_dual_commutator
        (ρ.comp (⊤ : Subgroup J).subtype)
    exact (Submodule.equivMapOfInjective e hinj _).finrank_eq.symm.trans hd.symm

/-- Every quadratic high-rank degree-five actor has factor codimensions two
and three, in one of the two actual marked orders. -/
theorem five_large_quadratic_parameters [Finite M] (S : SourceSetup 5 M E)
    (I : Subgroup M) [IsElementaryAbelian 2 I] (hr : 5 ≤ rank I)
    (hq : subspaceCommutator S.representation ⊤ I ≤ S.fixed I) :
    I ≤ componentLayer M ∧ fixedCodim S.representation I = 5 ∧
      ((fixedCodim (innerNatural S I) ⊤ = 2 ∧ fixedCodim (innerNatural S I).dual ⊤ = 3) ∨
       (fixedCodim (innerNatural S I) ⊤ = 3 ∧ fixedCodim (innerNatural S I).dual ⊤ = 2)) := by
  let : FiniteDimensional (ZMod 2) E := S.model.coordinates.symm.finiteDimensional
  have hi : I ≤ componentLayer M := SourceFiveActors.high_rank_inner S I (by
    rw [←IsElementaryAbelian.log_card_eq_primeRank I]
    exact hr)
  have hc := inner_quadratic_budget S I hi hq
  let J := I ⊓ componentLayer M
  let ρ := innerNatural S I
  have hj : J = I := inf_eq_left.mpr hi
  have hs := (inner_fixedCodim_eq S I).trans (congrArg (fixedCodim S.representation) hj)
  rw [fixedCodim_prod] at hs
  change fixedCodim ρ ⊤ + fixedCodim ρ.dual ⊤ = _ at hs
  have hm := rank_le_fixedCodim_mul_dual ρ (innerNatural_faithful S I) ⊤
  have hrt : rank (⊤ : Subgroup J) = rank I := by simp [rank,hj]
  rw [hrt] at hm
  have hp : 2 ≤ fixedCodim ρ ⊤ := by
    by_contra! hh
    interval_cases h : fixedCodim ρ ⊤ <;> simp only [zero_mul,one_mul] at hm <;> omega
  have hq' : 2 ≤ fixedCodim ρ.dual ⊤ := by
    by_contra! hh
    interval_cases h : fixedCodim ρ.dual ⊤ <;> simp only [mul_zero,mul_one] at hm <;> omega
  have hp' : fixedCodim ρ ⊤ ≤ 3 := by omega
  have hq'' : fixedCodim ρ.dual ⊤ ≤ 3 := by omega
  have hcases : (fixedCodim ρ ⊤ = 2 ∧ fixedCodim ρ.dual ⊤ = 3) ∨
      (fixedCodim ρ ⊤ = 3 ∧ fixedCodim ρ.dual ⊤ = 2) := by
    interval_cases a : fixedCodim ρ ⊤ <;> interval_cases b : fixedCodim ρ.dual ⊤ <;>
      norm_num at hm hs ⊢ <;> omega
  exact ⟨hi,by rcases hcases with h | h <;> omega,hcases⟩

variable {G : Type*} [Group G] [Finite G] {W : Subgroup G} [IsElementaryAbelian 2 W]

omit [Finite G] in
/-- Mutual normalization makes the actual elementary conjugation action quadratic. -/
theorem mutual_commutator_le_fixed (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hA : A ≤ normalizer (W : Set G)) (hW : W ≤ normalizer (A : Set G)) :
    subspaceCommutator (automizerRepresentation W) ⊤ (inducedAutomizer W A) ≤
      fixedSpace (automizerRepresentation W) (inducedAutomizer W A) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨a,ha,v,_,rfl⟩
  obtain ⟨b,hb,rfl⟩ := ha
  apply (mem_fixedSpace_inducedAutomizer W A hA _).mpr
  have hm : ((automizerRepresentation W (W.normalizerMonoidHom.rangeRestrict b) v - v).toMul : G) ∈ A := by
    rw [toMul_sub,div_eq_mul_inv]
    change (b : G) * (v.toMul : G) * (b : G)⁻¹ * (v.toMul : G)⁻¹ ∈ A
    exact le_normalizer_iff_commutator_le_left.mp hW (commutator_mem_commutator hb v.toMul.property)
  intro x hx
  exact congrArg Subtype.val (mul_comm (⟨x,hx⟩ : A) ⟨_,hm⟩)

/-- The large-rank branch of 12.1.3, including every rank at least five. -/
theorem five_large_false
    (S : SourceSetup 5 (Automizer W) (Additive W))
    (hρ : S.representation = automizerRepresentation W) (g : G)
    (hA : W.map (MulAut.conj g).toMonoidHom ≤ normalizer (W : Set G))
    (hW : W ≤ normalizer (W.map (MulAut.conj g).toMonoidHom : Set G))
    (hr : 5 ≤ rank (inducedAutomizer W (W.map (MulAut.conj g).toMonoidHom))) : False := by
  let A := W.map (MulAut.conj g).toMonoidHom
  let I := inducedAutomizer W A
  let A' := W.map (MulAut.conj g⁻¹).toMonoidHom
  let I' := inducedAutomizer W A'
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 I := inducedAutomizer_elementary W A hA
  have hq : subspaceCommutator S.representation ⊤ I ≤ S.fixed I := by
    rw [SourceSetup.fixed,hρ]
    exact mutual_commutator_le_fixed A hA hW
  obtain ⟨hi,hc,hcases⟩ := five_large_quadratic_parameters S I hr hq
  have hA' := reverse_normalizes g hW
  let : IsElementaryAbelian 2 A' := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 I' := inducedAutomizer_elementary W A' hA'
  have hr' : 5 ≤ rank I' := by
    rw [hρ,reverse_rank g hA hW] at hc
    exact hc.ge
  have hi' : I' ≤ componentLayer (Automizer W) := SourceFiveActors.high_rank_inner S I' (by
    rw [←IsElementaryAbelian.log_card_eq_primeRank I']
    exact hr')
  rcases hcases with ⟨hp,hq⟩ | ⟨hp,hq⟩
  · obtain ⟨hf,hm⟩ := inner_dual_dimensions S I hi
    apply reverse_subspace_false S hρ g hA hW hi' S.dual
    · change 2 ≤ finrank (ZMod 2) S.dual - finrank (ZMod 2) ↥(S.dual ⊓ S.fixed I)
      rw [hf,hq]
      decide
    · rw [hm,hp]
  · obtain ⟨hf,hm⟩ := inner_natural_dimensions S I hi
    apply reverse_subspace_false S hρ g hA hW hi' S.natural
    · change 2 ≤ finrank (ZMod 2) S.natural - finrank (ZMod 2) ↥(S.natural ⊓ S.fixed I)
      rw [hf,hp]
      decide
    · rw [hm,hq]
end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.ZeroClosure.Mutual

namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.ZeroClosure.Mutual
variable {G : Type*} [Group G] [Finite G] {W : Subgroup G} [IsElementaryAbelian 2 W]

/-- Both rank branches centralize the original mutually normalizing pair. -/
theorem five_mutual_centralizes
    (S : SourceSetup 5 (Automizer W) (Additive W))
    (hρ : S.representation = automizerRepresentation W) (g : G)
    (hA : W.map (MulAut.conj g).toMonoidHom ≤ normalizer (W : Set G))
    (hW : W ≤ normalizer (W.map (MulAut.conj g).toMonoidHom : Set G)) :
    ⁅W,W.map (MulAut.conj g).toMonoidHom⁆ = ⊥ := by
  exact five_centralizes_of_rank_cases
    (fun k hkA hkW hnc ho hr => five_small_false S hρ k hkA hkW hnc ho hr)
    (fun k hkA hkW _hnc hr => five_large_false S hρ k hkA hkW hr) g hA hW
end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.ZeroClosure.Mutual

