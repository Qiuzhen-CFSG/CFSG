module

public import Theory.Representation.SL3DoubledNaturalOffenders.Centralizer
public import Theory.Representation.SL3DoubledNaturalOffenders.TensorEstimate.ProjectionBounds
public import Theory.SpecificGroups.PSL3Even.AutomorphismTwoRank.SourceBound
public import Theory.GroupAction.PerfectCentralQuotient
public import Theory.ElementaryAbelian.Quotient

/-!
# Two-rank of the doubled natural normalizer

Conjugation on the identical SL₃ component has the full GL₂ multiplicity
centralizer as its kernel. Every elementary two-subgroup of GL₂ lies in SL₂
and has order at most the field order. Perfectness detects automorphisms of
SL₃ on its projective quotient, whose automorphism two-rank is 2n. The kernel
and image bounds therefore give 3n for the entire binary doubled normalizer.

The original full-module action consumes this estimate in LocalMinimum,
without an odd-degree restriction or an assumed normalizer description.

Source: Aschbacher--Smith, 11.3.6, printed p.772; the automorphism rank
calculation is the proved G.9/16.3.9 model theorem.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.SL3DoubledNaturalOffenders Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Doubled
namespace AutomizerRank
variable {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

local instance : Finite (Module.End (ZMod 2) (Space F)) :=
  Finite.of_injective DFunLike.coe DFunLike.coe_injective

private theorem multiplicity_rank {n : ℕ} (hF : Nat.card F = 2^n) :
    primeRank 2 (GL (Fin 2) F) ≤ n := by
  apply (primeRank_le_iff_elementary_card_le _).mpr
  intro E hE
  let := hE
  have hd (a : E) : a.val.val.det = 1 := by
    apply CharTwo.sq_injective
    have hp : (a.val : GL (Fin 2) F)^2 = 1 :=
      elemPow_eq_one_of_isElementaryAbelian a.val a.property
    have hh := congrArg (fun g : GL (Fin 2) F => g.val.det) hp
    simpa only [pow_two,Units.val_mul,Units.val_one,Matrix.det_mul,Matrix.det_one,one_mul] using hh
  let j : E →* MultiplicitySL F :=
    { toFun a := ⟨a.val.val,hd a⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
  have hj : Function.Injective j := by
    intro a b he
    apply Subtype.ext
    apply Units.ext
    exact congrArg Subtype.val he
  let : IsElementaryAbelian 2 j.range :=
    IsElementaryAbelian.of_surjective j.rangeRestrict j.rangeRestrict_surjective
  have h := multiplicity_elementary_card_le j.range
  rw [← Nat.card_congr (MonoidHom.ofInjective hj).toEquiv,hF] at h
  exact h

private def multiplicityCentralizer : GL (Fin 2) F →*
    centralizer (component F : Set (Ambient F)) :=
  (Units.map (multiplicityHom F).toMonoidHom).codRestrict _ (by
    intro c
    rw [mem_centralizer_iff]
    rintro _ ⟨g,rfl⟩
    apply Units.ext
    exact (multiplicity_commutes F c.val g).symm)

omit [Finite F] [CharP F 2] in
private theorem multiplicityCentralizer_bijective :
    Function.Bijective (multiplicityCentralizer (F := F)) := by
  constructor
  · intro a b he
    apply Units.ext
    apply multiplicity_injective F
    exact congrArg (fun x : centralizer (component F : Set (Ambient F)) => x.val.val) he
  · intro b
    obtain ⟨c,hc⟩ := centralizer_units b.val b.property
    refine ⟨c,?_⟩
    apply Subtype.ext
    apply Units.ext
    exact hc.symm

/-- The entire binary centralizer of the identical component has two-rank at most n. -/
theorem centralizer_rank {n : ℕ} (hF : Nat.card F = 2^n) :
    primeRank 2 (centralizer (component F : Set (Ambient F))) ≤ n := by
  rw [← primeRank_equiv 2 (MulEquiv.ofBijective
    (multiplicityCentralizer (F := F)) multiplicityCentralizer_bijective)]
  exact multiplicity_rank hF

omit [CharP F 2] in
private theorem component_automorphism_rank {n : ℕ} (hn : 0<n)
    (hF : Nat.card F = 2^n) : primeRank 2 (MulAut (component F)) ≤ 2*n := by
  have hi : Function.Injective (representation F).asGroupHom :=
    fun _ _ he => representation_injective F (congrArg Units.val he)
  let e : SL F ≃* component F := MonoidHom.ofInjective hi
  rw [← primeRank_equiv 2 (MulAut.congr e)]
  let := Atlas.sl_perfect (F := F) 3 (by decide)
  have h := primeRank_le_of_injective 2 (Subgroup.quotientAut (center (SL F)))
    MulAut.quotient_center_injective
  exact h.trans_eq (Matrix.PSL3Even.automorphism_two_rank_eq F hn hF)

/-- The full binary normalizer of doubled natural SL₃ has two-rank at most 3n.
Conjugation has a multiplicity GL₂ kernel and an image in Aut(SL₃). -/
theorem normalizer_rank {n : ℕ} (hn : 0<n) (hF : Nat.card F = 2^n) :
    primeRank 2 (SL3DoubledNaturalOffenders.normalizer F) ≤ 3*n := by
  have h := primeRank_le_ker_add (p := 2) (component F).normalizerMonoidHom
  have hk : primeRank 2 (component F).normalizerMonoidHom.ker ≤ n := by
    rw [Subgroup.normalizerMonoidHom_ker,
      primeRank_equiv 2 (subgroupOfEquivOfLe (centralizer_le_normalizer (component F : Set (Ambient F))))]
    exact centralizer_rank hF
  have ha := component_automorphism_rank hn hF
  change primeRank 2 (SL3DoubledNaturalOffenders.normalizer F) ≤ _ at h
  omega
end AutomizerRank
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Doubled
