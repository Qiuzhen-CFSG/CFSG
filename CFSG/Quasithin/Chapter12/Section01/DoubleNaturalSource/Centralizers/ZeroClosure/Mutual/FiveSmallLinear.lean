module

public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.WeakClosure.LowRank.SmallFixed
public import CFSG.Quasithin.ChapterH.Section05To09.NaturalDual.SourceFiveActors.Outer
public import CFSG.Quasithin.ChapterH.Section05To09.NaturalDual.SourceVectorGeometry
public import Theory.Representation.BinaryOffender.MovedDimension

/-!
# The small degree-five offender budget

An outer involution fixes exactly half of the doubled module. Consequently
an elementary actor of fixed codimension below five is inner. For its
faithful natural action and contragredient, counting displacement maps gives
r ≤ ab, while the offender inequality gives a+b ≤ r < 5. Positivity forces
a=b=2 and r=4. The marked natural embedding transfers these dimensions to
the original summand, including its actual displacement span.

These calculations feed the literal mutually normalizing pair in
`FiveSmall`. No offender classification or pure-vector fusion is assumed.
Source: Aschbacher--Smith, 12.1.3, printed pp.789--790 (PDF806--807),
and H.9.2(1), printed p.390.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender Module
open CFSG.Quasithin.ChapterH.NaturalDual
open CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.WeakClosure.LowRank
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.ZeroClosure.Mutual
variable {M E : Type*} [Group M] [Finite M] [AddCommGroup E] [Module (ZMod 2) E]

omit [Finite M] in
/-- An elementary actor of fixed codimension less than five is inner. -/
theorem five_inner_of_small_fixed (S : SourceSetup 5 M E) (I : Subgroup M)
    [IsElementaryAbelian 2 I] (hc : fixedCodim S.representation I < 5) :
    I ≤ componentLayer M := by
  let : FiniteDimensional (ZMod 2) E := S.model.coordinates.symm.finiteDimensional
  have hd : finrank (ZMod 2) E = 10 := by
    rw [S.model.coordinates.finrank_eq]
    norm_num [BinaryNaturalDual.CoordinateSpace, BinaryLinear.OuterCyclic.Space,
      Module.finrank_prod]
  intro a ha
  by_contra ho
  have hp : a ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian a ha
  have hf := SourceFiveActors.involutionFixed_finrank S a hp ho
  have he := fixedCodim_add_finrank S.representation (zpowers a)
  change finrank (ZMod 2) (fixedSpace S.representation (zpowers a)) = 5 at hf
  have hm := CFSG.Quasithin.ChapterE.fixedCodim_mono S.representation (zpowers_le.mpr ha)
  omega

/-- The dimension budget forces the small offender to have rank four,
with codimension two on each of its faithful dual factors. -/
theorem five_small_offender_parameters (S : SourceSetup 5 M E) (I : Subgroup M)
    [IsElementaryAbelian 2 I] (hne : I ≠ ⊥)
    (ho : fixedCodim S.representation I ≤ rank I) (hr : rank I < 5) :
    I ≤ componentLayer M ∧ rank I = 4 ∧ fixedCodim S.representation I = 4 ∧
      fixedCodim (innerNatural S I) ⊤ = 2 ∧
      fixedCodim (innerNatural S I).dual ⊤ = 2 := by
  let : FiniteDimensional (ZMod 2) E := S.model.coordinates.symm.finiteDimensional
  have hi := five_inner_of_small_fixed S I (lt_of_le_of_lt ho hr)
  let J := I ⊓ componentLayer M
  let ρ := innerNatural S I
  have hj : J = I := inf_eq_left.mpr hi
  have ht : (⊤ : Subgroup J) ≠ ⊥ := by
    intro he
    have hh := congrArg (Subgroup.map J.subtype) he
    apply hne
    simpa only [←MonoidHom.range_eq_map, range_subtype, Subgroup.map_bot, hj] using hh
  have h1 := fixedCodim_pos_of_faithful ρ (innerNatural_faithful S I) ht
  have h2 := fixedCodim_pos_of_faithful ρ.dual
    (faithful_dual ρ (innerNatural_faithful S I)) ht
  have hm := rank_le_fixedCodim_mul_dual ρ (innerNatural_faithful S I) ⊤
  have hrt : rank (⊤ : Subgroup J) = rank I := by simp [rank, hj]
  rw [hrt] at hm
  have hs := (inner_fixedCodim_eq S I).trans
    (congrArg (fixedCodim S.representation) hj)
  rw [fixedCodim_prod] at hs
  change fixedCodim ρ ⊤ + fixedCodim ρ.dual ⊤ = _ at hs
  have hp : 2 ≤ fixedCodim ρ ⊤ := by
    by_contra! hh
    have hh' : fixedCodim ρ ⊤ = 1 := by omega
    rw [hh',one_mul] at hm
    omega
  have hq : 2 ≤ fixedCodim ρ.dual ⊤ := by
    by_contra! hh
    have hh' : fixedCodim ρ.dual ⊤ = 1 := by omega
    rw [hh',mul_one] at hm
    omega
  have hp2 : fixedCodim ρ ⊤ = 2 := by omega
  have hq2 : fixedCodim ρ.dual ⊤ = 2 := by omega
  exact ⟨hi, by omega, by omega, hp2, hq2⟩

omit [Finite M] in
/-- The natural summand retains its exact fixed codimension and moved
dimension under the literal inner action. -/
theorem inner_natural_dimensions {n : ℕ} (S : SourceSetup n M E) (I : Subgroup M)
    (hi : I ≤ componentLayer M) :
    finrank (ZMod 2) S.natural - finrank (ZMod 2) ↥(S.natural ⊓ S.fixed I) =
        fixedCodim (innerNatural S I) ⊤ ∧
      finrank (ZMod 2) (subspaceCommutator S.representation S.natural I) =
        fixedCodim (innerNatural S I).dual ⊤ := by
  let : FiniteDimensional (ZMod 2) E := S.model.coordinates.symm.finiteDimensional
  let J := I ⊓ componentLayer M
  let ρ := innerNatural S I
  let e := S.naturalEmbedding
  have hinj : Function.Injective e :=
    S.natural.injective_subtype.comp S.naturalCoordinates.symm.injective
  have hj : J = I := inf_eq_left.mpr hi
  have ha (a : J) (x : BinaryLinear.OuterCyclic.Space n) :
      S.representation a (e x) = e (ρ a x) := by
    apply S.model.coordinates.injective
    rw [innerNatural_equivariant S I, S.naturalEmbedding_coordinates,
      S.naturalEmbedding_coordinates]
    change (ρ a x, ρ.dual a 0) = (ρ a x,0)
    rw [map_zero]
  have hf : fixedSpace (S.representation.comp J.subtype) ⊤ = S.fixed I := by
    rw [fixedSpace_comp_map,←MonoidHom.range_eq_map,range_subtype,hj]
    rfl
  have hcomap : (S.fixed I).comap e = fixedSpace ρ ⊤ := by
    ext x
    change e x ∈ S.fixed I ↔ x ∈ fixedSpace ρ ⊤
    rw [←hf]
    simpa only [Subgroup.map_id] using embedding_mem_fixedSpace_iff
      (S.representation.comp J.subtype) ρ (MonoidHom.id J) e hinj ha ⊤ x
  have hfixed : (fixedSpace ρ ⊤).map e = S.natural ⊓ S.fixed I := by
    rw [←hcomap,Submodule.map_comap_eq, S.naturalEmbedding_range,inf_comm]
  have hcomm : subspaceCommutator S.representation S.natural I =
      (subspaceCommutator ρ ⊤ ⊤).map e := by
    have hh := subspaceCommutator_map_embedding (S.representation.comp J.subtype)
      ρ (MonoidHom.id J) e ha ⊤ ⊤
    rw [Submodule.map_top,S.naturalEmbedding_range,Subgroup.map_id,
      subspaceCommutator_comp_map,←MonoidHom.range_eq_map,range_subtype] at hh
    exact (congrArg (subspaceCommutator S.representation S.natural) hj).symm.trans hh
  have hfn : finrank (ZMod 2) ↥(S.natural ⊓ S.fixed I) =
      finrank (ZMod 2) (fixedSpace ρ ⊤) := by
    rw [←hfixed]
    exact (Submodule.equivMapOfInjective e hinj _).finrank_eq.symm
  constructor
  · have hd := S.naturalCoordinates.finrank_eq
    have hc := fixedCodim_add_finrank ρ ⊤
    rw [hfn]
    change finrank (ZMod 2) S.natural - finrank (ZMod 2) (fixedSpace ρ ⊤) =
      fixedCodim ρ ⊤
    omega
  · rw [hcomm]
    exact (Submodule.equivMapOfInjective e hinj _).finrank_eq.symm.trans
      (fixedCodim_dual_eq_moved_finrank ρ ⊤).symm

end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.ZeroClosure.Mutual
