module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.WeakClosure.LowRank.Linear
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.WeakClosure.LowRank.FixedSpaces
public import CFSG.Quasithin.ChapterH.Section05To09.NaturalDual.SourceTransport
public import Theory.ElementaryAbelian.BinaryRankDifference

/-!
# The inner actor rank bound on the marked source action

Restrict the original layer marking to the inner part of the actor. The
whole-module comparison identifies its action with a faithful representation
and its contragredient. When both pure generated cores are fixed by that
inner part, every nonidentity cyclic fixed space is common. The displacement
bound therefore gives twice its rank at most the natural dimension. The
actual index-two layer loses at most one rank from the original actor.
Source: Aschbacher--Smith, 12.1.8, printed pp.792--793 (PDF809--810).
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender BinaryNaturalDual
open CFSG.Quasithin.ChapterH.NaturalDual
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.WeakClosure.LowRank
variable {n : ℕ} {M E : Type*} [Group M] [Finite M]
  [AddCommGroup E] [Module (ZMod 2) E]

/-- The faithful natural action of the inner part of a source actor. -/
def innerNatural (S : SourceSetup n M E) (I : Subgroup M) :
    Representation (ZMod 2) ↥(I ⊓ componentLayer M) (BinaryLinear.OuterCyclic.Space n) :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
    (S.layer.toMonoidHom.comp (Subgroup.inclusion inf_le_right))

omit [Finite M] in
theorem innerNatural_faithful (S : SourceSetup n M E) (I : Subgroup M) :
    Function.Injective (innerNatural S I) := by
  intro a b he
  have hh := LinearEquiv.toLinearMap_injective he
  exact (Subgroup.inclusion_injective inf_le_right) (S.layer.injective hh)

omit [Finite M] in
theorem innerNatural_equivariant (S : SourceSetup n M E) (I : Subgroup M)
    (a : ↥(I ⊓ componentLayer M)) (v : E) :
    S.model.coordinates (S.representation a v) =
      ((innerNatural S I).prod (innerNatural S I).dual) a (S.model.coordinates v) := by
  rw [S.model.equivariant,
    show S.model.group a = MulAut.conj (S.layer (Subgroup.inclusion inf_le_right a)) from
      S.model.on_layer (Subgroup.inclusion inf_le_right a),
    (ModelOrbits.AutomorphismModel.coordinateAction S.degree).on_inner,
    naturalDualRepresentation_apply]
  apply Prod.ext
  · rfl
  · apply LinearMap.ext
    intro y
    change (S.model.coordinates v).2 ((S.layer (Subgroup.inclusion inf_le_right a)).symm y) =
      (S.model.coordinates v).2 (S.layer (Subgroup.inclusion inf_le_right a⁻¹) y)
    rw [map_inv, map_inv]
    rfl

/-- Both pure core restrictions imply the common-involution fixed-space
condition, hence the half-dimension bound for the actual inner actor. -/
theorem inner_rank_bound_of_core (S : SourceSetup n M E) (I : Subgroup M)
    [IsElementaryAbelian 2 I]
    (hn : S.natural ⊓ generatedCore (S.representation.comp I.subtype) (rank I-1) ≤
      S.fixed (I ⊓ componentLayer M))
    (hd : S.dual ⊓ generatedCore (S.representation.comp I.subtype) (rank I-1) ≤
      S.fixed (I ⊓ componentLayer M)) :
    2 * rank (I ⊓ componentLayer M) ≤ n := by
  let J := I ⊓ componentLayer M
  let : IsElementaryAbelian 2 J := IsElementaryAbelian.of_le inf_le_left
  let ρ := innerNatural S I
  have hcore (a : J) (ha : a ≠ 1) (v : E) (hv : S.representation a v = v) :
      v ∈ generatedCore (S.representation.comp I.subtype) (rank I-1) := by
    let b : I := ⟨a,a.property.1⟩
    have hb : b ≠ 1 := by
      intro he
      apply ha
      apply Subtype.ext
      change (a : M) = 1
      exact congrArg Subtype.val he
    apply cyclic_fixed_le_core (S.representation.comp I.subtype) b hb
    rw [mem_fixedSpace_zpowers_iff]
    exact hv
  have hnat : ∀ a : J, a ≠ 1 →
      fixedSpace ρ (zpowers a) ≤ fixedSpace ρ ⊤ := by
    intro a ha x hx b
    let v := S.model.coordinates.symm (x,0)
    have hvn : v ∈ S.natural :=
      (ModelOrbits.MarkedGeometry.mem_natural_iff_of_marking S.model.coordinates
        S.naturalCoordinates S.model.natural_marking v).mpr (by simp [v])
    have hv : S.representation a v = v := by
      apply S.model.coordinates.injective
      rw [innerNatural_equivariant]
      change (ρ a (S.model.coordinates v).1, ρ.dual a (S.model.coordinates v).2) = _
      simp only [v, LinearEquiv.apply_symm_apply, map_zero,
        (mem_fixedSpace_zpowers_iff ρ a x).mp hx]
    have hh := congrArg S.model.coordinates (hn ⟨hvn,hcore a ha v hv⟩ b.val)
    change S.model.coordinates (S.representation (b.val : M) v) = S.model.coordinates v at hh
    rw [innerNatural_equivariant S I b.val v] at hh
    have hb := congrArg Prod.fst hh
    simp only [Representation.prod, MonoidHom.coe_mk, OneHom.coe_mk,
      LinearMap.prodMap_apply] at hb
    simpa only [v, LinearEquiv.apply_symm_apply, ρ, MonoidHom.comp_apply,
      Subgroup.subtype_apply] using hb
  have hdual : ∀ a : J, a ≠ 1 →
      fixedSpace ρ.dual (zpowers a) ≤ fixedSpace ρ.dual ⊤ := by
    intro a ha x hx b
    let v := S.model.coordinates.symm (0,x)
    have hvd : v ∈ S.dual :=
      (ModelOrbits.MarkedGeometry.mem_dual_iff_of_marking S.model.coordinates
        S.model.dualCoordinates S.model.dual_marking v).mpr (by simp [v])
    have hv : S.representation a v = v := by
      apply S.model.coordinates.injective
      rw [innerNatural_equivariant]
      change (ρ a (S.model.coordinates v).1, ρ.dual a (S.model.coordinates v).2) = _
      simp only [v, LinearEquiv.apply_symm_apply, map_zero,
        (mem_fixedSpace_zpowers_iff ρ.dual a x).mp hx]
    have hh := congrArg S.model.coordinates (hd ⟨hvd,hcore a ha v hv⟩ b.val)
    change S.model.coordinates (S.representation (b.val : M) v) = S.model.coordinates v at hh
    rw [innerNatural_equivariant S I b.val v] at hh
    have hb := congrArg Prod.snd hh
    simp only [Representation.prod, MonoidHom.coe_mk, OneHom.coe_mk,
      LinearMap.prodMap_apply] at hb
    simpa only [v, LinearEquiv.apply_symm_apply, ρ, MonoidHom.comp_apply,
      Subgroup.subtype_apply] using hb
  have hh := rank_bound_of_common_dual_fixed ρ (innerNatural_faithful S I) hnat hdual
  simpa [rank, J, BinaryLinear.OuterCyclic.Space] using hh

/-- The actual layer has index two, so intersecting it loses at most one rank. -/
theorem rank_le_inner_rank_add_one (S : SourceSetup n M E) (I : Subgroup M)
    [IsElementaryAbelian 2 I] : rank I ≤ rank (I ⊓ componentLayer M) + 1 := by
  have hi : (componentLayer M).index = 2 :=
    ModelOrbits.SourceComparison.componentLayer_index S.degree S.projective
  have hrel : (I ⊓ componentLayer M).relIndex I ≤ 2 := by
    rw [inf_relIndex_left]
    exact (Nat.le_of_dvd (by decide)
      (by simpa only [hi] using (componentLayer M).relIndex_dvd_index_of_normal I))
  have hh := Subgroup.log_card_sub_log_card_eq_log_relIndex I
    (I ⊓ componentLayer M) inf_le_left
  have hl := Nat.log_mono_right (b := 2) hrel
  change rank I - rank (I ⊓ componentLayer M) = _ at hh
  norm_num at hl
  omega

end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.WeakClosure.LowRank
