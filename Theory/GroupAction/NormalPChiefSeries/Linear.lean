module
public import Theory.GroupAction.NormalPChiefSeries
public import Theory.ElementaryAbelian.AbelianNormalClosure
public import Theory.ElementaryAbelian.Quotient
public import Theory.ElementaryAbelian.VectorSpace
public import Theory.Representation.BinaryOffender.FlagCodimension

/-!
# Linearization of an actual chief series

For an elementary abelian normal two-subgroup U, ambient conjugation on
Additive U carries each term of a chosen chief series to its corresponding
binary subrepresentation. The actual group quotient projection is linear;
its kernel is the lower term. Its first-isomorphism equivalence identifies
the linear section with Additive of the original group chief factor, and
intertwines the previously defined quotient conjugation action.

Consequently all these literal chief factors are irreducible binary
representations, and their fixed codimensions sum to at most that on U.
No splitting or semisimplicity is used. Source: Aschbacher--Smith, D.1.3(n),
printed p.175; the group series also serves D.1.4--D.1.5.
-/

@[expose] public section
open scoped IsMulCommutative
namespace NoncentralChiefRefinement
open Subgroup Representation Representation.BinaryOffender
variable {H : Type*} [Group H] (U : Subgroup H) [U.Normal] [IsElementaryAbelian 2 U]

/-- Ambient conjugation linearized on the same elementary abelian subgroup. -/
noncomputable def normalRepresentation : Representation (ZMod 2) H (Additive U) where
  toFun h := (MulAut.conjNormal h : MulAut U).toMonoidHom.toAdditive.toZModLinearMap 2
  map_one' := by
    apply LinearMap.ext
    intro v
    change Additive.ofMul (MulAut.conjNormal 1 v.toMul) = v
    rw [map_one]
    rfl
  map_mul' h k := by
    apply LinearMap.ext
    intro v
    change Additive.ofMul (MulAut.conjNormal (h * k) v.toMul) = _
    rw [map_mul]
    rfl

namespace SeriesOn
variable {U} (s : SeriesOn U)

omit [IsElementaryAbelian 2 U] in
theorem term_le (i : Fin (s.series.length + 1)) : (s.series i).val ≤ U := by
  have h := CompositionSeries.le_last (s := s.series) i
  rw [s.last_eq] at h
  exact h

/-- Each group-theoretic term becomes its actual conjugation-invariant binary subspace. -/
noncomputable def linearTerm (i : Fin (s.series.length + 1)) :
    Subrepresentation (normalRepresentation U) where
  toSubmodule := AddSubgroup.toZModSubmodule 2 ((s.series i).val.subgroupOf U).toAddSubgroup
  apply_mem_toSubmodule h := by
    intro v hv
    exact (s.series i).property.conj_mem v.toMul hv h

theorem linearTerm_mono : Monotone s.linearTerm := by
  intro i j hij v hv
  exact s.series.strictMono.monotone hij hv

@[simp] theorem linearTerm_zero : s.linearTerm 0 = ⊥ := by
  apply Subrepresentation.toSubmodule_injective
  ext v
  change (v.toMul : H) ∈ (s.series 0).val ↔ v = 0
  have hs : (s.series 0).val = ⊥ := congrArg Subtype.val s.head_eq
  rw [hs]
  constructor
  · intro hv
    apply Additive.toMul.injective
    apply Subtype.ext
    exact hv
  · rintro rfl
    exact Subgroup.one_mem _

@[simp] theorem linearTerm_last : s.linearTerm (Fin.last s.series.length) = ⊤ := by
  apply top_unique
  intro v _
  change (v.toMul : H) ∈ (s.series (Fin.last s.series.length)).val
  rw [show (s.series (Fin.last s.series.length)).val = U from congrArg Subtype.val s.last_eq]
  exact v.toMul.property

/-- Extend the finite flag constantly after its last term. -/
noncomputable def linearFlag (n : ℕ) : Subrepresentation (normalRepresentation U) :=
  s.linearTerm ⟨min n s.series.length, by omega⟩

theorem linearFlag_mono : Monotone s.linearFlag := by
  intro i j hij
  apply s.linearTerm_mono
  exact min_le_min_right _ hij

/-- The linear section uses precisely the two adjacent terms of the chosen chief series. -/
noncomputable def linearFactor (i : Fin s.series.length) :=
  sectionRepresentation (normalRepresentation U) (s.linearTerm i.castSucc) (s.linearTerm i.succ)

instance termElementary (i : Fin (s.series.length + 1)) :
    IsElementaryAbelian 2 (s.series i).val := IsElementaryAbelian.of_le (s.term_le i)

instance factorElementary (i : Fin s.series.length) : IsElementaryAbelian 2 (s.Factor i) := by
  change IsElementaryAbelian 2 ((s.series i.succ).val ⧸
    (s.series i.castSucc).val.subgroupOf (s.series i.succ).val)
  infer_instance

/-- Changing only the subtype presentation of a chief-series term. -/
noncomputable def termLinearEquiv (i : Fin (s.series.length + 1)) :
    (s.linearTerm i).toSubmodule ≃ₗ[ZMod 2] Additive (s.series i).val := by
  let e : (s.linearTerm i).toSubmodule ≃+ Additive (s.series i).val :=
    { toFun := fun v => Additive.ofMul ⟨v.val.toMul, v.property⟩
      invFun := fun v => ⟨Additive.ofMul ⟨v.toMul, s.term_le i v.toMul.property⟩, v.toMul.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  exact { e with map_smul' := ZMod.map_smul e }

/-- The actual group quotient projection, regarded as a binary linear map. -/
noncomputable def factorProjection (i : Fin s.series.length) :
    (s.linearTerm i.succ).toSubmodule →ₗ[ZMod 2] Additive (s.Factor i) :=
  ((QuotientGroup.mk' ((s.lower i).val.subgroupOf (s.upper i).val)).toAdditive.toZModLinearMap 2).comp
    (s.termLinearEquiv i.succ).toLinearMap

theorem factorProjection_surjective (i : Fin s.series.length) :
    Function.Surjective (s.factorProjection i) := by
  intro y
  let _ := Subgroup.Normal.comap (s.lower i).property (s.upper i).val.subtype
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective ((s.lower i).val.subgroupOf (s.upper i).val) y.toMul
  refine ⟨(s.termLinearEquiv i.succ).symm (Additive.ofMul x), ?_⟩
  change Additive.ofMul (QuotientGroup.mk' ((s.lower i).val.subgroupOf (s.upper i).val) ((s.termLinearEquiv i.succ)
    ((s.termLinearEquiv i.succ).symm (Additive.ofMul x))).toMul) = y
  rw [LinearEquiv.apply_symm_apply]
  exact congrArg Additive.ofMul hx

theorem factorProjection_ker (i : Fin s.series.length) :
    (s.factorProjection i).ker =
      (sectionLower (normalRepresentation U) (s.linearTerm i.castSucc)
        (s.linearTerm i.succ)).toSubmodule := by
  ext x
  change QuotientGroup.mk' ((s.lower i).val.subgroupOf (s.upper i).val)
    ⟨x.val.toMul, x.property⟩ = 1 ↔ (x.val.toMul : H) ∈ (s.lower i).val
  exact QuotientGroup.eq_one_iff _

/-- The literal linear section is the additive version of the literal group chief factor. -/
noncomputable def factorLinearEquiv (i : Fin s.series.length) :
    ((s.linearTerm i.succ).toSubmodule ⧸
      (sectionLower (normalRepresentation U) (s.linearTerm i.castSucc)
        (s.linearTerm i.succ)).toSubmodule) ≃ₗ[ZMod 2] Additive (s.Factor i) :=
  (Submodule.quotEquivOfEq _ _ (s.factorProjection_ker i).symm).trans
    ((s.factorProjection i).quotKerEquivOfSurjective (s.factorProjection_surjective i))

@[simp] theorem factorLinearEquiv_mk (i : Fin s.series.length)
    (x : (s.linearTerm i.succ).toSubmodule) :
    s.factorLinearEquiv i (Submodule.Quotient.mk x) = s.factorProjection i x := rfl

/-- Linearization of the previously constructed quotient conjugation action. -/
noncomputable def factorRepresentation (i : Fin s.series.length) :
    Representation (ZMod 2) H (Additive (s.Factor i)) where
  toFun h := (s.action i h).toMonoidHom.toAdditive.toZModLinearMap 2
  map_one' := by
    apply LinearMap.ext
    intro x
    change Additive.ofMul (s.action i 1 x.toMul) = x
    rw [map_one]
    rfl
  map_mul' h k := by
    apply LinearMap.ext
    intro x
    change Additive.ofMul (s.action i (h * k) x.toMul) = _
    rw [map_mul]
    rfl

theorem factorLinearEquiv_equivariant (i : Fin s.series.length) (h : H) (x) :
    s.factorLinearEquiv i (s.linearFactor i h x) =
      s.factorRepresentation i h (s.factorLinearEquiv i x) := by
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
    change s.factorLinearEquiv i (Submodule.Quotient.mk
      ((s.linearTerm i.succ).toRepresentation h x)) = _
    rw [factorLinearEquiv_mk, factorLinearEquiv_mk]
    change Additive.ofMul (QuotientGroup.mk' ((s.lower i).val.subgroupOf (s.upper i).val)
      (MulAut.conjNormal h ⟨x.val.toMul, x.property⟩)) =
        Additive.ofMul (s.action i h (QuotientGroup.mk'
          ((s.lower i).val.subgroupOf (s.upper i).val) ⟨x.val.toMul, x.property⟩))
    rw [s.action_mk]

theorem factorRepresentation_irreducible (i : Fin s.series.length) :
    Representation.IsIrreducible (s.factorRepresentation i) := by
  let _ : Nontrivial (s.Factor i) := s.factor_nontrivial i
  rw [Representation.IsIrreducible, isSimpleOrder_iff]
  refine ⟨inferInstance, ?_⟩
  intro W
  let K : Subgroup (s.Factor i) := AddSubgroup.toSubgroup' W.toSubmodule.toAddSubgroup
  have hi := s.factor_irreducible i K (fun h x hx => W.apply_mem_toSubmodule h hx)
  rcases hi with hi | hi
  · left
    apply bot_unique
    intro x hx
    have hx' : x.toMul ∈ K := hx
    rw [hi] at hx'
    exact hx'
  · right
    apply top_unique
    intro x _
    have hx' : x.toMul ∈ K := by rw [hi]; trivial
    exact hx'

variable [Finite H]

/-- Fixed codimensions on this actual group-theoretic chief flag are superadditive. -/
theorem sum_linearFactor_fixedCodim_le (A : Subgroup H) :
    ∑ i : Fin s.series.length, fixedCodim (s.linearFactor i) A ≤
      fixedCodim (normalRepresentation U) A := by
  have h := sum_fixedCodim_flag_le (normalRepresentation U) s.linearFlag s.linearFlag_mono
    s.series.length A
  rw [← Fin.sum_univ_eq_sum_range] at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  have hi : min (i : ℕ) s.series.length = i := min_eq_left (Nat.le_of_lt i.isLt)
  have hj : min ((i : ℕ) + 1) s.series.length = (i : ℕ) + 1 := min_eq_left i.isLt
  have ei : (⟨min (i : ℕ) s.series.length, by omega⟩ : Fin (s.series.length + 1)) =
      i.castSucc := Fin.ext hi
  have ej : (⟨min ((i : ℕ) + 1) s.series.length, by omega⟩ : Fin (s.series.length + 1)) =
      i.succ := Fin.ext hj
  change fixedCodim (s.linearFactor i) A =
    fixedCodim (sectionRepresentation (normalRepresentation U)
      (s.linearTerm _) (s.linearTerm _)) A
  rw [ei, ej]
  rfl

/-- The superadditivity statement on the literal group chief factors and their
previously constructed conjugation actions. -/
theorem sum_factor_fixedCodim_le (A : Subgroup H) :
    ∑ i : Fin s.series.length, fixedCodim (s.factorRepresentation i) A ≤
      fixedCodim (normalRepresentation U) A := by
  have he (i : Fin s.series.length) : fixedCodim (s.linearFactor i) A =
      fixedCodim (s.factorRepresentation i) A := by
    simpa only [Subgroup.map_id] using fixedCodim_map_equivariant
      (s.linearFactor i) (s.factorRepresentation i) (MonoidHom.id H)
      (s.factorLinearEquiv i) (s.factorLinearEquiv_equivariant i) A
  simpa only [he] using s.sum_linearFactor_fixedCodim_le A

end SeriesOn
end NoncentralChiefRefinement
