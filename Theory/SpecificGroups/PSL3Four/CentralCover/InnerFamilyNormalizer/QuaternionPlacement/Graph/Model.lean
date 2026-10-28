module

public import Theory.SpecificGroups.PSL3Four.CentralCover.InnerFamilyNormalizer.QuaternionPlacement.Reduction
public import Theory.SpecificGroups.PSL3Four.CentralCover.FixedResiduals.ProjectiveGraph
public import Theory.SpecificGroups.PSL3.FieldComponentFixer
public import Theory.AtlasPort.ExceptionalIsomorphisms.Elementary
public import Theory.GroupTheory.AutomorphismTowerSimple

/-!
# The orthogonal–field–graph candidate for the graph centralizer

The inverse-transpose fixed subgroup of SL₃(4), extended by the actual
entrywise Frobenius, acts on PSL₃(4). A second cyclic factor acts by the
graph involution. The two factors commute. The resulting homomorphism
into the full automorphism centralizer is faithful: binary transvections
separate the graph and field factors, and a scalar orthogonal matrix is
trivial in characteristic two.

Surjectivity and the Sylow calculation are separate requirements; the
construction itself asserts neither. Source: Aschbacher–Smith 16.1.4(6),
printed p.1171, and the quaternion application on printed p.1192.
-/

@[expose] public section
noncomputable section
open Subgroup
open Matrix.PSL3.OuterSolvable
open Matrix.PSL3Four.ExtendedCentralizer.ProjectiveFixer
namespace Matrix.PSL3Four.InnerFamilyNormalizer.QuaternionPlacement.Graph

/-- Orthogonal determinant-one matrices for the identity bilinear form. -/
abbrev Fixed := (PSL3.OuterSolvable.graphSL F).fixedSubgroup

private theorem graphSL_frobenius (x : SL) :
    graphSL F (slFrobenius x) = slFrobenius (graphSL F x) := by
  change (SpecialLinearGroup.transpose (slFrobenius x))⁻¹ =
    slFrobenius (SpecialLinearGroup.transpose x)⁻¹
  rw [map_inv]
  congr 1

/-- Frobenius restricted to the actual orthogonal subgroup. -/
def fixedFrobenius : MulAut Fixed where
  toFun x := ⟨slFrobenius x, by
    rw [MulAut.mem_fixedSubgroup, graphSL_frobenius,
      (MulAut.mem_fixedSubgroup _ _).mp x.property]⟩
  invFun x := ⟨slFrobenius x, by
    rw [MulAut.mem_fixedSubgroup, graphSL_frobenius,
      (MulAut.mem_fixedSubgroup _ _).mp x.property]⟩
  left_inv x := Subtype.ext (slFrobenius_involutive x)
  right_inv x := Subtype.ext (slFrobenius_involutive x)
  map_mul' x y := Subtype.ext (map_mul slFrobenius (x : SL) (y : SL))

@[simp] theorem fixedFrobenius_val (x : Fixed) :
    (fixedFrobenius x).val = slFrobenius x := rfl

theorem fixedFrobenius_sq : fixedFrobenius ^ 2 = 1 := by
  apply MulEquiv.ext
  intro x
  exact Subtype.ext (slFrobenius_involutive x)

/-- The field involution acts by squaring matrix entries. -/
def fixedFieldAction : C2 →* MulAut Fixed :=
  involutionHom fixedFrobenius fixedFrobenius_sq

/-- The orthogonal group extended by its actual field action. -/
abbrev Semilinear := Fixed ⋊[fixedFieldAction] C2

/-- The candidate for the full graph centralizer, with a separate graph factor. -/
abbrev Model := Semilinear × C2

instance : Finite Semilinear :=
  Finite.of_equiv (Fixed × C2) SemidirectProduct.equivProd.symm

/-- The actual orthogonal group has order sixty, via its SL₂(4) model. -/
theorem fixed_card : Nat.card Fixed = 60 := by
  rw [Nat.card_congr (GraphFixed.graphSLFixedEquivSL2 F).toEquiv,
    Nat.card_congr (Theory.PSL2.sl2QuotientEquiv F).toEquiv]
  have h := Atlas.ExceptionalSupport.card_psl_mul (F := F) 2
  norm_num [card_F, Fin.prod_univ_succ] at h
  change Nat.card (Theory.PSL2.Group F) * 3 = 180 at h
  omega

/-- Adjoining the actual field involution gives order one hundred and twenty. -/
theorem semilinear_card : Nat.card Semilinear = 120 := by
  rw [Nat.card_congr SemidirectProduct.equivProd, Nat.card_prod, fixed_card, card_C2]

/-- The actual projective quotient map on orthogonal matrices. -/
def projective : Fixed →* PSL :=
  (QuotientGroup.mk' (center SL)).comp (MulAut.fixedSubgroup (graphSL F)).subtype

theorem projective_fixed (x : Fixed) : graph F (projective x) = projective x := by
  change QuotientGroup.mk (graphSL F x.val) = QuotientGroup.mk x.val
  rw [(MulAut.mem_fixedSubgroup _ _).mp x.property]

/-- Orthogonal matrices act by their genuine inner automorphisms. -/
def inner : Fixed →* MulAut PSL := MulAut.conj.comp projective

theorem inner_commute_graph (x : Fixed) : Commute (inner x) (graph F) := by
  ext y
  change projective x * graph F y * (projective x)⁻¹ =
    graph F (projective x * y * (projective x)⁻¹)
  rw [map_mul, map_mul, map_inv, projective_fixed]

theorem projective_fixedFieldAction (s : C2) (x : Fixed) :
    projective (fixedFieldAction s x) = Matrix.PSL3Four.fieldAction s (projective x) := by
  change ZMod 2 at s
  fin_cases s
  · rfl
  · rfl

/-- The semidirect product acts on PSL₃(4) by inner and field automorphisms. -/
def semilinearHom : Semilinear →* MulAut PSL :=
  SemidirectProduct.lift inner Matrix.PSL3Four.fieldAction (by
    intro s
    ext x y
    change projective (fixedFieldAction s x) * y *
        (projective (fixedFieldAction s x))⁻¹ =
      Matrix.PSL3Four.fieldAction s
        (projective x * (Matrix.PSL3Four.fieldAction s)⁻¹ y * (projective x)⁻¹)
    rw [projective_fixedFieldAction, map_mul, map_mul, map_inv]
    simp)

theorem semilinearHom_apply (x : Semilinear) :
    semilinearHom x = inner x.left * Matrix.PSL3Four.fieldAction x.right := rfl

theorem fieldAction_commute_graph (s : C2) :
    Commute (Matrix.PSL3Four.fieldAction s) (graph F) :=
  graph_commute_field.symm.pow_left s.toAdd.val

theorem semilinearHom_commute_graph (x : Semilinear) :
    Commute (semilinearHom x) (graph F) :=
  (inner_commute_graph x.left).mul_left (fieldAction_commute_graph x.right)

/-- The full candidate's action includes the marked graph involution. -/
def modelHom : Model →* MulAut PSL :=
  semilinearHom.noncommCoprod (involutionHom (graph F) (graph_sq F))
    (fun x t => (semilinearHom_commute_graph x).pow_right t.toAdd.val)

theorem modelHom_apply (x : Model) :
    modelHom x = inner x.1.left * Matrix.PSL3Four.fieldAction x.1.right *
      involutionHom (graph F) (graph_sq F) x.2 := rfl

/-- The candidate embeds into the actual, full automorphism centralizer. -/
def centralizerHom : Model →* automorphismCentralizer (graph F) :=
  modelHom.codRestrict _ (fun x => mem_centralizer_singleton_iff.mpr
    (((semilinearHom_commute_graph x.1).mul_left
      ((Commute.refl (graph F)).pow_left x.2.toAdd.val)).eq))

@[simp] theorem centralizerHom_val (x : Model) :
    (centralizerHom x).val = modelHom x := rfl

private theorem inner_injective : Function.Injective inner := by
  have hconj : Function.Injective (MulAut.conj : PSL →* MulAut PSL) := by
    let := Atlas.sl_perfect (F := F) 3 (by decide)
    exact MulAut.conj_injective_of_center_eq_bot
      (Group.IsPerfect.center_quotient_center_eq_bot SL)
  apply hconj.comp
  apply (MonoidHom.ker_eq_bot_iff projective).mp
  apply eq_bot_iff.mpr
  intro x hx
  have hz : x.val ∈ center SL := (QuotientGroup.eq_one_iff _).mp hx
  obtain ⟨r, hr, he⟩ := SpecialLinearGroup.mem_center_iff.mp hz
  have htranspose : SpecialLinearGroup.transpose x.val = x.val := by
    apply Subtype.ext
    change x.val.val.transpose = x.val.val
    rw [← he]
    exact Matrix.diagonal_transpose _
  have hfix := (MulAut.mem_fixedSubgroup _ _).mp x.property
  change (SpecialLinearGroup.transpose x.val)⁻¹ = x.val at hfix
  rw [htranspose] at hfix
  have hsq : x.val ^ 2 = 1 := by
    rw [pow_two]
    calc
      _ = x.val⁻¹ * x.val := congrArg (fun y => y * x.val) hfix.symm
      _ = 1 := inv_mul_cancel _
  have hr2 : r ^ 2 = 1 := by
    have hh := congrArg (fun y : SL => y.val 0 0) hsq
    change (x.val.val ^ 2) 0 0 = 1 at hh
    rw [← he] at hh
    change ((Matrix.diagonal fun _ : Fin 3 => r) ^ 2) 0 0 = 1 at hh
    rw [Matrix.diagonal_pow] at hh
    exact hh
  have hr1 : r = 1 := CharTwo.sq_injective (by simpa using hr2)
  apply Subgroup.mem_bot.mpr
  apply Subtype.ext
  apply Subtype.ext
  rw [← he, hr1]
  simp

open PSL3.OuterSolvable.OddPrimeCoverage

private theorem frobenius_ne_one : pslFrobenius ≠ 1 := by
  intro h
  have he : fieldFrobenius = 1 := PSL3.FieldComponentFixer.fieldAction_injective
    (by simpa only [map_one] using frobenius_eq_fieldAction.symm.trans h)
  obtain ⟨c, hc⟩ := exists_fieldFrobenius_ne
  exact hc (congrArg (fun σ : F ≃+* F => σ c) he)

private theorem fieldAction_injective : Function.Injective Matrix.PSL3Four.fieldAction := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro s hs
  change ZMod 2 at s
  fin_cases s
  · exact Subgroup.one_mem _
  · exact (frobenius_ne_one hs).elim

private theorem fieldAction_binary_root (s : C2) {i j : Fin 3} (hij : i ≠ j) :
    Matrix.PSL3Four.fieldAction s (rootElement hij 1) = rootElement hij 1 := by
  change ZMod 2 at s
  fin_cases s
  · rfl
  · change pslFrobenius (rootElement hij 1) = _
    rw [frobenius_eq_fieldAction, PSL3.FieldComponentFixer.fieldAction_rootElement, map_one]

/-- Binary root elements separate the field and graph factors from a linear action. -/
theorem linear_field_graph_eq_one
    (A : GeneralLinearGroup (Fin 3) F) (s t : C2)
    (h : linearConj F A * Matrix.PSL3Four.fieldAction s *
      involutionHom (graph F) (graph_sq F) t = 1) :
    linearConj F A = 1 ∧ s = 1 ∧ t = 1 := by
  change ZMod 2 at t
  fin_cases t
  · change linearConj F A * Matrix.PSL3Four.fieldAction s * 1 = 1 at h
    have h' : linearConj F A * Matrix.PSL3Four.fieldAction s = 1 := by
      simpa only [mul_one] using h
    have hA : linearConj F A = 1 := by
      apply PSL3.FieldComponentFixer.linearConj_eq_one_of_fixes_roots
      intro i j hij
      have he := congrArg (fun a : MulAut PSL => a (rootElement hij 1)) h'
      simpa only [MulAut.mul_apply, MulAut.one_apply, fieldAction_binary_root] using he
    refine ⟨hA, fieldAction_injective ?_, rfl⟩
    simpa only [hA, one_mul, map_one] using h'
  · exfalso
    change linearConj F A * Matrix.PSL3Four.fieldAction s * graph F = 1 at h
    apply PSL3.FieldComponentFixer.not_linearConj_reverses_roots A
    intro i j hij
    have he := congrArg (fun a : MulAut PSL => a (rootElement hij 1)) h
    simpa only [MulAut.mul_apply, MulAut.one_apply,
      graph_rootElement, CharTwo.neg_eq, fieldAction_binary_root] using he

/-- The orthogonal, field and graph factors act faithfully on the actual PSL₃(4). -/
theorem modelHom_injective : Function.Injective modelHom := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro x hx
  have hlin (y : Fixed) : linearConj F (SpecialLinearGroup.toGL y.val) = inner y :=
    linearConj_toGL F y.val
  obtain ⟨hA, hs, ht⟩ := linear_field_graph_eq_one
    (SpecialLinearGroup.toGL x.1.left.val) x.1.right x.2 (by
      rwa [hlin])
  have hxleft : x.1.left = 1 := inner_injective (by simpa only [hlin, map_one] using hA)
  apply Subgroup.mem_bot.mpr
  apply Prod.ext
  · exact SemidirectProduct.ext hxleft hs
  · exact ht

/-- The candidate map into the full graph centralizer is injective. -/
theorem centralizerHom_injective : Function.Injective centralizerHom := by
  intro x y h
  exact modelHom_injective (congrArg Subtype.val h)

end Matrix.PSL3Four.InnerFamilyNormalizer.QuaternionPlacement.Graph
