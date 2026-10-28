module

public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.SourceStatements
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.GlobalClosure.ContraryFusion.DiagonalConstruction.Algebra
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.GlobalClosure.ContraryFusion.DiagonalConstruction.Inputs
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.GlobalClosure.ContraryFusion.DiagonalConstruction.Recognition.CyclicCentralizerInput
public import Theory.GroupTheory.PGroup.NormalizingInvolutionRecognition
public import Theory.GroupTheory.PGroup.CentralFourRank

/-!
# Two-group recognition in the central diagonal argument

The small-fixed-subgroup contract is proved by adjoining its normalizing
involution and constructing an actual dihedral equivalence. No two-group
assumption on the ambient group is used.

The diagonal rank contract follows from recognition from a cyclic centralizer
of an order-four element with central square. The square's centrality is proved
from the commuting factors and the diagonal's order. The literal restricted
factors are compared by explicit equivalences. A noncyclic centralizer contains
an elementary four because its central order-four element excludes the
quaternion alternative. The source's Sylow containment and elementary four
supply the cyclic-centralizer recognition theorem's remaining hypotheses.

Source: Aschbacher, *On finite groups of component type* (1975), Lemma 3.4,
printed p.95, the deductions from cyclic C_A(u) and from |C_B(y)| = 2.
-/

public section
open Subgroup Theory.GroupTheory BenderSuzuki.PFchapter1section1
namespace CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75

/-- The small fixed subgroup in the proper-centralizer branch is dihedral. -/
theorem smallFixedModel {G : Type*} [Group G] [Finite G] : SmallFixedModel G := by
  intro B hB hr y hy hyn hfix
  obtain ⟨E, hE, hs⟩ := hr
  let : IsElementaryAbelian 2 E := {
    toIsMulCommutative := isMulCommutative_of_forall_sq_one hs
    exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one hs }
  exact Or.inl (B.exists_dihedral_equiv_of_normalizing_involution_small_fixed
    hB E hE y hy hyn hfix)

namespace DiagonalConstruction
variable {G : Type*} [Group G] {S : Sylow 2 G} {A₁ A₂ : Subgroup G}

/-- The involutory diagonal forces the square of its preimage into the factor center. -/
theorem diagonal_square_central (h : Hypotheses S A₁ A₂) {t u : G}
    (hs : conjugate A₁ t = A₂) (hu : u ∈ A₁)
    (hy : orderOf (u * (t⁻¹ * u * t)) = 2) :
    (⟨u, hu⟩ : A₁) ^ 2 ∈ center A₁ := by
  have hv := conjugate_mem hs hu
  have hc := factors_commute h hu hv
  have hsq : u ^ 2 * (t⁻¹ * u * t) ^ 2 = 1 := by
    rw [← hc.mul_pow]
    exact hy ▸ pow_orderOf_eq_one _
  have huA₂ : u ^ 2 ∈ A₂ := by
    rw [eq_inv_of_mul_eq_one_left hsq]
    exact A₂.inv_mem (A₂.pow_mem hv 2)
  apply mem_center_iff.mpr
  intro x
  exact Subtype.ext (factors_commute h x.property huA₂).eq

/-- The intrinsic centralizer agrees with the literal factor restricted to C_G(y). -/
noncomputable def diagonalCentralizerEquiv (h : Hypotheses S A₁ A₂) {t u : G}
    (hs : conjugate A₁ t = A₂) (hu : u ∈ A₁) :
    centralizer ({(⟨u, hu⟩ : A₁)} : Set A₁) ≃*
      A₁.subgroupOf (centralizer ({u * (t⁻¹ * u * t)} : Set G)) where
  toFun x := ⟨⟨x.val.val, mem_centralizer_singleton_iff.mpr
    ((show Commute x.val.val u from congrArg Subtype.val
      (mem_centralizer_singleton_iff.mp x.property)).mul_right
        (factors_commute h x.val.property (conjugate_mem hs hu))).eq⟩, x.val.property⟩
  invFun x := ⟨⟨x.val.val, x.property⟩, mem_centralizer_singleton_iff.mpr (Subtype.ext (by
    have hh : Commute x.val.val (u * (t⁻¹ * u * t)) :=
      mem_centralizer_singleton_iff.mp x.val.property
    have hxv := factors_commute h x.property (conjugate_mem hs hu)
    change x.val.val * u = u * x.val.val
    simpa only [mul_inv_cancel_right] using (hh.mul_right hxv.inv_right).eq))⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- Conjugation by the exchanging involution identifies the two restricted factors. -/
noncomputable def diagonalFactorsEquiv (h : Hypotheses S A₁ A₂) {t u : G}
    (hs : conjugate A₁ t = A₂) (hs' : conjugate A₂ t = A₁)
    (ht : orderOf t = 2) (hu : u ∈ A₁) :
    A₁.subgroupOf (centralizer ({u * (t⁻¹ * u * t)} : Set G)) ≃*
      A₂.subgroupOf (centralizer ({u * (t⁻¹ * u * t)} : Set G)) := by
  let y := u * (t⁻¹ * u * t)
  let K := centralizer ({y} : Set G)
  let f := MulAut.conj t⁻¹
  have hfy : f y = y := by
    have hh := diagonal_range_centralizes h hs ht
      (show diagonalHom h hs ⟨u, hu⟩ ∈ (diagonalHom h hs).range from ⟨⟨u, hu⟩, rfl⟩)
    have hty : Commute t y := (mem_centralizer_singleton_iff.mp hh).symm
    change t⁻¹ * y * (t⁻¹)⁻¹ = y
    rw [inv_inv, hty.inv_left.eq]
    simp
  have hff (x : G) : f (f x) = x := by
    have ht2 : t * t = 1 := by simpa only [ht, pow_two] using pow_orderOf_eq_one t
    have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_left ht2
    change t⁻¹ * (t⁻¹ * x * (t⁻¹)⁻¹) * (t⁻¹)⁻¹ = x
    simp only [hti]
    calc
      t * (t * x * t) * t = (t * t) * x * (t * t) := by group
      _ = x := by rw [ht2]; simp
  have hK (x : G) (hx : x ∈ K) : f x ∈ K := by
    apply mem_centralizer_singleton_iff.mpr
    have he := congrArg f (mem_centralizer_singleton_iff.mp hx)
    simpa only [map_mul, hfy] using he
  refine {
    toFun := fun x => ⟨⟨f x.val.val, hK _ x.val.property⟩, ?_⟩
    invFun := fun x => ⟨⟨f x.val.val, hK _ x.val.property⟩, ?_⟩
    left_inv := fun x => Subtype.ext (Subtype.ext (hff _))
    right_inv := fun x => Subtype.ext (Subtype.ext (hff _))
    map_mul' := fun x z => Subtype.ext (Subtype.ext (map_mul f _ _)) }
  · change f x.val.val ∈ A₂
    have hx : x.val.val ∈ A₁ := x.property
    have hh : t⁻¹ * x.val.val * t ∈ A₂ := conjugate_mem hs hx
    simpa only [f, MulAut.conj_apply, inv_inv] using hh
  · change f x.val.val ∈ A₁
    have hx : x.val.val ∈ A₂ := x.property
    have hh : t⁻¹ * x.val.val * t ∈ A₁ := conjugate_mem hs' hx
    simpa only [f, MulAut.conj_apply, inv_inv] using hh

end DiagonalConstruction

/-- The diagonal rank conclusion reduced to recognition of a cyclic centralizer
of an order-four element with central square. -/
theorem diagonalCentralizerRanks_of_cyclicCentralizerRecognition
    {G : Type*} [Group G] [Finite G]
    {S : Sylow 2 G} {A₁ A₂ : Subgroup G}
    (recognize : ∀ u : A₁, orderOf u = 4 → u ^ 2 ∈ center A₁ →
      IsCyclic (centralizer ({u} : Set A₁)) → DihedralOrSemidihedral A₁) :
    DiagonalCentralizerRanks S A₁ A₂ := by
  intro h t u hs hs' ht _hcap hnot hu hu4 hy
  have huA : orderOf (⟨u, hu⟩ : A₁) = 4 := by simpa using hu4
  have hnc : ¬ IsCyclic (centralizer ({(⟨u, hu⟩ : A₁)} : Set A₁)) :=
    fun hc => hnot (recognize ⟨u, hu⟩ huA
      (DiagonalConstruction.diagonal_square_central h hs hu hy) hc)
  let C := centralizer ({(⟨u, hu⟩ : A₁)} : Set A₁)
  let uC : C := ⟨⟨u, hu⟩, mem_centralizer_singleton_iff.mpr rfl⟩
  have huc : uC ∈ center C := by
    apply mem_center_iff.mpr
    intro x
    exact Subtype.ext (mem_centralizer_singleton_iff.mp x.property)
  have hP := (S.isPGroup'.to_le h.left_le).to_subgroup C
  obtain ⟨E, hEe, hEc⟩ := hP.exists_elementary_four_of_noncyclic_of_central_order_four
    hnc uC (by simpa [uC] using huA) huc
  let : IsElementaryAbelian 2 E := hEe
  have hrC : TwoRankAtLeastTwo C := ⟨E, hEc,
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 E)⟩
  have hr₁ := DiagonalConstruction.rank_of_equiv
    (DiagonalConstruction.diagonalCentralizerEquiv h hs hu) hrC
  exact ⟨hr₁, DiagonalConstruction.rank_of_equiv
    (DiagonalConstruction.diagonalFactorsEquiv h hs hs' ht hu) hr₁⟩

/-- Both literal factors restricted to the diagonal centralizer contain an
elementary four. The source hypotheses discharge cyclic-centralizer recognition. -/
theorem diagonalCentralizerRanks
    {G : Type*} [Group G] [Finite G]
    {S : Sylow 2 G} {A₁ A₂ : Subgroup G} :
    DiagonalCentralizerRanks S A₁ A₂ := by
  intro h
  exact diagonalCentralizerRanks_of_cyclicCentralizerRecognition
    (cyclicCentralizerRecognition h) h


end CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75
end
