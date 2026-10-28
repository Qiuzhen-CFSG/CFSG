module

public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Recognition.CComponents
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Nonbinary
public import Theory.SpecificGroups.SymplecticFour.RootNormalizerResidual.Standard
public import Theory.SpecificGroups.SymplecticFour.RootNormalizerResidual.Weyl
public import Theory.SpecificGroups.SymplecticFour.RootSubgroup.ElementCentralizer
public import Theory.SpecificGroups.SymplecticFour.InvolutionTypes

/-!
# C-components in symplectic root centralizers

Centralizing one nonidentity root element is equivalent to centralizing its
whole root group. Explicit Weyl conjugation identifies these centralizers
with the point or plane determinant kernels. Their existing matrix quotient
and central-quotient coordinates give natural extensions over the original
field. Every relative C-component is the full root centralizer by the
perfect-subnormal supplement argument.

Source: Aschbacher--Smith, E.6.25, printed p.256, and the root cases of
16.1.4, printed p.1171 (combined manuscript of 1 March 2004).
-/

public section

open Subgroup
open Representation.OneCohomology.SymplecticFour
namespace Theory.SpecificGroups.SymplecticFour.InvolutionCentralizers
open RootNormalizerResidual InvolutionTypes
variable {F : Type*} [Field F] [CharP F 2]

private theorem centralizer_map {A D : Type*} [Group A] [Group D]
    (e : A ≃* D) (s : Set A) :
    (centralizer s).map e.toMonoidHom = centralizer (e '' s) := by
  apply le_antisymm (map_centralizer_le_centralizer_image _ _)
  intro x hx
  refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
  intro y hy
  apply e.injective
  simpa only [map_mul, e.apply_symm_apply] using hx (e y) ⟨y, hy, rfl⟩

private noncomputable def centralizer_map_equiv {A D : Type*} [Group A] [Group D]
    (e : A ≃* D) (s : Set A) : centralizer s ≃* centralizer (e '' s) :=
  (e.subgroupMap (centralizer s)).trans (MulEquiv.subgroupCongr (centralizer_map e s))

omit [CharP F 2] in
/-- A nonidentity root element and its root group have the same centralizer. -/
theorem root_element_centralizer_eq (r : Fin 8) {t : F} (ht : t ≠ 0) :
    centralizer ({rootElement r t} : Set (Sp F)) =
      centralizer (RootSubgroup.group (F := F) r : Set (Sp F)) := by
  ext g
  constructor
  · intro hg x hx
    obtain ⟨s, rfl⟩ := (RootSubgroup.mem_group_iff r x).mp hx
    exact (RootSubgroup.commute_element_of_ne_zero r ht g
      (mem_centralizer_singleton_iff.mp hg) s).symm.eq
  · intro hg
    exact mem_centralizer_singleton_iff.mpr
      (hg _ ((RootSubgroup.mem_group_iff r _).mpr ⟨t, rfl⟩)).symm

/-- Weyl conjugation identifies both root lengths with their actual local groups. -/
theorem root_group_centralizer_equiv_local (r : Fin 8) :
    Nonempty (centralizer (RootSubgroup.group (F := F) r : Set (Sp F)) ≃*
      pointLocal (F := F)) ∨
    Nonempty (centralizer (RootSubgroup.group (F := F) r : Set (Sp F)) ≃*
      planeLocal (F := F)) := by
  obtain ⟨w, hw⟩ := exists_root_conjugation (F := F) r
  let e := MulAut.conj w
  have hi : e '' (RootSubgroup.group (F := F) (if r.val < 4 then 0 else 4) : Set (Sp F)) =
      (RootSubgroup.group (F := F) r : Set (Sp F)) := by
    exact congrArg (fun H : Subgroup (Sp F) => (H : Set (Sp F))) hw
  let c := (centralizer_map_equiv e
    (RootSubgroup.group (F := F) (if r.val < 4 then 0 else 4) : Set (Sp F))).trans
    (MulEquiv.subgroupCongr (congrArg centralizer hi))
  by_cases hr : r.val < 4
  · left
    have he : centralizer
        (RootSubgroup.group (F := F) (if r.val < 4 then 0 else 4) : Set (Sp F)) =
        pointLocal := by simp only [if_pos hr, centralizer_zero_eq]
    exact ⟨c.symm.trans (MulEquiv.subgroupCongr he)⟩
  · right
    have he : centralizer
        (RootSubgroup.group (F := F) (if r.val < 4 then 0 else 4) : Set (Sp F)) =
        planeLocal := by simp only [if_neg hr, centralizer_four_eq]
    exact ⟨c.symm.trans (MulEquiv.subgroupCongr he)⟩

/-- The identification also holds for every conjugate root element. -/
theorem root_centralizer_equiv_local (g : Sp F) (hg : IsRootElement g) :
    Nonempty (centralizer ({g} : Set (Sp F)) ≃* pointLocal (F := F)) ∨
    Nonempty (centralizer ({g} : Set (Sp F)) ≃* planeLocal (F := F)) := by
  obtain ⟨h, r, t, ht, rfl⟩ := hg
  let e := MulAut.conj h
  have hi : e '' ({rootElement r t} : Set (Sp F)) =
      {h * rootElement r t * h⁻¹} := by simp [e, MulAut.conj_apply]
  let c := (centralizer_map_equiv e ({rootElement r t} : Set (Sp F))).trans
    (MulEquiv.subgroupCongr (congrArg centralizer hi))
  let d := c.symm.trans (MulEquiv.subgroupCongr (root_element_centralizer_eq r ht))
  rcases root_group_centralizer_equiv_local (F := F) r with ⟨⟨f⟩⟩ | ⟨⟨f⟩⟩
  · exact Or.inl ⟨d.trans f⟩
  · exact Or.inr ⟨d.trans f⟩

variable [Finite F]

/-- The projection and natural conjugation module use the same defining field. -/
theorem root_centralizer_naturalExtension {n : ℕ}
    (hcard : Nat.card F = 2 ^ n) (hn : 1 < n)
    (g : Sp F) (hg : IsRootElement g) :
    ∃ (Q : Subgroup (centralizer ({g} : Set (Sp F)))) (_ : Q.Normal),
      Nonempty (NaturalExtension (F := F) Q) := by
  rcases root_centralizer_equiv_local g hg with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · exact ⟨(pointRadical (F := F)).comap e.toMonoidHom, inferInstance,
      ⟨(pointNaturalExtension hcard hn).comap e⟩⟩
  · exact ⟨(Plane.radical (F := F)).comap e.toMonoidHom, inferInstance,
      ⟨(planeNaturalExtension hcard hn).comap e⟩⟩

/-- A C-component relative to a nonbinary root centralizer equals that centralizer. -/
theorem root_cComponent_eq_centralizer {n : ℕ}
    (hcard : Nat.card F = 2 ^ n) (hn : 1 < n)
    (g : Sp F) (hg : IsRootElement g)
    {B : Subgroup (Sp F)} (hBC : B ≤ centralizer ({g} : Set (Sp F)))
    (hB : (B.subgroupOf (centralizer ({g} : Set (Sp F)))).IsCComponent) :
    B = centralizer ({g} : Set (Sp F)) := by
  obtain ⟨Q, hQ, ⟨d⟩⟩ := root_centralizer_naturalExtension hcard hn g hg
  let := hQ
  have hF : 2 < Nat.card F := by
    rw [hcard]
    exact lt_of_eq_of_lt (by decide : 2 = 2 ^ 1)
      (Nat.pow_lt_pow_right (by decide) hn)
  exact le_antisymm hBC (subgroupOf_eq_top.mp (d.cComponent_eq_top hF hB))

end Theory.SpecificGroups.SymplecticFour.InvolutionCentralizers
