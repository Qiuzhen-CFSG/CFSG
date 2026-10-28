module
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Natural.Assembly
public import Theory.Representation.SL3OddNaturalNormalizer.Index
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizing

/-!
# Completed prime-field and odd-degree natural branches

A faithful binary natural SLₙ(2) layer is already the full ambient linear
action: its determinant is the only nonzero binary scalar. Actual field
transport handles every recognized copy of F₂. For SL₃ over an odd-degree
binary field, the proved semilinear normalizer index is odd, so every
elementary two-subgroup lies inside the component. The earlier hyperplane
calculations then give the exact ratios and B.4.2 clauses.

Consequently an elementary actor outside the component forces n=3 and
r=2s with s>0. The remaining even-degree centralizer and common-fixed-space
bounds are independent obligations; they are not part of these completed cases.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), K.3.2.1,
printed pp.454–455. The binary determinant and prime-field transport proofs
follow the checked B.5 source adapters, retained here without their downstream
classification imports. The normalizer index is supplied by
Theory.Representation.SL3OddNaturalNormalizer.Index.
-/

@[expose] public section

open Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.ChapterK.Linear.Natural

variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (L : Subgroup G)

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
lemma elementary_le_of_odd_degree [L.Normal] (hf : Function.Injective ρ)
    (F : BinaryField) (ho : Odd F.degree)
    (e : ActionEquiv (ρ.comp L.subtype) (linearNatural F 3))
    {A : Subgroup G} (hA : IsElementaryTwo A) : A ≤ L := by
  let τ : Representation (ZMod 2) G (Fin 3 → F.Carrier) :=
    e.linearEquiv.conjRingEquiv.toMonoidHom.comp ρ
  have hfaith : Function.Injective τ := e.linearEquiv.conjRingEquiv.injective.comp hf
  have hnat (g : L) (v : Fin 3 → F.Carrier) : τ g v = (e.groupEquiv g).val.mulVec v := by
    have h := e.intertwines g (e.linearEquiv.symm v)
    rw [e.linearEquiv.apply_symm_apply] at h
    exact h
  let : IsElementaryAbelian 2 A := hA.2
  exact SL3OddNaturalNormalizer.two_subgroup_le_of_natural F.degree_pos ho F.card_eq L
    e.groupEquiv τ hfaith hnat A (IsElementaryAbelian.isPGroup 2 A)

/-- Every odd field degree in the linear-three branch is complete. -/
theorem linearThree_of_odd_degree [L.Normal] (hf : Function.Injective ρ)
    (F : BinaryField) (ho : Odd F.degree)
    (e : ActionEquiv (ρ.comp L.subtype) (linearNatural F 3)) :
    quadraticRatio ρ = 1 / 2 ∧ (∀ A, IsBestOffender ρ A → A ≤ L) ∧
      offenderSubgroup ρ = L ∧
      ChapterB.SourceInduction.ProjectiveLine.IrreducibleActionCase ρ L (offenderSubgroup ρ) := by
  have houter : ∀ A : Subgroup G, IsElementaryTwo A → ¬ A ≤ L → rank A < fixedCodim ρ A := by
    intro A hA hAL
    exact (hAL (elementary_le_of_odd_degree ρ L hf F ho e hA)).elim
  obtain ⟨hq, hb, hg⟩ := conclusions_of_outer_actor_bound ρ L F 3 e (by decide) houter
  exact ⟨by simpa using hq, hb, hg, linearThree_of_outer_actor_bound ρ L F e houter⟩

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
/-- Over F₂ the full faithful ambient action equals the specified SL layer.
This is the determinant argument in B.5 ProductGeometry.Localization,
reproduced here to avoid importing the downstream B.5 classification. -/
lemma binary_component_eq_top (hf : Function.Injective ρ) (n : ℕ)
    (e : ActionEquiv (ρ.comp L.subtype) (linearNatural BinaryField.two n)) : L = ⊤ := by
  apply top_unique
  intro g _
  let τ : Representation (ZMod 2) G (Fin n → ZMod 2) :=
    e.linearEquiv.conjRingEquiv.toMonoidHom.comp ρ
  let M := Matrix.GeneralLinearGroup.toLin.symm (τ.asGroupHom g)
  have hdet : M.val.det = 1 := by
    have hn := M.det_ne_zero
    have he (x : ZMod 2) : x = 0 ∨ x = 1 := by
      fin_cases x
      · exact Or.inl rfl
      · exact Or.inr rfl
    exact (he M.val.det).resolve_left hn
  let m : Matrix.SpecialLinearGroup (Fin n) (ZMod 2) := ⟨M.val, hdet⟩
  let l : L := e.groupEquiv.symm m
  have he : ρ g = ρ l := by
    apply e.linearEquiv.conjRingEquiv.injective
    change τ g = τ l
    apply LinearMap.ext
    intro v
    have hn := e.intertwines l (e.linearEquiv.symm v)
    have hv : τ l v = Matrix.mulVec m.val v := by
      exact hn.trans (congrArg₂ (fun a w => linearNatural BinaryField.two n a w)
        (e.groupEquiv.apply_symm_apply m) (e.linearEquiv.apply_symm_apply v))
    rw [hv]
    have hm := congrArg (fun t : LinearMap.GeneralLinearGroup (ZMod 2) (Fin n → ZMod 2) =>
      t.val v) (Matrix.GeneralLinearGroup.toLin.apply_symm_apply (τ.asGroupHom g))
    exact hm.symm
  exact hf he ▸ l.property


set_option backward.isDefEq.respectTransparency false in
/-- Prime-field transport keeps both the matrix actor and the original binary
intertwiner. This avoids a dependency on the later B.5 extension arguments. -/
noncomputable def primeFieldActionEquiv (F : BinaryField) (hF : F.degree = 1) (n : ℕ)
    (e : ActionEquiv (ρ.comp L.subtype) (linearNatural F n)) :
    ActionEquiv (ρ.comp L.subtype) (linearNatural BinaryField.two n) := by
  let : Fintype F.Carrier := Fintype.ofFinite F.Carrier
  have hc : Fintype.card F.Carrier = 2 := by
    rw [← Nat.card_eq_fintype_card, F.card_eq, hF, pow_one]
  let f : F.Carrier ≃+* ZMod 2 := (ZMod.ringEquivOfPrime F.Carrier Nat.prime_two hc).symm
  let l : F.Carrier ≃ₗ[ZMod 2] ZMod 2 :=
    { f.toAddEquiv with map_smul' := ZMod.map_smul f }
  let E := LinearEquiv.piCongrRight (fun _ : Fin n => l)
  refine ⟨e.groupEquiv.trans (Atlas.fieldEquivSL n f), e.linearEquiv.trans E, ?_⟩
  intro g v
  change E (e.linearEquiv (ρ g v)) = _
  rw [show e.linearEquiv (ρ g v) = linearNatural F n (e.groupEquiv g) (e.linearEquiv v) from
    e.intertwines g v]
  funext i
  change f (∑ j, (e.groupEquiv g).val i j * e.linearEquiv v j) =
    ∑ j, f ((e.groupEquiv g).val i j) * f (e.linearEquiv v j)
  simp only [map_sum, map_mul]

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
lemma component_eq_top_of_degree_one (hf : Function.Injective ρ)
    (F : BinaryField) (hF : F.degree = 1) (n : ℕ)
    (e : ActionEquiv (ρ.comp L.subtype) (linearNatural F n)) : L = ⊤ :=
  binary_component_eq_top ρ L hf n (primeFieldActionEquiv ρ L F hF n e)

/-- The degree-four and degree-five prime-field source cases are complete. -/
theorem binaryLinear (hf : Function.Injective ρ) (n : ℕ) (hn : n = 4 ∨ n = 5)
    (e : ActionEquiv (ρ.comp L.subtype) (linearNatural BinaryField.two n)) :
    L = ⊤ ∧ quadraticRatio ρ = 1 / (n - 1 : ℕ) ∧
      offenderSubgroup ρ = L ∧
      ChapterB.SourceInduction.ProjectiveLine.IrreducibleActionCase ρ L (offenderSubgroup ρ) := by
  have ht := binary_component_eq_top ρ L hf n e
  have houter : ∀ A : Subgroup G, IsElementaryTwo A → ¬ A ≤ L → rank A < fixedCodim ρ A := by
    intro A _ hAL
    exact (hAL (ht ▸ le_top)).elim
  obtain ⟨hq, _, hg⟩ := conclusions_of_outer_actor_bound ρ L BinaryField.two n e
    (by rcases hn with rfl | rfl <;> omega) houter
  exact ⟨ht, hq, hg, binaryLinear_of_outer_actor_bound ρ L n hn e houter⟩

/-- Application with every standing source hypothesis and the actual generalized
Fitting subgroup retained. No outer exclusion is assumed in odd degree. -/
theorem source_linearThree_of_odd_degree (F : BinaryField) (ho : Odd F.degree)
    {K : GroupClass} (h : SourceInput ρ L F 3 K) :
    quadraticRatio ρ = 1 / 2 ∧ (∀ A, IsBestOffender ρ A → A ≤ L) ∧
      offenderSubgroup ρ = L ∧
      ChapterB.SourceInduction.ProjectiveLine.IrreducibleActionCase ρ L (offenderSubgroup ρ) := by
  let : L.Normal := h.fitting ▸ inferInstance
  exact linearThree_of_odd_degree ρ L h.faithful F ho h.natural

/-- The source degree-four/five branches, including any recognized copy of F₂. -/
theorem source_binaryLinear (F : BinaryField) (n : ℕ) (hn : n = 4 ∨ n = 5)
    {K : GroupClass} (h : SourceInput ρ L F n K) :
    L = ⊤ ∧ quadraticRatio ρ = 1 / (n - 1 : ℕ) ∧
      offenderSubgroup ρ = L ∧
      ChapterB.SourceInduction.ProjectiveLine.IrreducibleActionCase ρ L (offenderSubgroup ρ) := by
  have hF : F.degree = 1 := by
    rcases h.dimensions with he | he
    · rcases hn with hn | hn <;> omega
    · exact he.2
  exact binaryLinear ρ L h.faithful n hn (primeFieldActionEquiv ρ L F hF n h.natural)

omit [FiniteDimensional (ZMod 2) V] in
/-- An elementary actor outside the component forces precisely the remaining
source range n=3, r=2s, s>0. -/
theorem outside_elementary_parameters (F : BinaryField) (n : ℕ)
    {K : GroupClass} (h : SourceInput ρ L F n K)
    {A : Subgroup G} (hA : IsElementaryTwo A) (hAL : ¬ A ≤ L) :
    n = 3 ∧ ∃ s : ℕ, 0 < s ∧ F.degree = 2 * s := by
  have hn : n = 3 := by
    rcases h.dimensions with hn | ⟨hn, hF⟩
    · exact hn
    · have ht := component_eq_top_of_degree_one ρ L h.faithful F hF n h.natural
      exact (hAL (ht ▸ le_top)).elim
  refine ⟨hn, ?_⟩
  subst n
  let : L.Normal := h.fitting ▸ inferInstance
  have hnot : ¬ Odd F.degree := by
    intro ho
    exact hAL (elementary_le_of_odd_degree ρ L h.faithful F ho h.natural hA)
  obtain ⟨s, hs⟩ := (Nat.even_or_odd F.degree).resolve_right hnot
  refine ⟨s, ?_, ?_⟩
  · have hp := F.degree_pos
    omega
  · omega

end CFSG.Quasithin.ChapterK.Linear.Natural
