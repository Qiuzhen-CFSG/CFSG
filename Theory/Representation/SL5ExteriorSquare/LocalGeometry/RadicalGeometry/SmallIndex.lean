module

public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.RadicalGeometry.FixedSpaces
public import Theory.ElementaryAbelian.BinaryQuotientRank
public import Theory.Representation.BinaryOffender.Basic

/-!
# Small-index fixed spaces in the binary shear subgroup

The actual subgroups of the last-column shear group U correspond to subspaces
of its four-dimensional parameter space. Cardinalities and relative indices
therefore record dimensions and codimensions; the latter agree with the rank
of the literal quotient A / (B.subgroupOf A), with normality inside A.

A subgroup of order eight contains a parameter line of order two and index
four. Its fixed space is strictly larger than the common fixed space V₆ of
that order-eight subgroup. Ranks one and two are excluded from A₃ by the
trivial subgroup. Conversely every subgroup of U of index less than eight
has parameter dimension at least two and fixes V₆. Thus U is the unique
nontrivial subgroup of U satisfying the fixed-space condition at k = 3.

Source: Aschbacher--Smith, Definition E.3.8 (printed p.232), and the subgroup
rank step in the proof of 12.5.7 (printed p.820, PDF p.837), combined manuscript
of 1 March 2004. The identification of U with the parabolic radical R₆ belongs
to the separate parabolic calculation.
-/

@[expose] public section
namespace Representation.SL5ExteriorSquare
open SL5TenDimensional
open scoped IsMulCommutative

/-- The parameter subspace of an actual ambient subgroup. -/
def shearParameters (A : Subgroup Group) : Submodule (ZMod 2) ShearParameter where
  carrier := {u | shear u ∈ A}
  zero_mem' := by
    change shear 0 ∈ A
    rw [shear_zero]
    exact A.one_mem
  add_mem' := by
    intro u w hu hw
    change shear (u + w) ∈ A
    rw [shear_add]
    exact A.mul_mem (x := shear u) (y := shear w) hu hw
  smul_mem' c u hu := by
    change shear (c • u) ∈ A
    rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
    · rw [zero_smul, shear_zero]
      exact A.one_mem
    · rw [one_smul]
      exact hu

@[simp] theorem mem_shearParameters (A : Subgroup Group) (u : ShearParameter) :
    u ∈ shearParameters A ↔ shear u ∈ A := Iff.rfl

theorem shearParameters_mono {A B : Subgroup Group} (h : A ≤ B) :
    shearParameters A ≤ shearParameters B := fun _ hu => h hu

@[simp] theorem shearParameters_parameterShears (P : Submodule (ZMod 2) ShearParameter) :
    shearParameters (parameterShears P) = P := by
  ext u
  simp only [mem_shearParameters, mem_parameterShears, shear_injective.eq_iff]
  exact ⟨fun ⟨w, hw, he⟩ => he ▸ hw, fun hu => ⟨u, hu, rfl⟩⟩

theorem parameterShears_shearParameters {A : Subgroup Group} (hA : A ≤ shearSubgroup) :
    parameterShears (shearParameters A) = A := by
  ext g
  rw [mem_parameterShears]
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact hu
  · intro hg
    obtain ⟨u, rfl⟩ := (mem_shearSubgroup g).mp (hA hg)
    exact ⟨u, hg, rfl⟩

theorem parameterShears_mono {P Q : Submodule (ZMod 2) ShearParameter} (h : P ≤ Q) :
    parameterShears P ≤ parameterShears Q := by
  intro g hg
  obtain ⟨u, hu, rfl⟩ := (mem_parameterShears P g).mp hg
  exact (mem_parameterShears Q _).mpr ⟨u, h hu, rfl⟩

/-- Parameter subspaces correspond to all actual subgroups of U. -/
noncomputable def shearSubgroupOrderIso :
    Submodule (ZMod 2) ShearParameter ≃o {A : Subgroup Group // A ≤ shearSubgroup} where
  toFun P := ⟨parameterShears P, parameterShears_le P⟩
  invFun A := shearParameters A.val
  left_inv := shearParameters_parameterShears
  right_inv A := Subtype.ext (parameterShears_shearParameters A.property)
  map_rel_iff' := by
    intro P Q
    constructor
    · intro h
      change parameterShears P ≤ parameterShears Q at h
      simpa only [shearParameters_parameterShears] using shearParameters_mono h
    · exact parameterShears_mono

/-- The parameter map corestricted to an arbitrary subgroup. -/
def shearParametersToSubgroup (A : Subgroup Group) : Multiplicative (shearParameters A) →* A where
  toFun u := ⟨shear u.toAdd.val, u.toAdd.property⟩
  map_one' := Subtype.ext shear_zero
  map_mul' u w := Subtype.ext (shear_add u.toAdd.val w.toAdd.val)

/-- The correspondence is given by the literal shear matrices. -/
noncomputable def shearParametersEquiv (A : Subgroup Group) (hA : A ≤ shearSubgroup) :
    Multiplicative (shearParameters A) ≃* A :=
  MulEquiv.ofBijective (shearParametersToSubgroup A) ⟨by
    intro u w h
    change u.toAdd = w.toAdd
    apply Subtype.ext
    have he := congrArg (fun a : A => (a : Group)) h
    change shear u.toAdd.val = shear w.toAdd.val at he
    exact shear_injective he, by
    intro g
    obtain ⟨u, hu⟩ := (mem_shearSubgroup g.val).mp (hA g.property)
    have hm : u ∈ shearParameters A := by
      change shear u ∈ A
      rw [hu]
      exact g.property
    refine ⟨Multiplicative.ofAdd ⟨u, hm⟩, ?_⟩
    apply Subtype.ext
    change shear u = g.val
    exact hu⟩

@[simp] theorem shearParametersEquiv_apply (A : Subgroup Group) (hA : A ≤ shearSubgroup)
    (u : Multiplicative (shearParameters A)) :
    (shearParametersEquiv A hA u : Group) = shear u.toAdd.val := rfl

theorem card_eq_two_pow_finrank_shearParameters {A : Subgroup Group}
    (hA : A ≤ shearSubgroup) : Nat.card A = 2 ^ Module.finrank (ZMod 2) (shearParameters A) := by
  rw [← Nat.card_congr (shearParametersEquiv A hA).toEquiv]
  change Nat.card (shearParameters A) = _
  simpa only [Nat.card_zmod] using
    (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := shearParameters A))

theorem card_parameterShears (P : Submodule (ZMod 2) ShearParameter) :
    Nat.card (parameterShears P) = 2 ^ Module.finrank (ZMod 2) P := by
  rw [card_eq_two_pow_finrank_shearParameters (parameterShears_le P),
    shearParameters_parameterShears]

theorem finrank_shearParameters_le_four (A : Subgroup Group) :
    Module.finrank (ZMod 2) (shearParameters A) ≤ 4 := by
  simpa using (shearParameters A).finrank_le

theorem relIndex_eq_two_pow_shearParameters {A B : Subgroup Group}
    (hA : A ≤ shearSubgroup) (hBA : B ≤ A) :
    B.relIndex A = 2 ^ (Module.finrank (ZMod 2) (shearParameters A) -
      Module.finrank (ZMod 2) (shearParameters B)) := by
  have hcard := Subgroup.relIndex_mul_relIndex
    (⊥ : Subgroup Group) B A bot_le hBA
  rw [Subgroup.relIndex_bot_left, Subgroup.relIndex_bot_left,
    card_eq_two_pow_finrank_shearParameters hA,
    card_eq_two_pow_finrank_shearParameters (hBA.trans hA)] at hcard
  have hd := Submodule.finrank_mono (shearParameters_mono hBA)
  apply Nat.eq_of_mul_eq_mul_left (by positivity :
    0 < 2 ^ Module.finrank (ZMod 2) (shearParameters B))
  exact hcard.trans (pow_mul_pow_sub 2 hd).symm

theorem log_relIndex_eq_shearParameters_codim {A B : Subgroup Group}
    (hA : A ≤ shearSubgroup) (hBA : B ≤ A) :
    Nat.log 2 (B.relIndex A) = Module.finrank (ZMod 2) (shearParameters A) -
      Module.finrank (ZMod 2) (shearParameters B) := by
  rw [relIndex_eq_two_pow_shearParameters hA hBA, Nat.log_pow (by decide)]

theorem fixedSpace_eq_parameterShears {A : Subgroup Group} (hA : A ≤ shearSubgroup) :
    BinaryOffender.fixedSpace (exteriorAction 2) A =
      BinaryOffender.fixedSpace (exteriorAction 2) (parameterShears (shearParameters A)) := by
  rw [parameterShears_shearParameters hA]

theorem fixedSpace_eq_V₆_of_shearParameters_rank {A : Subgroup Group}
    (hA : A ≤ shearSubgroup) (hd : 2 ≤ Module.finrank (ZMod 2) (shearParameters A)) :
    BinaryOffender.fixedSpace (exteriorAction 2) A = V₆ := by
  rw [fixedSpace_eq_parameterShears hA]
  exact fixedSpace_parameterShears _ hd

/-- The fixed space of a parameter line is the fixed space of its generator. -/
theorem fixedSpace_parameterLine (u : ShearParameter) :
    BinaryOffender.fixedSpace (exteriorAction 2)
      (parameterShears (Submodule.span (ZMod 2) {u})) = fixedSpace (shear u) := by
  ext v
  rw [mem_fixedSpace_parameterShears]
  change (∀ w ∈ Submodule.span (ZMod 2) {u}, shearWedge (shearQuotient v) w = 0) ↔
    displacement (shear u) v = 0
  rw [shear_displacement]
  constructor
  · intro h
    exact h u (Submodule.subset_span (Set.mem_singleton u))
  · intro h w hw
    rcases (mem_parameterLine u w).mp hw with rfl | rfl
    · exact (shearWedge_eq_zero_iff _ _).mpr (Or.inr (Or.inl rfl))
    · exact h

/-- All subgroups under consideration are elementary abelian, including the trivial one. -/
theorem elementary_of_le_shearSubgroup {A : Subgroup Group} (hA : A ≤ shearSubgroup) :
    IsElementaryAbelian 2 A where
  toIsMulCommutative := ⟨⟨fun x y => Subtype.ext (congrArg (fun z : shearSubgroup => (z : Group))
    ((IsMulCommutative.is_comm (M := shearSubgroup)).comm
      (⟨x.val, hA x.property⟩ : shearSubgroup) ⟨y.val, hA y.property⟩))⟩⟩
  exponent_dvd_p := by
    rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    intro x
    apply Subtype.ext
    exact elemPow_eq_one_of_isElementaryAbelian x.val (hA x.property)

/-- The quotient-rank convention is exactly the one in E.3.8: normality is
inside A, and the quotient is by B.subgroupOf A. -/
theorem quotient_finrank_eq_shearParameters_codim {A B : Subgroup Group}
    (hA : A ≤ shearSubgroup) (hBA : B ≤ A) :
    let _ := elementary_of_le_shearSubgroup hA
    Module.finrank (ZMod 2) (Additive (A ⧸ B.subgroupOf A)) =
      Module.finrank (ZMod 2) (shearParameters A) -
        Module.finrank (ZMod 2) (shearParameters B) := by
  let _ := elementary_of_le_shearSubgroup hA
  dsimp only
  rw [← Subgroup.log_relIndex_eq_quotient_finrank]
  exact log_relIndex_eq_shearParameters_codim hA hBA

/-- A rank-three subgroup has a line of index four with a larger fixed space. -/
theorem exists_line_fixedSpace_lt_of_card_eight {A : Subgroup Group}
    (hA : A ≤ shearSubgroup) (hcard : Nat.card A = 8) :
    ∃ B : Subgroup Group, B ≤ A ∧ Nat.card B = 2 ∧ B.relIndex A = 4 ∧
      BinaryOffender.fixedSpace (exteriorAction 2) A <
        BinaryOffender.fixedSpace (exteriorAction 2) B := by
  have hd : Module.finrank (ZMod 2) (shearParameters A) = 3 := by
    apply Nat.pow_right_injective (by decide : 2 ≤ 2)
    simpa only [card_eq_two_pow_finrank_shearParameters hA] using hcard
  have hP : shearParameters A ≠ ⊥ := by
    intro h
    have hz := Submodule.finrank_eq_zero.mpr h
    omega
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP
  let P := Submodule.span (ZMod 2) {u}
  let B := parameterShears P
  have hBA : B ≤ A := by
    rw [← parameterShears_shearParameters hA]
    exact parameterShears_mono ((Submodule.span_singleton_le_iff_mem _ _).mpr hu)
  have hdimB : Module.finrank (ZMod 2) (shearParameters B) = 1 := by
    rw [shearParameters_parameterShears]
    exact finrank_span_singleton hu0
  refine ⟨B, hBA, ?_, ?_, ?_⟩
  · rw [card_eq_two_pow_finrank_shearParameters (hBA.trans hA), hdimB]
    norm_num
  · rw [relIndex_eq_two_pow_shearParameters hA hBA, hd, hdimB]
    norm_num
  · rw [fixedSpace_eq_V₆_of_shearParameters_rank hA (by omega)]
    change V₆ < BinaryOffender.fixedSpace (exteriorAction 2)
      (parameterShears (Submodule.span (ZMod 2) {u}))
    rw [fixedSpace_parameterLine]
    exact V₆_lt_fixedSpace_shear u hu0

/-- This is the hyperplane obstruction used in the proof of 12.5.7. -/
theorem not_smallIndex_three_of_card_eight {A : Subgroup Group}
    (hA : A ≤ shearSubgroup) (hcard : Nat.card A = 8) :
    ¬ HasSmallIndexFixedSpaceProperty 3 A := by
  intro h
  obtain ⟨B, hBA, _, hi, hlt⟩ := exists_line_fixedSpace_lt_of_card_eight hA hcard
  exact (ne_of_lt hlt) (h B hBA (by rw [hi]; decide))

/-- A nontrivial subgroup of U does not fix the whole exterior square. -/
theorem fixedSpace_ne_top_of_le_shearSubgroup {A : Subgroup Group}
    (hA : A ≤ shearSubgroup) (hne : A ≠ ⊥) :
    BinaryOffender.fixedSpace (exteriorAction 2) A ≠ ⊤ := by
  intro htop
  obtain ⟨g, hg⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  obtain ⟨u, hu⟩ := (mem_shearSubgroup g.val).mp (hA g.property)
  have hu0 : u ≠ 0 := by
    intro hz
    apply hg
    apply Subtype.ext
    simpa [hz] using hu.symm
  have hline : (⊤ : Submodule (ZMod 2) ShearParameter) ≤
      Submodule.span (ZMod 2) {u} := by
    intro w _
    have hfix : shearSection w ∈ BinaryOffender.fixedSpace (exteriorAction 2) A := by
      rw [htop]
      trivial
    have he : exteriorAction 2 (shear u) (shearSection w) = shearSection w := by
      change ∀ a : A, exteriorAction 2 a.val (shearSection w) = shearSection w at hfix
      exact hu.symm ▸ hfix g
    have hf : shearSection w ∈ fixedSpace (shear u) := by
      change exteriorAction 2 (shear u) (shearSection w) - shearSection w = 0
      exact sub_eq_zero.mpr he
    rw [fixed_shear_iff u hu0, shearQuotient_section] at hf
    exact (mem_parameterLine u w).mpr hf
  have hd := Submodule.finrank_mono hline
  rw [finrank_span_singleton hu0] at hd
  norm_num at hd

/-- E.3.8 also excludes ranks one and two, by taking B to be trivial. -/
theorem not_smallIndex_three_of_rank_le_two {A : Subgroup Group}
    (hA : A ≤ shearSubgroup) (hne : A ≠ ⊥)
    (hd : Module.finrank (ZMod 2) (shearParameters A) ≤ 2) :
    ¬ HasSmallIndexFixedSpaceProperty 3 A := by
  intro h
  have he := h ⊥ bot_le (by
    rw [Subgroup.relIndex_bot_left, card_eq_two_pow_finrank_shearParameters hA,
      Nat.log_pow (by decide)]
    omega)
  rw [BinaryOffender.fixedSpace_bot] at he
  exact fixedSpace_ne_top_of_le_shearSubgroup hA hne he

/-- Among nontrivial subgroups of U, the E.3.8 condition at k=3 forces A=U. -/
theorem eq_shearSubgroup_of_smallIndex_three {A : Subgroup Group}
    (hA : A ≤ shearSubgroup) (hne : A ≠ ⊥)
    (hsmall : HasSmallIndexFixedSpaceProperty 3 A) : A = shearSubgroup := by
  have hd := finrank_shearParameters_le_four A
  have hgt : 2 < Module.finrank (ZMod 2) (shearParameters A) := by
    by_contra h
    exact not_smallIndex_three_of_rank_le_two hA hne (by omega) hsmall
  have hne3 : Module.finrank (ZMod 2) (shearParameters A) ≠ 3 := by
    intro h3
    apply not_smallIndex_three_of_card_eight hA _ hsmall
    rw [card_eq_two_pow_finrank_shearParameters hA, h3]
    norm_num
  have h4 : Module.finrank (ZMod 2) (shearParameters A) = 4 := by omega
  apply Subgroup.eq_of_le_of_card_ge hA
  rw [card_shearSubgroup, card_eq_two_pow_finrank_shearParameters hA, h4]
  norm_num

/-- U itself satisfies E.3.8 at k=3: index below eight leaves parameter rank at least two. -/
theorem smallIndex_three_shearSubgroup : HasSmallIndexFixedSpaceProperty 3 shearSubgroup := by
  intro B hB hi
  have h4 : Module.finrank (ZMod 2) (shearParameters shearSubgroup) = 4 := by
    apply Nat.pow_right_injective (by decide : 2 ≤ 2)
    change 2 ^ Module.finrank (ZMod 2) (shearParameters shearSubgroup) = 2 ^ 4
    rw [← card_eq_two_pow_finrank_shearParameters le_rfl, card_shearSubgroup]
  rw [log_relIndex_eq_shearParameters_codim le_rfl hB, h4] at hi
  rw [fixedSpace_shearSubgroup, fixedSpace_eq_V₆_of_shearParameters_rank hB (by omega)]

/-- The full characterization, with the nontriviality clause of E.3.8 explicit. -/
theorem smallIndex_three_iff_eq_shearSubgroup {A : Subgroup Group}
    (hA : A ≤ shearSubgroup) (hne : A ≠ ⊥) :
    HasSmallIndexFixedSpaceProperty 3 A ↔ A = shearSubgroup := by
  constructor
  · exact eq_shearSubgroup_of_smallIndex_three hA hne
  · rintro rfl
    exact smallIndex_three_shearSubgroup

/-- Binary subgroup rank is parameter-space dimension. -/
theorem rank_eq_finrank_shearParameters {A : Subgroup Group} (hA : A ≤ shearSubgroup) :
    BinaryOffender.rank A = Module.finrank (ZMod 2) (shearParameters A) := by
  rw [BinaryOffender.rank, card_eq_two_pow_finrank_shearParameters hA,
    Nat.log_pow (by decide)]

/-- The relative-index definition is precisely the literal quotient formulation of E.3.8. -/
theorem smallIndex_iff_quotient_fixedSpace (k : ℕ) {A : Subgroup Group}
    (hA : A ≤ shearSubgroup) :
    let _ := elementary_of_le_shearSubgroup hA
    HasSmallIndexFixedSpaceProperty k A ↔
      ∀ B ≤ A, Module.finrank (ZMod 2) (Additive (A ⧸ B.subgroupOf A)) < k →
        BinaryOffender.fixedSpace (exteriorAction 2) A =
          BinaryOffender.fixedSpace (exteriorAction 2) B := by
  let _ := elementary_of_le_shearSubgroup hA
  dsimp only
  unfold HasSmallIndexFixedSpaceProperty
  apply forall_congr'
  intro B
  apply forall_congr'
  intro hBA
  rw [log_relIndex_eq_shearParameters_codim hA hBA,
    quotient_finrank_eq_shearParameters_codim hA hBA]

/-- The A₃ characterization with the book's literal quotient-rank quantifier. -/
theorem quotient_smallIndex_three_iff_eq_shearSubgroup {A : Subgroup Group}
    (hA : A ≤ shearSubgroup) (hne : A ≠ ⊥) :
    let _ := elementary_of_le_shearSubgroup hA
    (∀ B ≤ A, Module.finrank (ZMod 2) (Additive (A ⧸ B.subgroupOf A)) < 3 →
      BinaryOffender.fixedSpace (exteriorAction 2) A =
        BinaryOffender.fixedSpace (exteriorAction 2) B) ↔ A = shearSubgroup := by
  let _ := elementary_of_le_shearSubgroup hA
  dsimp only
  have he := smallIndex_iff_quotient_fixedSpace 3 hA
  dsimp only at he
  exact he.symm.trans (smallIndex_three_iff_eq_shearSubgroup hA hne)

/-- Including nontriviality and elementary abelianness, the only E.3.8 A₃ subgroup in U is U. -/
theorem elementaryTwo_smallIndex_three_iff {A : Subgroup Group} (hA : A ≤ shearSubgroup) :
    (BinaryOffender.IsElementaryTwo A ∧ HasSmallIndexFixedSpaceProperty 3 A) ↔
      A = shearSubgroup := by
  constructor
  · intro h
    exact eq_shearSubgroup_of_smallIndex_three hA h.1.1 h.2
  · rintro rfl
    refine ⟨⟨?_, inferInstance⟩, smallIndex_three_shearSubgroup⟩
    intro hbot
    have hc := card_shearSubgroup
    rw [hbot] at hc
    norm_num at hc

end Representation.SL5ExteriorSquare
