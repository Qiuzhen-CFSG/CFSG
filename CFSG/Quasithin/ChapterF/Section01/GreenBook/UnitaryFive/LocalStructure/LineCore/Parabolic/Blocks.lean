module

public import CFSG.Quasithin.ChapterF.Section01.GreenBook.UnitaryFive.LocalStructure.LineCore.Parabolic.Blocks.Exhaustion

/-!
# Assembly of the full line-parabolic block maps

The exhaustive and faithful matrix map identifies the actual projective line
parabolic with `Coord ⋊ (SU₃ × rootsOfUnity 3 F)`. Descending the two coordinate
projections gives the SU₃ projection and the cubic character. Their common
kernel is the unipotent subgroup, the character kernel is the radical–SU₃
subgroup, and the inverse image of the marked SU₃ line stabilizer is exactly
the original flag overlap. The cubic matrix section splits the character and
lies in the projection kernel.

The residual identification is a separate consequence requiring perfectness;
no residual or parabolic-order hypothesis enters this block calculation.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
F.1.11--12(7), printed pp.262--264.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterF.GreenBook.UnitaryFive.Model
open Theory.SpecificGroups.UnitaryFive.LineCore
open Theory.SpecificGroups.UnitaryFive.LineCore.Parabolic
open Theory.SpecificGroups.UnitaryFive.LineCore.Parabolic.Blocks
variable (M : Model 4)

/-- Full block coordinates on the actual projective line parabolic. -/
noncomputable def lineFullEquiv (c : M.F) (hc : c + M.form.conj c = 1) :
    M.LineFullProduct ≃* M.leftParabolic :=
  MulEquiv.ofBijective (M.lineFullMap c hc)
    ⟨M.lineFullMap_injective c hc, M.lineFullMap_surjective c hc⟩

@[simp] theorem lineFullEquiv_apply (c : M.F) (hc : c + M.form.conj c = 1)
    (x : M.LineFullProduct) : M.lineFullEquiv c hc x = M.lineFullMap c hc x := rfl

/-- The special-unitary middle block after removal of the scalar and cubic factors. -/
noncomputable def lineBlockProjection (c : M.F) (hc : c + M.form.conj c = 1) :
    M.leftParabolic →* M.LocalUnitaryGroup :=
  M.lineProductProjection.comp (M.lineFullEquiv c hc).symm.toMonoidHom

/-- The cubic diagonal character of the entire projective line parabolic. -/
noncomputable def lineBlockCharacter (c : M.F) (hc : c + M.form.conj c = 1) :
    M.leftParabolic →* M.LineCubic :=
  M.lineProductCharacter.comp (M.lineFullEquiv c hc).symm.toMonoidHom

@[simp] theorem lineBlockProjection_fullMap (c : M.F) (hc : c + M.form.conj c = 1)
    (x : M.LineFullProduct) :
    M.lineBlockProjection c hc (M.lineFullMap c hc x) = x.right.1 := by
  change M.lineProductProjection ((M.lineFullEquiv c hc).symm (M.lineFullEquiv c hc x)) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

@[simp] theorem lineBlockCharacter_fullMap (c : M.F) (hc : c + M.form.conj c = 1)
    (x : M.LineFullProduct) :
    M.lineBlockCharacter c hc (M.lineFullMap c hc x) = x.right.2 := by
  change M.lineProductCharacter ((M.lineFullEquiv c hc).symm (M.lineFullEquiv c hc x)) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

private theorem lineBlockMaps_spec (c : M.F) (hc : c + M.form.conj c = 1)
    (hsurj : Function.Surjective (M.lineFullMap c hc)) :
    (M.lineBlockProjection c hc).comp M.lineRadicalLeviMap = SemidirectProduct.rightHom ∧
    Function.Surjective (M.lineBlockCharacter c hc) ∧
    (M.lineBlockCharacter c hc).ker = M.lineRadicalLeviSubgroup ∧
    (M.lineBlockProjection c hc).ker ⊓ (M.lineBlockCharacter c hc).ker = M.lineUnipotent ∧
    M.localUnitaryLineStabilizer.comap (M.lineBlockProjection c hc) =
      M.overlap.subgroupOf M.leftParabolic ∧
    (∀ b, M.lineBlockProjection c hc (M.lineCubicEmbedding c hc b) = 1) ∧
    (∀ b, M.lineBlockCharacter c hc (M.lineCubicEmbedding c hc b) = b) := by
  let π := M.lineBlockProjection c hc
  let χ := M.lineBlockCharacter c hc
  have hπ (x : M.LineFullProduct) : π (M.lineFullMap c hc x) = x.right.1 :=
    M.lineBlockProjection_fullMap c hc x
  have hχ (x : M.LineFullProduct) : χ (M.lineFullMap c hc x) = x.right.2 :=
    M.lineBlockCharacter_fullMap c hc x
  have htor (b : M.LineCubic) : M.lineFullMap c hc
      (SemidirectProduct.inr (1, b)) = M.lineCubicEmbedding c hc b := by
    simp [lineFullMap, lineCubicEmbedding]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply MonoidHom.ext
    intro x
    have h := DFunLike.congr_fun (M.lineFullMap_comp_radicalLeviInclusion c hc) x
    change M.lineFullMap c hc (M.lineRadicalLeviInclusion x) = M.lineRadicalLeviMap x at h
    change π (M.lineRadicalLeviMap x) = x.right
    rw [← h, hπ]
    rfl
  · intro b
    refine ⟨M.lineCubicEmbedding c hc b, ?_⟩
    rw [← htor, hχ]
    rfl
  · ext g
    obtain ⟨x, rfl⟩ := hsurj g
    change χ (M.lineFullMap c hc x) = 1 ↔ M.lineFullMap c hc x ∈ M.lineRadicalLeviMap.range
    rw [hχ]
    constructor
    · intro hb
      let y : M.LineRadicalLevi := ⟨x.left, x.right.1⟩
      have hy : M.lineRadicalLeviInclusion y = x := by
        apply SemidirectProduct.ext
        · rfl
        · exact Prod.ext rfl hb.symm
      refine ⟨y, ?_⟩
      have he := DFunLike.congr_fun (M.lineFullMap_comp_radicalLeviInclusion c hc) y
      change M.lineFullMap c hc (M.lineRadicalLeviInclusion y) = M.lineRadicalLeviMap y at he
      exact he.symm.trans (congrArg (M.lineFullMap c hc) hy)
    · rintro ⟨y, hy⟩
      have he := DFunLike.congr_fun (M.lineFullMap_comp_radicalLeviInclusion c hc) y
      change M.lineFullMap c hc (M.lineRadicalLeviInclusion y) = M.lineRadicalLeviMap y at he
      have hx := M.lineFullMap_injective c hc (he.trans hy)
      exact (congrArg (fun z : M.LineFullProduct => z.right.2) hx).symm
  · ext g
    obtain ⟨x, rfl⟩ := hsurj g
    change (π (M.lineFullMap c hc x) = 1 ∧ χ (M.lineFullMap c hc x) = 1) ↔
      M.lineFullMap c hc x ∈ M.lineRadicalEmbedding.range
    rw [hπ, hχ]
    have hu (u : M.LineRadicalCoordinates) :
        M.lineFullMap c hc (SemidirectProduct.inl u) = M.lineRadicalEmbedding u := by
      simp [lineFullMap, lineRadicalEmbedding]
    constructor
    · rintro ⟨hA, hb⟩
      refine ⟨x.left, ?_⟩
      rw [← hu]
      congr 1
      apply SemidirectProduct.ext
      · rfl
      · exact Prod.ext hA.symm hb.symm
    · rintro ⟨u, hu'⟩
      have hx := M.lineFullMap_injective c hc ((hu u).trans hu')
      have he := congrArg (fun z : M.LineFullProduct => z.right) hx
      exact ⟨(congrArg Prod.fst he).symm, (congrArg Prod.snd he).symm⟩
  · ext g
    obtain ⟨x, rfl⟩ := hsurj g
    change π (M.lineFullMap c hc x) ∈ M.localUnitaryLineStabilizer ↔ _
    rw [hπ]
    exact (M.lineFullMap_mem_overlap_iff c hc x).symm
  · intro b
    rw [← htor, hπ]
    rfl
  · intro b
    rw [← htor, hχ]
    rfl

/-- On the established radical–SU₃ embedding, the full projection is its SU₃ coordinate. -/
theorem lineBlockProjection_comp_radicalLeviMap (c : M.F) (hc : c + M.form.conj c = 1) :
    (M.lineBlockProjection c hc).comp M.lineRadicalLeviMap = SemidirectProduct.rightHom :=
  (M.lineBlockMaps_spec c hc (M.lineFullMap_surjective c hc)).1

theorem lineBlockCharacter_surjective (c : M.F) (hc : c + M.form.conj c = 1) :
    Function.Surjective (M.lineBlockCharacter c hc) :=
  (M.lineBlockMaps_spec c hc (M.lineFullMap_surjective c hc)).2.1

/-- The character kernel is exactly the actual radical–SU₃ subgroup. -/
theorem lineBlockCharacter_ker (c : M.F) (hc : c + M.form.conj c = 1) :
    (M.lineBlockCharacter c hc).ker = M.lineRadicalLeviSubgroup :=
  (M.lineBlockMaps_spec c hc (M.lineFullMap_surjective c hc)).2.2.1

/-- Both diagonal coordinates must vanish to recover the unipotent subgroup. -/
theorem lineBlock_common_kernel (c : M.F) (hc : c + M.form.conj c = 1) :
    (M.lineBlockProjection c hc).ker ⊓ (M.lineBlockCharacter c hc).ker = M.lineUnipotent :=
  (M.lineBlockMaps_spec c hc (M.lineFullMap_surjective c hc)).2.2.2.1

/-- The full projection carries the actual flag condition to the marked SU₃ line. -/
theorem lineBlockProjection_flag_preimage (c : M.F) (hc : c + M.form.conj c = 1) :
    M.localUnitaryLineStabilizer.comap (M.lineBlockProjection c hc) =
      M.overlap.subgroupOf M.leftParabolic :=
  (M.lineBlockMaps_spec c hc (M.lineFullMap_surjective c hc)).2.2.2.2.1

@[simp] theorem lineBlockProjection_cubicEmbedding (c : M.F) (hc : c + M.form.conj c = 1)
    (b : M.LineCubic) : M.lineBlockProjection c hc (M.lineCubicEmbedding c hc b) = 1 :=
  (M.lineBlockMaps_spec c hc (M.lineFullMap_surjective c hc)).2.2.2.2.2.1 b

@[simp] theorem lineBlockCharacter_cubicEmbedding (c : M.F) (hc : c + M.form.conj c = 1)
    (b : M.LineCubic) : M.lineBlockCharacter c hc (M.lineCubicEmbedding c hc b) = b :=
  (M.lineBlockMaps_spec c hc (M.lineFullMap_surjective c hc)).2.2.2.2.2.2 b

/-- The full block maps and their actual cubic matrix section, with no exhaustion premise. -/
theorem exists_lineBlockMaps_with_torus (c : M.F) (hc : c + M.form.conj c = 1) :
    ∃ (π : M.leftParabolic →* M.LocalUnitaryGroup) (χ : M.leftParabolic →* M.LineCubic),
      π.comp M.lineRadicalLeviMap = SemidirectProduct.rightHom ∧
      Function.Surjective χ ∧
      χ.ker = M.lineRadicalLeviSubgroup ∧
      π.ker ⊓ χ.ker = M.lineUnipotent ∧
      M.localUnitaryLineStabilizer.comap π = M.overlap.subgroupOf M.leftParabolic ∧
      (∀ b, π (M.lineCubicEmbedding c hc b) = 1) ∧
      (∀ b, χ (M.lineCubicEmbedding c hc b) = b) :=
  ⟨M.lineBlockProjection c hc, M.lineBlockCharacter c hc, M.lineBlockMaps_spec c hc (M.lineFullMap_surjective c hc)⟩

/-- Compatibility with the earlier conditional assembly interface. Exhaustion is now proved. -/
theorem exists_lineBlockMaps_of_fullMap_surjective
    (c : M.F) (hc : c + M.form.conj c = 1)
    (hsurj : Function.Surjective (M.lineFullMap c hc)) :
    ∃ (π : M.leftParabolic →* M.LocalUnitaryGroup) (χ : M.leftParabolic →* M.LineCubic),
      π.comp M.lineRadicalLeviMap = SemidirectProduct.rightHom ∧
      Function.Surjective χ ∧
      χ.ker = M.lineRadicalLeviSubgroup ∧
      π.ker ⊓ χ.ker = M.lineUnipotent ∧
      M.localUnitaryLineStabilizer.comap π = M.overlap.subgroupOf M.leftParabolic ∧
      (∀ b, π (M.lineCubicEmbedding c hc b) = 1) ∧
      (∀ b, χ (M.lineCubicEmbedding c hc b) = b) := by
  exact ⟨M.lineBlockProjection c hc, M.lineBlockCharacter c hc,
    M.lineBlockMaps_spec c hc hsurj⟩

/-- The full-parabolic projection and cubic character exist for every parameter-four model.
The trace-one coordinate is supplied by the model's actual field and involution. -/
theorem exists_lineBlockMaps :
    ∃ (π : M.leftParabolic →* M.LocalUnitaryGroup) (χ : M.leftParabolic →* M.LineCubic),
      π.comp M.lineRadicalLeviMap = SemidirectProduct.rightHom ∧
      Function.Surjective χ ∧
      χ.ker = M.lineRadicalLeviSubgroup ∧
      π.ker ⊓ χ.ker = M.lineUnipotent ∧
      M.localUnitaryLineStabilizer.comap π = M.overlap.subgroupOf M.leftParabolic := by
  obtain ⟨c, hc⟩ := M.exists_lineTraceOne
  exact ⟨M.lineBlockProjection c hc, M.lineBlockCharacter c hc,
    M.lineBlockProjection_comp_radicalLeviMap c hc, M.lineBlockCharacter_surjective c hc,
    M.lineBlockCharacter_ker c hc, M.lineBlock_common_kernel c hc,
    M.lineBlockProjection_flag_preimage c hc⟩

end CFSG.Quasithin.ChapterF.GreenBook.UnitaryFive.Model
