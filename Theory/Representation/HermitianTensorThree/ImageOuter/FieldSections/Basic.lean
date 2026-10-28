module

public import Theory.Representation.HermitianTensorThree.ImageOuter.Overgroups

/-!
# The three literal sections of the Hermitian field involution

The centralizer in the binary image acts over the fixed field. Commutation
with the involution preserves both its fixed space and the range of its
commutator map. In characteristic two that range lies in the fixed space.
The three induced representations below use these actual subspaces and
quotient maps. Rank-nullity gives dimension three in each case.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, H.4.4(6),
printed pp.380–381, with the standing hypotheses on p.377.
-/

@[expose] public section
noncomputable section
namespace Representation.HermitianTensorThree.ImageOuter.FieldSections
variable (n : ℕ) [NeZero n]

/-- The full centralizer of the marked involution in the literal binary image. -/
def centralizer : Subgroup (Space n ≃ₗ[ZMod 2] Space n) :=
  binaryImage n ⊓ Subgroup.centralizer ({fieldSwapBinary n} : Set _)

/-- The same element in the fixed-field image, via the published equivalence. -/
def centralizerToImage : centralizer n →* Image n :=
  (binaryImageEquiv n).symm.toMonoidHom.comp
    (Subgroup.inclusion (show centralizer n ≤ binaryImage n from inf_le_left))

/-- The inherited action over F, on the original nine-dimensional space. -/
def centralizerAction : Representation (F n) (centralizer n) (Space n) :=
  (imageAction n).comp (centralizerToImage n)

theorem centralizerAction_apply (g : centralizer n) (X : Space n) :
    centralizerAction n g X = g.val X := by
  have h := (binaryImageEquiv n).apply_symm_apply
    (⟨g.val, g.property.1⟩ : binaryImage n)
  exact congrArg (fun a : binaryImage n => a.val X) h

theorem centralizerAction_commutes (g : centralizer n) (X : Space n) :
    centralizerAction n g (fieldSwap n X) = fieldSwap n (centralizerAction n g X) := by
  rw [centralizerAction_apply, centralizerAction_apply]
  exact congrArg (fun e : Space n ≃ₗ[ZMod 2] Space n => e X)
    (Subgroup.mem_centralizer_singleton_iff.mp g.property.2)

/-- The actual commutator space [V,σ]. -/
def moved : Submodule (F n) (Space n) :=
  LinearMap.range ((fieldSwap n).toLinearMap - LinearMap.id)

theorem moved_le_fixed : moved n ≤ fieldFixed n := by
  rintro X ⟨Y, rfl⟩
  rw [mem_fieldFixed]
  apply Subtype.ext
  ext i j
  change (Y.val i j - Y.val j i) = (Y.val j i - Y.val i j)
  simp only [CharTwo.sub_eq_add, add_comm]

/-- The fixed space as a subrepresentation of the centralizer. -/
def fixedSubrepresentation : Subrepresentation (centralizerAction n) where
  toSubmodule := fieldFixed n
  apply_mem_toSubmodule g X hX := by
    rw [mem_fieldFixed] at hX ⊢
    rw [← centralizerAction_commutes, hX]

/-- The commutator space as a subrepresentation of the centralizer. -/
def movedSubrepresentation : Subrepresentation (centralizerAction n) where
  toSubmodule := moved n
  apply_mem_toSubmodule g X hX := by
    obtain ⟨Y, rfl⟩ := hX
    refine ⟨centralizerAction n g Y, ?_⟩
    change fieldSwap n (centralizerAction n g Y) - centralizerAction n g Y =
      centralizerAction n g (fieldSwap n Y - Y)
    rw [map_sub, centralizerAction_commutes]

/-- The inherited action on [V,σ]. -/
def movedAction : Representation (F n) (centralizer n) (moved n) :=
  (movedSubrepresentation n).toRepresentation

/-- The inherited action on C_V(σ). -/
def fixedAction : Representation (F n) (centralizer n) (fieldFixed n) :=
  (fixedSubrepresentation n).toRepresentation

/-- The actual inverse image of [V,σ] under C_V(σ) ↪ V. -/
def movedInFixed : Submodule (F n) (fieldFixed n) :=
  (moved n).comap (fieldFixed n).subtype

theorem movedInFixed_invariant (g : centralizer n) :
    movedInFixed n ≤ (movedInFixed n).comap (fixedAction n g) := by
  intro X hX
  exact (movedSubrepresentation n).apply_mem_toSubmodule g hX

/-- The induced action on C_V(σ)/[V,σ], using the literal preimage. -/
def middleAction : Representation (F n) (centralizer n)
    ((fieldFixed n) ⧸ movedInFixed n) :=
  (fixedAction n).quotient (movedInFixed n) (movedInFixed_invariant n)

/-- The induced action on V/C_V(σ). -/
def topAction : Representation (F n) (centralizer n) ((Space n) ⧸ fieldFixed n) :=
  (centralizerAction n).quotient (fieldFixed n)
    (fixedSubrepresentation n).apply_mem_toSubmodule

theorem movedAction_apply (g : centralizer n) (X : moved n) :
    (movedAction n g X).val = g.val X.val := centralizerAction_apply n g X.val

theorem fixedAction_apply (g : centralizer n) (X : fieldFixed n) :
    (fixedAction n g X).val = g.val X.val := centralizerAction_apply n g X.val

theorem middleAction_mk (g : centralizer n) (X : fieldFixed n) :
    middleAction n g ((movedInFixed n).mkQ X) =
      (movedInFixed n).mkQ (fixedAction n g X) := rfl

theorem topAction_mk (g : centralizer n) (X : Space n) :
    topAction n g ((fieldFixed n).mkQ X) =
      (fieldFixed n).mkQ (centralizerAction n g X) := rfl

theorem finrank_moved : Module.finrank (F n) (moved n) = 3 := finrank_fieldMoved n

theorem finrank_middle : Module.finrank (F n) ((fieldFixed n) ⧸ movedInFixed n) = 3 := by
  have hdim := (movedInFixed n).finrank_quotient_add_finrank
  have he := (Submodule.comapSubtypeEquivOfLe (moved_le_fixed n)).finrank_eq
  change Module.finrank (F n) (movedInFixed n) = Module.finrank (F n) (moved n) at he
  rw [he, finrank_moved, finrank_fieldFixed] at hdim
  omega

theorem finrank_top : Module.finrank (F n) ((Space n) ⧸ fieldFixed n) = 3 := by
  have hdim := (fieldFixed n).finrank_quotient_add_finrank
  rw [finrank_fieldFixed, finrank_space] at hdim
  omega

end Representation.HermitianTensorThree.ImageOuter.FieldSections
