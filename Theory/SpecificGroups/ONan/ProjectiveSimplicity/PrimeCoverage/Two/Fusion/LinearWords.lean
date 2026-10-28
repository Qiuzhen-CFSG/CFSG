module

public import Theory.SpecificGroups.ONan.ProjectiveSimplicity.PrimeCoverage.Two.FusionReduction

/-!
# Linear lifts and indexing for the O'Nan fusion certificate

The binary index uses bit `j` for basis word `j`, in increasing product order.
All linear words project to the fixed words in `Two/Setup.lean`. These transport
lemmas allow numerical matrix certificates to be checked separately from the
finite conjugation trees. Word and matrix sources are preserved in `Two/source/`
and `refs/original/onan/`.
-/

@[expose] public section
namespace ONan.Simplicity.TwoCertificate.Fusion

/-- Little-endian binary digits of a normal-form index. -/
def bits (i : Fin 512) : Fin 9 → Bool :=
  fun j => finTwoEquiv (finFunctionFinEquiv.symm i j)

theorem bits_surjective : Function.Surjective bits := by
  intro v
  refine ⟨finFunctionFinEquiv (fun j => finTwoEquiv.symm (v j)), ?_⟩
  funext j
  change finTwoEquiv (finFunctionFinEquiv.symm
    (finFunctionFinEquiv (fun j => finTwoEquiv.symm (v j))) j) = v j
  rw [Equiv.symm_apply_apply, Equiv.apply_symm_apply]

/-- The project's normal form, indexed by a natural number below 512. -/
def indexedForm (i : Fin 512) : Model := normalForm (bits i)

theorem indexedForm_zero : indexedForm 0 = 1 := by
  have h : bits 0 = fun _ => false := by decide +kernel
  change normalForm (bits 0) = 1
  rw [h]
  exact Subgroup.BinaryNormalForm.product_zero _

/-- The fixed nine words evaluated in GL before projectivizing. -/
def linearBasis : Fin 9 → Matrix.GeneralLinearGroup (Fin 45) (ZMod 7) :=
  TwoCertificate.basis linearA linearB

/-- The fixed indexed product evaluated in GL. -/
def linearForm (i : Fin 512) : Matrix.GeneralLinearGroup (Fin 45) (ZMod 7) :=
  Subgroup.BinaryNormalForm.product linearBasis (bits i)

/-- Positive ambient words, with zero-based letters. -/
def ambientWord {G : Type*} [Group G] (a b : G) (w : List (Fin 2)) : G :=
  (w.map ![a, b]).prod

private theorem map_local {G H : Type*} [Group G] [Group H] (f : G →* H)
    (a b : G) (i : Fin 2) :
    f (localGenerators a b i) = localGenerators (f a) (f b) i := by
  fin_cases i <;> simp [localGenerators, map_mul, map_pow, map_inv]

private theorem map_basis {G H : Type*} [Group G] [Group H] (f : G →* H)
    (a b : G) (i : Fin 9) :
    f (TwoCertificate.basis a b i) = TwoCertificate.basis (f a) (f b) i := by
  simp only [TwoCertificate.basis, map_list_prod, List.map_map]
  congr 2
  funext j
  exact map_local f a b j

private theorem map_product {G H : Type*} [Group G] [Group H] (f : G →* H)
    (g : Fin 9 → G) (v : Fin 9 → Bool) :
    f (Subgroup.BinaryNormalForm.product g v) =
      Subgroup.BinaryNormalForm.product (fun j => f (g j)) v := by
  simp only [Subgroup.BinaryNormalForm.product, map_list_prod, List.map_ofFn]
  congr 2
  funext i
  split <;> simp_all

/-- Inclusion of the fixed generated projective subgroup. -/
def inclusion : Model →* Matrix.ProjGenLinGroup (Fin 45) (ZMod 7) where
  toFun g := g.val
  map_one' := rfl
  map_mul' _ _ := rfl

theorem project_linearBasis (j : Fin 9) :
    Matrix.ProjGenLinGroup.mk (linearBasis j) = (generators j).val := by
  change Matrix.ProjGenLinGroup.mk (TwoCertificate.basis linearA linearB j) =
    inclusion (TwoCertificate.basis generatorA generatorB j)
  rw [map_basis, map_basis]
  rfl

theorem project_linearForm (i : Fin 512) :
    Matrix.ProjGenLinGroup.mk (linearForm i) = (indexedForm i).val := by
  change Matrix.ProjGenLinGroup.mk
      (Subgroup.BinaryNormalForm.product linearBasis (bits i)) =
    inclusion (Subgroup.BinaryNormalForm.product generators (bits i))
  rw [map_product, map_product]
  congr 1
  funext j
  exact project_linearBasis j

private theorem map_ambientWord {G H : Type*} [Group G] [Group H] (f : G →* H)
    (a b : G) (w : List (Fin 2)) :
    f (ambientWord a b w) = ambientWord (f a) (f b) w := by
  simp only [ambientWord, map_list_prod, List.map_map]
  congr 2
  funext j
  fin_cases j <;> rfl

theorem project_ambientWord (w : List (Fin 2)) :
    Matrix.ProjGenLinGroup.mk (ambientWord linearA linearB w) =
      (ambientWord generatorA generatorB w).val := by
  change Matrix.ProjGenLinGroup.mk (ambientWord linearA linearB w) =
    inclusion (ambientWord generatorA generatorB w)
  rw [map_ambientWord, map_ambientWord]
  rfl

end ONan.Simplicity.TwoCertificate.Fusion
