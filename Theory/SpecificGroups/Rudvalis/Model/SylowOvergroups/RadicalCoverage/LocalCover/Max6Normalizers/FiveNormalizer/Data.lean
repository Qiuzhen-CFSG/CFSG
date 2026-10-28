module

public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.Max6Normalizers.Words
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.ElementaryCatalogue.ElementaryComparison

/-!
# Binary words for the small-orbit kernel of elementary 5

Reuse the checked elementary-word point maps. The five generators correspond
exactly to original indices 0, 1, 2, 3, and 5. Involution and commutativity
checks on all 4060 points support the binary-word closure proof in Algebra.

Source: the preserved ATLAS words, with the action convention and attribution
in LocalCover.Data. No catalogue, Sylow or ambient-order claim is used here.
-/

namespace Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover.Max6Certificate.Five

set_option maxRecDepth 30000
set_option Elab.async false

/-- The already certified point map of each unchanged elementary word. -/
@[expose] public def cached (i : Fin 6) : Model :=
  ⟨CatalogueCertificate.elementaryPermutation i,
    (CatalogueCertificate.elementaryPermutation_eq i).symm ▸
      (elementaryGenerator i).property⟩

public theorem cached_eq (i : Fin 6) : cached i = elementaryGenerator i :=
  Subtype.ext (CatalogueCertificate.elementaryPermutation_eq i)

/-- The branch uses original generator 5 as its last generator. -/
@[expose] public def gen : Fin 5 → Model :=
  ![cached 0, cached 1, cached 2, cached 3, cached 5]

public theorem gen_eq : gen =
    ![elementaryGenerator 0, elementaryGenerator 1, elementaryGenerator 2,
      elementaryGenerator 3, elementaryGenerator 5] := by
  simp only [gen, cached_eq]

/-- A single bit selects the corresponding generator. -/
@[expose] public def factor (i : Fin 5) (n : Fin 32) : Model :=
  if n.val.testBit i.val then gen i else 1

/-- The 32 products of distinct basis elements, with the first bit marking gen 0. -/
@[expose] public def word (n : Fin 32) : Model :=
  factor 0 n * factor 1 n * factor 2 n * factor 3 n * factor 4 n

@[expose] public def toggle (i : Fin 5) (n : Fin 32) : Fin 32 :=
  ⟨(n.val ^^^ (2 ^ i.val)) % 32, Nat.mod_lt _ (by decide)⟩

public theorem gen_inv (i : Fin 5) : (gen i)⁻¹ = gen i := by
  apply Subtype.ext
  fin_cases i <;> rfl

public theorem gen_sq (i : Fin 5) : gen i * gen i = 1 := by
  simpa only [gen_inv] using inv_mul_cancel (gen i)

public theorem gen_comm : ∀ i j : Fin 5, Commute (gen i) (gen j) := by
  have hc : ∀ p : Fin 4060, ∀ i j : Fin 5,
      (gen i * gen j).val p = (gen j * gen i).val p := by
    apply Rudvalis.Data.allFin
    decide +kernel
  intro i j
  exact Subtype.ext (Equiv.ext (fun p => hc p i j))

end Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover.Max6Certificate.Five
