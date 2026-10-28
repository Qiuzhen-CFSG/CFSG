module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.Construction.Products.SourceExclusions
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.Construction.Products.Supports

/-!
# The source two-factor decomposition in 13.6.13

The source seed eliminates singleton selections, so both native factors
are S₃. Their existing literal support product and constructed Thompson
image give every field of the required decomposition. The coordinate
maps are the original inclusions into the star quotient and into G.
Source: Aschbacher--Smith, combined manuscript, 13.6.13, printed p.929.
-/

public section
open Subgroup Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Products
open CFSG.Quasithin.ChapterB.SourceInduction
open CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives

private def twoCoordinates (W : Fin 2 → Type*) [∀ i, Group (W i)] :
    (∀ i, W i) ≃* W 0 × W 1 :=
  { piFinTwoEquiv W with map_mul' := fun _ _ => rfl }

private theorem coordinateProduct_single {D : Type*} [Group D]
    (F : Fin 2 → Subgroup D) (H : Subgroup D) (e : F 0 × F 1 ≃* H)
    (he : ∀ a b, (e (a, b) : D) = (a : D) * (b : D)) :
    ∀ i a, ((twoCoordinates (fun j => F j) |>.trans e) (Pi.mulSingle i a) : D) = a := by
  intro i a
  change (e ((Pi.mulSingle (M := fun j => F j) i a) 0,
    (Pi.mulSingle (M := fun j => F j) i a) 1) : D) = a
  rw [he]
  fin_cases i <;> simp

variable {G : Type*} [Group G] [Finite G]

set_option backward.isDefEq.respectTransparency false in
/-- The entire normal S₃ decomposition is constructed for the source
two-factor alternative, with no support or Thompson premise. -/
theorem normalS3Decomposition_of_source_twoFactors
    {L V : Subgroup G} (s : A5Module.Marking L V) (T : Subgroup G)
    [IsElementaryAbelian 2 (Uv (A5Module.markedZ s) (A5Module.markedV s))]
    (S : Sylow 2 (Gv (A5Module.markedV s)))
    (hS : (S : Subgroup (Gv (A5Module.markedV s))).map
      (Gv (A5Module.markedV s)).subtype = Tv T (A5Module.markedV s))
    (hfix : Tv T (A5Module.markedV s) ≤ centralizer ({A5Module.markedZ s} : Set G))
    (hL : Tv T (A5Module.markedV s) ≤ normalizer (Lv L (A5Module.markedV s) : Set G))
    (hcubic : Nat.card (Lv L (A5Module.markedV s) ⧸ pCore 2 (Lv L (A5Module.markedV s))) = 3)
    {X : Subgroup (Gstar (A5Module.markedZ s) (A5Module.markedV s))}
    (hX : MinimalSolvable L T (A5Module.markedZ s) (A5Module.markedV s) X)
    (c : SourceTwoFactorCase (FFFactors.offenderRepresentation
      (starRepresentation (A5Module.markedZ s) (A5Module.markedV s)))) :
    Nonempty (NormalS3Decomposition (A5Module.markedZ s) (A5Module.markedV s) X) := by
  let z := A5Module.markedZ s
  let v := A5Module.markedV s
  let I := FFFactors.offenderActor (starRepresentation z v)
  obtain ⟨⟨e₁⟩, ⟨e₂⟩, hF⟩ := source_twoFactor_both_residuals s T S hS hfix hL hcubic hX c
  let i₁ := c.first.equivMapOfInjective I.subtype I.subtype_injective
  let i₂ := c.second.equivMapOfInjective I.subtype I.subtype_injective
  let F : Fin 2 → Subgroup (Gstar z v) := Fin.cases (c.first.map I.subtype)
    (fun _ => c.second.map I.subtype)
  have hres : (pResidual 2 I).map I.subtype = X := by
    rw [← hF, map_subgroupOf_eq_of_le
      (XFamily_le_star_offender L T z v (A5Module.markedZ_mem_Gv s) S hS hX.1)]
  refine ⟨{
    H := I
    normal := inferInstance
    count := 2
    count_pos := by decide
    count_le_two := le_rfl
    factor := F
    factor_le := ?_
    model := Fin.cases (i₁.symm.trans e₁) (fun _ => i₂.symm.trans e₂)
    product := (twoCoordinates (fun i => F i)).trans
      ((i₁.symm.prodCongr i₂.symm).trans c.product.equiv)
    product_single := ?_
    residual_eq := hres
    thompson_eq := minimalSolvable_twoFactor_thompson L T z v
      (A5Module.markedZ_mem_Gv s) S hS hX c e₁ e₂ hF
    space := (twoCoordinates (fun i => factorSupport z v I (F i))).trans
      (Supports.twoFactor_supportProduct z v c e₁ e₂)
    space_single := ?_
    support_card := ?_ }⟩
  · intro i
    fin_cases i <;> exact map_subtype_le _
  · apply coordinateProduct_single F I
      ((i₁.symm.prodCongr i₂.symm).trans c.product.equiv)
    intro a b
    change ((c.product.equiv (i₁.symm a, i₂.symm b) : I) : Gstar z v) = _
    rw [c.product.apply_eq]
    change ((i₁ (i₁.symm a) : c.first.map I.subtype) : Gstar z v) *
      ((i₂ (i₂.symm b) : c.second.map I.subtype) : Gstar z v) = _
    rw [i₁.apply_symm_apply, i₂.apply_symm_apply]
  · exact coordinateProduct_single (fun i => factorSupport z v I (F i))
      (movedSubgroup z v I) (Supports.twoFactor_supportProduct z v c e₁ e₂)
      (Supports.twoFactor_supportProduct_apply z v c e₁ e₂)
  · intro i
    fin_cases i
    · exact Supports.twoFactor_support_card z v c e₁ e₂ c.first (Or.inl rfl)
    · exact Supports.twoFactor_support_card z v c e₁ e₂ c.second (Or.inr rfl)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Products
