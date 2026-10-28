module

public import Stellmacher.SectionOne.OneSevenGlobalProduct
public import Stellmacher.SectionOne.SelectedProductIrreducibleSupport

/-!
# The global canonical derived product is elementary abelian

Under the genuine Section One action hypotheses, the derived subgroup of
the full canonical factor product is elementary abelian at three. The
proved global factor theorem supplies an internal product of the actual
canonical SL₂(2) factors. Enumerating that finite family transports the
product to the existing finite-family theorem, whose proof uses the
order-three derived subgroup in each coordinate.

This exposes the elementary consequence of (1.7) needed after identifying
the geometric residual with this derived product in Stellmacher (9.10)(3),
printed p.57 of `refs/files/stellmacher-n-group.pdf`. It also applies when
the canonical factor family is empty.
-/

namespace Stellmacher.SectionOne

universe u

public theorem oneSeven_derived_isElementaryAbelian
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (hyp : Hypotheses G V) :
    IsElementaryAbelian 3
      ((commutator (oneSevenGenerated (G := G) (V := V))).map
        (oneSevenGenerated (G := G) (V := V)).subtype) := by
  classical
  let F := oneSevenFactors (G := G) (V := V)
  let E := oneSevenGenerated (G := G) (V := V)
  let sylow : Sylow 2 G := default
  obtain ⟨_, hproduct, _⟩ := oneSeven_global_product hyp sylow
  let I := {factor : Subgroup G // factor ∈ F}
  let n := Fintype.card I
  let enumeration : Fin n ≃ I := (Fintype.equivFin I).symm
  let D : Fin n → Subgroup G := fun i => (enumeration i).val
  have hDi (i : Fin n) : D i ∈ F := (enumeration i).property
  have hfactor (i : Fin n) : IsOneSevenFactor (V := V) (D i) :=
    (mem_oneSevenFactors_iff (D i)).mp (hDi i)
  have hinjective : Function.Injective D := by
    intro i j heq
    exact enumeration.injective (Subtype.ext heq)
  have hgen : E = ⨆ i : Fin n, D i := by
    change oneSevenGenerated (G := G) (V := V) = _
    rw [hproduct.1]
    apply le_antisymm
    · apply iSup_le
      intro factor
      obtain ⟨i, rfl⟩ := enumeration.surjective factor
      exact le_iSup D i
    · exact iSup_le fun i => le_iSup (fun factor : I => (factor : Subgroup G))
        (enumeration i)
  have hfamily : IsInternalDirectProductFamily E D := by
    refine ⟨hgen, ?_, ?_⟩
    · intro i j hij
      exact hproduct.2.2.1 (D i) (hDi i) (D j) (hDi j)
        (fun heq => hij (hinjective heq))
    · intro i j hij
      exact hproduct.2.2.2 (D i) (hDi i) (D j) (hDi j)
        (fun heq => hij (hinjective heq))
  exact internalOneSevenProduct_derived_isElementaryAbelian E D hfamily hfactor

end Stellmacher.SectionOne
