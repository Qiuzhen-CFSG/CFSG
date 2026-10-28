module

public import CFSG.Quasithin.ChapterG.Section06.SourceClassification.TwoFactorModelComparison
public import Theory.Representation.BinaryPermutation.FiveCentralExtension
public import Theory.GroupTheory.DisjointCommutingProduct

/-!
# Disjoint moved spaces in the paired S₅ row

The cross-commutator clause makes the first factor fix every vector in the
intersection of the two moved spaces.  Its natural five-letter module has no
S₅-fixed vector, so the intersection is zero.  This is the first concrete
bridge from the literal G.6 `TwoFactors` data toward a paired wreath action.

Source: Aschbacher--Smith G.6.4(3)(ii), pp.345--346.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterG.Section06
noncomputable section
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {a : G}

private theorem paired_five_natural_fixed_eq_zero (x : BinaryPermutation.natural (Fin 5))
    (hx : ∀ g : Equiv.Perm (Fin 5), BinaryPermutation.naturalRepresentation (Fin 5) g x = x) : x = 0 := by
  let y : BinaryPermutation.core (Fin 5) :=
    (BinaryPermutation.coreEquivNatural (Fin 5) (by decide)).symm x
  have hy (g : Equiv.Perm (Fin 5)) :
      BinaryPermutation.coreRepresentation (Fin 5) g y = y := by
    apply (BinaryPermutation.coreEquivNatural (Fin 5) (by decide)).injective
    rw [BinaryPermutation.coreEquivNatural_equivariant]
    simpa only [y, LinearEquiv.apply_symm_apply] using hx g
  have hs := BinaryPermutation.FiveCentralExtension.core_sum y
  have hsum : (∑ g ∈ BinaryPermutation.FiveCentralExtension.cubes,
      BinaryPermutation.coreRepresentation (Fin 5) g y) = 0 := by
    calc
      _ = ∑ g ∈ BinaryPermutation.FiveCentralExtension.cubes, y := by
        apply Finset.sum_congr rfl
        intro g hg
        rw [hy]
      _ = 20 • y := by
        rw [Finset.sum_const, BinaryPermutation.FiveCentralExtension.cubes_card]
      _ = 0 := by
        rw [← Nat.cast_smul_eq_nsmul (R := ZMod 2)]
        change (20 : ZMod 2) • y = 0
        have h20 : (20 : ZMod 2) = 0 := by decide
        rw [h20, zero_smul]
  rw [hsum] at hs
  have hy0 : y = 0 := hs.symm
  have hxy : (BinaryPermutation.coreEquivNatural (Fin 5) (by decide)) y =
      (BinaryPermutation.coreEquivNatural (Fin 5) (by decide)) 0 := congrArg _ hy0
  simpa only [y, LinearEquiv.apply_symm_apply, map_zero] using hxy

theorem TwoFactors.paired_five_spaces_disjoint (d : TwoFactors ρ a)
    (h₁ : HasModelOn ρ d.first (subspaceCommutator ρ ⊤ d.first)
      (BinaryPermutation.naturalRepresentation (Fin 5))) :
    Disjoint (subspaceCommutator ρ ⊤ d.first)
      (subspaceCommutator ρ ⊤ d.second) := by
  obtain ⟨e, E, hs, he⟩ := h₁
  apply disjoint_iff.mpr
  apply bot_unique
  rintro v ⟨h₁v, h₂v⟩
  have hvfix (k : d.first) : ρ k v = v := by
    apply sub_eq_zero.mp
    apply d.cross_first.le
    exact Submodule.subset_span ⟨k, k.property, v, h₂v, rfl⟩
  have hx : ∀ g : Equiv.Perm (Fin 5),
      BinaryPermutation.naturalRepresentation (Fin 5) g (E ⟨v,h₁v⟩) = E ⟨v,h₁v⟩ := by
    intro g
    obtain ⟨k, rfl⟩ := e.surjective g
    have hh := he k ⟨v,h₁v⟩
    have hk : (⟨ρ k v, hs k ⟨v,h₁v⟩⟩ : subspaceCommutator ρ ⊤ d.first) =
        ⟨v,h₁v⟩ := Subtype.ext (hvfix k)
    rw [hk] at hh
    exact hh.symm
  have hz : E ⟨v,h₁v⟩ = 0 := paired_five_natural_fixed_eq_zero _ hx
  have hz' : (⟨v,h₁v⟩ : subspaceCommutator ρ ⊤ d.first) = 0 :=
    E.injective (hz.trans E.map_zero.symm)
  exact congrArg Subtype.val hz'

theorem TwoFactors.paired_five_spaces_isCompl (d : TwoFactors ρ a)
    (h₁ : HasModelOn ρ d.first (subspaceCommutator ρ ⊤ d.first)
      (BinaryPermutation.naturalRepresentation (Fin 5))) :
    IsCompl (subspaceCommutator ρ ⊤ d.first)
      (subspaceCommutator ρ ⊤ d.second) := by
  exact ⟨d.paired_five_spaces_disjoint h₁, codisjoint_iff.mpr d.space_sum⟩

theorem TwoFactors.exists_paired_five_product_equiv (d : TwoFactors ρ a) :
    ∃ e : d.first × d.second ≃* ↥(normalClosure ({a} : Set G)),
      ∀ x y, (e (x, y) : G) = (x : G) * (y : G) := by
  have hdis : Disjoint d.first d.second := disjoint_iff.mpr d.disjoint
  have hcomm : d.first ≤ centralizer (d.second : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp d.commute
  obtain ⟨e, he⟩ := Subgroup.exists_mulEquiv_prod_sup_of_disjoint_of_commuting
    d.first d.second hdis hcomm
  let e' : ↥(d.first ⊔ d.second) ≃* ↥(normalClosure ({a} : Set G)) :=
    MulEquiv.subgroupCongr d.join_eq
  refine ⟨e.trans e', ?_⟩
  intro x y
  change (e (x, y) : G) = (x : G) * (y : G)
  exact he x y

end
end CFSG.Quasithin.ChapterG.Section06
