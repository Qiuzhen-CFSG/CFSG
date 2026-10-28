module
public import Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.EightCells
import Mathlib.Tactic.Group

/-!
# Kernels and full Borel images from marked Bruhat cells

An onto homomorphism carrying the model Borel into the source Borel and
carrying nonidentity Weyl words outside it has exactly the model Borel as
its Borel preimage. In particular its kernel is Borel-contained, and its
image contains the WHOLE source Borel. The model Bruhat theorem and source
Weyl quotient discharge these premises in the unitary applications.
Source: Steinberg, Lectures on Chevalley Groups, Theorem 4(b); DGS,
Groups and Graphs, Theorem D, printed p.224.
-/
@[expose] public section
namespace Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation
open Subgroup
variable {M Y : Type*} [Group M] [Group Y]

/-- A marked Weyl separation argument recovers the entire Borel preimage. -/
theorem borel_comap_of_cells (f : M →* Y) (B : Subgroup M) (B' : Subgroup Y)
    (s t : M) (hcell : ∀ g, ∃ w : WeylWord, InCell B (w.eval s t) g)
    (hB : B≤B'.comap f)
    (hw : ∀ w : WeylWord, f (w.eval s t)∈B' → w=.one) : B'.comap f=B := by
  apply le_antisymm _ hB
  intro g hg
  obtain ⟨w,l,hl,v,hv,he⟩ := hcell g
  have hn : f (w.eval s t)∈B' := by
    have hh : w.eval s t=l⁻¹*g*v⁻¹ := by rw [he]; group
    rw [hh,map_mul,map_mul,map_inv,map_inv]
    exact B'.mul_mem (B'.mul_mem (B'.inv_mem (hB hl)) hg) (B'.inv_mem (hB hv))
  have hew := hw w hn
  subst w
  exact InCell.mem_of_one ⟨l,hl,v,hv,he⟩

/-- Normality can now trap the kernel in the model Borel normal core. -/
theorem kernel_le_borel_of_cells (f : M →* Y) (B : Subgroup M) (B' : Subgroup Y)
    (s t : M) (hcell : ∀ g, ∃ w : WeylWord, InCell B (w.eval s t) g)
    (hB : B≤B'.comap f)
    (hw : ∀ w : WeylWord, f (w.eval s t)∈B' → w=.one) : f.ker≤B := by
  rw [←borel_comap_of_cells f B B' s t hcell hB hw]
  intro g hg
  change f g∈B'
  rw [show f g=1 from hg]
  exact B'.one_mem

/-- Surjectivity upgrades Borel containment to equality without any extra
Cartan-surjectivity hypothesis. -/
theorem borel_map_of_cells (f : M →* Y) (hf : Function.Surjective f)
    (B : Subgroup M) (B' : Subgroup Y) (s t : M)
    (hcell : ∀ g, ∃ w : WeylWord, InCell B (w.eval s t) g)
    (hB : B≤B'.comap f)
    (hw : ∀ w : WeylWord, f (w.eval s t)∈B' → w=.one) : B.map f=B' := by
  rw [←borel_comap_of_cells f B B' s t hcell hB hw]
  exact Subgroup.map_comap_eq_self_of_surjective hf B'
end Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation
