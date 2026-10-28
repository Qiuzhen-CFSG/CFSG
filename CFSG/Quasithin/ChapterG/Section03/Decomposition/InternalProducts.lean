module

public import CFSG.Quasithin.ChapterG.Section03.Decomposition.OrbitGeometry
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.GroupTheory.NoncommPiCoprod

/-!
# Independence and internal products for the orbit factors

Full linear action in dimension at least two has no nonzero common fixed
vector. Since a block group fixes all other block spans, its own span meets
the sum of the others trivially. An element in the corresponding intersection
of group factors has every displacement in both disjoint spans, so is the
identity on the ambient space.

The multiplication and summation maps now give the actual internal product
and direct-sum equivalences. Finiteness of the orbit index identifies the
vector-space direct sum with the full product. Both equivalences preserve
every canonical factor inclusion.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, proof of G.3.1(1), printed p. 337 (PDF p. 348).
-/

@[expose] public section

open BinaryLinear BinaryTransvectionGroups
namespace CFSG.Quasithin.ChapterG.Section03.DecompositionProof
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
variable {G : Subgroup (GL V)}

private theorem linear_move {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ e : GL V, e x = y := by
  let d := (LinearEquiv.coord (ZMod 2) V x hx).trans
    (LinearEquiv.coord (ZMod 2) V y hy).symm
  obtain ⟨e, he⟩ := Submodule.exists_linearEquiv_restrict_eq d
  refine ⟨e, ?_⟩
  have hh := he ⟨x, Submodule.mem_span_singleton_self x⟩
  have hd : d ⟨x, Submodule.mem_span_singleton_self x⟩ =
      ⟨y, Submodule.mem_span_singleton_self y⟩ := by
    apply (LinearEquiv.coord (ZMod 2) V y hy).injective
    simp [d, LinearEquiv.coord_self]
  rw [hd] at hh
  exact hh.symm

private theorem fixed_by_full_linear_group (hdim : 2 ≤ Module.finrank (ZMod 2) V)
    (x : V) (hx : ∀ e : GL V, e x = x) : x = 0 := by
  by_contra hx0
  have hd : Module.finrank (ZMod 2) V ≤ 1 := by
    apply finrank_le_one (R := ZMod 2) x
    intro y
    by_cases hy0 : y = 0
    · exact ⟨0, by simp [hy0]⟩
    · obtain ⟨e, he⟩ := linear_move hx0 hy0
      exact ⟨1, by rw [one_smul, ← he, hx]⟩
  omega

theorem block_fixed_zero {Δ : Set V} (hfull : FullAction G Δ)
    (i : OrbitBlock G Δ) (v : blockSpace G Δ i)
    (hv : ∀ g ∈ blockGroup G Δ i, g v.val = v.val) : v = 0 := by
  apply fixed_by_full_linear_group (hfull.dimension_ge_two i)
  intro e
  obtain ⟨g, rfl⟩ := hfull.surjective i e
  apply Subtype.ext
  exact hv g.val g.property

theorem blocks_space_independent [Finite G] {Δ : Set V} (h : Hypotheses G Δ)
    (hfull : FullAction G Δ) : iSupIndep (blockSpace G Δ) := by
  intro i
  apply Submodule.disjoint_def.mpr
  intro v hvi hvj
  have hfix : (⨆ (j : OrbitBlock G Δ) (_ : j ≠ i), blockSpace G Δ j) ≤
      fixedSpace (blockGroup G Δ i) := by
    apply iSup_le
    intro j
    apply iSup_le
    intro hj w hw g hg
    exact blocks_cross_fix h hj.symm g hg w hw
  have hh := block_fixed_zero hfull i ⟨v, hvi⟩ (hfix hvj)
  exact congrArg Subtype.val hh

theorem blocks_group_independent {Δ : Set V}
    (hspace : iSupIndep (blockSpace G Δ)) : iSupIndep (blockGroup G Δ) := by
  intro i
  apply disjoint_iff.mpr
  apply le_antisymm _ bot_le
  intro g hg
  apply Subgroup.mem_bot.mpr
  ext v
  apply sub_eq_zero.mp
  have hvi : g v - v ∈ blockSpace G Δ i := generated_le_quotientFixer G i.val hg.1 v
  have ho : (⨆ (j : OrbitBlock G Δ) (_ : j ≠ i), blockGroup G Δ j) ≤
      quotientFixer (⨆ (j : OrbitBlock G Δ) (_ : j ≠ i), blockSpace G Δ j) := by
    apply iSup_le
    intro j
    apply iSup_le
    intro hj k hk w
    have hle : blockSpace G Δ j ≤
        ⨆ (k : OrbitBlock G Δ) (_ : k ≠ i), blockSpace G Δ k :=
      le_iSup_of_le j (le_iSup_of_le hj le_rfl)
    exact hle (generated_le_quotientFixer G j.val hk w)
  exact (Submodule.disjoint_def.mp (hspace i)) _ hvi (ho hg.2 v)

theorem blocks_group_equiv [Finite G] {Δ : Set V} (h : Hypotheses G Δ)
    (hspace : iSupIndep (blockSpace G Δ)) :
    ∃ e : (∀ i : OrbitBlock G Δ, blockGroup G Δ i) ≃* generated G Δ,
      ∀ i g, (e (singleGroupElement i g) : GL V) = (g : GL V) := by
  classical
  let : Finite (OrbitBlock G Δ) := finite_blocks h
  let : Fintype (OrbitBlock G Δ) := Fintype.ofFinite _
  let hc : Pairwise fun i j : OrbitBlock G Δ =>
      ∀ x y : GL V, x ∈ blockGroup G Δ i → y ∈ blockGroup G Δ j → Commute x y :=
    fun _ _ hij x y hx hy => blocks_commute h hij x hx y hy
  let f := Subgroup.noncommPiCoprod hc
  have hf : f.range = generated G Δ :=
    Subgroup.noncommPiCoprod_range.trans (blocks_join h)
  let e := (MonoidHom.ofInjective
    (Subgroup.injective_noncommPiCoprod_of_iSupIndep (hcomm := hc)
      (blocks_group_independent hspace))).trans (MulEquiv.subgroupCongr hf)
  refine ⟨e, ?_⟩
  intro i g
  exact Subgroup.noncommPiCoprod_mulSingle (hcomm := hc) i g

theorem blocks_space_equiv [Finite G] {Δ : Set V} (h : Hypotheses G Δ)
    (hind : iSupIndep (blockSpace G Δ)) :
    ∃ e : (∀ i : OrbitBlock G Δ, blockSpace G Δ i) ≃ₗ[ZMod 2]
        Submodule.span (ZMod 2) Δ,
      ∀ i v, (e (singleSpaceElement i v) : V) = (v : V) := by
  classical
  let : Finite (OrbitBlock G Δ) := finite_blocks h
  let : Fintype (OrbitBlock G Δ) := Fintype.ofFinite _
  let f : (Π₀ i : OrbitBlock G Δ, blockSpace G Δ i) →ₗ[ZMod 2] V :=
    DFinsupp.lsum ℕ (fun i => (blockSpace G Δ i).subtype)
  have hf : f.range = Submodule.span (ZMod 2) Δ :=
    (Submodule.iSup_eq_range_dfinsupp_lsum _).symm.trans (blocks_span h)
  let e := (DFinsupp.linearEquivFunOnFintype (R := ZMod 2)
    (M := fun i : OrbitBlock G Δ => blockSpace G Δ i)).symm.trans
      ((LinearEquiv.ofInjective f hind.dfinsupp_lsum_injective).trans
        (LinearEquiv.ofEq _ _ hf))
  refine ⟨e, ?_⟩
  intro i v
  change f (DFinsupp.equivFunOnFintype.symm (Pi.single i v)) = v.val
  rw [DFinsupp.equivFunOnFintype_symm_single]
  exact DFinsupp.lsum_single (S := ℕ) (fun j => (blockSpace G Δ j).subtype) i v

end CFSG.Quasithin.ChapterG.Section03.DecompositionProof
