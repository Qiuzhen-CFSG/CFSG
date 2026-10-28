module

public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.Coordinates
public import Theory.Representation.SymplecticFourOrthogonalCover.Universal
public import Theory.Representation.TwoDimensionalOddOrder
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# The unique flag of a Sylow subgroup of the genuine derived symplectic group

Intersect the literal standard unipotent Sylow with Sp₄(K)′. Two paired
positive-root products are explicit commutators, even over F₂. Their coordinate
actions recover the fixed line and the fixed plane modulo that line. The
fixed-vector theorem for two-groups then proves uniqueness among invariant
one- and two-spaces. Thus the binary endpoint needs no full-group transvection.

Source: Aschbacher–Smith, I.2.3, printed p.413 / PDF p.424.
The invariant-subspace argument follows the existing G₂ cover's
`SylowFlag/Uniqueness` proof, specialized to these actual matrix calculations.
-/

@[expose] public section

noncomputable section
open Matrix Subgroup
open Representation.OneCohomology
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
open Representation.OneCohomology.SymplecticFour
open Theory.SpecificGroups.SymplecticFour
open scoped commutatorElement
namespace Representation.SymplecticFourOrthogonalCover.SylowFlag
variable {K : Type*} [Field K] [Finite K] [CharP K 2]

def standard : Subgroup (L (K := K)) := (unipotent (F := K)).subgroupOf (commutator (Sp K))

private lemma root_inv (r : Fin 8) (t : K) : (rootElement r t)⁻¹ = rootElement r t := by
  apply inv_eq_of_mul_eq_one_right
  rw [RootSubgroup.element_add, CharTwo.add_self_eq_zero, RootSubgroup.element_zero]

private def swapMatrix (i : Fin 2) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  ![fromBlocks !![0,1;1,0] 0 0 !![0,1;1,0],
    fromBlocks !![1,0;0,0] !![0,0;0,1] !![0,0;0,1] !![1,0;0,0]] i

private def swapHalf (i : Fin 2) : Sp K := ⟨swapMatrix i, by
  rw [SymplecticGroup.mem_iff]
  fin_cases i <;> ext a b <;>
    rcases a with a | a <;> rcases b with b | b <;> fin_cases a <;> fin_cases b <;>
    simp [swapMatrix, Matrix.J, Matrix.mul_apply, Matrix.fromBlocks,
      Matrix.one_apply, Fintype.sum_sum_type, Fin.sum_univ_two, CharTwo.neg_eq]⟩

private lemma swap_conjugates (i : Fin 2) (t : K) :
    swapHalf (K := K) i * rootElement (![0,4] i) t =
      rootElement (![2,6] i) t * swapHalf i := by
  apply Subtype.ext
  change swapMatrix i * rootMatrix (![0,4] i) t = rootMatrix (![2,6] i) t * swapMatrix i
  fin_cases i <;> ext a b <;>
    rcases a with a | a <;> rcases b with b | b <;> fin_cases a <;> fin_cases b <;>
    simp [swapMatrix, rootMatrix, Matrix.mul_apply, Matrix.fromBlocks,
      Matrix.single, Matrix.one_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
      CharTwo.neg_eq, CharTwo.add_self_eq_zero]

lemma paired_roots_derived (i : Fin 2) (t : K) :
    rootElement (![0,4] i) t * rootElement (![2,6] i) t ∈ commutator (Sp K) := by
  have h := Subgroup.commutator_mem_commutator
    (G := Sp K) (Subgroup.mem_top (rootElement (![0,4] i) t))
    (Subgroup.mem_top (swapHalf (K := K) i))
  have he : ⁅rootElement (![0,4] i) t, swapHalf (K := K) i⁆ =
      rootElement (![0,4] i) t * rootElement (![2,6] i) t := by
    simp only [commutatorElement_def, root_inv]
    calc
      _ = rootElement (![0,4] i) t *
          (swapHalf i * rootElement (![0,4] i) t) * (swapHalf i)⁻¹ := by group
      _ = _ := by rw [swap_conjugates]; group
  rw [he] at h
  exact h

def pairedRoot (i : Fin 2) (t : K) : standard (K := K) :=
  ⟨⟨_, paired_roots_derived i t⟩, by
    fin_cases i <;> exact (unipotent (F := K)).mul_mem
      (positive_root_mem_unipotent _ t (by simp)) (positive_root_mem_unipotent _ t (by simp))⟩

lemma firstLine_eq_point : firstLine (K := K) = point K := rfl

lemma secondPlane_eq_plane : secondPlane (K := K) = plane K := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro x hx
    rcases hx with rfl | hx
    · exact e_mem_plane 0
    · rw [Set.mem_singleton_iff] at hx
      subst x
      exact e_mem_plane 1
  · intro x hx
    rw [plane_decomposition x hx]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp [secondPlane, e, ClassicalOrthogonal.e])))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp [secondPlane, e, ClassicalOrthogonal.e])))

lemma natural_fixed :
    fixed ((symplecticDerivedNatural (k := K) 2).comp (standard (K := K)).subtype) = firstLine := by
  ext x
  constructor
  · intro hx
    have h0 := hx (pairedRoot 0 1)
    have h1 := hx (pairedRoot 1 1)
    have hc := congrFun h0 (.inl 0)
    have hd := congrFun h0 (.inl 1)
    have hb := congrFun h1 (.inl 0)
    simp [pairedRoot, symplecticDerivedNatural_apply, rootElement, rootMatrix,
      Matrix.mulVec_mulVec, Matrix.mulVec, dotProduct, Matrix.mul_apply,
      Fintype.sum_sum_type, Fin.sum_univ_two, Matrix.fromBlocks, Matrix.single,
      Matrix.one_apply, CharTwo.neg_eq] at hc hd hb
    rw [firstLine_eq_point, mem_point_iff]
    refine ⟨?_, ?_⟩
    · simpa [hc, hd] using hb
    · intro i
      fin_cases i <;> assumption
  · intro hx g
    exact unipotent_fixes_point g.property hx

lemma fixedModulo_firstLine (x : Natural (K := K)) :
    (∀ g : standard (K := K), symplecticDerivedNatural 2 g.val x - x ∈ firstLine) ↔
      x ∈ secondPlane := by
  constructor
  · intro h
    have h0 := (mem_point_iff _).mp (h (pairedRoot 0 1)) |>.1
    have h1 := (mem_point_iff _).mp (h (pairedRoot 1 1)) |>.1
    simp [pairedRoot, symplecticDerivedNatural_apply, rootElement, rootMatrix,
      Matrix.mulVec_mulVec, Matrix.mulVec, dotProduct, Matrix.mul_apply,
      Fintype.sum_sum_type, Fin.sum_univ_two, Matrix.fromBlocks, Matrix.single,
      Matrix.one_apply, CharTwo.neg_eq] at h0 h1
    rw [secondPlane_eq_plane]
    intro i
    fin_cases i <;> assumption
  · intro hx g
    exact unipotent_trivial_on_plane_mod_point g.property ((secondPlane_eq_plane (K := K)) ▸ hx)

lemma exists_standardSylow : ∃ S : Sylow 2 (L (K := K)),
    (S : Subgroup (L (K := K))) = standard := by
  let := Fintype.ofFinite K
  obtain ⟨n, _, hn⟩ := FiniteField.card K 2
  exact (unipotentSylow (by simpa only [Nat.card_eq_fintype_card] using hn)
    n.pos).exists_subgroupOf_eq_of_normal (commutator (Sp K))

noncomputable def standardSylow : Sylow 2 (L (K := K)) :=
  Classical.choose (exists_standardSylow (K := K))

lemma standardSylow_coe : (standardSylow (K := K) : Subgroup (L (K := K))) = standard :=
  Classical.choose_spec exists_standardSylow

lemma standard_isTwoGroup : IsPGroup 2 (standard (K := K)) := by
  rw [← standardSylow_coe]
  exact standardSylow.isPGroup'

lemma firstLine_finrank : Module.finrank K (firstLine (K := K)) = 1 := finrank_point

lemma secondPlane_finrank : Module.finrank K (secondPlane (K := K)) = 2 := by
  rw [secondPlane_eq_plane]
  exact finrank_plane

lemma firstLine_invariant (g : standard (K := K)) :
    firstLine ≤ firstLine.comap (symplecticDerivedNatural 2 g.val) := by
  intro x hx
  change symplecticDerivedNatural 2 g.val x ∈ firstLine
  rw [show symplecticDerivedNatural 2 g.val x = x from unipotent_fixes_point g.property hx]
  exact hx

lemma secondPlane_invariant (g : standard (K := K)) :
    secondPlane ≤ secondPlane.comap (symplecticDerivedNatural 2 g.val) := by
  intro x hx
  rw [secondPlane_eq_plane] at hx ⊢
  exact (mem_stabilizer_iff (plane K) g.val.val).mp
    (unipotent_le_borel g.property).2 x hx

private lemma pGroup_fixed_vector
    {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Nontrivial V]
    (hp : IsPGroup 2 G) (ρ : Representation K G V) :
    ∃ v : V, v ≠ 0 ∧ ∀ g : G, ρ g v = v :=
  pGroup_fix_nonzero_vector (by rw [ringChar.eq K 2]; decide)
    (by simpa only [ringChar.eq K 2] using hp) ρ

private lemma pGroup_line_trivial
    {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (hp : IsPGroup 2 G) (ρ : Representation K G V)
    (hdim : Module.finrank K V = 1) : ∀ g v, ρ g v = v := by
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (by omega : 0 < Module.finrank K V)
  obtain ⟨x, hx, hfix⟩ := pGroup_fixed_vector hp ρ
  intro g v
  obtain ⟨a, rfl⟩ := (finrank_eq_one_iff_of_nonzero' x hx).mp hdim v
  rw [map_smul, hfix]

lemma firstLine_le_of_invariant (W : Submodule K (Natural (K := K)))
    (hW : ∀ g : standard (K := K), W ≤ W.comap (symplecticDerivedNatural 2 g.val))
    (hne : W ≠ ⊥) : firstLine ≤ W := by
  let σ := Representation.subrepresentation
    ((symplecticDerivedNatural (k := K) 2).comp (standard (K := K)).subtype) W hW
  have : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hne
  obtain ⟨x, hx, hfix⟩ := pGroup_fixed_vector (V := W) (G := standard (K := K)) standard_isTwoGroup σ
  have hxf : x.val ∈ firstLine (K := K) := by
    rw [← natural_fixed]
    intro g
    exact congrArg Subtype.val (hfix g)
  have hx0 : x.val ≠ 0 := fun h => hx (Subtype.ext h)
  have he : firstLine (K := K) = K ∙ x.val :=
    eq_span_singleton_of_mem_of_finrank_eq_one (firstLine_finrank (K := K)) hxf hx0
  rw [he]
  exact (Submodule.span_singleton_le_iff_mem _ _).mpr x.property

lemma invariant_line_unique (W : Submodule K (Natural (K := K)))
    (hW : ∀ g : standard (K := K), W ≤ W.comap (symplecticDerivedNatural 2 g.val))
    (hdim : Module.finrank K W = 1) : W = firstLine := by
  symm
  apply Submodule.eq_of_le_of_finrank_eq
  · apply firstLine_le_of_invariant W hW
    intro h
    have hz : Module.finrank K W = 0 := by rw [h, finrank_bot]
    omega
  · rw [firstLine_finrank, hdim]

lemma invariant_plane_unique (W : Submodule K (Natural (K := K)))
    (hW : ∀ g : standard (K := K), W ≤ W.comap (symplecticDerivedNatural 2 g.val))
    (hdim : Module.finrank K W = 2) : W = secondPlane := by
  have hle : firstLine ≤ W := firstLine_le_of_invariant W hW (by
    intro h
    have hz : Module.finrank K W = 0 := by rw [h, finrank_bot]
    omega)
  let σ := Representation.subrepresentation
    ((symplecticDerivedNatural (k := K) 2).comp (standard (K := K)).subtype) W hW
  let A : Submodule K W := (firstLine (K := K)).comap W.subtype
  have hA (g : standard (K := K)) : A ≤ A.comap (σ g) := by
    intro x hx
    exact firstLine_invariant g hx
  have hAdim : Module.finrank K A = 1 :=
    (Submodule.comapSubtypeEquivOfLe hle).finrank_eq.trans firstLine_finrank
  have hquot : Module.finrank K (W ⧸ A) = 1 := by
    have h := A.finrank_quotient_add_finrank
    rw [hAdim, hdim] at h
    omega
  have htriv := pGroup_line_trivial standard_isTwoGroup (Representation.quotient σ A hA) hquot
  apply Submodule.eq_of_le_of_finrank_eq _ (hdim.trans secondPlane_finrank.symm)
  intro x hx
  apply (fixedModulo_firstLine x).mp
  intro g
  have he := htriv g (A.mkQ ⟨x,hx⟩)
  change A.mkQ (σ g ⟨x,hx⟩) = A.mkQ ⟨x,hx⟩ at he
  rw [← sub_eq_zero, ← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at he
  exact he


end Representation.SymplecticFourOrthogonalCover.SylowFlag
