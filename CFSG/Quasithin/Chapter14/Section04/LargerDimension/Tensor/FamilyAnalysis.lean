module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.FamilyAnalysis.FullMovement
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.FamilyAnalysis.FiniteImages
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.FamilyAnalysis.Constituents

/-!
# Common tensor calculations for Lemma 14.4.10

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, printed
pp.1010–1011, under case 14.4.2(5) on printed p.1006.

The exported coordinates distinguish the natural SL₂(4) and deleted A₅
constituents and retain H/O₂(H), U/Z(U), and the literal conjugation maps.
The finite actor classification proves X = {X₁,X₂}, with distinct members,
and identifies the actual component image as 1 × A₅. This discharges the
marking premise of the constituent construction: a nonidentity element of
the rank-three Wᵍ* centralizing that component selects the unique
T-invariant irreducible constituent and its cubic-translate complement.

For both source constituents, the canonical extraspecial form and the
complement intersection calculation put the first moved plane in Ẽ.
The central-kernel lift proves actual order eight and containment in E,
so X₁ ∈ Y. In particular, order eight is not inferred from quotient
dimension alone. All quotient maps and conjugation conventions are those
of the published CaseFiveCoordinates and EarlierGeometry.

The input boundary is the tensor case 14.4.2(5), extraspeciality, and the
precise earlier 12.8/14.3 facts in EarlierGeometry (including U = O₂(H)
from 14.4.7). There is no family, constituent, Borel, component marking,
form or moved-space premise. The source owner retains the genuine ambient
Hypothesis 14.3.10: Hypothesis 14.3.1, H = G₁ = N_G(V₁), and the
nonabelian closure U = ⟨V^G₁⟩. These local deductions do not purport to
construct that ambient configuration or prove its earlier source facts.
The all-five-clause assembly, including the natural/A₅ branch distinction,
belongs to Tensor.
-/

public section

open Subgroup TensorProduct Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.CaseFiveCoordinates

variable {G : Type*} [Group G] [Finite G]
  {D : Subgroup Five} {hAD : AltFive ≤ D}
  {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  {H U T P : Subgroup G} {g : G}
  (c : CaseFiveCoordinates hAD (V := V) H U)

/-- The actual marked component image, with no additional model premise. -/
theorem actorImage_component :
    c.actorImage (component H) = (⊥ : Subgroup Three).prod (AltFive.subgroupOf D) :=
  star_component_marked hAD c.actor

/-- Clause (1): classify all actual family members using the earlier Sylow
witness and the actor isomorphism from case (5). -/
theorem EarlierGeometry.family_eq_pair
    (h : c.EarlierGeometry T P g) :
    XFamily H T = {first H, second H T} ∧ first H ≠ second H T := by
  obtain ⟨S, hS⟩ := h.sylow
  exact family_eq_pair_of_model S hS c.actor_models

/-- Both named residual subgroups satisfy the literal X-conditions. -/
theorem EarlierGeometry.first_second_mem_X
    (h : c.EarlierGeometry T P g) :
    first H ∈ XFamily H T ∧ second H T ∈ XFamily H T := by
  obtain ⟨S, hS⟩ := h.sylow
  have hX := first_second_mem_X_and_distinct S hS c.actor_models
  exact ⟨hX.1, hX.2.1⟩

/-- Clause (2): existence and uniqueness with the independently proved
component marking discharged. Irreducibility is for the actual K₀ action. -/
theorem EarlierGeometry.unique_invariant_constituent
    (h : c.EarlierGeometry T P g) :
    ∃! M : Submodule (ZMod 2) (BinaryPermutation.core (Fin 3) ⊗[ZMod 2] V),
      c.IsIrreducibleFor (component H) M ∧
        c.actorImage T ≤ subspaceStabilizer (sourceTensorAction c.constituent) M :=
  h.exists_unique_T_invariant_constituent c c.actorImage_component

variable [IsExtraspecial 2 U]

/-- The source element, displacement constituent, complement, and both
intersection inequalities, all for the same constructed choice. The
SelectedConstituent also retains Ṽ₂ ≤ C_Ũ(T) ≤ Ũ₁, uniqueness and the
equivariant identification with either specified four-dimensional model. -/
theorem EarlierGeometry.constituent_geometry
    (h : c.EarlierGeometry T P g) :
    ∃ s : c.SelectedConstituent T P g,
      c.image (centralLayer U P) = (c.image P).orthogonalBilin c.canonicalForm.form ∧
      c.image (movedSpace P (first H)) = c.image P ⊔
        (c.image (movedSpace P (first H)) ⊓ s.secondSpace) ∧
      c.image (movedSpace P (first H)) ⊓ s.secondSpace ≤
        subspaceCommutator (sourceTensorAction c.constituent)
          (c.image (centralLayer U P) ⊓ s.secondSpace)
          (c.actorImage (conjugateLayer U P g) ⊓ c.actorImage (component H)) ∧
      subspaceCommutator (sourceTensorAction c.constituent)
        (c.image (centralLayer U P) ⊓ s.secondSpace)
        (c.actorImage (conjugateLayer U P g) ⊓ c.actorImage (component H)) ≤
          c.image (intersectionLayer U P g) :=
  h.exists_constituent_geometry c c.actorImage_component

/-- The actual quotient moved plane has order four and lies in Ẽ, in
both module alternatives and without an intersection-calculation premise. -/
theorem EarlierGeometry.first_quotient_plane
    (h : c.EarlierGeometry T P g) :
    Nat.card (tilde U (movedSpace P (first H))) = 4 ∧
      tilde U (movedSpace P (first H)) ≤ tilde U (intersectionLayer U P g) :=
  h.first_tilde_calculation c c.actorImage_component

/-- The common part of clause (4): X₁ ∈ Y for either tensor constituent.
The extraspecial central-kernel argument supplies the actual order eight. -/
theorem EarlierGeometry.first_mem_Y_of_source
    (h : c.EarlierGeometry T P g) :
    first H ∈ YFamily H T P (intersectionLayer U P g) :=
  h.first_mem_Y_from_geometry c c.actorImage_component

/-- Common input for both remaining source branches: the entire pair family,
its distinctness, the constructed constituent and complement, and the first
member's actual order and containment. Only earlier-source premises remain. -/
theorem EarlierGeometry.common_calculation
    (h : c.EarlierGeometry T P g) :
    XFamily H T = {first H, second H T} ∧ first H ≠ second H T ∧
      first H ∈ YFamily H T P (intersectionLayer U P g) ∧
      movedSpace U (first H) = U ∧ U ≤ first H ∧
      ∃ s : c.SelectedConstituent T P g,
        c.image P ≤ s.firstSpace ∧
        Module.finrank (ZMod 2) s.firstSpace = 4 ∧
        Nat.card (movedSpace P (first H)) = 8 ∧
        movedSpace P (first H) ≤ intersectionLayer U P g := by
  obtain ⟨hpair, hne⟩ := h.family_eq_pair c
  have hY := h.first_mem_Y_of_source c
  obtain ⟨s, _⟩ := h.constituent_geometry c
  exact ⟨hpair, hne, hY, c.commutator_first_eq, c.U_le_first, s,
    s.point_le_fixed.trans s.fixed_le_first,
    s.constituentEquiv.finrank_eq.symm.trans c.constituent_model.finrank_four,
    hY.2.1, hY.2.2⟩

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.CaseFiveCoordinates
