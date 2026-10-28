module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BorelGeometry.Placement.SourceImage.Factors.Selection
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.Actions
public import CFSG.Quasithin.ChapterB.Section06To07.Elementary
public import Theory.GroupTheory.GeneralizedFitting.Defs
public import Theory.Representation.NormalElementaryQuotient
public import Stellmacher.ElementaryAbelianMaxDefs

/-!
# The decomposition clauses used from E.2.3

The group being decomposed is the image of the global J(H), not J(H*).
Its factors are internal subgroups with an actual product isomorphism.
The module clauses retain [V,Hᵢ], V/C_V(O²(H)*), the direct-sum maps,
and the same factor isomorphism on both sides of each action comparison.
The S₅ clause concerns Vᵢ itself; only the linear clause uses its fixed-space
quotient. In odd degree the deleted natural permutation module is canonically
the augmentation core, so the S₅ convention agrees with B.6.9(5)(ii).

`SourceImplication` is an explicit universally quantified source input. This
module does not prove E.2.3; its proof belongs to the Chapter E source owner.
These are precisely the group/module clauses used for factor comparison,
not the separate Baumann and Sylow conclusions of E.2.3(2)–(4).

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
E.2.3(1)–(3), printed pp.216–217; B.6.9(2)–(5), pp.115–116.
-/

@[expose] public section
open Subgroup Matrix Stellmacher Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BorelGeometry.Placement.SourceFactors
open ChapterB.QuasisimpleSource

variable {A W : Type*} [Group A] [AddCommGroup W] [Module (ZMod 2) W]

/-- The actual displacement space of one factor. -/
abbrev factorSpace (ρ : Representation (ZMod 2) A W) (B : Subgroup A) :=
  subspaceCommutator ρ ⊤ B

/-- A factor preserves its own displacement space. -/
theorem factorSpace_invariant (ρ : Representation (ZMod 2) A W) (B : Subgroup A)
    (b : B) (w : factorSpace ρ B) : ρ b w ∈ factorSpace ρ B := by
  have hm : factorSpace ρ B ≤ (factorSpace ρ B).comap (ρ b) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a, ha, v, _, rfl⟩
    change ρ b (ρ a v - v) ∈ factorSpace ρ B
    have hba : ρ ((b : A) * a) v - v ∈ factorSpace ρ B :=
      Submodule.subset_span ⟨(b : A) * a, B.mul_mem b.property ha, v, trivial, rfl⟩
    have hb : ρ b v - v ∈ factorSpace ρ B :=
      Submodule.subset_span ⟨b, b.property, v, trivial, rfl⟩
    have he : ρ b (ρ a v - v) = (ρ ((b : A) * a) v - v) - (ρ b v - v) := by
      rw [map_sub, map_mul, Module.End.mul_apply]
      abel
    rw [he]
    exact (factorSpace ρ B).sub_mem hba hb
  exact hm w.property

/-- The literal image of a factor's displacement space in V/C_V(N). -/
abbrev factorQuotient (ρ : Representation (ZMod 2) A W) (N B : Subgroup A) :=
  factorSpace ρ B ⧸ (fixedSpace ρ N).comap (factorSpace ρ B).subtype

/-- The linear branch retains a field, an actor isomorphism, and equivariant
coordinates on the quotient by the actual residual fixed space. -/
structure LinearFactor (ρ : Representation (ZMod 2) A W) (N B : Subgroup A) where
  field : BinaryField
  actor : B ≃* Matrix.SpecialLinearGroup (Fin 2) field.Carrier
  coordinates : factorQuotient ρ N B ≃ₗ[ZMod 2] (Fin 2 → field.Carrier)
  equivariant : ∀ (b : B) (w : factorSpace ρ B),
    coordinates (Submodule.Quotient.mk (⟨ρ b w, factorSpace_invariant ρ B b w⟩ :
      factorSpace ρ B)) = (actor b).val *ᵥ coordinates (Submodule.Quotient.mk w)

/-- The symmetric branch uses the unquotiented Vᵢ and the actual five-point
permutation action. The same actor identifies the group and its action. -/
structure SymmetricFactor (ρ : Representation (ZMod 2) A W) (B : Subgroup A) where
  actor : B ≃* Equiv.Perm (Fin 5)
  coordinates : factorSpace ρ B ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 5)
  equivariant : ∀ (b : B) (w : factorSpace ρ B),
    coordinates ⟨ρ b w, factorSpace_invariant ρ B b w⟩ =
      BinaryPermutation.naturalRepresentation (Fin 5) (actor b) (coordinates w)

/-- E.2.3's two actual model alternatives, with their different module clauses. -/
inductive FactorModule (ρ : Representation (ZMod 2) A W) (N B : Subgroup A) where
  | linear : LinearFactor ρ N B → FactorModule ρ N B
  | symmetric : SymmetricFactor ρ B → FactorModule ρ N B

variable {H : Type*} [Group H]

/-- The image of the global Thompson subgroup under the specified quotient map. -/
noncomputable abbrev globalImage (q : H →* A) : Subgroup A :=
  (elementaryAbelianMaxJ (⊤ : Subgroup H)).map q

/-- Selection-relevant conclusions of E.2.3 and its cited B.6.9 decomposition.
None of the fields identifies the number of factors or the Thompson image
with the marked residual. -/
structure Decomposition (q : H →* A) (T : Subgroup H)
    (ρ : Representation (ZMod 2) A W) where
  residual_le_global : pResidual 2 H ≤ elementaryAbelianMaxJ (⊤ : Subgroup H)
  factors : InternalFactors (globalImage q)
  modules : ∀ i, FactorModule (ρ.comp (globalImage q).subtype)
    ((pResidual 2 A).subgroupOf (globalImage q)) (factors.factor i)
  cross_fixed : ∀ i j, i ≠ j → ∀ (b : factors.factor j)
    (w : factorSpace (ρ.comp (globalImage q).subtype) (factors.factor i)),
      ρ (b.val : A) w = w
  quotientSum :
    (W ⧸ fixedSpace ρ (pResidual 2 A)) ≃ₗ[ZMod 2]
      (∀ i, factorQuotient (ρ.comp (globalImage q).subtype)
        ((pResidual 2 A).subgroupOf (globalImage q)) (factors.factor i))
  quotientSum_single : ∀ i
    (w : factorSpace (ρ.comp (globalImage q).subtype) (factors.factor i)),
    quotientSum.symm (Pi.single i (Submodule.Quotient.mk w)) =
      Submodule.Quotient.mk (w : W)
  transitive : ∀ i j, ∃ t : T,
    ((factors.factor i).map (globalImage q).subtype).map
      (MulAut.conj (q t)).toMonoidHom = (factors.factor j).map (globalImage q).subtype

universe u
/-- A genuine universal E.2.3 group/module implication, with all its local
source hypotheses. It is an input here, not an asserted source theorem. -/
def SourceImplication (𝒞 : GroupClass) : Prop :=
  ∀ {H A : Type u} [Group H] [Finite H] [Group A] [Finite A]
    (T : Sylow 2 H) (V : Subgroup H) [V.Normal] [IsElementaryAbelian 2 V]
    (q : H →* A) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (V : Set H)),
    IsSQTK 𝒞 H → ChapterB.IsMinimalParabolicOver T ⊤ →
    Theory.GroupTheory.generalizedFitting H = pCore 2 H →
    pCore 2 A = ⊥ →
    ¬ elementaryAbelianMaxJ (T : Subgroup H) ≤ centralizer (V : Set H) →
    Nonempty (Decomposition q T
      (Representation.NormalElementaryQuotient.representation V q hq hker))

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BorelGeometry.Placement.SourceFactors
end
