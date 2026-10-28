module

public import CFSG.Quasithin.MainConverse.SporadicLocal.J3.Coverage.Fusion.Exhaustion
public import CFSG.Quasithin.MainConverse.SporadicLocal.J3.Coverage.Fusion.ClassReduction
public import CFSG.Quasithin.MainConverse.SporadicLocal.J3.Coverage.Fusion.Ambient

/-!
# Assembly of elementary-subgroup fusion in J₃

The checked extension catalogue exhausts elementary subgroups of the fixed
Sylow candidate. Its 140 nontrivial rows are conjugates of 28 Sylow classes.
The checked generator images of the supplied 28 ambient model words identify
these classes with conjugates of the five fixed representatives. Composing
the Sylow and ambient conjugators gives exhaustive fusion under the sole
numerical premise that the fixed Sylow candidate has order 128.

Source: GLS, Number 3, Table 5.3h, printed p.269. These five elementary
representatives support the maximal two-local coverage argument; they are
not themselves the maximal local subgroups listed in the table.
-/

namespace CFSG.Quasithin.MainConverse.SporadicLocal.J3Coverage
open Subgroup Sporadic.Janko3 Sporadic.Janko3.TwoLocal
open Fusion

/-- The finite ambient-word certificate implies the requested
fusion. The premise consists of identities in the concrete J₃ model. -/
public theorem elementary_fusion_of_generator_images
    (hS : Nat.card sylowCandidate = 128)
    (hambient : ∀ (c : Fin 28) (j : Fin 4),
      j ∈ representativeBasis (alignedClass c) →
      (MulAut.conj (ambientConjugator c)) (elementaryGenerator j) =
        element (generatorImage c j)) :
    ∀ A : Subgroup Model, A ≤ sylowCandidate → A ≠ ⊥ →
      IsElementaryAbelian 2 A → ∃ (i : Fin 5) (g : Model),
        A = (elementaryRepresentative i).map (MulAut.conj g).toMonoidHom := by
  intro A hAS hA hEA
  obtain ⟨i, rfl⟩ := elementary_eq_catalogue hS A hAS hA hEA
  rw [catalogueSubgroup_conjugate hS]
  rw [classSubgroup_conjugate_of_generator_images hS (catalogueClass i)
    (ambientConjugator (catalogueClass i)) (hambient (catalogueClass i))]
  refine ⟨alignedClass (catalogueClass i),
    element (catalogueConjugator i) * ambientConjugator (catalogueClass i), ?_⟩
  rw [Subgroup.map_map]
  congr 1

/-- Every nontrivial elementary abelian two-subgroup of the fixed Sylow
candidate is an ambient conjugate of one of the five fixed representatives.
The order premise is the only additional hypothesis on the concrete model. -/
public theorem elementary_fusion (hS : Nat.card sylowCandidate = 128) :
    ∀ A : Subgroup Model, A ≤ sylowCandidate → A ≠ ⊥ →
      IsElementaryAbelian 2 A → ∃ (i : Fin 5) (g : Model),
        A = (elementaryRepresentative i).map (MulAut.conj g).toMonoidHom :=
  elementary_fusion_of_generator_images hS ambient_generator_images

end CFSG.Quasithin.MainConverse.SporadicLocal.J3Coverage
