module

public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenExceptional.G2.GenerationTransfer
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicSolvable
public import Theory.GroupTheory.NormalizedSupConsequences
public import Mathlib.Algebra.CharP.CharAndCard

/-!
# Rank-one E-generation for every binary derived G₂ extension

Align T intersect L with the restricted positive-root Sylow subgroup of
G₂(2)'. The two root parabolics are solvable, and T normalizes their actual
images in G. Their joins with T are consequently solvable and hence are
rank-one E-generated. They generate G, so E-member inheritance proves
`IsEGenerated 1 G`.

The argument only requires that L be normal and actually isomorphic to
G₂(F)' for a field F of order two, with L T = G. In particular it includes
every almost-simple outer two-extension from E.1.14(1); it never identifies
G₂(2)' with full G₂(2). No simplicity, quotient-generation or automorphism
coverage premise is added to the source assumptions.

Source: Aschbacher--Smith, E.1.12--14, printed p.214. The binary parabolic
quotients used here retain their ATLAS attribution in the imported model
modules; see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public section

open Subgroup Atlas.G2 Atlas.G2.LieParabolicSetup Atlas.G2.SylowParabolicRecognition
namespace CFSG.Quasithin.ChapterE.ExceptionalValues.G2
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]

omit [Finite G] in
private theorem rootParabolic_isSolvable (hF : Nat.card F = 2) (i : Fin 2) :
    Group.IsSolvable (rootParabolic (F := F) i) := by
  let P : Subgroup (Model F) := if i = 0 then parabolic₁ else parabolic₂
  let : Group.IsSolvable P := BinaryParabolicSolvable.parabolic_isSolvable hF i
  let j : rootParabolic (F := F) i →* P :=
    (commutator (Model F)).subtype.subgroupComap P
  exact Group.isSolvable_of_isSolvable_injective (f := j)
    (fun x y h => Subtype.ext (Subtype.ext (congrArg (fun z : P => z.val) h)))

theorem binary_parabolicOvergroup_isSolvable (hF : Nat.card F = 2)
    (L : Subgroup G) [L.Normal] (T : Sylow 2 G) (e : L ≃* commutator (Model F))
    (he : ((T : Subgroup G).subgroupOf L).map e.toMonoidHom =
      unipotent.subgroupOf (commutator (Model F))) (i : Fin 2) :
    Group.IsSolvable (parabolicOvergroup L T e i) := by
  let : Group.IsSolvable (rootParabolic (F := F) i) := rootParabolic_isSolvable hF i
  let : Group.IsSolvable (ambientParabolic L e i) :=
    Group.isSolvable_of_surjective ((derivedEmbedding L e).subgroupMap_surjective _)
  let : Group.IsNilpotent T := T.isPGroup'.isNilpotent
  exact Group.isSolvable_sup_of_normalizes _ _ (sylow_normalizes_ambientParabolic L T e he i)

theorem binary_parabolicOvergroup_isEGenerated (hF : Nat.card F = 2)
    (L : Subgroup G) [L.Normal] (T : Sylow 2 G) (e : L ≃* commutator (Model F))
    (he : ((T : Subgroup G).subgroupOf L).map e.toMonoidHom =
      unipotent.subgroupOf (commutator (Model F))) (i : Fin 2) :
    IsEGenerated 1 (parabolicOvergroup L T e i) := by
  let : Group.IsSolvable (parabolicOvergroup L T e i) :=
    binary_parabolicOvergroup_isSolvable hF L T e he i
  exact isEGenerated_one_of_solvable

omit [CharP F 2] in
theorem isEGenerated_one_of_binary_socle (hF : Nat.card F = 2)
    (L : Subgroup G) [L.Normal] (T : Sylow 2 G) (e : L ≃* commutator (Model F))
    (hLT : L ⊔ (T : Subgroup G) = ⊤) : IsEGenerated 1 G := by
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (f := 1)
    (by simpa only [Nat.card_eq_fintype_card, pow_one] using hF)
  obtain ⟨a, ha⟩ := exists_sylow_aligned_equiv L T e
  exact isEGenerated_of_parabolicOvergroups L T a hLT
    (binary_parabolicOvergroup_isEGenerated hF L T a ha)
end CFSG.Quasithin.ChapterE.ExceptionalValues.G2
