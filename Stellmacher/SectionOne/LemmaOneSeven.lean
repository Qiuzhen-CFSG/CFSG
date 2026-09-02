module

public import Stellmacher.SectionsOneToFourDefs

open scoped BigOperators Pointwise

namespace Stellmacher.SectionOne

universe u

public structure LemmaOneSevenConclusion
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (S : Subgroup G) : Prop where
  part_a :
    IsInternalDirectProductFamily (oddCore G)
      (fun i : Fin 2 =>
        if i = 0 then
          (commutator (↥(oneE (G := G) (V := V) S))).map
            (oneE (G := G) (V := V) S).subtype
        else
          oddCore G ⊓ Subgroup.centralizer
            (oneE (G := G) (V := V) S : Set G))
  part_b :
    oneB (G := G) (V := V) S = oneJ (G := G) (V := V) S ∧
      oneA (G := G) (V := V) S (oneJ (G := G) (V := V) S)
  part_c :
    ∃ (n : ℕ) (E : Fin n → Subgroup G) (Vf : Fin n → Subgroup V),
      IsInternalDirectProductFamily (oneE (G := G) (V := V) S) E ∧
      (∀ i : Fin n, IsSL2Two (↥(E i))) ∧
      (∀ i : Fin n, Vf i = commutatorAction (E i) V ∧ Nat.card (Vf i) = 4) ∧
      IsInternalDirectProductFamily (⊤ : Subgroup V)
        (fun i : Option (Fin n) =>
          match i with
          | none => FixedPoints.subgroup (oneE (G := G) (V := V) S) V
          | some i => Vf i)

/-- **Stellmacher (1.7).**  If `J(V,S) ≠ 1`, the Baumann subgroup and the
normal closure of `J(V,S)` have the direct-product structure stated in the
paper. -/
public theorem lemma_one_seven
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) (S : Sylow 2 G)
    (hJ : oneJ (G := G) (V := V) (S : Subgroup G) ≠ ⊥) :
    LemmaOneSevenConclusion (G := G) (V := V) (S : Subgroup G) := by
  sorry

end Stellmacher.SectionOne
