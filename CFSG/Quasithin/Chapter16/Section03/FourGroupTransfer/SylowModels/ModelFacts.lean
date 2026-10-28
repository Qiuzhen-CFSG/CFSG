module

public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.Contracts

/-!
# The intrinsic model calculations used in 16.3.4

These are specifications, not assertions of the model calculations. The order
comparison concerns actual Sylow subgroups of Aut(L) and K. The center clauses
refer to the whole center of an actual Sylow subgroup of K, embedded in G.
They do not include normalization by the ambient Sylow subgroup, disjointness
from its centralizer of L, or the ambient order inequality.

The earlier 16.1.7 table supplies the full simple-group pairs below. In
particular no central quotient is substituted for either member of a pair.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
16.1.7 and the proof of 16.3.4, printed pp.1172 and 1178.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.FourGroupTransfer.SylowModels
open Subgroup Theory.GroupTheory ClassificationModels
variable {G : Type*} [Group G]

/-- The earlier pair table restricted to the five excluded full simple groups.
The source owner must derive this from 16.1.2, 16.1.4, 16.1.5 and 16.1.7. -/
def ExcludedPairModels (L K : Subgroup G) : Prop :=
  (∃ n : ℕ, 2 ≤ n ∧ ClassicalGroup.IsPSU K 3 (2 ^ n) ∧
    ClassicalGroup.IsPSL L 2 (2 ^ n)) ∨
  (Nonempty (K ≃* SporadicName.m12.Carrier) ∧
    Nonempty (L ≃* alternatingGroup (Fin 5))) ∨
  (Nonempty (K ≃* SporadicName.j2.Carrier) ∧
    (Nonempty (L ≃* alternatingGroup (Fin 5)) ∨ ClassicalGroup.IsPSL L 3 2)) ∨
  (Nonempty (K ≃* SporadicName.hs.Carrier) ∧
    (Nonempty (L ≃* alternatingGroup (Fin 6)) ∨
      Nonempty (L ≃* alternatingGroup (Fin 8)))) ∨
  (Nonempty (K ≃* SporadicName.ru.Carrier) ∧
    Nonempty (L ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 1))

/-- The strict comparison |Aut(L)|₂ < |K|₂, independent of ambient T. -/
def SylowOrderGap (L K : Subgroup G) : Prop :=
  ∀ (A : Sylow 2 (MulAut L)) (S : Sylow 2 K), Nat.card A < Nat.card S

/-- V is the entire center of an actual Sylow two-subgroup of K in G. -/
def SylowCenterEmbedding (K V : Subgroup G) : Prop :=
  ∃ S : Sylow 2 K,
    (center ((S : Subgroup K).map K.subtype)).map
      ((S : Subgroup K).map K.subtype).subtype = V

/-- In the unitary case every Sylow subgroup of the embedded L is a
full Sylow center in K. This is an embedding assertion, not an abstract
isomorphism between the two subgroups. -/
def FullSylowCenterLifting (L K : Subgroup G) : Prop :=
  ∀ P : Sylow 2 L, SylowCenterEmbedding K ((P : Subgroup L).map L.subtype)

/-- In the sporadic cases every central subgroup of order two in a Sylow
subgroup of L is a full Sylow center in K. -/
def InvolutionCenterLifting (L K : Subgroup G) : Prop :=
  ∀ (P : Sylow 2 L) (V : Subgroup G),
    V ≤ ((center P).map (P : Subgroup L).subtype).map L.subtype →
    Nat.card V = 2 → SylowCenterEmbedding K V

end CFSG.Quasithin.Chapter16.FourGroupTransfer.SylowModels
