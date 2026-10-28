module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.SourceOrbits.Representatives.Contracts
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.SourceOrbits.Representatives.SL23Local.CoreClosure
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.SourceOrbits.Representatives.SL23Local.CoreConstruction
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.SourceOrbits.Representatives.SL23Local.CubicModel
public import Theory.SpecificGroups.SL2.BinaryTetrahedralQuotient

/-!
# The Sylow stabilizer of a local SL₂(3) pair

The center of the literal SL₂(3) model has order two. Once the Q-conjugate
closure has been identified with this model and shown to contain z, its
center has ambient image ⟨z⟩. Hence every normalizer of the closure fixes z.
For two distinct cubic subgroups generating the closure, their ambient
pair normalizer therefore lies in H = C_G(z).

Intrinsic transitivity of X on the other three cubic subgroups makes
their N_H(X)-orbit have size three. With |N_H(X)| = 48 the stabilizer
has order sixteen. It is the full stabilizer in M = N_G(X), so |M| = 2160
identifies it as an actual Sylow two-subgroup. No abstract two-group
identification or outside-core involution fusion is used.

`nonempty_pair` constructs the literal `Representatives.SL23Pair` contract,
discharging the model and cubic-geometry premises of `CoreModel.nonempty_pair`
using `CoreConstruction` and `CubicModel`. Its only extra hypotheses are
the earlier three-local orders |N_G(X)| = 2160 and |N_H(X)| = 48 from the
proof of 47.3. The source three-local calculation owns these numerical
inputs; the pair representatives assembly consumes this result together
with the independent `FiveLocalPairs` construction. This proves the local
SL₂(3) representative branch, not the other branches of 47.5.

Source: Aschbacher, *Sporadic Groups* (1994), 47.3 and the final paragraph
of the proof of 47.5, printed pp.262–263. The printed semidihedral assertion
is not used.
-/

@[expose] public section

open Subgroup MulAction
open scoped Pointwise
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.SL23Local
variable {G : Type*} [Group G] [Finite G]

namespace CoreModel
variable {D : Seed G} (C : CoreModel D)
include C

theorem center_card : Nat.card (center (coreClosure D)) = 2 := by
  let e := C.equiv.trans GLS3.Chapter5.SchurPresentation.binaryTetrahedralEquivSL.symm
  rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv]
  exact GLS3.Chapter5.SchurPresentation.binaryTetrahedral_center_card

theorem center_image :
    (center (coreClosure D)).map (coreClosure D).subtype = zpowers D.z := by
  have hz : (⟨D.z, C.involution_mem⟩ : coreClosure D) ∈ center (coreClosure D) := by
    apply mem_center_iff.mpr
    intro x
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (coreClosure_le D x.property))
  apply (eq_of_le_of_card_ge (zpowers_le.mpr (mem_map_of_mem _ hz)) ?_).symm
  rw [card_map_of_injective (coreClosure D).subtype_injective, C.center_card,
    Nat.card_zpowers]
  change 2 ≤ orderOf D.z
  exact D.localType.involution.ge

theorem normalizer_le_centralizer :
    normalizer (coreClosure D : Set G) ≤ involutionCentralizer D.z :=
  normalizer_le_centralizer_of_characteristic_involution
    (coreClosure D) (center (coreClosure D)) D.z D.localType.involution C.center_image

/-- The characteristic center forces every pair fixer back into the source H. -/
theorem pair_normalizer_le (F : CubicGeometry (coreClosure D) D.X)
    (Y : OtherCubics (coreClosure D) D.X) :
    normalizer (D.X : Set G) ⊓ normalizer (Y.val : Set G) ≤ localNormalizer D := by
  apply le_inf ?_ inf_le_left
  apply le_trans (normalizer_inf_normalizer_le_normalizer_sup D.X Y.val)
  rw [F.generate Y]
  exact C.normalizer_le_centralizer
end CoreModel
namespace OtherCubics
variable {D : Seed G}

/-- Inclusion in H gives the genuine ambient conjugacy-class vertex. -/
def vertex (Y : OtherCubics (coreClosure D) D.X) : D.Vertex :=
  ⟨Y.val, D.mem_vertex_of_le_centralizer Y.val Y.property.2.1
    (Y.property.1.trans (coreClosure_le D))⟩

/-- The local normalizer permutes the other cubic subgroups of the closure. -/
def conjugate (g : localNormalizer D) (Y : OtherCubics (coreClosure D) D.X) :
    OtherCubics (coreClosure D) D.X := by
  refine ⟨Y.val.map (MulAut.conj (g : G)).toMonoidHom, ?_, ?_, ?_⟩
  · exact (map_mono Y.property.1).trans_eq
      (mem_normalizer_iff_map_conj_eq.mp (localNormalizer_le_normalizer_coreClosure D g.property))
  · rw [card_map_of_injective (MulAut.conj (g : G)).injective]
    exact Y.property.2.1
  · intro he
    exact Y.property.2.2 (map_injective (MulAut.conj (g : G)).injective
      (he.trans (mem_normalizer_iff_map_conj_eq.mp g.property.2).symm))

/-- The orbit consists of precisely the three other cubic subgroups. -/
noncomputable def orbitEquiv (F : CubicGeometry (coreClosure D) D.X)
    (Y : OtherCubics (coreClosure D) D.X) :
    orbit (localNormalizer D) Y.vertex ≃ OtherCubics (coreClosure D) D.X where
  toFun A := ⟨A.val.val, by
    obtain ⟨g, hg⟩ := A.property
    rw [← congrArg Subtype.val hg]
    exact (conjugate g Y).property⟩
  invFun W := ⟨W.vertex, by
    obtain ⟨x, hx⟩ := F.transitive Y W
    exact ⟨⟨x, X_le_localNormalizer D x.property⟩, Subtype.ext hx⟩⟩
  left_inv A := Subtype.ext (Subtype.ext rfl)
  right_inv W := Subtype.ext rfl

theorem orbit_card (F : CubicGeometry (coreClosure D) D.X)
    (Y : OtherCubics (coreClosure D) D.X) :
    Nat.card (orbit (localNormalizer D) Y.vertex) = 3 :=
  (Nat.card_congr (orbitEquiv F Y)).trans F.card

theorem local_stabilizer_card (F : CubicGeometry (coreClosure D) D.X)
    (hN : Nat.card (localNormalizer D) = 48)
    (Y : OtherCubics (coreClosure D) D.X) :
    Nat.card (stabilizer (localNormalizer D) Y.vertex) = 16 := by
  have hc := Nat.card_congr (orbitProdStabilizerEquivGroup (localNormalizer D) Y.vertex)
  rw [Nat.card_prod, orbit_card F Y, hN] at hc
  omega
end OtherCubics

private theorem stabilizer_card_eq_inf (D : Seed G) (K : Subgroup G) (V : D.Vertex) :
    Nat.card (stabilizer K V) = Nat.card (normalizer (V.val : Set G) ⊓ K : Subgroup G) := by
  have he : stabilizer K V = (normalizer (V.val : Set G)).subgroupOf K := by
    ext k
    rw [← D.stabilizer_eq_normalizer V]
    rfl
  rw [he, ← subgroupOf_map_subtype, card_map_of_injective K.subtype_injective]

namespace CoreModel
variable {D : Seed G} (C : CoreModel D)
include C

theorem stabilizer_card (F : CubicGeometry (coreClosure D) D.X)
    (hN : Nat.card (localNormalizer D) = 48)
    (Y : OtherCubics (coreClosure D) D.X) :
    Nat.card (stabilizer (normalizer (D.X : Set G)) Y.vertex) = 16 := by
  rw [stabilizer_card_eq_inf D, ← Y.local_stabilizer_card F hN,
    stabilizer_card_eq_inf D]
  apply congrArg (fun S : Subgroup G => Nat.card S)
  apply le_antisymm
  · exact le_inf inf_le_left (by
      rw [inf_comm]
      exact C.pair_normalizer_le F Y)
  · exact inf_le_inf_left _ inf_le_right

/-- The order-16 pair fixer is an actual Sylow subgroup of M. -/
theorem stabilizer_sylow (F : CubicGeometry (coreClosure D) D.X)
    (hM : Nat.card (normalizer (D.X : Set G)) = 2160)
    (hN : Nat.card (localNormalizer D) = 48)
    (Y : OtherCubics (coreClosure D) D.X) :
    ∃ P : Sylow 2 (normalizer (D.X : Set G)),
      (P : Subgroup (normalizer (D.X : Set G))) =
        stabilizer (normalizer (D.X : Set G)) Y.vertex := by
  have hc : Nat.card (stabilizer (normalizer (D.X : Set G)) Y.vertex) =
      2 ^ (Nat.card (normalizer (D.X : Set G))).factorization 2 := by
    rw [C.stabilizer_card F hN Y, hM]
    decide +kernel
  exact ⟨Sylow.ofCard (stabilizer (normalizer (D.X : Set G)) Y.vertex) hc, rfl⟩

/-- Every other local cubic subgroup gives the literal representative contract.
The final `SL23Local.nonempty_pair` supplies the model and intrinsic geometry. -/
noncomputable def pair (F : CubicGeometry (coreClosure D) D.X)
    (hM : Nat.card (normalizer (D.X : Set G)) = 2160)
    (hN : Nat.card (localNormalizer D) = 48)
    (Y : OtherCubics (coreClosure D) D.X) : Representatives.SL23Pair D where
  vertex := Y.vertex
  join := ⟨(MulEquiv.subgroupCongr (F.generate Y)).trans C.equiv⟩
  sylow := C.stabilizer_sylow F hM hN Y

/-- Conditional assembly for the SL₂(3) branch of 47.5; it assumes no pair fixer. -/
theorem nonempty_pair (F : CubicGeometry (coreClosure D) D.X)
    (hM : Nat.card (normalizer (D.X : Set G)) = 2160)
    (hN : Nat.card (localNormalizer D) = 48) :
    Nonempty (Representatives.SL23Pair D) := by
  have hn : Nonempty (OtherCubics (coreClosure D) D.X) :=
    (Nat.card_pos_iff.mp (by rw [F.card]; omega)).1
  exact ⟨C.pair F hM hN (Classical.choice hn)⟩
end CoreModel

/-- The local SL₂(3) representative, conditional only on the earlier three-local
orders in 47.3. The actual core closure, its marked central involution, and the
cubic geometry are constructed here rather than assumed as source inputs. -/
theorem nonempty_pair (D : Seed G)
    (hM : Nat.card (normalizer (D.X : Set G)) = 2160)
    (hN : Nat.card (localNormalizer D) = 48) :
    Nonempty (Representatives.SL23Pair D) := by
  obtain ⟨C⟩ := nonempty_coreModel D
  exact C.nonempty_pair C.cubicGeometry hM hN

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.SL23Local
