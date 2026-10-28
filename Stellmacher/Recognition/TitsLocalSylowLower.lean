module
public import Stellmacher.ExceptionalType
public import Stellmacher.SectionFiveToSeven.Result7_1

/-!
# Ambient Sylow lower bound for the twisted-F4 local type

The case-B data in (10.1) give `2^11 ≤ |S|` for the graph subgroup `S`.
The critical path places the offset-two vertex next to the first-step vertex,
so `lemma_seven_one_graph` identifies that shifted edge stabilizer with a
conjugate of the initial intersection `P₁ ∩ P₂`. Since the native `S` is
contained in the initial edge stabilizer, its lower bound transfers to the
shifted edge. Injectivity of the ambient embedding preserves its cardinality,
and the local-type intersection equation identifies its image with the
supplied ambient Sylow subgroup. Sylow conjugacy then transfers the bound to
any supplied ambient Sylow. No upper bound or equality between the native and
shifted graph subgroups is used.

Source: Stellmacher (10.1)(b), the type definition following that result, and
the intrinsic edge-conjugacy statement in (7.1).
-/

namespace Stellmacher.Recognition

open Later SectionsFiveToSeven

private theorem card_conjugateBy_eq {K : Type*} [Group K] [Finite K]
    (A : Subgroup K) (g : K) : Nat.card (conjugateBy A g) = Nat.card A := by
  unfold conjugateBy
  exact Subgroup.card_map_of_injective (MulAut.conj g).injective

/-- The actual ambient Sylow in a twisted-F4 local configuration has the
source lower bound from (10.1)(b). -/
public theorem sylow_card_lower_of_twistedF4TwoDerived_type
    {G : Type*} [Group G] [Finite G] (S0 : Sylow 2 G)
    (hType : IsOfTwistedF4TwoDerivedType G) : 2 ^ 11 ≤ Nat.card S0 := by
  obtain ⟨data⟩ := hType
  let _ := data.groupK
  let _ := data.finiteK
  let Γ : CosetGraphContext data.K data.S data.P1 data.P2 := data.Γ
  let cp : CriticalPath Γ := data.criticalPath
  have hlen : cp.length = 3 := data.caseB.critical_length
  have hcardNative : 2 ^ 11 ≤ Nat.card data.S := data.caseB.card_S.1
  have hSle : data.S ≤ GAt Γ cp.a ⊓ GAt Γ cp.firstStep :=
    cp.S_le_edge_stabilizers
  have hcardInitial : Nat.card data.S ≤
      Nat.card ↥(GAt Γ cp.a ⊓ GAt Γ cp.firstStep) :=
    Subgroup.card_le_of_le hSle
  have hcardP : Nat.card ↥(data.P1 ⊓ data.P2) =
      Nat.card ↥(GAt Γ cp.a ⊓ GAt Γ cp.firstStep) := by
    change Nat.card ↥(data.P1 ⊓ data.P2) =
      Nat.card ↥(Γ.stabilizer cp.a ⊓ Γ.stabilizer cp.firstStep)
    rcases cp.edge_stabilizers_are_P with ⟨hinit₁, hinit₂⟩ | ⟨hinit₁, hinit₂⟩
    · rw [hinit₁, hinit₂]
    · rw [hinit₁, hinit₂, inf_comm]
  have hcardNative' : 2 ^ 11 ≤ Nat.card ↥(data.P1 ⊓ data.P2) := by
    rw [hcardP]
    exact hcardNative.trans hcardInitial
  have hpath : Γ.adjacent (cp.path ⟨1, by omega⟩) (cp.path ⟨2, by omega⟩) := by
    exact cp.path_adj ⟨1, by omega⟩
  have hnext : cp.path ⟨2, by omega⟩ = data.aPlus2 := by
    obtain ⟨i, hi, hia⟩ := data.caseB.path_offset
    have hi' : i = ⟨2, by omega⟩ := Fin.ext hi
    simpa [hi'] using hia
  have hshift : Nat.card ↥(GAt Γ (cp.path ⟨2, by omega⟩) ⊓
      GAt Γ (cp.path ⟨1, by omega⟩)) = Nat.card ↥(data.P1 ⊓ data.P2) := by
    have hed := (lemma_seven_one_graph Γ).edge_stabilizers_conjugate
      _ _ (Γ.adjacent_symm hpath)
    obtain ⟨g, hg⟩ := hed
    rw [hg, card_conjugateBy_eq]
  have hshift' : 2 ^ 11 ≤ Nat.card ↥(GAt Γ (cp.path ⟨2, by omega⟩) ⊓
      GAt Γ (cp.path ⟨1, by omega⟩)) := by
    rw [hshift]
    exact hcardNative'
  have hmap : Nat.card ↥((GAt Γ (cp.path ⟨2, by omega⟩) ⊓
      GAt Γ (cp.path ⟨1, by omega⟩)).map data.embedding) =
      Nat.card ↥(GAt Γ (cp.path ⟨2, by omega⟩) ⊓
      GAt Γ (cp.path ⟨1, by omega⟩)) :=
    Subgroup.card_map_of_injective data.embedding_injective
  have hmapEq : (GAt Γ (cp.path ⟨2, by omega⟩) ⊓
      GAt Γ (cp.path ⟨1, by omega⟩)).map data.embedding =
      (data.sylowIntersection : Subgroup G) := by
    rw [hnext, cp.path_first,
      Subgroup.map_inf _ _ data.embedding data.embedding_injective]
    exact data.intersection_eq
  have hsyl : Nat.card data.sylowIntersection =
      Nat.card ↥(GAt Γ (cp.path ⟨2, by omega⟩) ⊓
      GAt Γ (cp.path ⟨1, by omega⟩)) := by
    rw [← hmapEq]
    exact hmap
  have hsyl0 : Nat.card S0 = Nat.card data.sylowIntersection :=
    Nat.card_congr (S0.equiv data.sylowIntersection).toEquiv
  rw [hsyl0, hsyl]
  exact hshift'

end Stellmacher.Recognition
