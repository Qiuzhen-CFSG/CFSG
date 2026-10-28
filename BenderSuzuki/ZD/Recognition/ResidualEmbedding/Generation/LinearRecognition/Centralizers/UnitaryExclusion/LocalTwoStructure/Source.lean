module
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.UnitaryExclusion.LocalTwoStructure.Abelian
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.UnitaryExclusion.LocalTwoStructure.Centralizer

/-!
# The subgroup normalizer in the unitary local construction

The source takes U=N_V(A⟨u⟩), the normalizer of a subgroup join.
The earlier `localU` annotates the join as a set, so elaborates it as union.
Its diagnostic theorems remain valid for that legacy expression. This module
supplies the actual source subgroup and the corresponding construction data,
then proves the commuting and large-abelian conclusions with the same coprime
Frattini and homocyclic-product arguments. No placement or homocyclic
existence conclusion is assumed to have been proved.

Source: GLS4, Chapter2, displayed definitions preceding Lemma13.4 and the
following construction (refs/KGroup/GLS4/Chapter2.tex, lines2385–2420).
-/

noncomputable section
namespace BenderSuzuki.ZD.UnitaryExclusion
open Subgroup Theory.GroupTheory
universe v
variable {G : Type v} [Group G] [Finite G]
variable {Z : Set G} {M : Subgroup G} {z t u : G} {n : ℕ}

/-- U=N_V(A⟨u⟩), with the join explicitly formed in the subgroup lattice. -/
@[expose] public def sourceLocalU (Z : Set G) (M B : Subgroup G) (u : G) : Subgroup G :=
  localV Z M B ⊓ normalizer
    ((closure (Z ∩ (M : Set G)) ⊔ zpowers u : Subgroup G) : Set G)

/-- Actual local placement data for the source subgroup normalizer. -/
public structure SourceHomocyclicLocalData
    (Z : Set G) (M : Subgroup G) (z t u : G) (n : ℕ)
    (d : SecondCentralizerData Z M z t u n) where
  sylow_T : ∃ S : Sylow 2 (centralizerClosure Z u),
    (S : Subgroup (centralizerClosure Z u)).map (centralizerClosure Z u).subtype = localT Z M u
  sylow_V : ∃ S : Sylow 2 (distinguishedCentralizer Z d.torus),
    (S : Subgroup (distinguishedCentralizer Z d.torus)).map
      (distinguishedCentralizer Z d.torus).subtype = localV Z M d.torus
  U_normalizes_T : sourceLocalU Z M d.torus u ≤ normalizer (localT Z M u : Set G)
  torus_moves_T : ⁅localT Z M u, d.torus⁆ ≠ ⊥
  torus_fixes_frattini : (frattini (localT Z M u)).map (localT Z M u).subtype ≤
    centralizer (d.torus : Set G)
  pair_normalizes_U : residualPairStabilizer M t ⊓ centralizerClosure Z u ≤
    normalizer (sourceLocalU Z M d.torus u : Set G)
  irreducible : ∀ W : Subgroup G, W ≤ localT Z M u →
    residualPairStabilizer M t ⊓ centralizerClosure Z u ≤ normalizer (W : Set G) →
    W ≤ (frattini (localT Z M u)).map (localT Z M u).subtype ∨
      W ⊔ (frattini (localT Z M u)).map (localT Z M u).subtype = localT Z M u
  U_homocyclic : Nonempty (sourceLocalU Z M d.torus u ≃* StandardHomocyclicCover (Fin n) 4)
  T₀ : Subgroup G
  T₀_le : T₀ ≤ localT Z M u
  T₀_homocyclic : Nonempty (T₀ ≃* StandardHomocyclicCover (Fin n) 4)
  intersection : T₀ ⊓ sourceLocalU Z M d.torus u = closure (Z ∩ (M : Set G))
  T₀_involutions : ∀ x : T₀, (x : G) ∈ closure (Z ∩ (M : Set G)) ↔ x ^ 2 = 1
  U_involutions : ∀ x : sourceLocalU Z M d.torus u,
    (x : G) ∈ closure (Z ∩ (M : Set G)) ↔ x ^ 2 = 1

omit [Finite G] in
/-- The specified normalizer U lies in both M and L_B. -/
public theorem sourceLocalU_le (B : Subgroup G) : sourceLocalU Z M B u ≤ M ⊓ distinguishedCentralizer Z B :=
  inf_le_left.trans (localTwoCore_le _ _)

omit [Finite G] in
/-- The specified normalizer U is a two-group. -/
public theorem sourceLocalU_isPGroup (B : Subgroup G) : IsPGroup 2 (sourceLocalU Z M B u) :=
  (localTwoCore_isPGroup M (distinguishedCentralizer Z B)).to_le inf_le_left


/-- The actual T and U commute, by the A×B and Frattini arguments. -/
public theorem sourceLocal_commutator_eq_bot
    (hn : 0 < n) (d : SecondCentralizerData Z M z t u n) (hd : SourceHomocyclicLocalData Z M z t u n d) :
    ⁅localT Z M u, sourceLocalU Z M d.torus u⁆ = ⊥ := by
  have hB : d.torus ≤ M ⊓ centralizerClosure Z u :=
    le_inf (d.torus_le_pair.trans inf_le_left) d.torus_le_local
  have hD : residualPairStabilizer M t ⊓ centralizerClosure Z u ≤
      M ⊓ centralizerClosure Z u :=
    inf_le_inf inf_le_left le_rfl
  have hUB : ⁅sourceLocalU Z M d.torus u, d.torus⁆ = ⊥ := by
    apply commutator_eq_bot_iff_le_centralizer.mpr
    apply (sourceLocalU_le d.torus).trans (inf_le_right.trans ?_)
    exact (closure_le _).mpr (fun _ hx => hx.2)
  exact commute_of_coprime_frattini_irreducible
    (localT Z M u) (sourceLocalU Z M d.torus u) d.torus
    (residualPairStabilizer M t ⊓ centralizerClosure Z u)
    (localTwoCore_isPGroup _ _) (sourceLocalU_isPGroup _)
    (torus_coprime hn d) hd.U_normalizes_T
    (hB.trans (inf_le_normalizer_localTwoCore _ _)) hUB hd.torus_moves_T
    hd.torus_fixes_frattini (hD.trans (inf_le_normalizer_localTwoCore _ _))
    hd.pair_normalizes_U hd.irreducible

/-- Construct R = T₀U, deriving its abelianness, exact rank and exact order. -/
@[expose] public def largeAbelianData_of_sourceHomocyclicLocalData
    (hn : 0 < n) (d : SecondCentralizerData Z M z t u n) (hd : SourceHomocyclicLocalData Z M z t u n d)
    (hcard : Nat.card (closure (Z ∩ (M : Set G))) = 2 ^ n) : LargeAbelianData M n := by
  let eT := Classical.choice hd.T₀_homocyclic
  let eU := Classical.choice hd.U_homocyclic
  have hcomm : hd.T₀ ≤ centralizer (sourceLocalU Z M d.torus u : Set G) :=
    hd.T₀_le.trans (commutator_eq_bot_iff_le_centralizer.mp (sourceLocal_commutator_eq_bot hn d hd))
  let facts := rank_card_sup_homocyclic_four
    hd.T₀ (sourceLocalU Z M d.torus u) (closure (Z ∩ (M : Set G)))
    eT eU hcomm hd.intersection hcard hd.T₀_involutions hd.U_involutions
  exact { subgroup := hd.T₀ ⊔ sourceLocalU Z M d.torus u
          le_pointStabilizer := sup_le
            (hd.T₀_le.trans ((localTwoCore_le _ _).trans inf_le_left))
            ((sourceLocalU_le _).trans inf_le_left)
          two_group := facts.1
          abelian := facts.2.1
          rank := facts.2.2.1
          card := facts.2.2.2 }

/-- The constructed subgroup is the literal join T₀U, not an abstract model. -/
public theorem sourceLargeAbelianData_subgroup
    (hn : 0 < n) (d : SecondCentralizerData Z M z t u n)
    (hd : SourceHomocyclicLocalData Z M z t u n d)
    (hcard : Nat.card (closure (Z ∩ (M : Set G))) = 2 ^ n) :
    (largeAbelianData_of_sourceHomocyclicLocalData hn d hd hcard).subgroup =
      hd.T₀ ⊔ sourceLocalU Z M d.torus u := rfl

/-- The unchanged two endgame conclusions from the corrected source placement.
The independent generation and fixed-centralizer rigidity inputs stay explicit. -/
public theorem local_consequences_of_generation_rigidity_and_source_placement
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (hu : PFAppendixIII.IsInvolution u) (hn : 0 < n)
    (d : SecondCentralizerData Z M z t u n)
    (hgen : centralizerClosure Z u ⊔ distinguishedCentralizer Z d.torus = ⊤)
    (hrigid : FixedCentralizerRigidity (secondInvolution d))
    (hd : SourceHomocyclicLocalData Z M z t u n d)
    (hcard : Nat.card (closure (Z ∩ (M : Set G))) = 2 ^ n) :
    CentralizerTwoBound Z u ∧ Nonempty (LargeAbelianData M n) :=
  ⟨(centralizer_sylow_and_bound_of_generation_and_rigidity h r hu d hgen hrigid).2,
    ⟨largeAbelianData_of_sourceHomocyclicLocalData hn d hd hcard⟩⟩

end BenderSuzuki.ZD.UnitaryExclusion
