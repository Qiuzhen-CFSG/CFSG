module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Configuration
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.FullSieve.SourceInterface.MSPairs
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.Actions
public import Theory.GroupTheory.NormalCentralQuotientAction
public import Theory.GroupTheory.PGroup.OmegaCenterIn
public import Theory.GroupTheory.TwoFixedLinesIrreducible

/-!
# Literal subgroups and elementary reductions for the nonblock rank-one branch

The source uses the full module W = [Ω₁Z(O₂(LT)), L]. Its root subgroup
Z_S = C_W(S ∩ L) is nontrivial and normalized by T. We prove these facts
without a classification premise, using the actual chosen module only to
normalize L. The secondary group is the solvable residual of C_K(Z_S),
not the two-residual or an arbitrary isomorphic subgroup.

`MSData` is the remaining original 4.3.8–10 construction contract. It retains
the MS pair, a common SL₃ quotient marking, the natural center and doubled
dual quotient, and C.1.34(3)'s radical inequality for every eligible Sylow.
`SecondaryData` is the remaining original 4.3.11–15 construction contract.
Its component lives inside the literal root normalizer. Its action is
conjugation on the full quotient K_Z/O₂(K_Z), with no central quotient
silently substituted. Neither record is asserted to exist here.

For any such secondary construction, movement of the core and of the
quotient implies [R₂,Y] = R₂. Its nontrivial quotient action then forces
the torus action to be nontrivial. This is the elementary contradiction
used after 4.3.16; proving the local automorphism and exceptional module
alternatives remains a separate obligation.

Source: Aschbacher–Smith, original 4.3.8–16 and conclusion of 4.3.2,
printed pp.616–619; C.1.31, C.1.34(3), pp.135–137.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
open ChapterB.QuasisimpleSource
namespace Nonblock
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The original component, embedded through K ≤ H ≤ G. -/
abbrev K (c : SourceConfiguration T L) : Subgroup G := c.K.map c.H.subtype
/-- The full Sylow intersection from the shared configuration. -/
abbrev S (c : SourceConfiguration T L) : Subgroup G := (T : Subgroup G) ⊓ c.H
/-- The full source module; it is not the chosen Chapter 12 module. -/
abbrev W (_c : SourceConfiguration T L) : Subgroup G :=
  Section02.Unitary.fullModule L ((L ⊔ (T : Subgroup G)).pCoreIn 2)
/-- The original commutator Q = [O₂(K),K], in G. -/
abbrev Q (c : SourceConfiguration T L) : Subgroup G := ⁅(K c).pCoreIn 2, K c⁆
/-- The literal center of Q, in G. -/
abbrev U (c : SourceConfiguration T L) : Subgroup G := (center (Q c)).map (Q c).subtype
/-- The fixed subgroup Z_S = C_W(S ∩ L). -/
abbrev root (c : SourceConfiguration T L) : Subgroup G :=
  W c ⊓ centralizer (S c ⊓ L : Set G)
/-- The source G_Z = N_G(Z_S). -/
abbrev rootNormalizer (c : SourceConfiguration T L) : Subgroup G :=
  normalizer (root c : Set G)
/-- The source K₂ = C_K(Z_S)^∞, using the solvable residual. -/
abbrev secondary (c : SourceConfiguration T L) : Subgroup G :=
  (solvableResidual (K c ⊓ centralizer (root c : Set G) : Subgroup G)).map
    (K c ⊓ centralizer (root c : Set G)).subtype
/-- The actual two-core O₂(K₂S). -/
abbrev R₂ (c : SourceConfiguration T L) : Subgroup G := (secondary c ⊔ S c).pCoreIn 2


omit [Finite G] in
/-- T preserves the full source module under its actual conjugation. -/
theorem fullModule_normalized {V : Subgroup G} (c : SourceConfiguration T L)
    (D : Chapter12.Section02.ChosenModule T L V) :
    (T : Subgroup G) ≤ normalizer (W c : Set G) := by
  intro t ht
  apply mem_normalizer_iff_map_conj_eq.mpr
  have hL : L.map (MulAut.conj t).toMonoidHom = L :=
    mem_normalizer_iff_map_conj_eq.mp (D.sylow_normalizes_component ht)
  have hQ : ((L ⊔ (T : Subgroup G)).pCoreIn 2).map (MulAut.conj t).toMonoidHom =
      (L ⊔ (T : Subgroup G)).pCoreIn 2 :=
    mem_normalizer_iff_map_conj_eq.mp
      (normalizer_le_normalizer_characteristic_image (L ⊔ (T : Subgroup G))
        (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G))
          ((L ⊔ (T : Subgroup G)).le_normalizer (mem_sup_right ht)))
  change (Section02.Unitary.fullModule L ((L ⊔ (T : Subgroup G)).pCoreIn 2)).map
    (MulAut.conj t).toMonoidHom = _
  rw [Section02.Unitary.fullModule_map,hL,hQ]

omit [Finite G] in
/-- The root normalizer contains the original Sylow T. -/
theorem root_normalized {V : Subgroup G} (c : SourceConfiguration T L)
    (D : Chapter12.Section02.ChosenModule T L V) :
    (T : Subgroup G) ≤ rootNormalizer c := by
  have hSL : S c ⊓ L = (T : Subgroup G) ⊓ L := by
    change ((T : Subgroup G) ⊓ c.H) ⊓ L = _
    rw [inf_assoc,inf_eq_right.mpr (c.le_component.trans (map_subtype_le _))]
  have hTSL : (T : Subgroup G) ≤ normalizer (S c ⊓ L : Set G) := by
    change (T : Subgroup G) ≤ normalizer ((S c ⊓ L : Subgroup G) : Set G)
    rw [hSL]
    exact (le_inf (T : Subgroup G).le_normalizer D.sylow_normalizes_component).trans
      inf_normalizer_le_normalizer_inf
  exact (le_inf (fullModule_normalized c D)
    (hTSL.trans (normalizer_le_normalizer_centralizer (S c ⊓ L)))).trans
      inf_normalizer_le_normalizer_inf

/-- A nontrivial two-group acted on by S ∩ L has a nontrivial fixed subgroup. -/
theorem root_ne_bot {V : Subgroup G} (c : SourceConfiguration T L)
    (D : Chapter12.Section02.ChosenModule T L V) : root c ≠ ⊥ := by
  let := c.c28.module_elementary
  exact inf_centralizer_ne_bot_of_pGroups (S c ⊓ L) (W c)
    (T.isPGroup'.to_le (inf_le_left.trans inf_le_left))
    (IsElementaryAbelian.isPGroup 2 (W c))
    ((inf_le_left.trans inf_le_left).trans (fullModule_normalized c D))
    c.c28.module_nontrivial

open Chapter1.RadicalExclusions.ModelReduction
open FullSieve.SourceInterface (LinearThreeMSPair HasSectionModel msQ linearThreeActor)

/-- Construction target for the third MS alternative on the original component.
The module clauses share the same quotient isomorphism and duality. -/
structure MSData (c : SourceConfiguration T L) (n : ℕ) where
  field : BinaryField
  degree_eq : field.degree = n
  model : (K c ⧸ pCore 2 (K c)) ≃* Matrix.SpecialLinearGroup (Fin 3) field.Carrier
  pair : LinearThreeMSPair KnownSimple.IsKnownSimple (K c) (c.I.pCoreIn 2) n field.Carrier
  commutator_eq : msQ (K c) (c.I.pCoreIn 2) = Q c
  natural : HasSectionModel (K c) (U c) ⊥ (linearThreeActor model)
    (Representation.specialLinearNatural (k := field.Carrier) 3)
  doubleDual : HasSectionModel (K c) (Q c) (U c) (linearThreeActor model)
    ((Representation.specialLinearNatural (k := field.Carrier) 3).dual.prod
      (Representation.specialLinearNatural (k := field.Carrier) 3).dual)
  radical_not_centralizer_core :
    ∀ P : Sylow 2 (K c ⊔ c.I.pCoreIn 2 : Subgroup G),
      c.I.pCoreIn 2 ≤ (P : Subgroup (K c ⊔ c.I.pCoreIn 2 : Subgroup G)).map
        (K c ⊔ c.I.pCoreIn 2 : Subgroup G).subtype →
      FullSieve.SourceInterface.MSNotCentralizerCore (K c) (c.I.pCoreIn 2)
        ((P : Subgroup (K c ⊔ c.I.pCoreIn 2 : Subgroup G)).map
          (K c ⊔ c.I.pCoreIn 2 : Subgroup G).subtype)
  fullModule : ⁅U c,L⁆ = W c
  centralizer : S c ⊓ centralizer (K c : Set G) = ⊥

/-- Construction target for the source secondary component and odd torus.
The quotient-movement premise is written as ambient generation by Q and
[R₂,Y]; `radical_moved` below removes Q using its separate movement. -/
structure SecondaryData (c : SourceConfiguration T L) (n : ℕ) where
  component : Subgroup (rootNormalizer c)
  torus : Subgroup G
  isComponent : component.IsCComponent
  normal : component.Normal
  quasisimple : IsQuasisimple (component ⧸ pCore 2 component)
  secondary_le : secondary c ≤ component.map (rootNormalizer c).subtype
  secondary_lt : secondary c < component.map (rootNormalizer c).subtype
  secondary_model : ClassicalGroup.IsPSL (secondary c ⧸ pCore 2 (secondary c)) 2 (2 ^ n)
  torus_le : torus ≤ rootNormalizer c
  torus_cyclic : IsCyclic torus
  torus_card : Nat.card torus = 2 ^ n - 1
  torus_faithful : torus ⊓ centralizer (root c : Set G) = ⊥
  torus_secondary : ⁅secondary c,torus⁆ ≤ (secondary c).pCoreIn 2
  torus_normalizes_radical : torus ≤ normalizer (R₂ c : Set G)
  core_eq : (K c ⊔ S c).pCoreIn 2 = Q c
  core_moved : ⁅Q c,torus⁆ = Q c
  radical_mod_core_moved : Q c ⊔ ⁅R₂ c,torus⁆ = R₂ c
  radical_le : R₂ c ≤ rootNormalizer c
  radical_normalizer : normalizer (R₂ c : Set G) ≤
    c.H ⊓ normalizer (secondary c : Set G)
  enlarged_core_le : (component.map (rootNormalizer c).subtype ⊔ (T : Subgroup G)).pCoreIn 2 ≤ R₂ c
  core_enlarges : secondary c < (component.map (rootNormalizer c).subtype).pCoreIn 2 ⊔ secondary c
  radical_action : letI := normal
    ((R₂ c).subgroupOf (rootNormalizer c)).map
      (normalQuotientAction component (pCore 2 component)) ≠ ⊥

/-- Literal conjugation on the full component quotient, not its central quotient. -/
noncomputable def SecondaryData.action {c : SourceConfiguration T L} {n : ℕ}
    (d : SecondaryData c n) :
    rootNormalizer c →* MulAut (d.component ⧸ pCore 2 d.component) := by
  letI := d.normal
  exact normalQuotientAction d.component (pCore 2 d.component)


omit [Finite G] in
/-- Movement of the actual core and quotient gives movement of all of R₂. -/
theorem SecondaryData.radical_moved {c : SourceConfiguration T L} {n : ℕ}
    (d : SecondaryData c n) : ⁅R₂ c,d.torus⁆ = R₂ c := by
  have hQ : Q c ≤ ⁅R₂ c,d.torus⁆ := by
    rw [← d.core_moved]
    exact commutator_mono (le_sup_left.trans d.radical_mod_core_moved.le) le_rfl
  exact (sup_eq_right.mpr hQ).symm.trans d.radical_mod_core_moved

omit [Finite G] in
/-- The same identity inside the actual root normalizer, with subtype maps. -/
theorem SecondaryData.radical_restricted_moved {c : SourceConfiguration T L} {n : ℕ}
    (d : SecondaryData c n) :
    ⁅(R₂ c).subgroupOf (rootNormalizer c),d.torus.subgroupOf (rootNormalizer c)⁆ =
      (R₂ c).subgroupOf (rootNormalizer c) := by
  apply map_injective (rootNormalizer c).subtype_injective
  rw [map_commutator,map_subgroupOf_eq_of_le d.radical_le,
    map_subgroupOf_eq_of_le d.torus_le,d.radical_moved]

omit [Finite G] in
/-- The torus cannot act trivially on K_Z/O₂(K_Z): it generates the
R₂-commutators, whereas the action of R₂ on this quotient is nontrivial. -/
theorem SecondaryData.torus_action_ne_bot {c : SourceConfiguration T L} {n : ℕ}
    (d : SecondaryData c n) :
    (d.torus.subgroupOf (rootNormalizer c)).map d.action ≠ ⊥ := by
  intro ht
  apply d.radical_action
  change ((R₂ c).subgroupOf (rootNormalizer c)).map d.action = ⊥
  rw [← d.radical_restricted_moved,map_commutator,ht,commutator_bot_right]

end Nonblock
end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
end
