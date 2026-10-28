module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.Supercritical.SourceAssembly
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.Reduction
public import CFSG.Quasithin.Chapter1.Section03
public import CFSG.Quasithin.Chapter1.Section01Overgroups.Sylow

/-!
# Solvable overgroups of the source Ξ family

The supercritical reduction makes the complement image normal or detects a
C-component. Solvability excludes the latter alternative, so every actual Ξ
member is normal in a solvable strongly quasithin overgroup containing its
Sylow subgroup. No model or cover inspection from the remaining cases of
Proposition 1.3.4 is used.

When maximal two-local overgroups of the chosen Sylow subgroup are solvable,
characteristic-two inheritance gives a nontrivial two-core in the Ξ member.
The normalizer maximality argument proves the conclusion of 1.3.7 even for
the unstarred family. Sylow conjugacy transports the solvability hypothesis.

Source: Aschbacher–Smith 1.3.2, the solvable branch of 1.3.4, and 1.3.7,
printed pp.508–512; applied using 15.4.2(2) in 15.4.10, pp.1157–1159.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.XiEmbedding
universe u
variable {G : Type u} [Group G] [Finite G]

/-- A solvable overgroup rules out the C-component detected by the Fitting branch. -/
theorem LocalInput.normal_of_solvable
    {p : ℕ} {T X P H : Subgroup G} (h : LocalInput p T X P H)
    (hH : IsStronglyQuasithin H) (hs : Group.IsSolvable H) :
    (X.subgroupOf H).Normal := by
  let := hs
  rcases h.quotient_normal_or_fitting_of_source hH with hn | hf
  · exact h.normal_of_complement_quotient_normal hn
  · obtain ⟨L, hL⟩ := h.exists_component_of_fitting hf
    exact (hL.mem.2.not_isSolvable inferInstance).elim

/-- All local inputs come from the actual Ξ member and the proved clauses of 1.3.2. -/
theorem normal_of_mem_Xi_of_solvable
    {T X H : Subgroup G} (hX : X ∈ Xi G T)
    (hT : IsSylowIn 2 T H) (hH : X ⊔ T ≤ H)
    (hstrong : IsStronglyQuasithin H) (hs : Group.IsSolvable H) :
    (X.subgroupOf H).Normal := by
  obtain ⟨p, hp, ho, hq⟩ := hX.odd_quotient
  let : Fact p.Prime := ⟨hp⟩
  exact (localInput_of_mem_Xi hX hT hH ho hq (default : Sylow p X)).normal_of_solvable
    hstrong hs

/-- The source uniqueness conclusion follows from solvability of the actual
maximal two-local overgroups; the star exclusion is unnecessary here. -/
theorem normalizer_unique_of_solvable_maximalTwoLocals
    {C : GroupClass} (hG : IsSimpleQTKE C G) (T : Sylow 2 G)
    (hsol : ∀ M : Subgroup G, IsMaximalTwoLocal M → (T : Subgroup G) ≤ M →
      Group.IsSolvable M)
    {X : Subgroup G} (hX : X ∈ Xi G (T : Subgroup G)) :
    IsMaximalTwoLocal (normalizer (X : Set G)) ∧
      {M : Subgroup G | IsMaximalTwoLocal M ∧ X ⊔ (T : Subgroup G) ≤ M} =
        {normalizer (X : Set G)} := by
  have hcore : X.pCoreIn 2 ≠ ⊥ := hX.pCoreIn_ne_bot
    (fun _ hM _ hN hNM hn => lemma_1_1_3_1 hM hN hNM hn)
    (lemma_1_1_4_6 T (hG.evenCharacteristic T))
  apply Section03.normalizer_unique_of_normal_in_maximalTwoLocals X T hX.invariant
    (fun he => hcore (by change (pCore 2 X).map X.subtype = ⊥; rw [he, Subgroup.map_bot]))
  intro M hM hXM
  have hTM : (T : Subgroup G) ≤ M := le_sup_right.trans hXM
  have hT : IsSylowIn 2 (T : Subgroup G) M := by
    refine ⟨T.subtype hTM, ?_⟩
    simp only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTM]
  exact normal_of_mem_Xi_of_solvable hX hT hXM
    (hG.twoLocal_sqtk hM.1).stronglyQuasithin (hsol M hM hTM)

/-- Conjugacy transports solvability of maximal two-local overgroups to every Sylow subgroup. -/
theorem solvable_maximalTwoLocals_of_sylow
    (T U : Sylow 2 G)
    (hsol : ∀ M : Subgroup G, IsMaximalTwoLocal M → (T : Subgroup G) ≤ M →
      Group.IsSolvable M) :
    ∀ M : Subgroup G, IsMaximalTwoLocal M → (U : Subgroup G) ≤ M →
      Group.IsSolvable M := by
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G T U
  intro M hM hTM
  let e : G ≃* G := MulAut.conj g
  have hmap : (T : Subgroup G).map e.toMonoidHom ≤ M := hTM
  have hpre : (T : Subgroup G) ≤ M.map e.symm.toMonoidHom := by
    simpa [map_map] using map_mono (f := e.symm.toMonoidHom) hmap
  let : Group.IsSolvable (M.map e.symm.toMonoidHom) :=
    hsol _ (Theory.Quasithin.isMaximalTwoLocal_map e.symm hM) hpre
  let eM := M.equivMapOfInjective e.symm.toMonoidHom e.symm.injective
  exact Group.isSolvable_of_surjective
    (f := eM.symm.toMonoidHom) eM.symm.surjective

end CFSG.Quasithin.Chapter1.XiEmbedding
