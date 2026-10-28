module
public import CFSG.Quasithin.ChapterD.Section02.RatioDecomposition.SymmetricThreeSeed
public import Theory.Representation.BinaryOffender.IrreducibleOrbitAction

/-!
# A singleton ratio partition in the original ambient action

If the literal ratio decomposition has a unique factor, its embedded actor
and support are exactly the original marked subgroup and moved support. The
ambient support permutation then fixes that support. Outside the full-orbit
branch its complement has a nonzero fixed vector. These identities preserve
the actual embeddings, rather than replacing the factor action by a model.

Source: Aschbacher--Smith 15.1.2, printed p.1085, the conclusion s=a=1.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterD.RatioDecomposition.FactorData
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {K : Subgroup G} {U : Submodule (ZMod 2) V}
  (c : FactorData ρ K U) (d : Decomposition c.representation)

theorem ambient_actors_generate : (⨆ j, (c.ambientFactor d j).actor) = K := by
  simp only [ambientFactor,Factor.map_actor,embedding,←Subgroup.map_iSup,
    d.group_generation,←MonoidHom.range_eq_map,Subgroup.range_subtype]

theorem unique_factor_actor (i : d.Index) (hi : ∀ j : d.Index, j = i) :
    (c.ambientFactor d i).actor = K := by
  apply Eq.trans _ (c.ambient_actors_generate d)
  apply le_antisymm
  · exact le_iSup (fun j => (c.ambientFactor d j).actor) i
  · exact iSup_le fun j => hi j ▸ le_rfl

theorem unique_factor_space (i : d.Index) (hi : ∀ j : d.Index, j = i) :
    (c.ambientFactor d i).space = U := by
  apply Eq.trans _ (c.ambient_spaces_generate d)
  apply le_antisymm
  · exact le_iSup (fun j => (c.ambientFactor d j).space) i
  · exact iSup_le fun j => hi j ▸ le_rfl

theorem unique_factor_support_stabilizer (i : d.Index) (hi : ∀ j : d.Index, j = i)
    (π : G →* Equiv.Perm d.Index)
    (hs : ∀ g j, (c.ambientFactor d j).space.map (ρ g) =
      (c.ambientFactor d (π g j)).space) :
    subspaceStabilizer ρ (c.ambientFactor d i).space = ⊤ := by
  apply eq_top_iff.mpr
  intro g _
  apply (subspace_map_eq_iff ρ _ _).mp
  rw [hs,hi (π g i)]

theorem unique_factor_space_ne_top_of_not_full_orbit
    (i : d.Index) (hi : ∀ j : d.Index, j = i) (π : G →* Equiv.Perm d.Index)
    (hnt : ¬ (U = ⊤ ∧ ∀ j k, ∃ g : G, π g j = k)) :
    (c.ambientFactor d i).space ≠ ⊤ := by
  intro ht
  apply hnt
  refine ⟨(c.unique_factor_space d i hi).symm.trans ht,?_⟩
  intro j k
  refine ⟨1,?_⟩
  simp only [map_one,Equiv.Perm.one_apply]
  exact (hi j).trans (hi k).symm

theorem unique_factor_fixed_space_ne_bot
    (i : d.Index) (hi : ∀ j : d.Index, j = i) (π : G →* Equiv.Perm d.Index)
    (hnt : ¬ (U = ⊤ ∧ ∀ j k, ∃ g : G, π g j = k)) :
    fixedSpace ρ K ≠ ⊥ := by
  intro hb
  have hu : U = ⊤ := by simpa only [hb,sup_bot_eq] using c.fixed_complement
  exact c.unique_factor_space_ne_top_of_not_full_orbit d i hi π hnt
    ((c.unique_factor_space d i hi).trans hu)

noncomputable def unique_factor_equiv
    (i : d.Index) (hi : ∀ j : d.Index, j = i) : (d.factor i).Carrier ≃* K :=
  (MonoidHom.ofInjective (c.ambientFactor d i).embedding.group_injective).trans
    (MulEquiv.subgroupCongr (c.unique_factor_actor d i hi))

theorem unique_factor_finrank (i : d.Index) (hi : ∀ j : d.Index, j = i) :
    Module.finrank (ZMod 2) U = Module.finrank (ZMod 2) (d.factor i).Space := by
  exact (congrArg (fun W : Submodule (ZMod 2) V => Module.finrank (ZMod 2) W)
    (c.unique_factor_space d i hi).symm).trans
      (LinearMap.finrank_range_of_inj (c.ambientFactor d i).embedding.space_injective)
end CFSG.Quasithin.ChapterD.RatioDecomposition.FactorData
