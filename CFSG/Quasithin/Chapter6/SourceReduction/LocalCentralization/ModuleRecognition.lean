module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalLinearLayerMultiplicity
public import CFSG.Quasithin.Chapter5.RankOneBaumannSourceSelection
public import CFSG.Quasithin.Chapter6.SourceReduction.LocalCentralization.Torus
public import CFSG.Quasithin.Chapter6.SourceReduction.LocalCentralization.Geometry

public import Theory.Representation.BinaryAlternatingFiveFixedPoint.Submodules
public import CFSG.Quasithin.Chapter6.SourceReduction.LocalCentralization.ModuleRestriction

/-!
# The complete Cartan module conclusion at field degree two

Outside centralization kills the fixed space of all R₂(LT). Once the Borel
centralizes omega, its canonical deleted-type complement vanishes. The
original HStar witness bounds the whole action's cubic ratio, and therefore
its multiplicity, by two. Restricting to the literal [W,L] preserves the
complete deleted decomposition and the bound; noncentrality excludes zero
copies. Neither splitting nor chosen-module invariance is an assumption.

For a local Cartan witness at degree two its escaping cubic is the whole
left Cartan, so actual component centralization supplies Borel fixation.
The universal source owner qt-d-1222-rankone-cartan-local-classification
still has to derive degree two from centralization. Its sieve and A₇ block
contradiction are separate remaining steps; this is not an unconditional
LocalCartanModuleRecognition inhabitant.

Source: Aschbacher--Smith 5.1.13, final paragraph on p.638, using I.1.6
and the original guarded cubic-ratio bound of 3.1.8.
-/

set_option backward.isDefEq.respectTransparency false

public noncomputable section
open scoped IsMulCommutative MonoidAlgebra
open Subgroup Theory.GroupTheory Representation
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
open Chapter12.Section02 Chapter12.Section02.RankOneModule
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H : Subgroup G} {n : ℕ}

/-- The original reduced subgroup embeds in the entire reduced module. -/
theorem Input.le_wholeReduced (h : Input KnownSimple.IsKnownSimple T L W n) :
    W ≤ wholeReduced T L := by
  have hh := map_mono (f := (L ⊔ (T : Subgroup G)).subtype)
    h.reduced_internal.le_reducedPSubgroup
  rwa [map_subgroupOf_eq_of_le h.reduced.1] at hh

/-- Borel fixation identifies the whole deleted type and bounds its full dimension. -/
theorem Input.whole_deleted_bound_of_borel
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hHC : H ≤ omegaCentralizer T)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hB : localBorel T L ≤ omegaCentralizer T) :
    Representation.typeReject (wholeMarkedAction h.sylow_normalizes e)
      (BinaryPermutation.alternatingCoreRepresentation (Fin 5)) = ⊥ ∧
      Module.finrank (ZMod 2) (wholeSpace T L) ≤ 8 := by
  have hfixed : wholeReduced T L ⊓ centralizer (L : Set G) = ⊥ :=
    Subgroup.inf_centralizer_eq_bot_of_omega_disjoint T L (wholeReduced T L)
      wholeReduced_mem.2.1 wholeReduced_le_sylow
      (le_sup_right.trans wholeReduced_normalized) h.sylow_normalizes
      (h.centralOmega_disjoint_of_outside_centralizes hH hHC)
  have hr := wholeMarkedAction_typeReject_eq_bot h.sylow_normalizes e hfixed hB
  refine ⟨hr,?_⟩
  obtain ⟨V,⟨D⟩⟩ := h.original_section1221.exists_chosen_of_normalizes h.sylow_normalizes
  obtain ⟨k,c,hc⟩ := wholeMarkedAction_exists_coordinates h.sylow_normalizes e hfixed hB
  have hm := whole_model_of_coordinates e c hc
  obtain ⟨a,⟨ca⟩⟩ := D.whole_coordinates_of_model hm
  have hk : k ≤ 2 := D.rankOne_whole_multiplicity_le_two_of_cubicRatio
    (D.rankOne_whole_cubicRatio_le_two h.original_section1221 hH) a ca
  have he := c.finrank_eq
  have hd := BinaryPermutation.finrank_natural_odd (Fin 5) (by decide)
  simp only [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at he
  simp only [Fintype.card_fin] at hd
  rw [hd] at he
  norm_num at he
  omega

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric

end
public noncomputable section
open scoped IsMulCommutative MonoidAlgebra
open Subgroup Theory.GroupTheory Representation
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
open Chapter12.Section02 Chapter12.Section02.RankOneModule
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H U : Subgroup G} {n : ℕ}

/-- Every nonzero invariant subgroup of the bounded deleted module has one or two copies. -/
theorem subgroup_oneOrTwoA5_of_whole_deleted
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hLU : L ≤ normalizer (U : Set G)) (hU : U ≤ wholeReduced T L) (hU0 : U ≠ ⊥)
    (hr : Representation.typeReject (wholeMarkedAction hTL e)
      (BinaryPermutation.alternatingCoreRepresentation (Fin 5)) = ⊥)
    (hd : Module.finrank (ZMod 2) (wholeSpace T L) ≤ 8) :
    IsOneOrTwoA5Modules L U := by
  let S := moduleSubrepresentation hTL e hLU
  let b := moduleSubrepresentationEquiv hTL e hLU hU
  obtain ⟨m,c,hc,hm⟩ := BinaryAlternatingFiveFixedPoint.subrepresentation_coordinates
    (wholeMarkedAction hTL e) hr S
  have hm2 : m ≤ 2 := by omega
  have hm0 : 0 < m := by
    apply Nat.pos_of_ne_zero
    intro hz
    subst m
    let : Subsingleton S.toSubmodule := c.injective.subsingleton
    let : Subsingleton U := b.symm.injective.subsingleton
    apply hU0
    apply bot_unique
    intro u hu
    exact congrArg Subtype.val (Subsingleton.elim (⟨u,hu⟩ : U) 1)
  exact oneOrTwoA5Modules_of_copies hm0 hm2
    (subgroup_model_of_coordinates hTL e hLU hU c hc)

/-- Borel fixation and the outside centralization identify the full original layer. -/
theorem Input.layer_oneOrTwoA5_of_marked_borel
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hHC : H ≤ omegaCentralizer T)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hB : localBorel T L ≤ omegaCentralizer T) :
    IsOneOrTwoA5Modules L (layer L W) := by
  obtain ⟨hr,hd⟩ := h.whole_deleted_bound_of_borel hH hHC e hB
  exact subgroup_oneOrTwoA5_of_whole_deleted h.sylow_normalizes e
    (le_sup_left.trans (reduced_normalizes h.commutator_reduced))
    h.commutator_input.le_wholeReduced h.noncentral hr hd

/-- At degree two, actual omega-centralization gives the complete one/two A₅ module
on all of [W,L]. No splitting, multiplicity or chosen-module invariance is assumed. -/
theorem LocalCartanWitness.module_of_exponent_eq_two
    {A B Y X D : Subgroup G}
    (d : LocalCartanWitness T H A Y X D)
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hXC : X ≤ omegaCentralizer T) (hn : n = 2) :
    IsOneOrTwoA5Modules L (layer L W) := by
  obtain ⟨F,_,_,hF,⟨f⟩⟩ := h.linear
  have hfour : Nat.card F = 4 := by simpa [hn] using hF
  obtain ⟨a⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hfour
  exact h.layer_oneOrTwoA5_of_marked_borel hH
    ((residual_le_omegaCentralizer_iff hH.1.1.2).mp (d.residual_le.trans hXC))
    (f.trans a) (d.borel_centralizes_of_exponent_eq_two h c hn hXC)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
end
