module

public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.ZeroClosure.Mutual.Pair
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.ZeroClosure.Normalization
public import CFSG.Quasithin.ChapterH.Section05To09.NaturalDual.SourceStabilizers

/-!
# Pure intersections exclude mutual normalization without commutation

A vanishing natural intersection forces the inner actor to fix the whole
natural summand, hence to be trivial. The actor consequently has rank at
most one, since the source layer has index two. A nontrivial outer actor
fixes no nonzero natural vector, so its fixed codimension is at least n.
Apply this argument also to the inverse conjugate and use the exact
reverse-action rank identity to obtain a contradiction.

This gives the mutual branch of 12.1.7 from its permitted pure-intersection
premise, without requiring an offender classification. It does not supply
that premise in degree five.
Source: Aschbacher--Smith, H.9.1 and 12.1.7, printed pp.389--390,792.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender Module
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterE CFSG.Quasithin.ChapterH.NaturalDual
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.ZeroClosure.Mutual
section Actors
variable {n : ℕ} {M X : Type*} [Group M] [AddCommGroup X] [Module (ZMod 2) X]
  (S : SourceSetup n M X)

theorem inner_eq_one (a : M) (ha : a ∈ componentLayer M)
    (hf : ∀ u : S.natural, S.representation a u = u) : a = 1 := by
  let l : componentLayer M := ⟨a, ha⟩
  have hl : S.layer l = 1 := by
    apply LinearEquiv.ext
    intro x
    change S.layer l x = x
    have he := S.natural_action l x
    rw [hf] at he
    have he' := congrArg S.naturalCoordinates (Subtype.ext he)
    simpa only [LinearEquiv.apply_symm_apply] using he'.symm
  exact congrArg Subtype.val (S.layer.injective (hl.trans (map_one S.layer).symm))

theorem actor_rank_le_one [Finite M] (I : Subgroup M)
    (hf : S.natural ≤ S.fixed (I ⊓ componentLayer M)) : rank I ≤ 1 := by
  have hz : I ⊓ componentLayer M = ⊥ := by
    apply bot_unique
    intro a ha
    exact inner_eq_one S a ha.2 (fun u => hf u.property ⟨a, ha⟩)
  have hi : (componentLayer M).index = 2 := by
    rw [← Subgroup.index_map_equiv _ S.model.group]
    change ((componentLayer M).map S.model.group.toMonoidHom).index = 2
    rw [S.layer_map]
    exact BinaryNaturalDual.ModelOrbits.AutomorphismModel.inner_index S.degree
  let : (componentLayer M).Normal := Subgroup.normal_of_index_eq_two hi
  have hd := (componentLayer M).relIndex_dvd_index_of_normal I
  rw [← inf_relIndex_left, hz, relIndex_bot_left, hi] at hd
  exact (Nat.log_mono_right (Nat.le_of_dvd (by decide) hd)).trans_eq (by decide)

theorem actor_codim_ge [Finite M] [FiniteDimensional (ZMod 2) X]
    (I : Subgroup M) (hI : I ≠ ⊥)
    (hf : S.natural ≤ S.fixed (I ⊓ componentLayer M)) :
    n ≤ fixedCodim S.representation I := by
  obtain ⟨a, ha, hne⟩ := (Subgroup.bot_or_exists_ne_one I).resolve_left hI
  have hout : a ∉ componentLayer M := by
    intro h
    exact hne (inner_eq_one S a h (fun u => hf u.property ⟨a, ha, h⟩))
  have hd : S.natural ⊓ S.fixed I = ⊥ := by
    apply bot_unique
    intro u hu
    change u = 0
    by_contra hne
    exact hout ((S.pure_stabilizer_eq_residual ⟨u, hu.1⟩ hne).2 (hu.2 ⟨a, ha⟩))
  have hn : finrank (ZMod 2) S.natural = n := by
    rw [S.naturalCoordinates.finrank_eq]
    simp [BinaryLinear.OuterCyclic.Space]
  have hs := Submodule.finrank_sup_add_finrank_inf_eq S.natural (S.fixed I)
  rw [hd, finrank_bot, add_zero, hn] at hs
  have hb := Submodule.finrank_le (S.natural ⊔ S.fixed I)
  have hc := fixedCodim_add_finrank S.representation I
  change fixedCodim S.representation I + finrank (ZMod 2) (S.fixed I) = _ at hc
  omega
end Actors

open CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource
variable {G : Type*} [Group G] [Finite G] {W : Subgroup G}
  [IsElementaryAbelian 2 W]

omit [Finite G] in
theorem natural_fixed {n : ℕ}
    (S : SourceSetup n (Automizer W) (Additive W))
    (hρ : S.representation = automizerRepresentation W) (g : G)
    (hW : W ≤ normalizer (W.map (MulAut.conj g).toMonoidHom : Set G))
    (hz : S.natural ⊓ subgroupSpace W (W.map (MulAut.conj g).toMonoidHom) = ⊥) :
    S.natural ≤ S.fixed (inducedAutomizer W (W.map (MulAut.conj g).toMonoidHom) ⊓
      componentLayer (Automizer W)) := by
  intro u hu
  exact ZeroClosure.natural_normalizer_le_inner_fixed S hρ g hz
    ⟨hu, (mem_subgroupSpace W _ u).mpr (hW u.toMul.property)⟩

theorem centralizes_of_pure {n : ℕ}
    (S : SourceSetup n (Automizer W) (Additive W))
    (hρ : S.representation = automizerRepresentation W)
    (hz : ∀ g : G, ⁅W, W.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ →
      S.natural ⊓ subgroupSpace W (W.map (MulAut.conj g).toMonoidHom) = ⊥)
    (g : G)
    (hA : W.map (MulAut.conj g).toMonoidHom ≤ normalizer (W : Set G))
    (hW : W ≤ normalizer (W.map (MulAut.conj g).toMonoidHom : Set G)) :
    ⁅W, W.map (MulAut.conj g).toMonoidHom⁆ = ⊥ := by
  by_contra hc
  have hf := natural_fixed S hρ g hW (hz g hc)
  have hr := actor_codim_ge S _ (inducedAutomizer_ne_bot_of_commutator_ne_bot hA hc) hf
  have hn : W ≤ normalizer (W.map (MulAut.conj g⁻¹).toMonoidHom : Set G) := by
    exact reverse_is_normalized g hA
  have hrev := actor_rank_le_one S _
    (natural_fixed S hρ g⁻¹ hn (hz g⁻¹ (reverse_noncentral g hc)))
  rw [hρ, reverse_rank g hA hW] at hr
  have := S.degree
  omega

end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.ZeroClosure.Mutual
