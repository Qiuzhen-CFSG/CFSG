module
public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.GTwo.Derived
public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.Symmetric
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.G2Recognition.BinarySix
public import Theory.SpecificGroups.G2Even.BinaryDerivedAutomorphismRank
public import CFSG.Quasithin.ChapterG.Section09.Basic
public import CFSG.Quasithin.ChapterG.Section11.LowRank

/-!
# Excluding the whole binary derived G2 component

The actual automorphism-rank bound and complete small-degree filtration force
degree six. Native-module recognition and the binary normalizer embed the
entire original group into G2(2), retaining its normal derived component.
A derived involution has a transitive moved-plane stabilizer already in that
component. An outer involution forces the full ambient group, where the
original type-a2 condition gives the established long-root exclusion.

`StrictWholePair` applies this to the literal strict quotient.
Source: Aschbacher--Smith G.9.3(10), G.11.7 and 6.2.19,
printed pp.354,367,691.
-/

public noncomputable section
open Subgroup Representation

open Module Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterG.Section11.WholeBinaryG2
open Section09.DefiningCharacteristic.G2Recognition
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {B : LinearMap.BilinForm (ZMod 2) V}
  {v : V} {W : Submodule (ZMod 2) V} {X L : Subgroup G}
  [IsElementaryAbelian 2 X] {X₀ : Subgroup X} {C : GroupClass}

set_option backward.isDefEq.respectTransparency false in
/-- No whole binary G2-derived component has the original strict type-a2
rank-two involution with a nontransitive moved plane. -/
theorem not_binary_model
    (h : Section10.Hypothesis ρ B v W X X₀)
    (h9 : Section09.ComponentHypothesis C ρ X L L
      (finrank (ZMod 2) (Additive X)))
    (hd : 6 ≤ finrank (ZMod 2) V)
    (e : L ≃* commutator (Atlas.G2.Model (ZMod 2)))
    (a : G) (ha : a^2=1) (hr : finrank (ZMod 2) (RankTwo.movedSpace ρ a)=2)
    (htype : ∀ u, B u (ρ a u)=0)
    (hnt : ¬ RankTwo.StabilizerTransitive ρ (RankTwo.movedSpace ρ a)) : False := by
  let := h9.normal_H
  have hu := h9.single_component_degree_bound
  rw [primeRank_equiv 2 (MulAut.congr e)] at hu
  have hb := Atlas.G2.binary_derived_automorphism_two_rank_le_three
  let σ := (ρ.comp L.subtype).comp e.symm.toMonoidHom
  let : IsIrreducible σ :=
    (irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective _).mpr h9.irreducible
  obtain ⟨Ω,hΩ,τ,o,H,hH,hstab,htrans,hfil⟩ :=
    G2DerivedPermutationFiltration.exists_permutation_filtration
  let := hΩ
  have hs := BinaryPermutation.finrank_mem_of_factorDegreeFiltration
    τ o H hH hstab htrans hfil σ
  change finrank (ZMod 2) V=1 ∨ finrank (ZMod 2) V=6 ∨ 8<finrank (ZMod 2) V at hs
  have hdim : finrank (ZMod 2) V=6 := by omega
  obtain ⟨b,f₀,hf⟩ := BinarySix.quasiequivalent_of_finrank_eq_six σ hdim
  let f : V ≃ₗ[ZMod 2] Atlas.G2.Natural.Space (ZMod 2) :=
    LinearEquiv.ofBijective (f₀.toAddMonoidHom.toZModLinearMap 2) f₀.bijective
  have hLf (l : L) (u : V) : f (ρ l u)=
      Atlas.G2.Natural.derivedAction (ZMod 2) ((e.trans b) l) (f u) := by
    have hh := hf (e l) u
    change f (ρ (e.symm (e l)) u)=_ at hh
    rw [e.symm_apply_apply] at hh
    exact hh
  obtain ⟨q,hqi,hq,hact⟩ := Atlas.G2.Natural.BinaryNormalizer.ambient_embedding
    ρ L (e.trans b) f hLf h.faithful
  have hD : commutator (Atlas.G2.Model (ZMod 2)) ≤ q.range := by
    intro g hg
    obtain ⟨l,hl⟩ := (e.trans b).surjective ⟨g,hg⟩
    exact ⟨l,(hq l).trans (congrArg Subtype.val hl)⟩
  have ha1 : a≠1 := by
    intro he
    rw [he,RankTwo.movedSpace,map_one,sub_self,LinearMap.range_zero,finrank_bot] at hr
    omega
  by_cases had : q a ∈ commutator (Atlas.G2.Model (ZMod 2))
  · let E := MonoidHom.ofInjective hqi
    have he (g : G) (u : V) : f (ρ g u)=
        ((Atlas.G2.Natural.action (ZMod 2)).comp q.range.subtype) (E g) (f u) := hact g u
    apply hnt
    apply RankTwo.stabilizerTransitive_transport ρ _ E f he a
    apply RankTwo.GTwo.stabilizerTransitive_intermediate_derived q.range hD (E a)
    · rw [←map_pow,ha,map_one]
    · exact fun he => ha1 (E.injective (he.trans E.map_one.symm))
    · exact had
    · exact (RankTwo.finrank_movedSpace_transport ρ _ E f he a).symm.trans hr
  · have hfull := Atlas.G2.Natural.BinaryNormalizer.eq_top_of_derived_le hD
      (⟨a,rfl⟩ : q a ∈ q.range) had
    let E := MulEquiv.ofBijective q ⟨hqi,MonoidHom.range_eq_top.mp hfull⟩
    have hp := RankTwo.Symmetric.smallConjugateProducts_of_type_a2
      B ρ h.alternating h.nondegenerate h.faithful h.preserves a ha hr htype
    exact RankTwo.GTwo.exclusion_of_equivariant_model ρ E f hact a
      (orderOf_eq_prime ha ha1) hr hp hnt
end CFSG.Quasithin.ChapterG.Section11.WholeBinaryG2
