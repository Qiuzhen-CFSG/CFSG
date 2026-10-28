module

public import CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.Conjugates
public import CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.Enlargement

/-!
# The other factors normalize the local C-component

The subgroup C_G(U) is normal inside N_G(U). A C-component of that
centralizer is consequently a C-component of N_G(U). Apply the earlier
source 1.2.1(3) there: the two-residual normalizes every C-component.
Each nondistinguished residual lift lies in N_G(U) and is two-perfect,
so it lies in that normalizer's two-residual and normalizes L and L ∩ M.
Commutation of the action images then puts its commutator with X in
C_{L ∩ M}(V). The further two-core bound remains a model calculation.

All normality and residuals are computed in the stated local overgroups.
The universal earlier residual-normalization theorem remains an explicit
premise, as in the existing enlargement construction.
Source: Aschbacher–Smith, E.6.25, printed p.255 (PDF p.266).
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.CommutingLifts
universe u
variable {G : Type u} [Group G] [Finite G]
variable {K : GroupClass.{u}} {T : Sylow 2 G} {M V U X L : Subgroup G}

omit [Finite G] in
/-- A C-component of C_G(U) remains one inside N_G(U): the centralizer
is normal in that normalizer, not in the ambient group. -/
theorem local_cComponent_in_normalizer
    (hL : L ∈ Chapter1.cComponentsIn (centralizer (U : Set G))) :
    (L.subgroupOf (normalizer (U : Set G))).IsCComponent := by
  let H := centralizer (U : Set G)
  let N := normalizer (U : Set G)
  have hHN : H ≤ N := centralizer_le_normalizer _
  let e := subgroupOfEquivOfLe hHN
  have hnormal : (H.subgroupOf N).Normal := by
    rw [← U.normalizerMonoidHom_ker]
    infer_instance
  have hC := (hL.2.map_equiv e.symm).map_subtype hnormal.isSubnormal
  have he : ((L.subgroupOf H).map e.symm.toMonoidHom).map (H.subgroupOf N).subtype =
      L.subgroupOf N := by
    ext x
    constructor
    · rintro ⟨a, ⟨b, hb, rfl⟩, rfl⟩
      exact hb
    · intro hx
      exact ⟨e.symm ⟨x, hL.1 hx⟩, ⟨⟨x, hL.1 hx⟩, hx, rfl⟩, rfl⟩
  rwa [he] at hC

/-- Two-perfect lifts of nondistinguished factors normalize the actual local
C-component, by the earlier source 1.2.1(3) in N_G(U). -/
theorem residualLift_normalizes_local_component [IsElementaryAbelian 2 V]
    (h : HypothesisE61 K T M V) (earlier : EarlierResidualNormalization K)
    (hU : U ∈ obstructionFamily M V) (hX : RegularCyclicSection M V U X)
    (D : Representation.RegularCyclicNormalClosure.Decomposition
      (automizerRepresentation V) (inducedAutomizer V X))
    (i : Fin D.size) (hi : i ≠ D.distinguished)
    (hL : L ∈ Chapter1.cComponentsIn (centralizer (U : Set G))) :
    residualLift V (D.factor i) ≤ normalizer (L : Set G) := by
  let N := normalizer (U : Set G)
  let R := residualLift V (D.factor i)
  have hRN : R ≤ N := residualLift_factor_normalizes_fixed hX D i hi
  have hN : IsSQTK K N := h.simpleQTKE.twoLocal_sqtk
    ⟨U, hU.2.1, (IsElementaryAbelian.isPGroup 2 V).to_le hU.1, rfl⟩
  have hn := earlier N hN (L.subgroupOf N) (local_cComponent_in_normalizer hL)
  have hLN : L ≤ N := hL.1.trans (centralizer_le_normalizer _)
  have hr : R ≤ (pResidual 2 N).map N.subtype := by
    intro x hx
    have hxR : (⟨x, hx⟩ : R) ∈ pResidual 2 R := by
      rw [(pResidual_eq_top_iff 2 R).mpr (residualLift_twoPerfect V (D.factor i))]
      trivial
    exact ⟨inclusion hRN ⟨x, hx⟩,
      map_pResidual_le 2 (inclusion hRN) (mem_map_of_mem _ hxR), rfl⟩
  apply hr.trans
  have hm := (map_mono (f := N.subtype) hn).trans (le_normalizer_map N.subtype)
  rwa [map_subgroupOf_eq_of_le hLN] at hm

end CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.CommutingLifts

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.CommutingLifts
universe u
variable {G : Type u} [Group G]

private theorem commutator_action_kernel {V A B : Subgroup G}
    (hA : A ≤ normalizer (V : Set G)) (hB : B ≤ normalizer (V : Set G))
    (hc : ∀ a ∈ inducedAutomizer V A, ∀ b ∈ inducedAutomizer V B, Commute a b) :
    ⁅A, B⁆ ≤ centralizer (V : Set G) := by
  let N := normalizer (V : Set G)
  let f := V.normalizerMonoidHom.rangeRestrict
  have hmap : (⁅A.subgroupOf N, B.subgroupOf N⁆).map f = ⊥ := by
    rw [map_commutator]
    apply commutator_eq_bot_iff_le_centralizer.mpr
    intro a ha
    apply mem_centralizer_iff.mpr
    intro b hb
    exact (hc a ha b hb).eq.symm
  have hk := (Subgroup.map_eq_bot_iff _).mp hmap
  dsimp only [f] at hk
  rw [MonoidHom.ker_rangeRestrict, normalizerMonoidHom_ker] at hk
  have hm := map_mono (f := N.subtype) hk
  rwa [map_commutator, map_subgroupOf_eq_of_le hA, map_subgroupOf_eq_of_le hB,
    map_subgroupOf_eq_of_le (centralizer_le_normalizer (V : Set G))] at hm

variable [Finite G]
variable {K : GroupClass.{u}} {T : Sylow 2 G} {M V U X L : Subgroup G}

/-- Normalization also holds for the actual local intersection L ∩ M. -/
theorem residualLift_normalizes_local_intersection [IsElementaryAbelian 2 V]
    (h : HypothesisE61 K T M V) (earlier : EarlierResidualNormalization K)
    (hU : U ∈ obstructionFamily M V) (hX : RegularCyclicSection M V U X)
    (D : Representation.RegularCyclicNormalClosure.Decomposition
      (automizerRepresentation V) (inducedAutomizer V X))
    (i : Fin D.size) (hi : i ≠ D.distinguished)
    (hL : L ∈ Chapter1.cComponentsIn (centralizer (U : Set G))) :
    residualLift V (D.factor i) ≤ normalizer ((L ⊓ M : Subgroup G) : Set G) := by
  apply le_trans (le_inf (residualLift_normalizes_local_component h earlier hU hX D i hi hL)
    (((residualLift_le V _).trans h.normalizer_le).trans M.le_normalizer))
  exact inf_normalizer_le_normalizer_inf

/-- Commuting images put the local commutator in C_{L ∩ M}(V).
Its further containment in O₂(L ∩ M) needs the local model calculation. -/
theorem residualLift_commutator_le_local_kernel [IsElementaryAbelian 2 V]
    (h : HypothesisE61 K T M V) (earlier : EarlierResidualNormalization K)
    (hU : U ∈ obstructionFamily M V) (hX : RegularCyclicSection M V U X)
    (D : Representation.RegularCyclicNormalClosure.Decomposition
      (automizerRepresentation V) (inducedAutomizer V X))
    (i : Fin D.size) (hi : i ≠ D.distinguished)
    (hL : L ∈ Chapter1.cComponentsIn (centralizer (U : Set G))) (hXL : X ≤ L) :
    ⁅residualLift V (D.factor i), X⁆ ≤ (L ⊓ M) ⊓ centralizer (V : Set G) := by
  have hXLM : X ≤ L ⊓ M := le_inf hXL
    (hX.contained.trans (inf_le_left.trans inf_le_left))
  refine le_inf ((commutator_mono le_rfl hXLM).trans
    (le_normalizer_iff_commutator_le_right.mp
      (residualLift_normalizes_local_intersection h earlier hU hX D i hi hL))) ?_
  apply commutator_action_kernel (residualLift_le V _)
    (hX.contained.trans (inf_le_left.trans inf_le_right))
  intro a ha b hb
  have hpre : inducedAutomizer V (residualLift V (D.factor i)) ≤ D.factor i := by
    have hh := Subgroup.map_mono (f := V.normalizerMonoidHom.rangeRestrict)
      (Subgroup.comap_mono (f := (normalizer (V : Set G)).subtype)
        (residualLift_le_preimage V (D.factor i)))
    exact hh.trans (inducedAutomizer_preimage V (D.factor i)).le
  exact D.commuting hi a (hpre ha) b (D.contained hb)

end CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.CommutingLifts
