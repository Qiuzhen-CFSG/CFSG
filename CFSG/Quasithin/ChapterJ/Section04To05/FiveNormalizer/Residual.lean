module

public import CFSG.Quasithin.ChapterJ.Section04To05.FiveNormalizer.Hyperplane
public import Theory.SpecificGroups.SymmetricFive.FiveNormalizerOvergroups
public import Theory.GroupTheory.PResidual.SupplementCommutator

/-!
# The actual five-normalizer residual in J.4.4

The original hyperplane normalizer has proper S₅ image containing the
Sylow-five normalizer. The finite S₅ overgroup calculation identifies both
that image and its two-residual image. Pulling back through the actual map,
prime residuals of supplements give O²(N_H(Q₀Q₅))=B₅Q₅.

Consequently every subgroup of H normalizing Q₀Q₅ normalizes B₅Q₅ and Q₅.
The latter is the original Q-intersection of B₅Q₅. These are the actual
normalization implications in Aschbacher–Smith J.4.4(3), printed p.441.
-/

public section
noncomputable section
open Subgroup
open scoped commutatorElement Pointwise
namespace CFSG.Quasithin.ChapterJ.RuSubgroup
open Centralizers.Choices
variable {G : Type*} [Group G] [Finite G] (d : LocalSetup G)
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

theorem fiveHyperplaneNormalizer_image (B5 : Sylow 5 d.toTypeRuSetup.H) :
    (fiveHyperplaneNormalizer d B5).map d.ru2.quotientMap =
      normalizer (B5.map d.ru2.quotientMap:Set S5) := by
  let P := B5.mapSurjective d.ru2.quotient_surjective
  exact Theory.SpecificGroups.SymmetricFive.FiveNormalizerOvergroups.eq_normalizer_of_proper
    P _ (five_quotient_normalizer_le_image d B5) (fiveHyperplaneNormalizer_image_ne_top d B5)

theorem fiveHyperplaneNormalizer_residual_image (B5 : Sylow 5 d.toTypeRuSetup.H) :
    ((pResidual 2 (fiveHyperplaneNormalizer d B5)).map (fiveHyperplaneNormalizer d B5).subtype).map
      d.ru2.quotientMap = B5.map d.ru2.quotientMap := by
  let P := B5.mapSurjective d.ru2.quotient_surjective
  exact (Theory.SpecificGroups.SymmetricFive.FiveNormalizerOvergroups.image_and_residual_eq
    P d.ru2.quotientMap (fiveHyperplaneNormalizer d B5)
    (five_quotient_normalizer_le_image d B5) (fiveHyperplaneNormalizer_image_ne_top d B5)).2

private theorem B5_twoPerfect (B5 : Sylow 5 d.toTypeRuSetup.H) :
    IsPPerfect 2 (B5:Subgroup d.toTypeRuSetup.H) := by
  have hc : Nat.card (B5:Subgroup d.toTypeRuSetup.H)=5 := by
    have h := B5Image_card d.card_Z B5
    change Nat.card ((B5:Subgroup d.toTypeRuSetup.H).map d.toTypeRuSetup.H.subtype)=5 at h
    rwa [card_map_of_injective d.toTypeRuSetup.H.subtype_injective] at h
  apply (pResidual_eq_top_iff 2 _).mp
  apply top_unique
  intro x _
  apply mem_pResidual_of_orderOf_coprime
  apply (by decide : Nat.Coprime 2 5).of_dvd_right
  exact (orderOf_dvd_natCard x).trans (dvd_of_eq hc)

private theorem le_embedded_residual {X : Type*} [Group X]
    (A J:Subgroup X) (hAJ:A≤J) (hp:IsPPerfect 2 A) :
    A≤(pResidual 2 J).map J.subtype := by
  have he := subgroupOfEquivOfLe hAJ
  have hA := le_pResidual_of_isPPerfect (A.subgroupOf J)
    (hp.of_surjective he.symm.toMonoidHom he.symm.surjective)
  have hh := Subgroup.map_mono (f:=J.subtype) hA
  rwa [map_subgroupOf_eq_of_le hAJ] at hh

theorem fiveHyperplaneNormalizer_residual (B5 : Sylow 5 d.toTypeRuSetup.H) :
    (pResidual 2 (fiveHyperplaneNormalizer d B5)).map (fiveHyperplaneNormalizer d B5).subtype =
      (B5:Subgroup d.toTypeRuSetup.H) ⊔ ⁅d.ru2.quotientMap.ker,(B5:Subgroup d.toTypeRuSetup.H)⁆ := by
  let N := fiveHyperplaneNormalizer d B5
  let R := (pResidual 2 N).map N.subtype
  let Q := d.ru2.quotientMap.ker
  let B := (B5:Subgroup d.toTypeRuSetup.H)
  have hB : IsPPerfect 2 B := B5_twoPerfect d B5
  have hBN : B≤N := B.le_normalizer.trans (five_normalizer_le_fiveHyperplaneNormalizer d B5)
  have hBR : B≤R := le_embedded_residual B N hBN hB
  have hQN : Q≤N := fiveHyperplaneNormalizer_ker d B5
  have hNR : N≤normalizer (R:Set d.toTypeRuSetup.H) := by
    have hh := (pResidual 2 N).le_normalizer_map N.subtype
    rwa [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] at hh
  have hRJ : R≤Q⊔B := by
    have hh := (le_comap_map d.ru2.quotientMap R).trans
      (Subgroup.comap_mono (f:=d.ru2.quotientMap)
        (fiveHyperplaneNormalizer_residual_image d B5).le)
    simpa only [comap_map_eq,sup_comm,Q,B,R,N] using hh
  have hQ : IsPGroup 2 Q := by
    change IsPGroup 2 d.ru2.quotientMap.ker
    rw [d.ru2.quotient_kernel]
    exact (isPGroup_pCoreIn 2 d.toTypeRuSetup.H).comap_subtype
  have hRR := le_embedded_residual R (Q⊔B) hRJ (isPPerfect_embedded_pResidual 2 N)
  rw [embedded_pResidual_sup_eq_sup_commutator Q B hQ hB] at hRR
  apply le_antisymm hRR
  exact sup_le hBR ((commutator_mono le_rfl hBR).trans
    (le_normalizer_iff_commutator_le_right.mp (hQN.trans hNR)))

/-- The literal source identity O²(N_H(Q₀Q₅))=B₅Q₅, in the original group. -/
theorem fiveNormalizer_twoResidual (B5 : Sylow 5 d.toTypeRuSetup.H) :
    (pResidual 2 (d.toTypeRuSetup.H⊓normalizer (fiveHyperplane d B5:Set G):Subgroup G)).map
      (d.toTypeRuSetup.H⊓normalizer (fiveHyperplane d B5:Set G)).subtype =
      B5Image B5⊔Q₅ d B5 := by
  have h := congrArg (Subgroup.map d.toTypeRuSetup.H.subtype)
    (fiveHyperplaneNormalizer_residual d B5)
  rw [map_embedded_pResidual] at h
  have hn : (fiveHyperplaneNormalizer d B5).map d.toTypeRuSetup.H.subtype =
      d.toTypeRuSetup.H⊓normalizer (fiveHyperplane d B5:Set G) := by
    rw [fiveHyperplaneNormalizer,subgroupOf_map_subtype,inf_comm]
  rw [hn,Subgroup.map_sup,Subgroup.map_commutator,d.ru2.quotient_kernel,
    map_subgroupOf_eq_of_le (pCoreIn_le 2 _)] at h
  exact h

theorem fiveProduct_inf_Q (B5 : Sylow 5 d.toTypeRuSetup.H) :
    (B5Image B5⊔Q₅ d B5)⊓d.toTypeRuSetup.Q=Q₅ d B5 := by
  have hd : Disjoint (B5Image B5) d.toTypeRuSetup.Q := by
    apply disjoint_of_coprime_natCard
    rw [B5Image_card d.card_Z B5,d.ru2.card_Q d.card_Z]
    decide
  have hn : B5Image B5≤normalizer (Q₅ d B5:Set G) := normalizer_commutator_ge_right _ _
  apply le_antisymm
  · intro x hx
    have hprod : x∈(Q₅ d B5:Set G)*(B5Image B5:Set G) := by
      rw [←coe_mul_of_right_le_normalizer_left _ _ hn,sup_comm]
      exact hx.1
    obtain ⟨a,ha,b,hb,he⟩ := hprod
    have hbQ : b∈d.toTypeRuSetup.Q := by
      have hbe : b=a⁻¹*x := by rw [←he]; group
      rw [hbe]
      exact mul_mem (inv_mem (Q₅_le_Q d B5 ha)) hx.2
    have hb1 := disjoint_def.mp hd hb hbQ
    have hax : a=x := by simpa only [hb1,mul_one] using he
    exact hax ▸ ha
  · exact le_inf le_sup_right (Q₅_le_Q d B5)

/-- The original H-normalizer of D normalizes its actual two-residual. -/
theorem normalizes_fiveProduct_of_normalizes_fiveHyperplane
    (B5 : Sylow 5 d.toTypeRuSetup.H) (A:Subgroup G)
    (hAH:A≤d.toTypeRuSetup.H) (hAD:A≤normalizer (fiveHyperplane d B5:Set G)) :
    A≤normalizer ((B5Image B5⊔Q₅ d B5:Subgroup G):Set G) := by
  rw [←fiveNormalizer_twoResidual]
  let N := d.toTypeRuSetup.H⊓normalizer (fiveHyperplane d B5:Set G)
  have h := (pResidual 2 N).le_normalizer_map N.subtype
  rw [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] at h
  exact (le_inf hAH hAD).trans h

/-- The same actors normalize Q₅, the actual Q-intersection of B₅Q₅. -/
theorem normalizes_Q₅_of_normalizes_fiveHyperplane
    (B5 : Sylow 5 d.toTypeRuSetup.H) (A:Subgroup G)
    (hAH:A≤d.toTypeRuSetup.H) (hAD:A≤normalizer (fiveHyperplane d B5:Set G)) :
    A≤normalizer (Q₅ d B5:Set G) := by
  have h := (le_inf (normalizes_fiveProduct_of_normalizes_fiveHyperplane d B5 A hAH hAD)
    (hAH.trans d.ru2.six.normalized)).trans inf_normalizer_le_normalizer_inf
  rwa [fiveProduct_inf_Q] at h

end CFSG.Quasithin.ChapterJ.RuSubgroup
