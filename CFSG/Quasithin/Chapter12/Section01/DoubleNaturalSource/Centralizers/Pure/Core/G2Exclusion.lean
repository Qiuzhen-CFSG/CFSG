module

public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Pure.Core.NormalizedQuotient
public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.NormalizerCover
public import Theory.AtlasPort.LinearGroups.G2.ParabolicLocalOrder
public import Theory.AtlasPort.LinearGroups.G2.Order
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support

/-!
# Excluding the G₂(4) component at the original pure point

The pure-point residual maps onto L_(n-1)(2), whose order has a factor seven
in both source dimensions. That factor survives its image in K/O₂(K).
It normalizes the actual nontrivial elementary moved image. In the concrete
G₂(4) model every nontrivial two-group normalizer lies in a conjugate root
parabolic, and the two parabolic orders are prime to seven.

Thus the literal G₂(4) alternative is impossible. Core.Complete applies the
result without leaving a local order or normalizer premise.
Source: Aschbacher--Smith 12.1.6, printed p.791, and 1.1.5(3)(b), p.501.
The imported octonion and projective-linear results retain the ATLAS license
and attribution in LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch.SourceModel
open Chapter15.Section03.Candidates.ComponentStructure ClassificationModels

private theorem g2_four_normalizer_not_seven {F : Type*} [Field F] [Finite F]
    (hF : Nat.card F = 4) (E : Subgroup (Atlas.G2.Model F))
    (hE : E ≠ ⊥) (hp : IsPGroup 2 E) :
    ¬ 7 ∣ Nat.card (normalizer (E : Set (Atlas.G2.Model F))) := by
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (f := 2)
    (by norm_num only [←Nat.card_eq_fintype_card,hF])
  obtain ⟨g,hg | hg⟩ := Atlas.G2.EvenLocal.NormalizerCover.normalizer_conjugate_le_parabolic E hE hp
  · intro hd
    have hh := card_dvd_of_le hg
    rw [card_map_of_injective (MulAut.conj g).injective] at hh
    have hd' := hd.trans hh
    rw [Atlas.G2.ParabolicCells.short_card,Atlas.G2.card_borel,hF] at hd'
    norm_num at hd'
  · intro hd
    have hh := card_dvd_of_le (hg.trans Atlas.G2.parabolic_le_pointStabilizer)
    rw [card_map_of_injective (MulAut.conj g).injective] at hh
    have hd' := hd.trans hh
    rw [Atlas.G2.card_pointStabilizer_formula,hF] at hd'
    norm_num at hd'

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}
  {B : DoubledBranch T L V n}
  [IsElementaryAbelian 2 (componentOrbit V (T : Subgroup G))]
  (S : B.SourceModel)

include S in
/-- The actual pure residual retains the factor seven of L_(n−1)(2). -/
theorem pure_residual_seven_dvd
    (w : componentOrbit V (T : Subgroup G)) (hw : w ≠ 1)
    (hp : (B.coordinates w).toAdd.2 = 0) : 7 ∣ Nat.card (B.pointResidual w) := by
  let u : S.setup.natural := ⟨Additive.ofMul w,(S.natural_marking w).mpr hp⟩
  let X := B.pointResidual w
  let f : X →* S.setup.stabilizer (Additive.ofMul w) :=
    (S.pureLocalAction w).comp (inclusion
      (le_inf (B.pointResidual_le_normalizer w) ((B.pointResidual_le w).trans inf_le_right)))
  have hf : Function.Surjective f := by
    intro a
    have ha : a.val ∈ S.setup.residual (Additive.ofMul w) :=
      (S.setup.pure_stabilizer_eq_residual u hw).1 ▸ a.property
    rw [← S.pointResidual_image w] at ha
    obtain ⟨l,hl,he⟩ := ha
    exact ⟨⟨l,mem_map_of_mem _ hl⟩,Subtype.ext he⟩
  let := S.setup.finite_group
  obtain ⟨e⟩ := S.setup.pure_quotient_projective u hw
  have hd : 7 ∣ Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin (n-1)) (ZMod 2)) := by
    rcases B.degree with rfl | rfl
    · have h := Atlas.ExceptionalSupport.card_psl_mul (F := ZMod 2) 3
      norm_num [Nat.card_zmod,Fin.prod_univ_succ] at h
      change 7 ∣ Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2))
      rw [Nat.card_eq_fintype_card,h]
      decide
    · have h := Atlas.ExceptionalSupport.card_psl_mul (F := ZMod 2) 4
      norm_num [Nat.card_zmod,Fin.prod_univ_succ] at h
      change 7 ∣ Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 4) (ZMod 2))
      rw [Nat.card_eq_fintype_card,h]
      decide
  rw [←Nat.card_congr e.toEquiv] at hd
  exact hd.trans ((card_dvd_of_surjective _ (QuotientGroup.mk'_surjective _)).trans
    (card_dvd_of_surjective f hf))

include S in
/-- The factor seven survives passage through the literal component two-core. -/
theorem pure_component_residual_image_seven
    (w : componentOrbit V (T : Subgroup G)) (hw : w ≠ 1)
    (hp : (B.coordinates w).toAdd.2 = 0)
    (K : Subgroup (B.pointCentralizer w))
    (hX : (B.pointResidual w).subgroupOf (B.pointCentralizer w) ≤ K) :
    let X := ((B.pointResidual w).subgroupOf (B.pointCentralizer w)).subgroupOf K
    7 ∣ Nat.card (X.map (QuotientGroup.mk' (pCore 2 K))) := by
  let H := B.pointCentralizer w
  let j : K →* G := H.subtype.comp K.subtype
  let X := (B.pointResidual w).comap j
  let q := QuotientGroup.mk' (pCore 2 K)
  have hXH : B.pointResidual w ≤ H := (B.pointResidual_le w).trans inf_le_right
  have hXm : X.map j = B.pointResidual w := by
    apply map_comap_eq_self
    rw [MonoidHom.range_comp,range_subtype]
    rw [←map_subgroupOf_eq_of_le hXH]
    exact map_mono hX
  have hxcard : Nat.card X = Nat.card (B.pointResidual w) := by
    rw [←card_map_of_injective (f := j) (H.subtype_injective.comp K.subtype_injective),hXm]
  have h7 : 7 ∣ Nat.card X := hxcard ▸ S.pure_residual_seven_dvd w hw hp
  let f := q.comp X.subtype
  have hk : IsPGroup 2 f.ker := by
    change IsPGroup 2 (q.ker.comap X.subtype)
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_of_injective _ X.subtype_injective
  have hnot : ¬ 7 ∣ Nat.card f.ker := by
    obtain ⟨k,hk⟩ := hk.exists_card_eq
    rw [hk]
    intro hd
    exact (by decide : ¬ 7 ∣ 2) (Nat.Prime.dvd_of_dvd_pow (by decide : Nat.Prime 7) hd)
  have hd : 7 ∣ Nat.card f.range := by
    rw [←f.ker.card_mul_index,index_ker] at h7
    exact (Nat.Prime.dvd_mul (by decide : Nat.Prime 7)).mp h7 |>.resolve_left hnot
  change 7 ∣ Nat.card (X.map q)
  simpa only [f,MonoidHom.range_comp,range_subtype] using hd

/-- The actual normalized moved image excludes the G₂(4) cover alternative. -/
theorem pure_component_not_g2_four
    (hNM : normalizer (componentOrbit V (T : Subgroup G) : Set G) = normalizer (L : Set G))
    (w : componentOrbit V (T : Subgroup G)) (hw : w ≠ 1)
    (hp : (B.coordinates w).toAdd.2 = 0)
    (K : Subgroup (B.pointCentralizer w))
    (hX : (B.pointResidual w).subgroupOf (B.pointCentralizer w) ≤ K)
    (hU : B.naturalSummand ⊔ S.pureDualHyperplane w hp ≤ K.map (B.pointCentralizer w).subtype)
    (hc : center K = pCore 2 K)
    (hm : IsG2At (K ⧸ pCore 2 K) 4) : False := by
  let H := B.pointCentralizer w
  let U := B.naturalSummand ⊔ S.pureDualHyperplane w hp
  let j : K →* G := H.subtype.comp K.subtype
  let A := U.comap j
  let X := (B.pointResidual w).comap j
  let q := QuotientGroup.mk' (pCore 2 K)
  obtain ⟨hE,hcard,_⟩ := S.pure_component_quotient_card_rank w hw hp K hX hU hc
  let : IsElementaryAbelian 2 (A.map q) := hE
  change Nat.card (A.map q) = 2^(2*n-2) at hcard
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let E := (A.map q).map e.toMonoidHom
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map e.toMonoidHom
  have hne : E ≠ ⊥ := by
    intro he
    have hz : Nat.card E = 1 := by rw [he]; simp
    dsimp only [E] at hz
    rw [card_map_of_injective e.injective,hcard] at hz
    rcases B.degree with rfl | rfl <;> norm_num at hz
  have hXN : X ≤ normalizer (A : Set K) := by
    apply le_trans _ (U.le_normalizer_comap j)
    intro x hx
    exact S.pure_moving_normalized hNM w hw hp
      ⟨B.pointResidual_le_normalizer w hx,((B.pointResidual_le w).trans inf_le_right) hx⟩
  have hn : (X.map q).map e.toMonoidHom ≤ normalizer (E : Set (Atlas.G2.Model F)) :=
    (map_mono ((map_mono hXN).trans (le_normalizer_map q))).trans
      (le_normalizer_map e.toMonoidHom)
  apply g2_four_normalizer_not_seven hF E hne (IsElementaryAbelian.isPGroup 2 E)
  have hd := S.pure_component_residual_image_seven w hw hp K hX
  have he : 7 ∣ Nat.card ((X.map q).map e.toMonoidHom) := by
    rwa [card_map_of_injective e.injective]
  exact he.trans (card_dvd_of_le hn)
end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch.SourceModel
