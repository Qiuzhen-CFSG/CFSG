module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Centralizer.SourceCount.Definitions

/-!
# Placement and centralizers in the original source normalizer

The distinguished normal two-subgroup A and U = O₂(J) both lie in V = O₂(M).
Thus AU lies in R₁ = N_V(AU), which centralizes A. The source centralizer product AJ and D ∩ V = U prove the local-normalizer
equality (15F). Every element of R₁ outside AU therefore has trivial
centralizer in U. This uses the already proved involution transporter in G.

All subgroups are the original subtype images; no order-two or normal-closure
count is used. These facts are the inputs to the source normalizer growth and
involution census of GLS IV, Chapter 2, Lemma 15.6,
refs/KGroup/GLS4/Chapter2.tex, lines 2718–2745.
-/

noncomputable section
namespace BenderSuzuki.ZD.LinearExclusion.SourceCount
open Subgroup Theory.GroupTheory
open scoped Pointwise
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {n : ℕ} (d : Context Z M z t n)
local notation "L" => residualGenerated M z t
local notation "J" => centralizer (L : Set G)
local notation "V" => pointCore M
local notation "U" => twoCore M z t
local notation "A" => closure (Z ∩ (M : Set G))
local notation "R" => sourceNormalizer Z M z t

/-- The subtype image of the nontrivial two-core remains nontrivial. -/
public theorem twoCore_ne_bot (hs : CentralizerLocalTwoData d) : U ≠ ⊥ := by
  intro he
  apply hs.twoCore_ne_bot
  apply Subgroup.map_injective (f := (J).subtype) Subtype.val_injective
  simpa only [twoCore, Subgroup.map_bot] using he

/-- Lemma 15.5 places the actual U inside the actual V. -/
public theorem twoCore_le_pointCore (hs : CentralizerLocalTwoData d) : U ≤ pointCore M := by
  change (pCore 2 J).map (J).subtype ≤ (pCore 2 M).map M.subtype
  rw [← hs.pair_core_eq]
  exact inf_le_right

include d in
/-- The distinguished elementary abelian normal subgroup lies in O₂(M). -/
public theorem distinguished_le_pointCore : A ≤ pointCore M := by
  let : ((A).subgroupOf M).Normal := distinguishedClosure_normal d.minimal.disconnected
  have hp : IsPGroup 2 ((A).subgroupOf M) :=
    (IsPGroup.of_card d.distinguished_elementary_card.2).of_equiv
      (subgroupOfEquivOfLe distinguishedClosure_le).symm
  have hc : (A).subgroupOf M ≤ pCore 2 M := le_sSup ⟨inferInstance, hp⟩
  intro a ha
  exact ⟨⟨a, distinguishedClosure_le ha⟩, hc ha, rfl⟩

/-- The original product AU is contained in its normalizer inside V. -/
public theorem sup_le_sourceNormalizer (hs : CentralizerLocalTwoData d) : A ⊔ U ≤ R :=
  le_inf (sup_le (distinguished_le_pointCore d) (twoCore_le_pointCore d hs)) le_normalizer

omit [Finite G] in
/-- The normalizer under study is contained in the original point stabilizer. -/
public theorem sourceNormalizer_le_point : R ≤ M :=
  inf_le_left.trans (map_subtype_le _)

include d in
/-- The original point two-core centralizes A, before any counting conclusion. -/
public theorem pointCore_centralizes_distinguished : V ≤ centralizer (A : Set G) := by
  rintro _ ⟨v, hv, rfl⟩ a ha
  exact congrArg Subtype.val
    (mem_centralizer_iff.mp
      (linear_twoCore_le_distinguished_centralizer d.minimal.disconnected d.reduction hv)
      ⟨a, distinguishedClosure_le ha⟩ ha)

/-- Source (15F), strengthened to equality: N_V(L) = AU. The product AJ
comes from the actual normalizer centralizer, and D ∩ V = U removes its
remaining factor. No order of U or supplement for M is assumed. -/
public theorem pointCore_inf_normalizer (hs : CentralizerLocalTwoData d) :
    V ⊓ normalizer (L : Set G) = A ⊔ U := by
  have hAV : A ≤ V := distinguished_le_pointCore d
  have hUC : U ≤ J := map_subtype_le _
  have hJA : J ≤ centralizer (A : Set G) := centralizer_le d.distinguished_le
  apply le_antisymm
  · intro x hx
    have hAJ : x ∈ A ⊔ J := d.normalizer_inf_centralizer_eq ▸
      (show x ∈ normalizer (L : Set G) ⊓ centralizer (A : Set G) from
        ⟨hx.2, pointCore_centralizes_distinguished d hx.1⟩)
    have hprod := coe_mul_of_right_le_normalizer_left A J
      (hJA.trans (Subgroup.centralizer_le_normalizer _))
    obtain ⟨a, ha, j, hj, rfl⟩ := (Set.ext_iff.mp hprod x).mp hAJ
    have hjV : j ∈ V := by
      have hh := (V).mul_mem ((V).inv_mem (hAV ha)) hx.1
      simpa only [inv_mul_cancel_left] using hh
    have hjD : j ∈ residualPairStabilizer M t :=
      centralizer_residualGenerated_le_pair d.minimal.disconnected d.z_mem d.z_mem_M hj
    have hjU : j ∈ U := by
      change j ∈ (pCore 2 J).map (J).subtype
      rw [← hs.pair_core_eq]
      exact ⟨hjD, hjV⟩
    exact (A ⊔ U).mul_mem ((show A ≤ A ⊔ U from le_sup_left) ha)
      ((show U ≤ A ⊔ U from le_sup_right) hjU)
  · exact sup_le (le_inf hAV (d.distinguished_le.trans (L).le_normalizer))
      (le_inf (twoCore_le_pointCore d hs) (hUC.trans (Subgroup.centralizer_le_normalizer _)))

/-- Source (15E) and (15F) also identify the normalizer of U inside V. -/
public theorem pointCore_inf_twoCore_normalizer (hs : CentralizerLocalTwoData d) :
    V ⊓ normalizer (U : Set G) = A ⊔ U := by
  change V ⊓ normalizer ((pCore 2 J).map (J).subtype : Set G) = _
  rw [d.centralizer_twoCore_normalizer_eq hs.twoCore_ne_bot]
  exact pointCore_inf_normalizer d hs

include d in
/-- The actual R₁ centralizes A, by the source Lemma 15.2(h). -/
public theorem sourceNormalizer_centralizes_distinguished : R ≤ centralizer (A : Set G) :=
  inf_le_left.trans (pointCore_centralizes_distinguished d)

/-- Equation (15F) forces C_U(x)=1 for x in R₁ outside AU. This is the
fixed-point input to the subsequent square and involution census. -/
public theorem twoCore_centralizer_outside_sup (hs : CentralizerLocalTwoData d)
    {x : G} (hx : x ∈ R) (hxA : x ∉ A ⊔ U) :
    U ⊓ centralizer ({x} : Set G) = ⊥ := by
  apply eq_bot_iff.mpr
  intro u hu
  change u = 1
  by_contra hu1
  have huJ : u ∈ J := map_subtype_le _ hu.1
  have hu2 : u ^ 2 = 1 := congrArg Subtype.val
    (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      hs.twoCore_elementary.exponent_dvd_p ⟨u, hu.1⟩)
  have hxN : x ∈ normalizer (residualGenerated M z t : Set G) :=
    d.involution_centralizer_le huJ ⟨hu1, hu2⟩
      (mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp hu.2).symm)
  apply hxA
  rw [← pointCore_inf_normalizer d hs]
  exact ⟨hx.1, hxN⟩


end BenderSuzuki.ZD.LinearExclusion.SourceCount
