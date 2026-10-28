module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientQuintic

/-!
# The exact two-core quotient of the original quintic residual

The same order-five torus complements the intersection of X with T∩L.
That intersection is the normal Sylow two-subgroup of X, hence exactly
O₂(X). Thus the literal quotient X/O₂(X) has order five, with its ambient
kernel identified as X∩T. No quotient model is an input.
Source: Aschbacher--Smith 6.1.4, printed p.665.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise
attribute [local instance] Representation.SL2.BinarySmall.spaceBinaryModule
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V : Subgroup G} {n : ℕ}

private theorem two_core_of_quintic_supplement
    (X U D : Subgroup G) (hU : IsPGroup 2 U) (hD : Nat.card D = 5)
    (hDU : D ≤ normalizer (U : Set G)) (hDX : D ≤ X) (hX : X ≤ U ⊔ D) :
    X.pCoreIn 2 = X ⊓ U ∧ Nat.card (X ⧸ pCore 2 X) = 5 := by
  have hdis : Disjoint U D := by
    obtain ⟨k,hk⟩ := hU.exists_card_eq
    exact disjoint_of_coprime_natCard (by rw [hk,hD]; exact (by decide : Nat.Coprime 2 5).pow_left k)
  have hn : X ≤ normalizer (U : Set G) := hX.trans (sup_le U.le_normalizer hDU)
  have hgen : (X ⊓ U) ⊔ D = X := by
    apply le_antisymm (sup_le inf_le_left hDX)
    intro x hx
    have hp : x ∈ (U : Set G) * (D : Set G) := by
      rw [←coe_mul_of_right_le_normalizer_left U D hDU]
      exact hX hx
    obtain ⟨u,hu,d,hd,he⟩ := hp
    have huX : u ∈ X := by
      have hh := X.mul_mem hx (X.inv_mem (hDX hd))
      rwa [←he,mul_inv_cancel_right] at hh
    exact he ▸ mul_mem_sup ⟨huX,hu⟩ hd
  have hDn : D ≤ normalizer (X ⊓ U : Set G) :=
    (le_inf (hDX.trans X.le_normalizer) hDU).trans inf_normalizer_le_normalizer_inf
  have hc : Nat.card X = Nat.card (X ⊓ U : Subgroup G) * 5 := by
    calc
      Nat.card X = Nat.card ((X ⊓ U) ⊔ D : Subgroup G) := congrArg Nat.card (congrArg (fun K : Subgroup G => ↥K) hgen.symm)
      _ = Nat.card (X ⊓ U : Subgroup G) * Nat.card D :=
        card_sup_eq_mul_of_normalizes_of_disjoint _ _ hDn (hdis.mono_left inf_le_right)
      _ = _ := by rw [hD]
  let N := U.subgroupOf X
  let : N.Normal := normal_subgroupOf_of_le_normalizer hn
  have hN : IsPGroup 2 N := hU.comap_subtype
  have hmap : N.map X.subtype = X ⊓ U := by rw [subgroupOf_map_subtype,inf_comm]
  have hcardN : Nat.card N = Nat.card (X ⊓ U : Subgroup G) := by
    rw [←hmap,card_map_of_injective X.subtype_injective]
  have hi : N.index = 5 := by
    have hi := N.card_mul_index
    rw [hcardN,hc] at hi
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos hi
  let P : Sylow 2 X := hN.toSylow (by rw [hi]; decide)
  have hcore : pCore 2 X = N :=
    le_antisymm (pCore_isPGroup.le_sylow_of_normal P) (le_sSup ⟨inferInstance,hN⟩)
  constructor
  · rw [pCoreIn,hcore,hmap]
  · rw [←index_eq_card,hcore,hi]

/-- The literal original quintic residual has the asserted two-core and
quotient of order five. The kernel is its actual intersection with T. -/
theorem original_hermitian_quintic_core_quotient
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hm : IsConjugationModel L (reducedSubgroup (L ⊔ (T : Subgroup G)))
      (Representation.SL2.BinarySmall.hermitian 2)) :
    (quinticResidual T L).pCoreIn 2 = quinticResidual T L ⊓ (T : Subgroup G) ∧
      Nat.card (quinticResidual T L ⧸ pCore 2 (quinticResidual T L)) = 5 := by
  obtain ⟨D,hD,hDB,hDX,hX,_,_⟩ := original_hermitian_quintic_torus h hout hm
  have hh := two_core_of_quintic_supplement (quinticResidual T L) ((T : Subgroup G) ⊓ L) D
    (T.isPGroup'.to_le inf_le_left) hD (hDB.trans inf_le_right) hDX hX
  have hXL : quinticResidual T L ≤ L := (map_subtype_le _).trans inf_le_left
  have he : quinticResidual T L ⊓ ((T : Subgroup G) ⊓ L) =
      quinticResidual T L ⊓ (T : Subgroup G) := by
    exact le_antisymm (inf_le_inf_left _ inf_le_left)
      (le_inf inf_le_left (le_inf inf_le_right (inf_le_left.trans hXL)))
  exact ⟨hh.1.trans he,hh.2⟩

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
