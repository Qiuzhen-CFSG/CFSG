module
public import Theory.GroupTheory.SelfCentralizingCoreNormalExtension
public import CFSG.Quasithin.Chapter6.Section01.SourceHStarMixedF11
public import CFSG.Quasithin.Chapter6.Section01.SourceHStarLeftCartanOvergroup

/-!
# Characteristic two for the actual mixed right parabolic

Source 6.1.5 uses the right local factor K=K₁S but the right parabolic
is KD_L. The S₃ quotient makes N_K(S)=S. Since D_L normalizes K and
S, the centralizer of S in KD_L lies in SD_L. The already established
faithfulness of D_L on Ω₁Z(T) then places this centralizer in S.
The normal-extension criterion passes characteristic two from K to KD_L.

Here S is literally Baum(T). The final consumer selects the actual left
Hall using Hypothesis611 and its natural fixed quotient, and obtains
characteristic two in K by subnormal inheritance from the H-star group.
Only the intervening selection and normalization premises remain explicit:
K≤H, subnormality, S Sylow in K, K/O₂(K)≃S₃, and D_L normalizing K and S.
No IsNaturalModule or conclusion of mixed F.1.12 is assumed.

Source: Aschbacher--Smith 6.1.5, printed p.667; F.1.1(f), printed p.259.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise
namespace CFSG.Quasithin.Chapter6.Source.Hypothesis611
variable {G : Type*} [Group G] [Finite G]

/-- The right parabolic in 6.1.5 inherits characteristic two from its cubic
local factor, using the actual Baumann subgroup and faithful left Hall. -/
theorem mixed_right_characteristic_two (T : Sylow 2 G) (K D : Subgroup G)
    (hK : K ∈ Chapter1.He G)
    (hS : Chapter1.IsSylowIn 2 (ChapterB.baumann (T : Subgroup G)) K)
    (e : (K ⧸ pCore 2 K) ≃* Equiv.Perm (Fin 3))
    (hDK : D ≤ normalizer (K : Set G))
    (hDS : D ≤ normalizer (ChapterB.baumann (T : Subgroup G) : Set G))
    (hfaith : D ⊓ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) = ⊥) :
    generalizedFitting (K ⊔ D : Subgroup G) = pCore 2 (K ⊔ D : Subgroup G) := by
  let S := ChapterB.baumann (T : Subgroup G)
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  have hSK : S ≤ K := (Chapter1.isSylowIn_iff.mp hS).2.1
  have hB : K ⊓ normalizer (S : Set G) = S := by
    have hb := ChapterF.Source.borel_eq_of_cubic_local_sylow K S hS e
    change K ⊓ normalizer ((S ⊓ K : Subgroup G) : Set G) = S at hb
    rwa [inf_eq_left.mpr hSK] at hb
  have hJT : elementaryAbelianMaxJ (T : Subgroup G) ≤ (T : Subgroup G) :=
    sSup_le fun _ hE => hE.1
  have hZS : Z ≤ S := by
    intro z hz
    have hzT := (mem_omegaOneCenterAmbient_iff _ _).mp hz
    refine ⟨hzT.1,?_⟩
    intro a ha
    have haJ := (mem_omegaOneCenterAmbient_iff _ _).mp ha
    exact hzT.2.2 a (hJT haJ.1)
  have hSZ : S ≤ centralizer (Z : Set G) := by
    intro s hs z hz
    exact ((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2 s hs.1 |>.symm
  apply generalizedFitting_eq_pCore_of_selfCentralizing 2
  exact core_selfCentralizing_sup_of_faithful_seed K S D Z
    (Chapter1.mem_He_iff.mp hK) (T.isPGroup'.to_le inf_le_left) hSK
    hDK hDS hB hZS hSZ hfaith

variable {T : Sylow 2 G} {L M V H : Subgroup G} {n : ℕ}
  (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
include h

/-- Subnormality inside the actual H-star subgroup supplies the local
characteristic-two premise by source 1.1.3(1). -/
theorem mixed_right_characteristic_two_of_subnormal
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (K D : Subgroup G) (hKH : K ≤ H) (hsub : (K.subgroupOf H).IsSubnormal)
    (hS : Chapter1.IsSylowIn 2 (ChapterB.baumann (T : Subgroup G)) K)
    (e : (K ⧸ pCore 2 K) ≃* Equiv.Perm (Fin 3))
    (hDK : D ≤ normalizer (K : Set G))
    (hDS : D ≤ normalizer (ChapterB.baumann (T : Subgroup G) : Set G))
    (hfaith : D ⊓ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) = ⊥) :
    generalizedFitting (K ⊔ D : Subgroup G) = pCore 2 (K ⊔ D : Subgroup G) := by
  have hc := Chapter1.mem_He_iff.mp
    (Chapter1.lemma_1_1_4_6 T (h.simpleQTKE.evenCharacteristic T) hH.1.1)
  have hK : K ∈ Chapter1.He G := Chapter1.mem_He_iff.mpr
    ((Theory.Quasithin.centralizer_pCore_le_iff 2 (subgroupOfEquivOfLe hKH)).mp
      (subnormal_core_selfCentralizing hc (K.subgroupOf H) hsub))
  exact mixed_right_characteristic_two T K D hK hS e hDK hDS hfaith

/-- The original source hypotheses choose one left Hall subgroup that has the
required characteristic-two extension property for each selected cubic factor.
The natural fixed quotient is the earlier 6.1.4 input. The normalizing and
cubic-factor selection clauses belong to the intervening 6.1.5 argument. -/
theorem exists_hstar_left_cartan_mixed_characteristic
    (hout : Chapter3.HasMaximalOutside T M)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hm : IsNaturalFixedQuotient L
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L) n)
    (hZH : ⁅omegaOneCenterAmbient (T : Subgroup G), H⁆ ≠ ⊥) :
    ∃ D : Subgroup G, D ≤ RankOneGeneric.localBorel T L ∧
      IsHallSubgroup OddHall.oddPrimes (D.subgroupOf (RankOneGeneric.localBorel T L)) ∧
      (D : Set G) * (T : Set G) = (T : Set G) * (D : Set G) ∧
      D ⊓ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) = ⊥ ∧
      D ⊔ H ∈ Chapter1.HOver G (T : Set G) ∧
      ∀ K : Subgroup G, K ≤ H → (K.subgroupOf H).IsSubnormal →
        Chapter1.IsSylowIn 2 (ChapterB.baumann (T : Subgroup G)) K →
        Nonempty ((K ⧸ pCore 2 K) ≃* Equiv.Perm (Fin 3)) →
        D ≤ normalizer (K : Set G) →
        D ≤ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) →
        generalizedFitting (K ⊔ D : Subgroup G) = pCore 2 (K ⊔ D : Subgroup G) := by
  obtain ⟨D,hD,hHall,hperm,hfaith,hX⟩ := h.exists_hstar_left_cartan_overgroup hout hH hm hZH
  refine ⟨D,hD,hHall,hperm,hfaith,hX,?_⟩
  intro K hKH hsub hS he hDK hDS
  obtain ⟨e⟩ := he
  exact h.mixed_right_characteristic_two_of_subnormal hH K D hKH hsub hS e hDK hDS hfaith
end CFSG.Quasithin.Chapter6.Source.Hypothesis611
