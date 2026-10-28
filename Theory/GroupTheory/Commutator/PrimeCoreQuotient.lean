module
public import Theory.GroupTheory.PResidualCommutator
public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# Coprime commutator idempotence modulo the two-core

Let J be a two-subgroup normalizing Y, with Y/O₂(Y) a d-group for an
odd prime d. In YJ/O₂(Y), coprime commutator idempotence gives
[Y,J] ≤ [[Y,J],J] O₂(Y). The two-core is embedded from Y and its
normality is relative to YJ throughout.

This permits exact idempotence in any action that kills O₂(Y), without
requiring the entire preimage [Y,J] to be two-perfect.
Source application: Aschbacher--Smith 13.1.9, printed pp.870--871.
-/

public noncomputable section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]
/-- Coprime action gives idempotence after adjoining the original two-core. -/
theorem commutator_le_iterated_sup_twoCore (Y J : Subgroup G)
    (hJY : J ≤ normalizer (Y : Set G)) (hJ : IsPGroup 2 J)
    {d : ℕ} (hd : d.Prime) (hd2 : d ≠ 2) (hY : IsPGroup d (Y ⧸ pCore 2 Y)) :
    ⁅Y,J⁆ ≤ ⁅⁅Y,J⁆,J⁆ ⊔ Y.pCoreIn 2 := by
  let : Fact d.Prime := ⟨hd⟩
  let E := Y ⊔ J
  let N := (Y.pCoreIn 2).subgroupOf E
  have hEN : E ≤ normalizer (Y.pCoreIn 2 : Set G) :=
    (sup_le Y.le_normalizer hJY).trans
      (normalizer_le_normalizer_characteristic_image Y (pCore 2 Y))
  let : N.Normal := normal_subgroupOf_of_le_normalizer hEN
  let q := QuotientGroup.mk' N
  let Y₀ := Y.subgroupOf E
  let J₀ := J.subgroupOf E
  let : Y₀.Normal := normal_subgroupOf_of_le_normalizer (sup_le Y.le_normalizer hJY)
  have hpY : IsPGroup d (Y₀.map q) := by
    rintro ⟨_,y,hy,rfl⟩
    change (y : G) ∈ Y at hy
    obtain ⟨n,hn⟩ := hY (QuotientGroup.mk' (pCore 2 Y) ⟨y.val,hy⟩)
    refine ⟨n,Subtype.ext ?_⟩
    change q y ^ d ^ n = 1
    rw [← map_pow]
    apply (QuotientGroup.eq_one_iff _).mpr
    have hycore : (⟨y.val,hy⟩ : Y) ^ d ^ n ∈ pCore 2 Y :=
      (QuotientGroup.eq_one_iff _).mp (by
        change QuotientGroup.mk' (pCore 2 Y) ((⟨y.val,hy⟩ : Y) ^ d ^ n) = 1
        rw [map_pow]
        exact hn)
    exact mem_map_of_mem Y.subtype hycore
  have hpJ : IsPGroup 2 (J₀.map q) := hJ.comap_subtype.map q
  have hcop := IsPGroup.coprime_card_of_ne 2 d hd2.symm (J₀.map q) (Y₀.map q) hpJ hpY
  have hid := commutator_closure_coprime_idempotent (Y₀.map q) (J₀.map q : Set (E ⧸ N))
    (by rw [closure_eq]; exact le_normalizer_of_normal)
    (fun a ha => hcop.of_dvd_left ((J₀.map q).orderOf_dvd_natCard ha))
  simp only [closure_eq] at hid
  have hmap : (⁅Y₀,J₀⁆).map q ≤ (⁅⁅Y₀,J₀⁆,J₀⁆).map q := by
    rw [map_commutator,map_commutator,map_commutator,hid]
  have hb : ⁅Y₀,J₀⁆ ≤ ⁅⁅Y₀,J₀⁆,J₀⁆ ⊔ N := by
    have hh := (le_comap_map q ⁅Y₀,J₀⁆).trans (comap_mono hmap)
    simpa only [comap_map_eq,q,QuotientGroup.ker_mk'] using hh
  have hm := map_mono (f := E.subtype) hb
  simpa only [Y₀,J₀,N,map_commutator,map_sup,
    map_subgroupOf_eq_of_le (show Y ≤ E from le_sup_left),
    map_subgroupOf_eq_of_le (show J ≤ E from le_sup_right),
    map_subgroupOf_eq_of_le (show Y.pCoreIn 2 ≤ E from (pCoreIn_le 2 Y).trans le_sup_left)] using hm


end Subgroup
