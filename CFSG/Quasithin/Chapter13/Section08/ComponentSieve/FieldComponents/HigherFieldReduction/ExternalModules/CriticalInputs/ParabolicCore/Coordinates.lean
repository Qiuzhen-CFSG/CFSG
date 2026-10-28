module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.LinearTwo.FiveReconstruction.MovedAction
public import Theory.SpecificGroups.Alternating.FiveBorelCentralFactor
public import Theory.GroupTheory.SymmetricThreeTwoCore
public import Theory.GroupTheory.PCoreProduct

/-!
# The marked exceptional parabolic in the tensor coordinates

Borel normalization places the subgroup inside a point stabilizer S₄ × S₃.
Its actual Sylow two-subgroup supplies the factor sixteen, and the covered
local quotient supplies the factor nine, forcing equality of orders.
The two-core has trivial second coordinate; an odd first coordinate would
have a nontrivial cubic commutator in a two-group. Finally the intrinsic
Sylow-normalizer core recovers the prescribed Sylow intersection.

Source: Aschbacher–Smith, proof of 13.8.20(a), printed p.954/PDF p.971.
These are coordinate calculations; the source marking and order-nine input
are discharged in the parent module.
-/

open Subgroup
open scoped commutatorElement
public section

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.CriticalInputs.ParabolicCore.Coordinates
local notation "S5" => Equiv.Perm (Fin 5)
local notation "S3" => Equiv.Perm (Fin 3)
local notation "A5" => alternatingGroup (Fin 5)

private theorem point_card (i : Fin 5) :
    Nat.card (MulAction.stabilizer S5 i) = 24 := by
  rw [Nat.card_eq_fintype_card]
  exact (by decide +kernel : ∀ i : Fin 5,
    Fintype.card (MulAction.stabilizer S5 i) = 24) i

private theorem point_core_even (i : Fin 5) :
    (MulAction.stabilizer S5 i).pCoreIn 2 ≤ A5 := by
  let J := MulAction.stabilizer S5 i
  let Q := J.pCoreIn 2
  intro t ht
  by_contra hodd
  obtain ⟨b, hb, hc, hn⟩ :=
    Theory.SpecificGroups.Alternating.FiveBorelCentralFactor.odd_actor_cubic_witness
      i t ((pCoreIn_le 2 J) ht) hodd
  have hmem : ⁅b, t⁆ ∈ Q := by
    rw [commutatorElement_def]
    exact Q.mul_mem
      (le_normalizer_iff.mp
        (J.le_normalizer.trans (normalizer_le_normalizer_characteristic_image J (pCore 2 J)))
        b hb.2 t ht) (Q.inv_mem ht)
  let x : Q := ⟨⁅b, t⁆, hmem⟩
  have hx : x ^ 3 = 1 := Subtype.ext hc
  have hone : x = 1 := orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes
      ((isPGroup_pCoreIn 2 J).orderOf_coprime (by decide : Nat.Coprime 2 3) x)
      dvd_rfl (orderOf_dvd_of_pow_eq_one hx))
  exact hn (congrArg Subtype.val hone)

private theorem three_core : (⊤ : Subgroup S3).pCoreIn 2 = ⊥ := by
  have hc : pCore 2 S3 = ⊥ := by
    have h := ker_eq_twoCore_of_surjective_perm_three (MonoidHom.id S3)
      Function.surjective_id (by rw [MonoidHom.ker_id]; exact IsPGroup.of_bot)
    simpa using h.symm
  have hm := pCore_map_iso 2 (Subgroup.topEquiv : (⊤ : Subgroup S3) ≃* S3)
  change (⊤ : Subgroup S3).pCoreIn 2 = pCore 2 S3 at hm
  exact hm.trans hc

private theorem model_core_le (i : Fin 5) :
    ((MulAction.stabilizer S5 i).prod (⊤ : Subgroup S3)).pCoreIn 2 ≤ (A5).prod ⊥ := by
  rw [pCoreIn_prod, three_core]
  exact prod_mono (point_core_even i) le_rfl

private theorem model_card (i : Fin 5) :
    Nat.card ((MulAction.stabilizer S5 i).prod (⊤ : Subgroup S3)) = 144 := by
  rw [Nat.card_congr (prodEquiv _ _).toEquiv, Nat.card_prod, point_card,
    Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup S3) ≃* S3).toEquiv]
  norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]

variable {D U : Type*} [Group D] [Finite D] [AddCommGroup U] [Module (ZMod 2) U]
  {ρ : Representation (ZMod 2) D U} {K : Subgroup D} {s : S3 →* D}
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.LinearTwo.FiveReconstruction

private theorem marked_borel_coordinates (c : FullCoordinates ρ K s) (S : Sylow 2 K) :
    ∃ i : Fin 5, ((normalizer (S : Set K)).map K.subtype).map c.groupEquiv.toMonoidHom =
      (A5 ⊓ MulAction.stabilizer S5 i).prod ⊥ := by
  let S' := S.mapSurjective (f := c.component.toMonoidHom) c.component.surjective
  obtain ⟨i, hi⟩ :=
    Theory.SpecificGroups.Alternating.FiveBorelOvergroups.sylow_normalizer_eq_stabilizer S'
  let emb : A5 →* S5 × S3 :=
    { toFun a := (a.val, 1)
      map_one' := rfl
      map_mul' _ _ := by simp }
  have hhom : c.groupEquiv.toMonoidHom.comp K.subtype = emb.comp c.component.toMonoidHom := by
    apply MonoidHom.ext
    intro k
    exact c.component_apply k
  refine ⟨i, ?_⟩
  rw [map_map, hhom, ← map_map]
  change ((normalizer ((S : Subgroup K) : Set K)).map c.component.toMonoidHom).map emb = _
  rw [map_equiv_normalizer_eq]
  change (normalizer (S' : Set A5)).map emb = _
  rw [hi]
  ext p
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a.property, ha⟩, rfl⟩
  · rintro ⟨⟨ha, hi⟩, h3⟩
    exact ⟨⟨p.1, ha⟩, hi, Prod.ext rfl (mem_bot.mp h3).symm⟩

private theorem normalizing_borel_bound (c : FullCoordinates ρ K s) (S : Sylow 2 K)
    (J : Subgroup D)
    (hn : J ≤ normalizer ((normalizer (S : Set K)).map K.subtype : Set D)) :
    ∃ i : Fin 5, J.map c.groupEquiv.toMonoidHom ≤
      (MulAction.stabilizer S5 i).prod (⊤ : Subgroup S3) := by
  obtain ⟨i, hi⟩ := marked_borel_coordinates c S
  let π := (MonoidHom.fst S5 S3).comp c.groupEquiv.toMonoidHom
  have hB : ((normalizer (S : Set K)).map K.subtype).map π =
      A5 ⊓ MulAction.stabilizer S5 i := by
    rw [← map_map, hi]
    ext x
    exact ⟨fun ⟨p, hp, he⟩ => he ▸ hp.1, fun hx => ⟨(x,1), ⟨hx, rfl⟩, rfl⟩⟩
  have hN := (map_mono (f := π) hn).trans (le_normalizer_map π)
  rw [hB,
    Theory.SpecificGroups.Alternating.FiveBorelCentralFactor.even_stabilizer_normalizer] at hN
  refine ⟨i, ?_⟩
  rintro p ⟨x, hx, rfl⟩
  exact ⟨hN (mem_map_of_mem π hx), mem_top _⟩

/-- The actual normalizing subgroup fills the marked point stabilizer product. -/
theorem parabolic_coordinates (c : FullCoordinates ρ K s) (S : Sylow 2 K)
    (J : Subgroup D) (P : Sylow 2 D) (hPJ : (P : Subgroup D) ≤ J)
    (hn : J ≤ normalizer ((normalizer (S : Set K)).map K.subtype : Set D))
    (h9 : 9 ∣ Nat.card J) :
    ∃ i : Fin 5, J.map c.groupEquiv.toMonoidHom =
      (MulAction.stabilizer S5 i).prod (⊤ : Subgroup S3) := by
  obtain ⟨i, hi⟩ := normalizing_borel_bound c S J hn
  have hD : Nat.card D = 720 := by
    rw [Nat.card_congr c.groupEquiv.toEquiv, Nat.card_prod]
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  have h16 : 16 ∣ Nat.card J :=
    (P.pow_dvd_card_of_pow_dvd_card (n := 4) (by rw [hD]; norm_num)).trans
      (card_dvd_of_le hPJ)
  have h144 : 144 ∣ Nat.card J :=
    (by decide : Nat.Coprime 16 9).mul_dvd_of_dvd_of_dvd h16 h9
  refine ⟨i, eq_of_le_of_card_ge hi ?_⟩
  rw [card_map_of_injective c.groupEquiv.injective, model_card]
  exact Nat.le_of_dvd Nat.card_pos h144

/-- Its two-core is exactly the prescribed component Sylow intersection. -/
theorem parabolic_core (c : FullCoordinates ρ K s) (S : Sylow 2 K)
    (J : Subgroup D) (P : Sylow 2 D) (hPJ : (P : Subgroup D) ≤ J)
    (hn : J ≤ normalizer ((normalizer (S : Set K)).map K.subtype : Set D))
    (hS : (S : Subgroup K).map K.subtype = (P : Subgroup D) ⊓ K)
    (h9 : 9 ∣ Nat.card J) : J.pCoreIn 2 = (P : Subgroup D) ⊓ K := by
  have hcore : (normalizer (S : Set K)).pCoreIn 2 = (S : Subgroup K) := by
    have hSC : (S : Subgroup K) ≤ (normalizer (S : Set K)).pCoreIn 2 :=
      le_pCoreIn_of_normalizes S.isPGroup' (S : Subgroup K).le_normalizer le_rfl
    exact S.is_maximal' (isPGroup_pCoreIn 2 _) hSC
  have hBcore : ((normalizer (S : Set K)).map K.subtype).pCoreIn 2 =
      (P : Subgroup D) ⊓ K := by
    rw [← map_pCoreIn_of_injective 2 _ K.subtype K.subtype_injective, hcore, hS]
  have hJn : J ≤ normalizer (((P : Subgroup D) ⊓ K : Subgroup D) : Set D) := by
    rw [← hBcore]
    exact hn.trans (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
  apply le_antisymm
  · have hQP : J.pCoreIn 2 ≤ (P : Subgroup D) := by
      have h := pCoreIn_le_sylow J (P.subtype hPJ)
      simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hPJ] using h
    refine le_inf hQP ?_
    obtain ⟨i, hi⟩ := parabolic_coordinates c S J P hPJ hn h9
    apply (map_le_map_iff_of_injective (f := c.groupEquiv.toMonoidHom) c.groupEquiv.injective).mp
    rw [map_pCoreIn_of_injective 2 _ _ c.groupEquiv.injective, hi, c.map_component]
    exact model_core_le i
  · exact le_pCoreIn_of_normalizes (P.isPGroup'.to_le inf_le_left)
      (inf_le_left.trans hPJ) hJn

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.CriticalInputs.ParabolicCore.Coordinates

end
