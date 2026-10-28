module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.SymplecticBorel
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.ContainedNormalizer
public import Theory.GroupTheory.PCoreImage

/-!
# The symplectic contained-normalizer branch on original source hypotheses

The original saturated pair supplies its mark. The proved symplectic source
Borel theorem identifies M∩D, whose two-core is the full component Sylow.
The contained-normalizer reduction places that core in D∩O₂(H_U), and
Sylow maximality gives equality. No Borel, centerlessness or action premise
is assumed; q=4 is included by the actual central-kernel theorem.

Source: Aschbacher--Smith 2.5.2(2) and 2.5.3(4), printed pp.551--553.
-/

public section
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.SymplecticFour
variable {G : Type*} [Group G] [Finite G] {M H U HU : Subgroup G}

/-- The literal source contained branch has no remaining Borel input. -/
theorem symplectic_contained_original_source_sylow
    {C : GroupClass} (hG : IsSimpleQTKE C G)
    (T₀ : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hT₀M : (T₀ : Subgroup G) ≤ M)
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T₀ : Subgroup G) ≤ N → N = M)
    (hH : H ∈ gammaZero (Chapter1.He G) M)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    {n : ℕ} (B : Fin n → Subgroup G)
    (hp : ∀ i, IsPGroup 2 (B i)) (hBH : ∀ i, B i ≤ H)
    (hHnorm : H = ⨅ i, normalizer (B i : Set G))
    (hpair : (U, HU) ∈ localPairsIn (Chapter1.He G) M H)
    (hsat : ∀ P : Subgroup G, P ≤ H → IsPGroup 2 P →
      HU ≤ normalizer (P : Set G) → P ≤ twoCore HU)
    (D : Subgroup H) (hD : IsComponent H D)
    (F : Type) [Field F] [Finite F] {k : ℕ} (hk : 2 ≤ k) (hF : Nat.card F = 2 ^ k)
    (e : D ⧸ center D ≃* ClassicalGroup.PSp 2 F)
    (hinside : (D ⊓ normalizer ((D ⊓ (twoCore HU).subgroupOf H : Subgroup H) : Set H)).map
      H.subtype ≤ M) :
    ∃ P : Sylow 2 D, (P : Subgroup D).map D.subtype = D ⊓ (twoCore HU).subgroupOf H := by
  obtain ⟨S,z,h,_hz⟩ := exists_marking_of_saturated_pair hG T₀ hM hT₀M hunique hH
    B hp hBH hHnorm hpair hsat
  obtain ⟨j,_hU,hB,_hinterchange⟩ := symplectic_borel_of_source_marking hH hempty h D hD F hk hF e
  let I := (M.subgroupOf H).subgroupOf D
  let Q := (twoCore HU).subgroupOf H
  let P₀ := unipotentSylow hF (by omega)
  let P := P₀.mapSurjective (f := j.symm.toMonoidHom) j.symm.surjective
  have hBm : I.map j.toMonoidHom = Theory.SpecificGroups.SymplecticFour.borel := by
    rw [show I = Theory.SpecificGroups.SymplecticFour.borel.comap j.toMonoidHom from hB, map_comap_eq_self_of_surjective j.surjective]
  have hcore : (I.pCoreIn 2).map j.toMonoidHom = unipotent := by
    rw [map_pCoreIn_of_injective 2 I j.toMonoidHom j.injective, hBm,
      EvenBorelTorus.borel_twoCoreIn hF]
  have hP : (P : Subgroup D) = I.pCoreIn 2 := by
    apply Subgroup.map_injective (f := j.toMonoidHom) j.injective
    rw [hcore]
    change ((P₀ : Subgroup (Sp F)).map j.symm.toMonoidHom).map j.toMonoidHom = _
    have hei : j.toMonoidHom.comp j.symm.toMonoidHom = MonoidHom.id _ := by
      apply MonoidHom.ext; intro x; exact j.apply_symm_apply x
    rw [map_map, hei, map_id, coe_unipotentSylow]
  have hPR : (P : Subgroup D) ≤ Q.subgroupOf D := hP.le.trans
    (intersection_core_le_saturated_component_of_normalizer_le hpair hsat D hD hinside)
  have heq : Q.subgroupOf D = (P : Subgroup D) :=
    P.is_maximal' (isPGroup_pCoreIn 2 HU).comap_subtype.comap_subtype hPR
  refine ⟨P, ?_⟩
  rw [← heq, subgroupOf_map_subtype, inf_comm]

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
