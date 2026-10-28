module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.BorelActions.Reduction
public import Theory.SpecificGroups.Suzuki.RootCenter

/-!
# The Suzuki Borel witness in E.6.11

The displacement lies in the center of the prescribed Sylow subgroup and
has the same order q, so they are equal. Suzuki root-element centralizers
then identify C_L(V) with that Sylow subgroup. The direct decomposition of V
shows that its Sylow normalizer lies in M; conversely L ∩ M normalizes C_L(V).
Thus the transported split torus supplies the required cyclic complement in
L ∩ M, and the Sylow-center containment follows from the displacement equality.

The intrinsic center, centralizer and split-torus facts are transported through
an actual equivalence with the Suzuki matrix group. The only chapter inputs
are the genuine E.6.1 hypotheses and the E.6.8 output supplied in the contract.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.8(1)
and E.6.11, printed pp.247,249–250 (PDF pp.258,260–261).
-/

public section

open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterE.Section06.Components.BorelActions
variable {G : Type*} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {M V U Q L : Subgroup G} {n : ℕ}

/-- The cyclic complement and ambient Sylow-center comparison for the
Suzuki alternative, with its specified Sylow subgroup and matrix model. -/
theorem modelWitness_suzuki
    (h : HypothesisE61 K T M V) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (b : BorelAlternative M V U L n) (hn : 1 < n)
    (hVL : V ≤ normalizer (L : Set G))
    (hQ : Q = sylowCentralizer (T : Subgroup G) V)
    (S : Sylow 2 L) (hS : (S : Subgroup L).map L.subtype = L ⊓ Q)
    (m : ℕ) (hm : 1 ≤ m) (hnm : n = 2 * m + 1)
    (e : L ≃* SuzukiMatrixGroup m) : ModelWitness M V Q L n := by
  obtain ⟨hcard, hcent, D, ⟨eD⟩, hsup, hdis⟩ :=
    suzukiSylow_borel_structure (Nat.succ_le_iff.mp hm) e S
  let A := L ⊓ Q
  have hSA : (S : Subgroup L).map L.subtype = A := hS
  let W := ⁅V, L ⊓ M⁆
  let Z := (center A).map A.subtype
  let X := D.map L.subtype
  let N := L ⊓ normalizer (A : Set G)
  have hWV : W ≤ V := le_sup_left.trans (b.decomposition hn).1.le
  have hWZ : W ≤ Z := displacement_le_center h hU hL hVL hQ
  have hZA : Z ≤ A := map_subtype_le (center A)
  have hWL : W ≤ L := hWZ.trans (hZA.trans inf_le_left)
  let eS : S ≃* A := ((S : Subgroup L).equivMapOfInjective L.subtype
    L.subtype_injective).trans (MulEquiv.subgroupCongr hS)
  have hZcard : Nat.card Z = 2 ^ n := by
    calc
      Nat.card Z = Nat.card (center A) := card_map_of_injective A.subtype_injective
      _ = Nat.card (center S) := (Nat.card_congr (centerCongr eS).toEquiv).symm
      _ = 2 ^ n := by simpa only [hnm] using hcard
  have hW : W = Z := eq_of_le_of_card_ge hWZ (by
    rw [hZcard, displacement_card h b hn])
  have hWne : W ≠ ⊥ := by
    intro hh
    have hc := displacement_card h b hn
    change Nat.card W = 2 ^ n at hc
    simp only [hh, Subgroup.card_bot] at hc
    have : 1 < 2 ^ n := one_lt_pow₀ (by decide) (by omega)
    omega
  obtain ⟨⟨w, hw⟩, hwne'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hWne
  have hwne : w ≠ 1 := fun he => hwne' (Subtype.ext he)
  have hwS : (⟨w, hWL hw⟩ : L) ∈ (S : Subgroup L) := by
    have hwA := hZA (hWZ hw)
    rw [← hSA] at hwA
    obtain ⟨z, hz, he⟩ := hwA
    have he' : z = (⟨w, hWL hw⟩ : L) := Subtype.ext he
    exact he' ▸ hz
  have hC : L ⊓ centralizer (V : Set G) = A := by
    rw [← displacement_centralizer b hn]
    apply le_antisymm
    · rintro c ⟨hcL, hcV⟩
      have hc : (⟨c, hcL⟩ : L) ∈ centralizer ({⟨w, hWL hw⟩} : Set L) := by
        apply mem_centralizer_singleton_iff.mpr
        apply Subtype.ext
        exact (mem_centralizer_iff.mp hcV w hw).symm
      have hcS := hcent ⟨w, hWL hw⟩ hwS (fun he => hwne (congrArg Subtype.val he)) hc
      exact hSA ▸ (mem_map_of_mem L.subtype hcS)
    · exact inf_le_inf_left L ((hQ.symm ▸
        (show sylowCentralizer (T : Subgroup G) V ≤ centralizer (V : Set G)
          from inf_le_right)).trans (Subgroup.centralizer_le hWV))
  have hBN : L ⊓ M ≤ N := by
    apply le_inf inf_le_left
    rw [← hC]
    exact (le_inf (inf_le_left.trans L.le_normalizer)
      ((component_intersection_normalizes h hU hL.1).trans
        (normalizer_le_normalizer_centralizer V))).trans
      inf_normalizer_le_normalizer_inf
  have hNB : N ≤ L ⊓ M := by
    apply le_inf inf_le_left
    apply le_trans ?_ h.normalizer_le
    have hNW : N ≤ normalizer (W : Set G) := by
      rw [hW]
      exact inf_le_right.trans (normalizer_le_normalizer_characteristic_image A (center A))
    have hNF : N ≤ normalizer ((V ⊓ centralizer (L : Set G) : Subgroup G) : Set G) :=
      (inf_le_left.trans (le_centralizer_iff.mpr inf_le_right)).trans
        (centralizer_le_normalizer _)
    rw [← (b.decomposition hn).1]
    exact (le_inf hNW hNF).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hAS : A.subgroupOf L = (S : Subgroup L) := by
    rw [← hSA]
    exact comap_map_eq_self_of_injective L.subtype_injective _
  have hNmap : (normalizer (S : Set L)).map L.subtype = N := by
    change (normalizer ((S : Subgroup L) : Set L)).map L.subtype = N
    rw [← hAS, ← subgroupOf_normalizer_eq (show A ≤ L from inf_le_left),
      subgroupOf_map_subtype]
    exact inf_comm _ _
  have hAX : A ⊔ X = L ⊓ M := by
    rw [show A = (S : Subgroup L).map L.subtype from hS.symm,
      ← Subgroup.map_sup, hsup, hNmap]
    exact le_antisymm hNB hBN
  have hX : X ≤ L ⊓ M := hAX ▸ le_sup_right
  have eX : X ≃* Multiplicative (ZMod (2 ^ n - 1)) := by
    rw [hnm]
    exact (D.equivMapOfInjective L.subtype L.subtype_injective).symm.trans eD
  refine ⟨⟨X, hX, ⟨eX⟩, ?_, ?_⟩, ?_⟩
  · rwa [hC]
  · rw [hC, show A = (S : Subgroup L).map L.subtype from hS.symm,
      ← Subgroup.map_inf _ _ _ L.subtype_injective, hdis, Subgroup.map_bot]
  · change Z ≤ _
    rw [← hW]
    exact le_sup_right

end CFSG.Quasithin.ChapterE.Section06.Components.BorelActions
