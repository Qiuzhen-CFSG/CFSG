module

public import Stellmacher.Recognition.Parrott.SecondTransferQuotientFusion
public import Theory.GroupTheory.LocalNormalizerUniqueness

/-!
# Unrestricted containment after Parrott's second transfer

The quotient-centralizer calculation on the literal second-transfer
subgroup supplies normality of its Sylow subgroup. Characteristicity then
makes the first transfer subgroup normalize Ω₁(Y)=F. Its index two, and
the known local Sylow order 512, give C_G(v) ≤ N_G(F).

This module replaces the solvable-Sylow step of the earlier containment
proof by the unrestricted TI argument. The quotient-centralizer calculation
remains the single explicit source input and has a separate producer;
neither solvability of C_G(v) nor IsNTwoGroup G is assumed.

Source: Parrott, *A characterization of the Tits' simple group* (1972),
printed p. 683, conclusion of Lemma 8.
-/

open Subgroup

namespace Stellmacher.Recognition.ParrottNormalizerFusionData

variable {G : Type*} [Group G] [Finite G] {z : G}
  {d : ParrottSecondElementaryData z} (n : ParrottNormalizerFusionData d)

/-- The actual second transfer implies ambient containment once the
quotient-centralizer transfer calculation has been supplied. -/
public theorem second_centralizer_le_normalizer_of_quotient_centralizers
    (h : ParrottCentralizerHypotheses z) :
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let W := (omega₁ K (p := 2)).map (N.subtype.comp K.subtype)
    let C := centralizer ({n.v} : Set G)
    let P := (d.sylow : Subgroup G) ⊓ C
    ∀ (M : Subgroup C) (L : Subgroup M),
    M.index = 2 → M.map C.subtype ⊓ P = W → L.Normal →
    let LG := L.map (C.subtype.comp M.subtype)
    let Y := W ⊓ LG
    (omega₁ Y (p := 2)).map Y.subtype = d.F →
    Nat.card P = 512 →
    ∀ S : Sylow 2 L,
    (S : Subgroup L).map (C.subtype.comp (M.subtype.comp L.subtype)) = Y →
    ∀ (B : Type*) [Group B] (v : L), ((v : M) : C).val = n.v →
    ∀ q : L →* B, Function.Surjective q → q.ker = zpowers v →
    (∀ x ∈ (S : Subgroup L).map q, orderOf x = 2 →
      centralizer ({x} : Set B) ≤ (S : Subgroup L).map q) →
    C ≤ N := by
  intro N K W C P M L hMi hMP hLn LG Y hYO hPcard S hS B _ v hv q hq hker hcent
  let : L.Normal := hLn
  let f : L →* G := C.subtype.comp (M.subtype.comp L.subtype)
  have hf : Function.Injective f :=
    C.subtype_injective.comp (M.subtype_injective.comp L.subtype_injective)
  have hFY : d.F ≤ Y := by
    rw [← hYO]
    exact map_subtype_le _
  have hFS : d.F ≤ (S : Subgroup L).map f := hS.symm ▸ hFY
  have hSn : (S : Subgroup L).Normal :=
    n.second_transfer_sylow_normal_of_quotient_centralizers h f hf S hFS v hv q hq hker hcent
  let : (S : Subgroup L).Characteristic := S.characteristic_of_normal hSn
  let U := (S : Subgroup L).map L.subtype
  have hMY : M.map C.subtype ≤ normalizer (Y : Set G) := by
    have hUn : U.Normal := inferInstance
    have hh := U.le_normalizer_map (C.subtype.comp M.subtype)
    rw [normalizer_eq_top, ← MonoidHom.range_eq_map, MonoidHom.range_comp,
      range_subtype] at hh
    simpa only [U, map_map, MonoidHom.comp_assoc, hS] using hh
  let : (omega₁ Y (p := 2)).Characteristic := omega₁_characteristic _
  have hMN : M.map C.subtype ≤ N := by
    have hh := hMY.trans (normalizer_le_normalizer_characteristic_image Y
      (omega₁ Y (p := 2)))
    rwa [hYO] at hh
  have hPN : P ≤ N := inf_le_left.trans d.sylow_le_normalizer
  have hex : ∃ w : G, w ∈ P ∧ w ∉ M.map C.subtype := by
    by_contra! hn
    have hPW : P = W := by rw [← hMP, inf_eq_right.mpr hn]
    have hcW : Nat.card W = 256 :=
      (card_map_of_injective (f := N.subtype.comp K.subtype)
        (K := omega₁ K (p := 2)) (N.subtype_injective.comp K.subtype_injective)).trans
        n.omega_card
    rw [hPW, hcW] at hPcard
    omega
  obtain ⟨w, hwP, hwM⟩ := hex
  intro x hxC
  let wC : C := ⟨w, hwP.2⟩
  let xC : C := ⟨x, hxC⟩
  have hw : wC ∉ M := fun hh => hwM (mem_map_of_mem C.subtype hh)
  by_cases hx : xC ∈ M
  · exact hMN (mem_map_of_mem C.subtype hx)
  · have hprod : wC * xC ∈ M := (mul_mem_iff_of_index_two hMi).mpr (iff_of_false hw hx)
    have hprodN : w * x ∈ N := hMN (mem_map_of_mem C.subtype hprod)
    exact (N.mul_mem_cancel_left (hPN hwP)).mp hprodN

end Stellmacher.Recognition.ParrottNormalizerFusionData
