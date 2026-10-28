module
public import Theory.GroupTheory.SylowSeedCommutator

/-!
# The centralizer of a moved Sylow seed

For Z = Ω₁Z(S), with S Sylow in XS and normalizing X, assume the
conjugate span W = ⟨Z^X⟩ is elementary and contained in S. Odd-index
Sylow averaging splits each z in Z into a vector of [W,X]∩Z and a
vector centralizing X. Hence C_X([W,X]∩Z) = C_X(Z).

This retains the original seed, rather than just its generated module.
Source: Aschbacher--Smith, 15.2.23, printed p.1116, using B.2.14.
-/

public section
open Subgroup Stellmacher
open scoped IsMulCommutative commutatorElement
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- The original Sylow-fixed seed splits into a moved seed and a central seed. -/
theorem omegaCenter_le_moved_seed_sup_centralizer
    (X S Z : Subgroup G) (hZ : Z = omegaOneCenterAmbient S)
    (hSX : S ≤ normalizer (X : Set G))
    [IsElementaryAbelian 2 (conjugateSpanBy Z X)]
    (hWS : conjugateSpanBy Z X ≤ S)
    (P : Sylow 2 (X ⊔ S : Subgroup G))
    (hP : (P : Subgroup (X ⊔ S : Subgroup G)).map (X ⊔ S).subtype = S) :
    Z ≤ (⁅conjugateSpanBy Z X, X⁆ ⊓ Z) ⊔ (Z ⊓ centralizer (X : Set G)) := by
  let W := conjugateSpanBy Z X
  let U := ⁅W,X⁆
  let E := X ⊔ S
  have hZW : Z ≤ W := le_conjugateSpanBy Z X
  have hSZ : S ≤ centralizer (Z : Set G) := by
    intro s hs z hz
    have hh := ((mem_omegaOneCenterAmbient_iff S z).mp (hZ ▸ hz)).2.2 s hs
    exact hh.symm
  have hXW : X ≤ normalizer (W : Set G) := le_normalizer_conjugateSpanBy Z X
  have hSW : S ≤ normalizer (W : Set G) :=
    normalizes_conjugateSpanBy Z X S
      (hSZ.trans (centralizer_le_normalizer _)) hSX
  have hEW : E ≤ normalizer (W : Set G) := sup_le hXW hSW
  have hEX : E ≤ normalizer (X : Set G) := sup_le X.le_normalizer hSX
  have hEU : E ≤ normalizer (U : Set G) := by
    intro e he
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (⁅W,X⁆).map (MulAut.conj e).toMonoidHom = _
    have hw : W.map (MulAut.conj e).toMonoidHom = W :=
      mem_normalizer_iff_map_conj_eq.mp (hEW he)
    have hx : X.map (MulAut.conj e).toMonoidHom = X :=
      mem_normalizer_iff_map_conj_eq.mp (hEX he)
    rw [map_commutator, hw, hx]
  have hUW : U ≤ W := le_normalizer_iff_commutator_le_left.mp hXW
  have hEZ : ⁅E,Z⁆ ≤ U := by
    apply commutator_sup_le_of_relative_normal E X S Z U hEU le_sup_left le_sup_right
    · simpa only [commutator_comm X W] using commutator_mono (le_rfl : X ≤ X) hZW
    · exact (commutator_eq_bot_iff_le_centralizer.mpr hSZ).le.trans bot_le
  intro z hz
  let : IsElementaryAbelian 2 U :=
    IsElementaryAbelian.of_injective (inclusion hUW) (inclusion_injective hUW)
  obtain ⟨u,hu,hc⟩ := fixed_coset_of_sylow E U hEU
    (fun u hu => elemPow_eq_one_of_isElementaryAbelian u hu) P z
    (fun e he => hEZ (commutator_mem_commutator he hz))
    (fun e he => (hSZ (hP ▸ mem_map_of_mem E.subtype he) z hz).symm)
  have hcW : u*z ∈ W := W.mul_mem (hUW hu) (hZW hz)
  have hcZ : u*z ∈ Z := by
    rw [hZ]
    apply (mem_omegaOneCenterAmbient_iff S _).mpr
    exact ⟨hWS hcW, elemPow_eq_one_of_isElementaryAbelian _ hcW,
      fun s hs => hc s (mem_sup_right hs)⟩
  have huZ : u ∈ Z := by
    simpa only [mul_inv_cancel_right] using Z.mul_mem hcZ (Z.inv_mem hz)
  have hprod := mul_mem_sup ((U ⊓ Z).inv_mem ⟨hu,huZ⟩)
    (show u*z ∈ Z ⊓ centralizer (X : Set G) from
      ⟨hcZ,centralizer_le (show X ≤ E from le_sup_left) hc⟩)
  simpa only [inv_mul_cancel_left] using hprod

/-- Centralization of the moved seed already centralizes the original seed. -/
theorem centralizer_moved_omegaCenter_eq
    (X S Z : Subgroup G) (hZ : Z = omegaOneCenterAmbient S)
    (hSX : S ≤ normalizer (X : Set G))
    [IsElementaryAbelian 2 (conjugateSpanBy Z X)]
    (hWS : conjugateSpanBy Z X ≤ S)
    (P : Sylow 2 (X ⊔ S : Subgroup G))
    (hP : (P : Subgroup (X ⊔ S : Subgroup G)).map (X ⊔ S).subtype = S) :
    X ⊓ centralizer ((⁅conjugateSpanBy Z X, X⁆ ⊓ Z : Subgroup G) : Set G) =
      X ⊓ centralizer (Z : Set G) := by
  apply le_antisymm
  · refine le_inf inf_le_left ?_
    have hsplit := omegaCenter_le_moved_seed_sup_centralizer X S Z hZ hSX hWS P hP
    apply (le_centralizer_iff.mp ?_ :
      (X ⊓ centralizer ((⁅conjugateSpanBy Z X, X⁆ ⊓ Z : Subgroup G) : Set G)) ≤ centralizer (Z : Set G))
    apply hsplit.trans
    apply sup_le
    · exact le_centralizer_iff.mp inf_le_right
    · exact inf_le_right.trans (centralizer_le inf_le_left)
  · exact inf_le_inf_left X (centralizer_le inf_le_right)

end Subgroup
