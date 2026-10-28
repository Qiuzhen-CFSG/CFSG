module
public import Theory.SpecificGroups.AlternatingSix.CubicLift
public import Theory.SpecificGroups.SymmetricSix.TranspositionCubic

/-!
# The selected cubic under the original ambient conjugation action

A normal quasisimple odd-center A₆ cover carries the restriction of the
original symmetric-six permutation map. For a prescribed two-subgroup
whose actual image is a transposition, choose the overlapping native cubic
and apply the invariant lifting theorem to conjugation on this normal cover.
The resulting order-three subgroup lies in the original group, is normalized
by the original two-subgroup, and has precisely the selected permutation image.
The native generation and fixed-space movement conclusions are retained.

Source: Aschbacher–Smith C.1.24(c), printed pp.130–131, applied in the
quotient by the original two-core. No assertion identifies the full action
kernel with that two-core.
-/

public section

open Subgroup Equiv Theory.GroupTheory
namespace Theory.SpecificGroups.AlternatingSix.CubicLift
open GLS3.Chapter5
open SymmetricSix.TranspositionCubic
variable {G : Type*} [Group G] [Finite G]

theorem exists_ambient_cubic (L : Subgroup G) [L.Normal] [IsQuasisimple L]
    (e : L ⧸ center L ≃* alternatingGroup (Fin 6)) (hodd : Odd (Nat.card (center L)))
    (q : G →* Sym) (hqL : ∀ x : L, q x = (alternatingQuotientHom e x : Sym))
    (R : Subgroup G) (hpR : IsPGroup 2 R) (r : Sym) (hr : r.IsSwap)
    (hR : R.map q = zpowers r) :
    ∃ (c : Sym) (Y : Subgroup G), Y ≤ L ∧ Nat.card Y = 3 ∧
      R ≤ normalizer (Y : Set G) ∧ Y.map q = zpowers c ∧
      orderOf c = 3 ∧ c ∈ alternatingGroup (Fin 6) ∧ r*c*r⁻¹=c⁻¹ ∧
      normalizer (zpowers r : Set Sym) ⊔ zpowers c=⊤ ∧
      Nat.card (zpowers c ⊔ zpowers r : Subgroup Sym)=6 ∧
      ¬Representation.BinaryOffender.fixedSpace (BinaryPermutation.naturalRepresentation (Fin 6)) (zpowers r) ≤
        Representation.BinaryOffender.fixedSpace (BinaryPermutation.naturalRepresentation (Fin 6)) (zpowers c) := by
  obtain ⟨c,hc,hce,hci,hcg,hcard,hmove⟩ := exists_cubic_for_transposition r hr
  let z : alternatingGroup (Fin 6) := ⟨c,hce⟩
  let P := zpowers z
  have hP : Nat.card P = 3 := by
    rw [Nat.card_zpowers,←Subgroup.orderOf_coe z]
    exact hc
  have hPm : P.map (alternatingGroup (Fin 6)).subtype = zpowers c := MonoidHom.map_zpowers _ z
  have hnorm : zpowers r ≤ normalizer (zpowers c : Set Sym) := by
    apply zpowers_le.mpr
    rw [mem_normalizer_iff_map_conj_eq,MonoidHom.map_zpowers]
    change zpowers (r*c*r⁻¹)=zpowers c
    rw [hci,zpowers_inv]
  let ρ : R →* MulAut L := MulAut.conjNormal.comp R.subtype
  have hstable : ∀ a : R, ∀ x : L, alternatingQuotientHom e x ∈ P →
      alternatingQuotientHom e (ρ a x) ∈ P := by
    intro a x hx
    have hx' : q (x:G) ∈ zpowers c := by
      rw [hqL x,←hPm]
      exact mem_map_of_mem (alternatingGroup (Fin 6)).subtype hx
    have ha : q (a:G) ∈ zpowers r := hR ▸ mem_map_of_mem q a.property
    have hy := le_normalizer_iff.mp hnorm (q (a:G)) ha (q (x:G)) hx'
    have he : (alternatingQuotientHom e (ρ a x) : Sym) =
        q (a:G)*q (x:G)*(q (a:G))⁻¹ := by
      rw [←hqL (ρ a x)]
      change q ((a:G)*(x:G)*(a:G)⁻¹)=_
      rw [map_mul,map_mul,map_inv]
    have hmem : (alternatingQuotientHom e (ρ a x) : Sym) ∈
        P.map (alternatingGroup (Fin 6)).subtype := by rwa [hPm,he]
    obtain ⟨y,hy,hey⟩ := hmem
    exact (Subtype.ext hey : y = alternatingQuotientHom e (ρ a x)) ▸ hy
  obtain ⟨M,hM,hMp,hMc,hMi⟩ := exists_invariant_lift_of_odd_center e hodd ρ hpR P hP hstable
  let Y := M.map L.subtype
  have hY : R ≤ normalizer (Y : Set G) := by
    apply le_normalizer_iff.mpr
    intro a ha x hx
    obtain ⟨x,hx,rfl⟩ := hx
    exact ⟨ρ ⟨a,ha⟩ x,hMi ⟨a,ha⟩ x hx,rfl⟩
  have hm : Y.map q = zpowers c := by
    have hf : q.comp L.subtype =
        (alternatingGroup (Fin 6)).subtype.comp (alternatingQuotientHom e) :=
      MonoidHom.ext hqL
    change (M.map L.subtype).map q=zpowers c
    rw [map_map,hf,←map_map,hMp,hPm]
  exact ⟨c,Y,map_subtype_le M,(card_map_of_injective L.subtype_injective).trans hM,
    hY,hm,hc,hce,hci,hcg,hcard,hmove⟩
end Theory.SpecificGroups.AlternatingSix.CubicLift
