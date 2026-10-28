module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixEscapingSource
public import Theory.SpecificGroups.PSL3Four.CentralCover.AutomorphismLifting

/-! The same original point component is a perfect central four-cover of
actual PSL₃(4). Its center is the original point four-group. Consequently the
proved cover uniqueness applies to this literal local group. -/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- Construct the four-cover on the original normal closure, retaining its
literal central kernel and the original point four-group. -/
theorem original_tripleSix_escaping_component_cover
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t≠1)
    (heven : 2∣(centralizer ({(t:G)} : Set G)).relIndex K)
    (hout : ¬centralizer ({(t:G)} : Set G)≤normalizer (K : Set G)) :
    let H := centralizer ({(t:G)} : Set G)
    let Lt := (pResidual 2 (K⊓H : Subgroup G)).map (K⊓H).subtype
    let B := conjugateSpanBy Lt H
    centerIn B=tripleSixPoint D a t ∧ Nonempty (Matrix.PSL3Four.FourCover B) := by
  let H := centralizer ({(t:G)} : Set G)
  let Lt := (pResidual 2 (K⊓H : Subgroup G)).map (K⊓H).subtype
  let B := conjugateSpanBy Lt H
  obtain ⟨hB,hcenter,hV,hn,he⟩ :=
    original_tripleSix_point_identification_at h structural D a t ht heven hout
  let := hn
  obtain ⟨e₀⟩ := he
  let e := (QuotientGroup.quotientMulEquivOfEq hV.symm).trans e₀
  have hBH : B≤H := conjugateSpanBy_le_self ((map_subtype_le _).trans inf_le_right)
  let := hB.2
  let : IsQuasisimple B := IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hBH)
  let := D.elementary
  have hVt := tripleSixPoint_properties D a t ht
  have hZU : centerIn B≤U := hcenter.symm ▸ hVt.2.1
  have hZc : Nat.card (center B)=4 := by
    have hc : Nat.card (centerIn B)=4 := hcenter.symm ▸ hVt.2.2.1
    rw [centerIn_eq_map_center,card_map_of_injective B.subtype_injective] at hc
    exact hc
  have hsq (x : center B) : x^2=1 := by
      apply Subtype.ext
      apply Subtype.ext
      have hx : (x.val : G)∈U := hZU
        (by rw [centerIn_eq_map_center]; exact mem_map_of_mem B.subtype x.property)
      exact elemPow_eq_one_of_isElementaryAbelian (p := 2) (x.val : G) hx
  let : Nontrivial (center B) := Finite.one_lt_card_iff_nontrivial.mp (by rw [hZc]; decide)
  let hZ : IsKleinFour (center B) := {
    card_four := hZc
    exponent_two := (Monoid.exponent_eq_prime_iff (by decide : Nat.Prime 2)).mpr
      (fun x hx => orderOf_eq_prime (hsq x) hx) }
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center B))
  have hk : f.ker=center B := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  exact ⟨hcenter,⟨{
    toMonoidHom := f
    surjective := e.surjective.comp (QuotientGroup.mk'_surjective (center B))
    isPerfect := inferInstance
    ker_le_center := hk.le
    ker_eq_center := hk
    center_isKleinFour := hZ }⟩⟩

end CFSG.Quasithin.Chapter12.Section07
