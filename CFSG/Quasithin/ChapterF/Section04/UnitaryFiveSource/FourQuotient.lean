module
public import CFSG.Quasithin.ChapterF.Section04.UnitarySource.MaximalNormalizerPerfect
public import Theory.GroupTheory.PPrimeCoreReduction

/-!
# The second short-centralizer quotient when the fixed line has order four

A maximal proper subgroup of the four-element line containing the central
involution line is exactly that involution line. Its normalizer is therefore
the whole involution centralizer. The known trivial odd core applies to
this particular normalizer. The literal maximal-normalizer quotient has a
centerless Bender normal closure, contradicted by the perfect local group
which contains the line and centralizes it.

Source: Aschbacher–Smith F.4.42, final paragraph, printed p.296.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.UnitaryFiveSource
open UnitarySource
variable {G : Type*} [Group G] [Finite G]

/-- The full four-element line needs odd-core vanishing only in the ambient
centralizer, because its maximal intermediate subgroup is central. -/
theorem eq_top_of_perfect_four
    (X U Z : Subgroup G) [IsElementaryAbelian 2 U]
    (hUX : U ≤ X) (hZU : Z ≤ U) (hZ : Z ≤ center G)
    (hNU : normalizer (U : Set G) = X)
    (S : Sylow 2 G) (hSX : (S : Subgroup G) ≤ X)
    (z : G) (hzS : z ∈ (S : Subgroup G))
    (hzcentral : ∀ a ∈ (S : Subgroup G), Commute z a)
    (hfix : ∃! q : G ⧸ X, z • q = q)
    (P : Subgroup G) [Group.IsPerfect P]
    (hUP : U ≤ P) (hPC : P ≤ centralizer (U : Set G))
    (hUcard : Nat.card U = 4) (hZcard : Nat.card Z = 2)
    (hodd : pPrimeCore 2 G = ⊥) :
    X = ⊤ := by
  by_contra hX
  obtain ⟨W,hZW,hWU,hWX,hmax,hVne,hYne,hNY,hVe,hVN,hfixV,_,_⟩ :=
    maximal_normalizer_section X U Z hX hUX hZU hZ hNU S hSX z hzS hzcentral hfix
  have hWZ : W = Z := by
    have hd : Nat.card W ∣ 4 := by simpa only [hUcard] using card_dvd_of_le hWU.le
    have hge : 2 ≤ Nat.card W := by
      rw [←hZcard]
      exact Nat.card_le_card_of_injective (inclusion hZW) (inclusion_injective hZW)
    have hle : Nat.card W ≤ 4 := Nat.le_of_dvd (by decide) hd
    have hne : Nat.card W ≠ 4 := by
      intro he
      exact hWU.ne (eq_of_le_of_card_ge hWU.le (by rw [hUcard,he]))
    have hc : Nat.card W = 2 := by
      interval_cases hw : Nat.card W
      · rfl
      · norm_num at hd
      · exact (hne rfl).elim
    exact (eq_of_le_of_card_ge hZW (by rw [hZcard,hc])).symm
  have hWN : normalizer (W : Set G) = ⊤ := by
    rw [hWZ]
    apply top_unique
    intro g _
    apply Subgroup.centralizer_le_normalizer
    intro z hz
    exact (mem_center_iff.mp (hZ hz) g).symm
  let N := normalizer (W : Set G)
  have hoddN : pPrimeCore 2 N = ⊥ := pPrimeCore_eq_bot_of_equiv
    ((MulEquiv.subgroupCongr hWN).trans topEquiv) hodd
  let f := QuotientGroup.mk' (W.subgroupOf N)
  let V := (U.subgroupOf N).map f
  let Y := (X.subgroupOf N).map f
  have hPN : P ≤ N :=
    (hPC.trans (centralizer_le hWU.le)).trans (Subgroup.centralizer_le_normalizer _)
  have hPX : P ≤ X := hNU ▸ hPC.trans (Subgroup.centralizer_le_normalizer _)
  have hUN : U ≤ N := hUP.trans hPN
  let : IsElementaryAbelian 2 (U.subgroupOf N) := IsElementaryAbelian.subgroupOf hUN
  obtain ⟨_,hcenter,hquasi,hmodel,hBorel,hB,_⟩ :=
    quotient_bender_of_odd_core (U.subgroupOf N) (W.subgroupOf N)
      (comap_mono hWU.le) hoddN Y (map_mono (comap_mono hUX))
      hVne hYne hNY hfixV
  let : Group.IsPerfect (P.subgroupOf N) := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hPN).symm.toMonoidHom)
    (subgroupOfEquivOfLe hPN).symm.surjective
  let : Group.IsPerfect ((P.subgroupOf N).map f) := Group.IsPerfect.map f
  exact hVne (eq_bot_of_perfect_normalizer V ((P.subgroupOf N).map f)
    (map_mono (comap_mono hUP))
    ((map_mono (comap_mono hPX)).trans hNY.ge) hcenter hquasi hmodel
    (hBorel ▸ hB.1))

end CFSG.Quasithin.ChapterF.UnitaryFiveSource
