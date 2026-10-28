module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.CharacteristicBlock
public import Theory.GroupTheory.SylowSubnormalIntersection

/-!
# The literal odd-index radical in LQ₁

In the full-image branch, put J = LQ₁ and P = L₁T. The original Sylow
normalizes both L and Q₁, so J is normal in LT. Consequently P ∩ J is
normal in P and its two-core is R₁ ∩ J = Q₁. Intersecting a Sylow subgroup
of LT with J proves that P ∩ J has odd index in J. It is proper because
otherwise L normalizes V₁, contradicting the preceding normalizer control
and 11.5.4.

These are exactly MS2(a), with the original Q₁ restricted to J. The final
application combines this with MS3 from CharacteristicBlock. No abstract
radical witness, ambient subnormality of L, or block conclusion is assumed.
The full MS1 verification, root-image exclusion and block classification
remain with qt-d-1222-natural-closure-sp4.

Source: Aschbacher--Smith 11.5.7, printed p.783, and C.1.31(MS2), p.135.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.CharacteristicBlock
open Subgroup Theory.SpecificGroups.SymplecticFour
open CFSG.Quasithin.Chapter12.Section02
open RadicalAction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (E : Geometry D)

/-- The source outside-centralizer clause excludes normalization of the
marked point by the entire component. -/
theorem component_not_le_point_normalizer (m : MarkedFlag E)
    (hout : ¬ centralizer (E.V₁ : Set G) ≤ E.M) : ¬ L ≤ E.G₁ := by
  intro hL
  have hn := D.normal_subgroup_normalizer_le E.input.source.toHypothesis1221
    ((E.V₁_le.trans D.le_sylow).trans le_sup_right) m.point_nontrivial
    (sup_le hL m.sylow_le_point_normalizer)
  exact hout ((Subgroup.centralizer_le_normalizer _).trans hn)

/-- The actual local intersection witnesses MS2(a) in LQ₁. -/
theorem msOddIndexRadical_of_full_image (m : MarkedFlag E)
    (g : Sp E.input.field.Carrier)
    (hpoint : m.flag.space 0 = (point E.input.field.Carrier).map (toLinear g).toLinearMap)
    (hout : ¬ centralizer (E.V₁ : Set G) ≤ E.M)
    (hcore : L.pCoreIn 2 ≤ E.G₁.pCoreIn 2)
    (hfull : actionImage (V := V) (E.G₁.pCoreIn 2) = actionImage (V := V) E.R₁) :
    ChapterC.MSOddIndexRadical
      ((E.G₁.pCoreIn 2).subgroupOf (L ⊔ E.G₁.pCoreIn 2)) := by
  let Q := E.G₁.pCoreIn 2
  let J := L ⊔ Q
  let P := E.L₁ ⊔ (T : Subgroup G)
  let B := L ⊔ (T : Subgroup G)
  let H := P ⊓ J
  have hQT : Q ≤ (T : Subgroup G) := core_le_sylow E m
  have hQJ : Q ≤ J := le_sup_right
  have hQR : Q ≤ E.R₁ := core_le_local_radical E m
  have hQP : Q ≤ P := hQR.trans (pCoreIn_le 2 P)
  have hPB : P ≤ B := sup_le_sup_right E.L₁_le _
  have hJB : J ≤ B := sup_le le_sup_left (hQT.trans le_sup_right)
  have hPG : P ≤ E.G₁ := sup_le E.L₁_le_G₁ m.sylow_le_point_normalizer
  have hTN : (T : Subgroup G) ≤ normalizer (J : Set G) :=
    (le_inf D.sylow_normalizes_component
      (m.sylow_le_point_normalizer.trans (point_normalizer_normalizes_core E))).trans
        (normalizer_inf_normalizer_le_normalizer_sup L Q)
  have hBN : B ≤ normalizer (J : Set G) :=
    sup_le (le_sup_left.trans J.le_normalizer) hTN
  have hPH : P ≤ normalizer (H : Set G) :=
    (le_inf P.le_normalizer (hPB.trans hBN)).trans inf_normalizer_le_normalizer_inf
  have hcut : E.R₁ ⊓ J = Q := radical_intersection_join_eq E m g hpoint hcore hfull
  have hHQ : H.pCoreIn 2 = Q := by
    apply le_antisymm
    · rw [← hcut]
      exact le_inf (pCoreIn_mono_of_normalizes inf_le_left hPH)
        ((pCoreIn_le 2 H).trans inf_le_right)
    · exact (le_inf (le_inf hQP hQJ) hQR).trans
        (inf_pCoreIn_le_of_le 2 (show H ≤ P from inf_le_left))
  have hproper : P.subgroupOf J < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    intro he
    apply component_not_le_point_normalizer E m hout
    apply le_trans _ hPG
    intro x hx
    have hxJ : x ∈ J := mem_sup_left hx
    have hh : (⟨x,hxJ⟩ : J) ∈ P.subgroupOf J := he ▸ mem_top _
    exact hh
  have hodd : Odd (P.subgroupOf J).index := by
    let N := J.subgroupOf B
    let : N.Normal := (normal_subgroupOf_iff_le_normalizer hJB).mpr hBN
    let S := T.subtype (show (T : Subgroup G) ≤ B from le_sup_right)
    obtain ⟨S',hS'⟩ := S.exists_subgroupOf_eq_of_subnormal N
      (inferInstance : N.Normal).isSubnormal
    have hSP : (S' : Subgroup N) ≤ (P.subgroupOf B).subgroupOf N := by
      rw [hS']
      intro x hx
      exact (show (T : Subgroup G) ≤ P from le_sup_right) hx
    have hi : ¬ 2 ∣ ((P.subgroupOf B).subgroupOf N).index := fun hd =>
      S'.not_dvd_index (hd.trans (index_dvd_of_le hSP))
    change Odd (P.relIndex J)
    rw [← relIndex_subgroupOf hJB]
    apply Nat.not_even_iff_odd.mp
    rw [even_iff_two_dvd]
    change ¬ 2 ∣ ((P.subgroupOf B).subgroupOf N).index
    exact hi
  refine ⟨P.subgroupOf J,hproper,hodd,?_⟩
  change (P.subgroupOf J).pCoreIn 2 = Q.subgroupOf J
  rw [← inf_subgroupOf_right P J, pCoreIn_subgroupOf 2 (P ⊓ J) J inf_le_right]
  exact congrArg (fun A : Subgroup G => A.subgroupOf J) hHQ

/-- Both radical conditions for the same original Q₁ in LQ₁. The
source classification still has to verify MS1 and apply C.1.32. -/
theorem ms_conditions_of_full_image (m : MarkedFlag E)
    (g : Sp E.input.field.Carrier)
    (hpoint : m.flag.space 0 = (point E.input.field.Carrier).map (toLinear g).toLinearMap)
    (hout : ¬ centralizer (E.V₁ : Set G) ≤ E.M)
    (hcore : L.pCoreIn 2 ≤ E.G₁.pCoreIn 2)
    (hfull : actionImage (V := V) (E.G₁.pCoreIn 2) = actionImage (V := V) E.R₁) :
    ChapterC.MSOddIndexRadical
      ((E.G₁.pCoreIn 2).subgroupOf (L ⊔ E.G₁.pCoreIn 2)) ∧
    ChapterC.MSCharacteristicCondition
      ((E.G₁.pCoreIn 2).subgroupOf (L ⊔ E.G₁.pCoreIn 2)) :=
  ⟨msOddIndexRadical_of_full_image E m g hpoint hout hcore hfull,
    msCharacteristic E m hout⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.CharacteristicBlock
