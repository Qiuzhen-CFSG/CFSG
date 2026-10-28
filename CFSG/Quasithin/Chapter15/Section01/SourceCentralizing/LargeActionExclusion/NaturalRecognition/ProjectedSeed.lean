module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.NaturalRecognition.Splitting

/-!
# Recovering the original projected seed from a Sylow-fixed line

If the moved module has a single nonzero S-fixed vector, Sylow averaging
puts the projection of every original seed element on that line. Seed
noncentrality makes the projection nonzero. Equality modulo C_U(L) then
identifies the line's stabilizer with the original ML. This works for either
source plane size, without presupposing that Z2 itself has order two.

Source: Aschbacher--Smith 15.1.28, printed p.1103.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Theory.SpecificGroups.BinaryComponentResidual ChapterA.Section05To06 Section03 Section03.InitialSource
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterC.C27Source
variable {G : Type*} [Group G] [Finite G]
namespace CaseIComponentData
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- A Sylow-fixed line is the actual nonzero projected seed, and its
stabilizer is ML, with the literal original subgroups and conjugator. -/
theorem exchanged_projected_seed (d : CaseIComponentData T M Mc V) (s : d.ExchangedSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (hi : Input KnownSimple.IsKnownSimple d.G1 d.Q1 d.MZ d.L)
    (hf : Facts (d.L ⧸ pCore 2 d.L))
    (t : G) (ht : t ∈ (T : Subgroup G)) (htS : t ∉ d.S)
    (hline : Nat.card (d.UL t ⊓ centralizer (d.S : Set G) : Subgroup G) = 2) :
    ∃ ZU : Subgroup G, ZU ≤ d.UL t ∧ Nat.card ZU = 2 ∧
      ZU ≤ centralizer (d.S : Set G) ∧
      d.Z2 t ⊔ (d.U t ⊓ centralizer (d.L : Set G)) =
        ZU ⊔ (d.U t ⊓ centralizer (d.L : Set G)) ∧
      d.L ⊓ centralizer (ZU : Set G) = d.ML := by
  let ZU := d.UL t ⊓ centralizer (d.S : Set G)
  let C := d.U t ⊓ centralizer (d.L : Set G)
  have hcoset (z : G) (hz : z ∈ d.Z2 t) : ∃ u ∈ ZU, u * z ∈ C := by
    obtain ⟨u,huU,huC⟩ := d.exchanged_Z2_fixed_coset s hG hM hu h hi hf t ht hz
    have huS : u ∈ centralizer (d.S : Set G) := by
      have hh := (centralizer (d.S : Set G)).mul_mem
        (centralizer_le (show d.S ≤ d.L ⊔ d.S from le_sup_right) huC.2)
        ((centralizer (d.S : Set G)).inv_mem (d.exchanged_Z2_le_centralizer_S s t ht hz))
      simpa only [mul_inv_cancel_right] using hh
    exact ⟨u,⟨huU,huS⟩,⟨huC.1,
      centralizer_le (show d.L ≤ d.L ⊔ d.S from le_sup_left) huC.2⟩⟩
  have hforward : d.Z2 t ≤ ZU ⊔ C := by
    intro z hz
    obtain ⟨u,huU,huC⟩ := hcoset z hz
    have hh := mul_mem_sup (ZU.inv_mem huU) huC
    simpa only [inv_mul_cancel_left] using hh
  obtain ⟨z,hz,hzC⟩ := Set.not_subset.mp
    (d.exchanged_Z2_not_centralizes_L s hM hu h t ht htS)
  obtain ⟨u,huU,huC⟩ := hcoset z hz
  have hu1 : u ≠ 1 := by
    intro he
    apply hzC
    intro l hl
    simpa only [he,one_mul] using huC.2 l hl
  have huZ : u ∈ d.Z2 t ⊔ C := by
    have hh := (d.Z2 t ⊔ C).mul_mem (mem_sup_right huC)
      (mem_sup_left ((d.Z2 t).inv_mem hz))
    simpa only [mul_inv_cancel_right] using hh
  have hback : ZU ≤ d.Z2 t ⊔ C := by
    obtain ⟨w,_,hw⟩ := (Nat.card_eq_two_iff' (1 : ZU)).mp hline
    intro v hv
    by_cases hv1 : v = 1
    · exact hv1 ▸ one_mem _
    have hvu : v = u := congrArg Subtype.val
      ((hw ⟨v,hv⟩ (fun he => hv1 (congrArg Subtype.val he))).trans
        (hw ⟨u,huU⟩ (fun he => hu1 (congrArg Subtype.val he))).symm)
    exact hvu ▸ huZ
  have hproj : d.Z2 t ⊔ C = ZU ⊔ C :=
    le_antisymm (sup_le hforward le_sup_right) (sup_le hback le_sup_right)
  have hcentral : d.L ⊓ centralizer (ZU : Set G) =
      d.L ⊓ centralizer (d.Z2 t : Set G) := by
    have htransfer (A B : Subgroup G) (hAB : A ≤ B ⊔ C) :
        d.L ⊓ centralizer (B : Set G) ≤ d.L ⊓ centralizer (A : Set G) := by
      rintro x ⟨hxL,hxB⟩
      refine ⟨hxL,?_⟩
      have hBC : B ⊔ C ≤ centralizer ({x} : Set G) := by
        apply sup_le
        · intro b hb
          exact mem_centralizer_singleton_iff.mpr (hxB b hb)
        · intro c hc
          exact mem_centralizer_singleton_iff.mpr (hc.2 x hxL).symm
      intro a ha
      exact mem_centralizer_singleton_iff.mp (hBC (hAB ha))
    exact le_antisymm (htransfer _ _ hforward) (htransfer _ _ hback)
  exact ⟨ZU,inf_le_left,hline,inf_le_right,hproj,
    hcentral.trans (d.exchanged_Z2_component_centralizer_eq_ML s hM hu h t ht htS)⟩

end CaseIComponentData
end CFSG.Quasithin.Chapter15.Section01
