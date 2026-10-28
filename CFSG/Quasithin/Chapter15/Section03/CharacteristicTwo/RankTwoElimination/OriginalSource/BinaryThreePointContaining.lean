module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreeAmbientSourceNormalizer
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.BinaryContaining
public import CFSG.Quasithin.Chapter1.Section03.Radical.Structure.QuotientShape
public import Theory.SpecificGroups.SL2.LinearThreeSection
public import Theory.GroupTheory.PerfectNormalizerLift

/-!
# The nonquasisimple containing component at the original binary point

The smaller local component has its actual PSL₃(2) two-core quotient.
In the nonquasisimple A.3.6 alternatives, this section forces the natural
prime to be seven and excludes the nilpotent SL₂(5) alternative. The
smaller component covers the SL₂(7) quotient of the containing component.
Thus its actual seven-core and the smaller component generate the latter.

Source: Aschbacher--Smith A.3.6 and the original setting of 15.3.23,
printed pp.43--45 and 1128--1129.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open Chapter1.Section02.LocalModels

private theorem seven_natural_of_binary_section
    {A B : Type*} [Group A] [Finite A] [Group B] [Finite B]
    [Group.IsPerfect B] [IsSimpleGroup (B ⧸ pCore 2 B)]
    (hB : Nat.card (B ⧸ pCore 2 B) = 168)
    (f : B →* A) [Group.IsSolvable f.ker]
    (h : Chapter1.Section02.A36Natural A ∨ Chapter1.Section02.A36Nilpotent A) :
    NaturalSL2Action A (pCore 7 A) 7 := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  have parameter (N : Subgroup A) [N.Normal] [Group.IsSolvable N]
      {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hm : IsSL (A ⧸ N) 2 p) : p = 7 := by
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    let g := e.toMonoidHom.comp ((QuotientGroup.mk' N).comp f)
    let : Group.IsSolvable g.ker := by
      change Group.IsSolvable (e.toMonoidHom.comp ((QuotientGroup.mk' N).comp f)).ker
      rw [MonoidHom.ker_comp_of_injective _ _ e.injective, ←MonoidHom.comap_ker,
        QuotientGroup.ker_mk']
      exact isSolvable_comap_of_solvable_ker f N
    exact Theory.SL2.prime_eq_seven_of_solvable_kernel hB hp hp3 hF g
  rcases h with h | h
  · obtain ⟨p,hp,hp3,ha⟩ := h.2
    let N := generalizedFitting A
    let : Group.IsNilpotent N := by
      change Group.IsNilpotent (generalizedFitting A)
      rw [h.1]
      infer_instance
    have hp7 : p = 7 := by
      obtain ⟨F,_,_,hF,v,ρ,hact⟩ := ha
      exact parameter N hp hp3 ⟨F,inferInstance,inferInstance,hF,⟨ρ⟩⟩
    subst p
    have hc := (Chapter1.RadicalStructure.natural_elementary ha).2
    have hN : generalizedFitting A = pCore 7 A := h.1.trans
      (Chapter1.RadicalStructure.fitting_eq_core (by
        rw [←h.1]
        exact IsPGroup.of_card hc))
    simpa only [hN] using ha
  · let := h.2.1
    have he := parameter (generalizedFitting A) (by decide : Nat.Prime 5)
      (by decide) h.2.2.1
    norm_num at he

private theorem seven_quotient_covered_by_binary_section
    {A B : Type*} [Group A] [Finite A] [Group.IsPerfect A]
    [Group B] [Finite B] [Group.IsPerfect B] [IsSimpleGroup (B ⧸ pCore 2 B)]
    (hB : Nat.card (B ⧸ pCore 2 B) = 168)
    (f : B →* A) [Group.IsSolvable f.ker]
    (ha : NaturalSL2Action A (pCore 7 A) 7) :
    Function.Surjective ((QuotientGroup.mk' (pCore 7 A)).comp f) := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  obtain ⟨F,_,_,hF,v,e,hact⟩ := ha
  let N := pCore 7 A
  let : Group.IsNilpotent N := pCore_isNilpotent
  let g := e.toMonoidHom.comp ((QuotientGroup.mk' N).comp f)
  let : Group.IsSolvable g.ker := by
    change Group.IsSolvable (e.toMonoidHom.comp ((QuotientGroup.mk' N).comp f)).ker
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, ←MonoidHom.comap_ker,
      QuotientGroup.ker_mk']
    exact isSolvable_comap_of_solvable_ker f N
  have hp := (Theory.SL2.prime_seven_and_projective_surjective_of_solvable_kernel hB
    (by decide : Nat.Prime 7) (by decide) hF g).2
  let : Group.IsPerfect SL(2,F) := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  let q := QuotientGroup.mk' (center SL(2,F))
  have hgmap : g.range.map q = ⊤ := by
    rw [←MonoidHom.range_comp]
    exact MonoidHom.range_eq_top.mpr hp
  have hg : Function.Surjective g := MonoidHom.range_eq_top.mp (top_le_iff.mp (by
    apply le_of_map_le_of_perfect q (by rw [QuotientGroup.ker_mk']) ⊤ g.range
    rw [hgmap]
    exact le_top))
  intro z
  obtain ⟨b,hb⟩ := hg (e z)
  exact ⟨b,e.injective hb⟩

/-- A nonquasisimple containing C-component with the actual binary-three
local section is the natural seven-core row, and that core supplements the
same smaller component. No embedding classification is assumed. -/
theorem binary_three_nonquasisimple_containing_seven
    {X : Type*} [Group X] [Finite X]
    (hX : IsSQTK KnownSimple.IsKnownSimple X) (hO : pCore 2 X = ⊥)
    (S : Sylow 2 X) {B K : Subgroup X}
    (hB : B ∈ ChapterA.Section03.localCComponents S)
    (hK : K.IsCComponent) (hBK : B ≤ K)
    (e : (B ⧸ pCore 2 B) ≃* PSL(3,ZMod 2))
    (hn : ¬ IsQuasisimple K) :
    NaturalSL2Action K (pCore 7 K) 7 ∧ K.pCoreIn 7 ⊔ B = K := by
  let a := subgroupOfEquivOfLe (show B ≤ B ⊔ (S : Subgroup X) from le_sup_left)
  let : Group.IsPerfect (B.subgroupOf (B ⊔ (S : Subgroup X))) := hB.perfect
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective (f := a.toMonoidHom) a.surjective
  let : Group.IsPerfect K := hK.perfect
  let eSL := e.trans (BinaryLinear.OuterCyclic.projectiveEquivSL (by decide))
  let : IsSimpleGroup Matrix.PSL3Two.SL := Atlas.Comparisons.Exceptional.sl3Two_simple
  let : IsSimpleGroup (B ⧸ pCore 2 B) := eSL.isSimpleGroup
  have hb : Nat.card (B ⧸ pCore 2 B) = 168 :=
    (Nat.card_congr eSL.toEquiv).trans Atlas.Comparisons.Exceptional.sl3Two_card
  let f : B →* K := inclusion hBK
  let : Group.IsSolvable f.ker := by
    rw [(MonoidHom.ker_eq_bot_iff f).mpr (inclusion_injective hBK)]
    infer_instance
  have ha := ChapterA.SQTKStructure.a36Input_of_theoremsAC
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple) X hX hO K hK
  have hnat := seven_natural_of_binary_section hb f
    (Chapter1.RadicalStructure.nonsimple_radical ha hn)
  refine ⟨hnat,?_⟩
  let q := QuotientGroup.mk' (pCore 7 K)
  have hs := seven_quotient_covered_by_binary_section hb f hnat
  have hr : (q.comp f).range = (B.subgroupOf K).map q := by
    rw [MonoidHom.range_comp]
    congr 1
    ext x
    constructor
    · rintro ⟨b,rfl⟩
      exact b.property
    · intro hx
      exact ⟨⟨x,hx⟩,rfl⟩
  have ht : (B.subgroupOf K).map q = ⊤ := hr.symm.trans (MonoidHom.range_eq_top.mpr hs)
  have hi := congrArg (comap q) ht
  rw [comap_map_eq,QuotientGroup.ker_mk',comap_top] at hi
  have hm := congrArg (map K.subtype) hi
  rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hBK,
    ←MonoidHom.range_eq_map,range_subtype] at hm
  exact (sup_comm _ _).trans hm

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
