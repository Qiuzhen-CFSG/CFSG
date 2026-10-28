module

public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingFiveRankOne
public import Theory.SpecificGroups.PSL2.BinaryPerfectCentralizer
public import Theory.SpecificGroups.PSL2.TwentyFiveThirteen
public import Theory.GroupTheory.SolvableOuterQuotient
public import Theory.GroupTheory.CComponent.QuasisimpleFactors

/-!
# The outer Sylow action in the PSL₂(25) row

A full Sylow two-subgroup of PSL₂(25) cannot lie in a normalized A₅
subgroup: their two-parts are eight and four. A perfect nontrivial
subgroup has trivial centralizer in this rank-one group. If every Sylow
element acted inwardly, it would therefore belong to A₅, a contradiction.

For a proper local C-component with A₅ two-core quotient, the proved
quadratic-field embedding theorem identifies that actual component as A₅.
Its two-core is consequently trivial, and the witness acts outwardly on
the literal quotient. Perfectness of the ambient simple group is obtained
from its nontrivial perfect local subgroup; no model-simplicity or
perfectness input is added.

The ambient quotient transport and chosen-flag application are in
FirstTwentyFive. These results establish the outer-actor step, not the
remaining natural-module contradiction or the complete model sieve.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
the PSL₂(25) case in the proof of 11.1.2, printed p.762, using A.3.12(8)
and A.3.14, printed pp.47--49.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.TwentyFive
open ChapterA.Section03.SourceEmbeddings
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem perfect_centralizer (B : Subgroup G) [Group.IsPerfect B]
    (hB : B ≠ ⊥) (hm : ClassicalGroup.IsPSL G 2 25) :
    centralizer (B : Set G) = ⊥ := by
  obtain ⟨F,_,_,_,⟨e⟩⟩ := hm
  let E := B.map e.toMonoidHom
  let : Group.IsPerfect E := Group.IsPerfect.map _
  have hn : E ≠ ⊥ := fun he => hB ((map_eq_bot_iff_of_injective B e.injective).mp he)
  have hc := Theory.PSL2.centralizer_eq_bot_of_perfect E hn
  apply bot_unique
  intro x hx
  have hx' : e x ∈ centralizer (E : Set _) := by
    rintro _ ⟨b,hb,rfl⟩
    change e b * e x = e x * e b
    simpa only [← map_mul] using congrArg e (hx b hb)
  exact e.map_eq_one_iff.mp (hc.le hx')

/-- A full Sylow subgroup of PSL₂(25) normalizing A₅ induces a noninner
automorphism: its order has a factor eight, while the two-part of A₅ is four
and its centralizer in the containing rank-one group is trivial. -/
theorem exists_outer_on_five (S : Sylow 2 G) (B : Subgroup G)
    (hn : (S : Subgroup G) ≤ normalizer (B : Set G))
    (eB : B ≃* alternatingGroup (Fin 5))
    (hm : ClassicalGroup.IsPSL G 2 25) :
    ∃ s : G, ∃ hs : s ∈ (S : Subgroup G),
      B.normalizerMonoidHom ⟨s,hn hs⟩ ∉ MulAut.innerSubgroup B := by
  let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective
    (f := eB.symm.toMonoidHom) eB.symm.surjective
  have hBcard : Nat.card B = 60 := by
    rw [Nat.card_congr eB.toEquiv,nat_card_alternatingGroup]
    norm_num
  have hB : B ≠ ⊥ := by intro he; simp [he] at hBcard
  have hc := perfect_centralizer B hB hm
  have hcard : Nat.card G = 7800 := by
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    exact (Nat.card_congr e.toEquiv).trans (Theory.PSL2.TwentyFive.card hF)
  have hnot : ¬ (S : Subgroup G) ≤ B := by
    intro h
    have hd := (S.pow_dvd_card_of_pow_dvd_card (n := 3)
      (by rw [hcard]; decide)).trans (card_dvd_of_le h)
    norm_num [hBcard] at hd
  obtain ⟨s,hs,hsB⟩ := Set.not_subset.mp hnot
  refine ⟨s,hs,?_⟩
  rintro ⟨b,hb⟩
  have hz : b.val⁻¹ * s ∈ centralizer (B : Set G) := by
    intro x hx
    have he := congrArg Subtype.val (DFunLike.congr_fun hb ⟨x,hx⟩)
    change b.val * x * b.val⁻¹ = s * x * s⁻¹ at he
    have hh : (b.val⁻¹*s)*x*(b.val⁻¹*s)⁻¹ = x := by
      calc
        _ = b.val⁻¹*(s*x*s⁻¹)*b.val := by group
        _ = x := by rw [← he]; group
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  have he : (b : G) = s := inv_mul_eq_one.mp (hc.le hz)
  exact hsB (he ▸ b.property)

/-- The same outer Sylow action on the literal two-core quotient of a
proper local component. The quadratic-field embedding theorem identifies
the original subgroup with A₅, so no central-kernel assumption is added. -/
theorem local_five_has_outer_sylow (S : Sylow 2 G) (B : Subgroup G)
    (hl : B ∈ ChapterA.Section03.localCComponents S)
    (hn : (S : Subgroup G) ≤ normalizer (B : Set G)) (hne : B ≠ ⊤)
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5))
    (hm : ClassicalGroup.IsPSL G 2 25) :
    ∃ s : G, ∃ hs : s ∈ (S : Subgroup G),
      (quotientAut (pCore 2 B)) (B.normalizerMonoidHom ⟨s,hn hs⟩) ∉
        MulAut.innerSubgroup (B ⧸ pCore 2 B) := by
  let : IsSimpleGroup G := by
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    exact e.isSimpleGroup_congr.mpr
      (Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega))
  let : Group.IsPerfect (B.subgroupOf (B ⊔ (S : Subgroup G))) := hl.perfect
  let d : B.subgroupOf (B ⊔ (S : Subgroup G)) ≃* B := subgroupOfEquivOfLe le_sup_left
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective
    (f := d.toMonoidHom) d.surjective
  have hB : B ≠ ⊥ := by
    intro he
    exact hl.ne_bot (by simp only [he,bot_subgroupOf])
  have hBle : B ≤ commutator G := by
    rw [← commutator_eq_self (H := B)]
    exact commutator_mono le_top le_top
  let : Group.IsPerfect G := ⟨
    (inferInstance : (commutator G).Normal).eq_bot_or_eq_top.resolve_left
      (fun he => hB (bot_unique (he ▸ hBle)))⟩
  have hz : center G = ⊥ := by
    rcases (inferInstance : (center G).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exact (Group.IsPerfect.not_isMulCommutative G (center_eq_top_iff.mp h)).elim
  let : IsQuasisimple G :=
    ⟨((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).isSimpleGroup⟩
  have ht : (⊤ : Subgroup G).IsCComponent :=
    (show IsComponent G ⊤ from ⟨.top,IsQuasisimple.of_mulEquiv topEquiv.symm⟩).isCComponent
  obtain ⟨_,⟨a⟩⟩ := proper_quadraticPSL2_five_models S hl ht le_top hne
    (by decide : Nat.Prime 5) (by decide : Odd 5) (hm.of_mulEquiv topEquiv) ⟨eB⟩
  have hcore : pCore 2 B = ⊥ := by
    let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
    let : IsSimpleGroup B := a.isSimpleGroup
    rcases (inferInstance : (pCore 2 B).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · have hc := Nat.card_congr eB.toEquiv
      rw [h,nat_card_alternatingGroup] at hc
      norm_num at hc
  let q := QuotientGroup.mk' (pCore 2 B)
  have hqi : Function.Injective q := (MonoidHom.ker_eq_bot_iff q).mp
    ((QuotientGroup.ker_mk' _).trans hcore)
  obtain ⟨s,hs,hout⟩ := exists_outer_on_five S B hn a hm
  refine ⟨s,hs,?_⟩
  rintro ⟨b,hb⟩
  obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 B) b
  apply hout
  refine ⟨b,?_⟩
  apply MulEquiv.ext
  intro x
  apply hqi
  have hh := DFunLike.congr_fun hb (q x)
  simpa only [q,quotientAut_apply_mk,MulAut.conj_apply,map_mul,map_inv] using hh

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.TwentyFive
