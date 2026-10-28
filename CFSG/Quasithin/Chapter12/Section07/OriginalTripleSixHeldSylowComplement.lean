module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixHeldFullAffine
public import Theory.Mathieu.M24.LocalGeometry.SextetCore.Comparison
public import Theory.Mathieu.M24.LocalGeometry.SylowNormalizer.ElementarySixteenComplement

/-! Complements to the actual normal self-centralizing elementary sixteen
subgroups of the original escaping Sylow. The unchanged affine normalizer
embeds the actual T in native M24. Transport retains the supplied A. -/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Atlas.Codes
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- The original full affine normalizer supplies a complement to each
actual normal self-centralizing elementary sixteen of the original T. -/
theorem original_tripleSix_escaping_sylow_complement
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K)
    (hout : ¬centralizer ({(t : G)} : Set G) ≤ normalizer (K : Set G))
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hA : Nat.card A = 16)
    (hAT : A ≤ (T : Subgroup G))
    (hTA : (T : Subgroup G) ≤ normalizer (A : Set G))
    (hself : (T : Subgroup G) ⊓ centralizer (A : Set G) ≤ A) :
    ∃ L : Subgroup T, (A.subgroupOf T).IsComplement' L := by
  obtain ⟨hTc, _, _, _, E, _, _, _⟩ :=
    original_tripleSix_escaping_full_affine_model h structural D a t ht heven hout
  let M := normalizer (K : Set G)
  let H := Sporadic.Mathieu.M24LocalGeometry.sextetStabilizer
    Sporadic.Mathieu.M24LocalGeometry.standardSextet
  let eM : M ≃* H := (E.trans sextetAffineEquiv).trans
    Sporadic.Mathieu.M24LocalGeometry.SextetCore.sextetEquiv.symm
  let f : M →* Sporadic.Mathieu.M24 := H.subtype.comp eM.toMonoidHom
  have hf : Function.Injective f := H.subtype_injective.comp eM.injective
  have hTM : (T : Subgroup G) ≤ M := by
    rw [show M = normalizer (K : Set G) from rfl,
      (original_tripleSix_escaping_core h structural D a t ht heven hout).2.2.2.2.2]
    exact le_sup_right
  let S₀ := ((T : Subgroup G).subgroupOf M).map f
  have hSc : Nat.card S₀ = 1024 := by
    rw [card_map_of_injective hf, Nat.card_congr (subgroupOfEquivOfLe hTM).toEquiv, hTc]
  let S : Sylow 2 Sporadic.Mathieu.M24 := Sylow.ofCard S₀ (by
    rw [hSc, Sporadic.Mathieu.m24_order]; decide +kernel)
  let eT : T ≃* S := (subgroupOfEquivOfLe hTM).symm.trans
    (((T : Subgroup G).subgroupOf M).equivMapOfInjective f hf)
  let R : Sylow 2 Sporadic.Mathieu.M24 := Sylow.ofCard
    Sporadic.Mathieu.M24LocalGeometry.SylowNormalizer.candidate (by
      rw [Sporadic.Mathieu.M24LocalGeometry.SylowNormalizer.candidate_card,
        Sporadic.Mathieu.m24_order]; decide +kernel)
  let e := eT.trans (S.equiv R)
  let A₀ := A.subgroupOf T
  let : A₀.Normal := normal_subgroupOf_of_le_normalizer hTA
  let : IsElementaryAbelian 2 A₀ := IsElementaryAbelian.subgroupOf hAT
  have hA₀ : Nat.card A₀ = 16 :=
    (Nat.card_congr (subgroupOfEquivOfLe hAT).toEquiv).trans hA
  have hself₀ : centralizer (A₀ : Set T) ≤ A₀ := by
    intro x hx
    apply hself
    refine ⟨x.property, ?_⟩
    intro y hy
    exact congrArg Subtype.val (hx ⟨y, hAT hy⟩ hy)
  exact Sporadic.Mathieu.M24LocalGeometry.SylowNormalizer.ElementarySixteenComplement.exists_complement_of_equiv
    e A₀ hA₀ hself₀

end CFSG.Quasithin.Chapter12.Section07
