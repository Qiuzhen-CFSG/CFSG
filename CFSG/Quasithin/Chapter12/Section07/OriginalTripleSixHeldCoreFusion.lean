module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixPointCentralizer
public import Theory.Representation.HexacodeAction.EvenOrbitWeights
public import Theory.GroupTheory.NormalSylowQuotientAction
public import Theory.GroupTheory.Recognition.TransvectionFive.LocalData

/-!
A coordinate kernel in the original sixteen-element overlap has at least
four elements. A nonidentity element different from the prescribed z has
weight four, hence belongs to the same original K-orbit as the Sylow-fixed z.
This supplies actual fusion inside the prescribed P, without replacing z or P.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Atlas.Codes
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

omit [Finite G] in
private theorem weight_four_in_sixteen
    (c : U ≃* Multiplicative hexacode) (A : Subgroup U) (hA : Nat.card A = 16)
    (z : U) : ∃ w : U, w ∈ A ∧ w ≠ 1 ∧ w ≠ z ∧
      hammingNorm (c w).toAdd.val = 4 := by
  classical
  let φ : A →* Multiplicative Atlas.Codes.K :=
    (hexCoordinate (0, 0)).toAddMonoidHom.toMultiplicative.comp
      (c.toMonoidHom.comp A.subtype)
  have hrange : Nat.card φ.range ≤ 4 := by
    have hh := Nat.card_le_card_of_injective φ.range.subtype φ.range.subtype_injective
    have hc : Nat.card (Multiplicative Atlas.Codes.K) = 4 := by
      rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative Atlas.Codes.K ≃ Atlas.Codes.K)]
      simp [Atlas.Codes.K, Letter, Bit]
    exact hh.trans_eq hc
  have hmul : Nat.card φ.ker * Nat.card φ.range = 16 := by
    have hh := φ.ker.card_mul_index
    rw [index_ker, hA] at hh
    exact hh
  have hex : ∃ w : φ.ker, (w.val : U) ≠ 1 ∧ (w.val : U) ≠ z := by
    by_contra! hn
    let f : φ.ker → Bool := fun x => if (x.val : U) = 1 then false else true
    have hf : Function.Injective f := by
      intro x y hxy
      apply Subtype.ext
      apply Subtype.ext
      by_cases hx : (x.val : U) = 1
      · have hy : (y.val : U) = 1 := by
          by_contra hy
          simp only [f, if_pos hx, if_neg hy] at hxy
          cases hxy
        exact hx.trans hy.symm
      · have hy : (y.val : U) ≠ 1 := by
          intro hy
          simp only [f, if_neg hx, if_pos hy] at hxy
          cases hxy
        exact (hn x hx).trans (hn y hy).symm
    have hc : Nat.card φ.ker ≤ 2 := by
      simpa using Nat.card_le_card_of_injective f hf
    nlinarith
  obtain ⟨w, hw1, hwz⟩ := hex
  have hw0 : (c (w.val : U)).toAdd ≠ 0 := by
    intro hh
    exact hw1 (c.injective (hh.trans c.map_one.symm))
  have hwcoord : (c (w.val : U)).toAdd.val (0, 0) = 0 := w.property
  refine ⟨w.val, w.val.property, hw1, hwz, ?_⟩
  rcases hex_weights (c (w.val : U)).toAdd with h0 | h4 | h6
  · exact (hw0 (Subtype.ext (hammingNorm_eq_zero.mp h0))).elim
  · exact h4
  · exact (Hexacode.full_weight_coordinate_ne_zero _ h6 (0, 0) hwcoord).elim

/-- A Sylow-fixed point has a distinct actual K-conjugate in any prescribed
P meeting the original module in sixteen elements. -/
theorem tripleSix_conjugate_in_sixteen_overlap
    (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction)
    (P : Subgroup G) (hUP : Nat.card (U ⊓ P : Subgroup G) = 16)
    (z : U) (hz : z ≠ 1)
    (hTz : (T : Subgroup G) ≤ centralizer ({(z : G)} : Set G)) :
    ∃ k ∈ K, k * (z : G) * k⁻¹ ∈ P ∧ k * (z : G) * k⁻¹ ≠ (z : G) := by
  let c := tripleSixPointCoordinates D a
  have hz0 : (c z).toAdd ≠ 0 := by
    intro hh
    exact hz (c.injective (hh.trans c.map_one.symm))
  obtain ⟨S, hS⟩ := NormalSylowQuotientAction.intersection_sylow T K
    D.sylow_normalizes_component
  have hodd : ¬ 2 ∣ (centralizer ({(z : G)} : Set G)).relIndex K := by
    intro hi
    apply S.not_dvd_index
    apply hi.trans
    apply index_dvd_of_le
    rw [hS]
    exact fun k hk => hTz hk
  have hzweight : hammingNorm (c z).toAdd.val = 4 := by
    have hc := Hexacode.evenAction_orbit_card (c z).toAdd hz0
    rw [tripleSixPoint_orbit_card D a z] at hc
    by_contra hn
    rw [if_neg hn] at hc
    exact hodd (hc ▸ (by decide : 2 ∣ 18))
  let A := (U ⊓ P : Subgroup G).subgroupOf U
  have hA : Nat.card A = 16 :=
    (Nat.card_congr (subgroupOfEquivOfLe (show U ⊓ P ≤ U from inf_le_left)).toEquiv).trans hUP
  obtain ⟨w, hw, _, hwz, hw4⟩ := weight_four_in_sixteen c A hA z
  have hm : (c w).toAdd ∈ Set.range (fun g : HexEvenAutomorphisms =>
      Hexacode.evenAction g (c z).toAdd) := by
    rw [Hexacode.evenAction_orbit_eq_weight _ hz0]
    exact hw4.trans hzweight.symm
  obtain ⟨g, hg⟩ := hm
  change Hexacode.evenAction g (tripleSixPointCoordinates D a z).toAdd =
    (tripleSixPointCoordinates D a w).toAdd at hg
  obtain ⟨k, hk⟩ := QuotientGroup.mk'_surjective (pCore 2 K) (a.groupEquiv.symm g)
  have he := tripleSixPointCoordinates_conjugate D a k z
  rw [hk, a.groupEquiv.apply_symm_apply, hg] at he
  change (c.symm (c w) : G) = _ at he
  rw [c.symm_apply_apply] at he
  exact ⟨k, k.property, he ▸ hw.2, fun hh => hwz (Subtype.ext (he.trans hh))⟩

/-- Once its literal centralizer core is identified, the same prescribed
point satisfies the marked-transvection recognition fusion hypothesis. -/
theorem tripleSix_point_core_fusion
    (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction)
    (P : Subgroup G) (hUP : Nat.card (U ⊓ P : Subgroup G) = 16)
    (z : U) (hz : z ≠ 1)
    (hTz : (T : Subgroup G) ≤ centralizer ({(z : G)} : Set G))
    (hcore : (centralizer ({(z : G)} : Set G)).pCoreIn 2 = P) :
    TransvectionFive.PointCoreFusion (z : G) := by
  obtain ⟨k, _, hk, hne⟩ := tripleSix_conjugate_in_sixteen_overlap D a P hUP z hz hTz
  exact ⟨k, hcore.symm ▸ hk, hne⟩

end CFSG.Quasithin.Chapter12.Section07
