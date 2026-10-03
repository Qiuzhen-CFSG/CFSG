module
public import ABG.ChapterII.Section1.WreathedAbelianMaximal
public import ABG.ChapterII.Section1.WreathedBaseFrattini
public import ABG.ChapterII.Section1.FusionPatterns
public import Theory.GroupTheory.PGroup.FrattiniAutomorphismKernel
public import Theory.GroupTheory.SylowDetectsKernel
public import Theory.GroupTheory.SpecificGroups.KleinFourAut
public import Mathlib.GroupTheory.IndexNormal

/-!
# The faithful Frattini action on the wreathed base

For a finite group with a wreathed fusion frame, the actual abelian maximal
subgroup U has Klein four Frattini quotient, and the normalizer's automorphism
image acts faithfully on this quotient. When the automizer has order six,
the quotient action is surjective. This is the substantive action
calculation underlying the U automizer bound and subsequent focal and
involution-fusion steps in Alperin--Brauer--Gorenstein, Chapter II, Section 1,
Proposition 2, article p.12 (the second proof paragraph in page-013.tex).

Identify U with the abelian base of the chosen Sylow presentation. The
Frattini quotient equivalence transfers the presentation's Klein four
structure and distinct generator classes. The presentation involution swaps
those classes, while the base acts trivially. Maximality of the base therefore
identifies the Sylow kernel of the quotient action. The full Frattini
automorphism kernel is a two-group, so Sylow detection makes the normalizer
image act faithfully. All exported constructions use the actual subgroup U
and its normalizer action. The surjectivity corollary compares the faithful
image's cardinality with the six automorphisms of a Klein four group.
-/

open scoped IsMulCommutative

namespace ABG.Wreathed

/-- The wreathed base has Klein four Frattini quotient, and its normalizer
automorphism image acts faithfully on that quotient. -/
public theorem u_frattini_action {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (n : ℕ) (U V : Subgroup G)
    (hf : WreathedFusionFrame S n U V) :
    IsKleinFour (U ⧸ frattini U) ∧
      Function.Injective ((Subgroup.quotientAut (frattini U)).comp
        U.normalizerMonoidHom.range.subtype) := by
  obtain ⟨P⟩ := nonempty_presentation hf.1
  have hUS : U ≤ S := hf.2.1
  have hUP : U.subgroupOf (S : Subgroup G) = P.U := by
    apply P.abelian_eq_U_of_isCoatom
    · let := hf.2.2.1
      apply IsMulCommutative.of_comm
      intro a b
      apply (Subgroup.subgroupOfEquivOfLe hUS).injective
      simp only [map_mul, mul_comm]
    · exact hf.2.2.2.1
  have hnU : (U.subgroupOf (S : Subgroup G)).Normal := by
    rw [hUP]
    exact Subgroup.normal_of_index_eq_two P.index_U
  have hSN : (S : Subgroup G) ≤ Subgroup.normalizer (U : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUS).mp hnU
  let N := Subgroup.normalizer (U : Set G)
  let i : S →* N := Subgroup.inclusion hSN
  let e : P.U ≃* U := (MulEquiv.subgroupCongr hUP.symm).trans
    (Subgroup.subgroupOfEquivOfLe hUS)
  have hefrat : (frattini P.U).map e.toMonoidHom = frattini U := by
    apply le_antisymm
    · exact Subgroup.map_le_iff_le_comap.mpr
        (frattini_le_comap_frattini_of_surjective e.surjective)
    · intro u hu
      refine ⟨e.symm u, ?_, e.apply_symm_apply u⟩
      exact frattini_le_comap_frattini_of_surjective
        (φ := e.symm.toMonoidHom) e.symm.surjective hu
  let qe : P.U ⧸ frattini P.U ≃* U ⧸ frattini U :=
    QuotientGroup.congr _ _ e hefrat
  have hfour : IsKleinFour (U ⧸ frattini U) := by
    let := P.base_frattini_structure.1
    constructor
    · rw [← Nat.card_congr qe.toEquiv]
      exact IsKleinFour.card_four
    · rw [← Monoid.exponent_eq_of_mulEquiv qe]
      exact IsKleinFour.exponent_two
  refine ⟨hfour, ?_⟩
  let f := U.normalizerMonoidHom
  let q := Subgroup.quotientAut (frattini U)
  let r := (q.comp f).comp i
  have ef (g : S) (u : P.U) : (f (i g) (e u) : G) =
      (g : G) * (e u : G) * (g : G)⁻¹ := by rfl
  have htriv (g : S) (hg : g ∈ P.U) : f (i g) = 1 := by
    apply MulEquiv.ext
    intro u
    obtain ⟨v, rfl⟩ := e.surjective u
    apply Subtype.ext
    rw [ef]
    have hc := congrArg Subtype.val (P.commute_of_mem_U hg v.property).eq
    change (g : G) * (v : G) = (v : G) * (g : G) at hc
    change (g : G) * (v : G) * (g : G)⁻¹ = (v : G)
    rw [hc, mul_assoc, mul_inv_cancel, mul_one]
  have hUker : P.U ≤ r.ker := by
    intro g hg
    change q (f (i g)) = 1
    rw [htriv g hg, map_one]
  let s : P.U := ⟨P.s, Subgroup.subset_closure (by simp)⟩
  let t : P.U := ⟨P.t, Subgroup.subset_closure (by simp)⟩
  have hzt : f (i P.z) (e s) = e t := by
    apply Subtype.ext
    rw [ef]
    change (P.z : G) * (P.s : G) * (P.z : G)⁻¹ = (P.t : G)
    have hz : P.z⁻¹ = P.z := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using P.z_sq)
    have hzG : (P.z : G)⁻¹ = (P.z : G) := congrArg Subtype.val hz
    rw [hzG]
    exact congrArg Subtype.val (by simpa only [hz] using P.conj_s)
  have hrz : r P.z ≠ 1 := by
    intro h
    have hh := DFunLike.congr_fun h (QuotientGroup.mk' (frattini U) (e s))
    change q (f (i P.z)) (QuotientGroup.mk' (frattini U) (e s)) = _ at hh
    rw [Subgroup.quotientAut_apply_mk, hzt] at hh
    apply P.base_frattini_structure.2 s t rfl rfl
    apply qe.injective
    exact hh.symm
  have hrproper : r.ker ≠ ⊤ := by
    intro he
    have hzmem : P.z ∈ r.ker := he ▸ Subgroup.mem_top P.z
    exact hrz hzmem
  have hrker : r.ker = P.U := (P.U_isCoatom.le_iff_eq hrproper).mp hUker
  have hlocal : ∀ g : S, q (f (i g)) = 1 → f (i g) = 1 := by
    intro g hg
    exact htriv g (hrker ▸ hg)
  exact Sylow.injective_on_range_of_isPGroup_kernel (S.subtype hSN) f q
    (Subgroup.isPGroup_quotientAut_frattini_kernel
      ((S.isPGroup'.to_subgroup P.U).of_equiv e))
    (fun g hg => hlocal ((Subgroup.subgroupOfEquivOfLe hSN) g) hg)

/-- An automizer of order six induces every automorphism of the base's
Frattini quotient. -/
public theorem u_frattini_action_surjective {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (n : ℕ) (U V : Subgroup G)
    (hf : WreathedFusionFrame S n U V) (hindex : automizerIndex U = 6) :
    Function.Surjective ((Subgroup.quotientAut (frattini U)).comp
      U.normalizerMonoidHom) := by
  obtain ⟨hfour, hfaith⟩ := u_frattini_action S n U V hf
  let := hfour
  let f := U.normalizerMonoidHom
  let q := Subgroup.quotientAut (frattini U)
  have hcard : Nat.card f.range = Nat.card (MulAut (U ⧸ frattini U)) := by
    rw [IsKleinFour.card_mulAut, ← hindex, ← Subgroup.index_ker]
    rw [Subgroup.normalizerMonoidHom_ker]
    rfl
  have hsurj := (Nat.bijective_iff_injective_and_card (q.comp f.range.subtype)).mpr
    ⟨hfaith, hcard⟩
  intro a
  obtain ⟨b, hb⟩ := hsurj.2 a
  obtain ⟨g, hg⟩ := b.property
  refine ⟨g, ?_⟩
  change q (f g) = a
  rw [hg]
  exact hb

end ABG.Wreathed
