module
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.LocalCover.Algebra
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ComponentIntersection.InnerSplitting.SectionAction

/-!
# Conjugation on the marked projective quotient

The marked action transports literal conjugation on L/O₂(L) through the
same equivalence as the diagonal actor. Its kernel is the chapter's section
centralizer. Full intrinsic automorphism coverage by the three local factors
therefore yields a literal set product after the centralizer is known to lie
in L. No change of field or quotient marking is made.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
proof of 15.3.38, printed p.1136.
-/

@[expose] public section
open Subgroup
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.LocalCover
variable {G : Type*} [Group G] {L : Subgroup G} {q : ℕ}

/-- Conjugation on the same marked two-core quotient used by the diagonal actor. -/
def markedAction (c : ProjectiveMarking L q) :
    normalizer (L : Set G) →* MulAut PSL(3,c.F) :=
  (MulAut.congr c.equivalence).toMonoidHom.comp
    (ComponentIntersection.InnerSplitting.sectionAction L)

theorem markedAction_apply (c : ProjectiveMarking L q)
    (g : normalizer (L : Set G)) (l : L) :
    markedAction c g (projectiveMap c l) =
      projectiveMap c (L.normalizerMonoidHom g l) := by
  change c.equivalence (ComponentIntersection.InnerSplitting.sectionAction L g
    (c.equivalence.symm (c.equivalence (QuotientGroup.mk' (pCore 2 L) l)))) = _
  rw [c.equivalence.symm_apply_apply, ComponentIntersection.InnerSplitting.sectionAction_apply]
  rfl

theorem markedAction_realizes (c : ProjectiveMarking L q)
    (g : normalizer (L : Set G)) : c.Realizes g (markedAction c g) := by
  exact ⟨L.normalizerMonoidHom g, fun _ => rfl, fun l => (markedAction_apply c g l).symm⟩

theorem markedAction_eq_of_realizes (c : ProjectiveMarking L q)
    (g : normalizer (L : Set G)) {α : MulAut PSL(3,c.F)} (h : c.Realizes g α) :
    markedAction c g = α := by
  obtain ⟨β, hβ, hcompat⟩ := h
  have hβeq : β = L.normalizerMonoidHom g :=
    MulEquiv.ext (fun l => Subtype.ext (hβ l))
  subst β
  apply MulEquiv.ext
  intro x
  obtain ⟨u, rfl⟩ := c.equivalence.surjective x
  obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) u
  exact (markedAction_apply c g l).trans (hcompat l)

theorem markedAction_eq_one_iff (c : ProjectiveMarking L q)
    (g : normalizer (L : Set G)) :
    markedAction c g = 1 ↔ (g : G) ∈ Chapter4.sectionCentralizer L := by
  change MulAut.congr c.equivalence (ComponentIntersection.InnerSplitting.sectionAction L g) = 1 ↔ _
  rw [← (MulAut.congr c.equivalence).map_one,
    (MulAut.congr c.equivalence).injective.eq_iff,
    ComponentIntersection.InnerSplitting.sectionAction_eq_one_iff]

theorem markedAction_on_component (c : ProjectiveMarking L q) (l : L) :
    markedAction c (inclusion L.le_normalizer l) = MulAut.conj (projectiveMap c l) := by
  apply MulEquiv.ext
  intro x
  obtain ⟨u, rfl⟩ := c.equivalence.surjective x
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) u
  rw [show c.equivalence (QuotientGroup.mk' (pCore 2 L) a) = projectiveMap c a from rfl,
    markedAction_apply]
  change projectiveMap c (l * a * l⁻¹) = _
  simp only [map_mul, map_inv, MulAut.conj_apply]

/-- Full intrinsic automorphism coverage supplies the source's action-coverage
premise and hence the literal three-factor product. -/
theorem product_of_marked_automorphism_coverage
    (c : ProjectiveMarking L q) {I D S : Subgroup G}
    [Group.IsPerfect L] (hcore : pCore 2 L ≤ center L)
    (hLI : L ≤ I) (hDI : D ≤ I) (hSI : S ≤ I)
    (hIL : I ≤ normalizer (L : Set G))
    (hC : I ⊓ centralizer (L : Set G) ≤ L)
    (hcover : ∀ α : MulAut PSL(3,c.F), ∃ l ∈ L, ∃ d ∈ D, ∃ s ∈ S,
      c.Realizes (l * d * s) α) :
    (I : Set G) = (L : Set G) * (D : Set G) * (S : Set G) := by
  apply product_of_section_action_coverage hcore hLI hDI hSI hC
  intro i hi
  let i' : normalizer (L : Set G) := ⟨i, hIL hi⟩
  obtain ⟨l, hl, d, hd, s, hs, he⟩ := hcover (markedAction c i')
  let u : normalizer (L : Set G) :=
    ⟨l * d * s, hIL (I.mul_mem (I.mul_mem (hLI hl) (hDI hd)) (hSI hs))⟩
  have hu : markedAction c u = markedAction c i' := markedAction_eq_of_realizes c u he
  refine ⟨l, hl, d, hd, s, hs, ?_⟩
  exact (markedAction_eq_one_iff c (i' * u⁻¹)).mp (by rw [map_mul, map_inv, hu, mul_inv_cancel])


/-- The diagonal branch puts the whole residual action in the actual
inner-diagonal matrix subgroup, retaining the given marking. -/
theorem markedAction_mem_innerDiagonal {Y : Subgroup G} {y : G}
    (c : ProjectiveMarking L q) (hYL : Y ≤ normalizer (L : Set G))
    (hyY : y ∈ Y) (hy : c.Diagonal y)
    (hprod : (Y : Set G) = (componentPart Y L : Set G) * (zpowers y : Set G))
    {d : G} (hd : d ∈ Y) :
    markedAction c ⟨d, hYL hd⟩ ∈ Matrix.PSL3.OuterSolvable.innerDiagonal c.F := by
  let N := normalizer (L : Set G)
  have hyN : y ∈ N := hYL hyY
  obtain ⟨_, a, _, ha⟩ := hy
  have hyin : markedAction c ⟨y, hyN⟩ ∈ Matrix.PSL3.OuterSolvable.innerDiagonal c.F := by
    exact ⟨a, (markedAction_eq_of_realizes c ⟨y, hyN⟩ ha).symm⟩
  have hdprod : d ∈ (componentPart Y L : Set G) * (zpowers y : Set G) := hprod ▸ hd
  obtain ⟨l, hl, z, hz, rfl⟩ := hdprod
  have hlL : l ∈ L := (map_subtype_le _ hl).2
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hz
  have hlin : markedAction c (inclusion L.le_normalizer ⟨l, hlL⟩) ∈
      Matrix.PSL3.OuterSolvable.innerDiagonal c.F := by
    rw [markedAction_on_component]
    exact Matrix.PSL3.OuterSolvable.inner_le_innerDiagonal c.F ⟨_, rfl⟩
  change markedAction c ((inclusion L.le_normalizer ⟨l, hlL⟩) *
    (⟨y, hyN⟩ : N) ^ k) ∈ _
  rw [map_mul, map_zpow]
  exact (Matrix.PSL3.OuterSolvable.innerDiagonal c.F).mul_mem hlin
    ((Matrix.PSL3.OuterSolvable.innerDiagonal c.F).zpow_mem hyin k)

/-- After centralizer elimination, inner action on the quotient detects
membership in the actual component. -/
theorem markedAction_inner_iff_mem (c : ProjectiveMarking L q) {I : Subgroup G}
    [Group.IsPerfect L] (hcore : pCore 2 L ≤ center L)
    (hLI : L ≤ I) (hIL : I ≤ normalizer (L : Set G))
    (hC : I ⊓ centralizer (L : Set G) ≤ L) {d : G} (hd : d ∈ I) :
    markedAction c ⟨d, hIL hd⟩ ∈ MulAut.innerSubgroup PSL(3,c.F) ↔ d ∈ L := by
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨u, rfl⟩ := c.equivalence.surjective x
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) u
    let d' : normalizer (L : Set G) := ⟨d, hIL hd⟩
    let l' := inclusion L.le_normalizer l
    have he : markedAction c d' = markedAction c l' := by
      rw [markedAction_on_component]
      exact hx.symm
    have hk : d * (l : G)⁻¹ ∈ Chapter4.sectionCentralizer L :=
      (markedAction_eq_one_iff c (d' * l'⁻¹)).mp (by rw [map_mul, map_inv, he, mul_inv_cancel])
    rw [sectionCentralizer_eq_centralizer_of_perfect hcore] at hk
    have hmem : d * (l : G)⁻¹ ∈ L := hC ⟨I.mul_mem hd (I.inv_mem (hLI l.property)), hk⟩
    simpa using L.mul_mem hmem l.property
  · intro hdL
    have he := markedAction_on_component c (⟨d, hdL⟩ : L)
    exact ⟨_, he.symm⟩

/-- An order-three element of Y_D outside L inherits a genuinely outer
diagonal action on the same marked quotient as the original actor. -/
theorem diagonal_of_order_three_outside {I Y : Subgroup G} {y d : G}
    (c : ProjectiveMarking L q) [Group.IsPerfect L]
    (hcore : pCore 2 L ≤ center L) (hLI : L ≤ I)
    (hYI : Y ≤ I) (hIL : I ≤ normalizer (L : Set G))
    (hC : I ⊓ centralizer (L : Set G) ≤ L)
    (hyY : y ∈ Y) (hy : c.Diagonal y)
    (hprod : (Y : Set G) = (componentPart Y L : Set G) * (zpowers y : Set G))
    (hdY : d ∈ Y) (hd3 : orderOf d = 3) (hdL : d ∉ L) : c.Diagonal d := by
  obtain ⟨a, ha⟩ := markedAction_mem_innerDiagonal c (hYI.trans hIL) hyY hy hprod hdY
  refine ⟨hd3, a, ?_, ?_⟩
  · rw [ha]
    exact fun h => hdL ((markedAction_inner_iff_mem c hcore hLI hIL hC (hYI hdY)).mp h)
  · rw [ha]
    exact markedAction_realizes c ⟨d, hIL (hYI hdY)⟩

/-- The original cyclic supplement detects inner action before center
identification. In particular the complementary residual's order-three actor
is available to the intrinsic cover calculations without circularity. -/
theorem diagonal_from_cyclic_supplement {L Y : Subgroup G} {q : ℕ} {y d : G}
    (c : ProjectiveMarking L q) (hYL : Y ≤ normalizer (L : Set G))
    (hyY : y ∈ Y) (hy : c.Diagonal y)
    (hprod : (Y : Set G) = (componentPart Y L : Set G) * (zpowers y : Set G))
    (hdY : d ∈ Y) (hd3 : orderOf d = 3) (hdL : d ∉ L) : c.Diagonal d := by
  let N := normalizer (L : Set G)
  let y' : N := ⟨y, hYL hyY⟩
  let f := (QuotientGroup.mk' (MulAut.innerSubgroup PSL(3,c.F))).comp (markedAction c)
  obtain ⟨a, ha⟩ := markedAction_mem_innerDiagonal c hYL hyY hy hprod hdY
  refine ⟨hd3, a, ?_, ?_⟩
  · rw [ha]
    intro hdinner
    have hyorder : orderOf y' = 3 := by simpa [y'] using hy.1
    have hyout : f y' ≠ 1 := by
      intro he
      obtain ⟨_, ay, hout, hreal⟩ := hy
      have hyaction := markedAction_eq_of_realizes c y' hreal
      apply hout
      rw [← hyaction]
      exact (QuotientGroup.eq_one_iff _).mp he
    have hy3 : y' ^ 3 = 1 := (orderOf_eq_prime_iff.mp hyorder).1
    have hforder : orderOf (f y') = 3 := orderOf_eq_prime
      (by rw [← map_pow, hy3, map_one]) hyout
    have hd0 : f ⟨d, hYL hdY⟩ = 1 := (QuotientGroup.eq_one_iff _).mpr hdinner
    have hdprod : d ∈ (componentPart Y L : Set G) * (zpowers y : Set G) := hprod ▸ hdY
    obtain ⟨l, hl, z, hz, hdz⟩ := hdprod
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hz
    have hlL : l ∈ L := (map_subtype_le _ hl).2
    let l' := inclusion L.le_normalizer (⟨l, hlL⟩ : L)
    have hl0 : f l' = 1 := by
      apply (QuotientGroup.eq_one_iff _).mpr
      rw [show markedAction c l' = MulAut.conj (projectiveMap c ⟨l, hlL⟩) from
        markedAction_on_component c ⟨l, hlL⟩]
      exact ⟨_, rfl⟩
    have hdz' : l' * y' ^ k = (⟨d, hYL hdY⟩ : N) := Subtype.ext hdz
    rw [← hdz', map_mul, map_zpow, hl0, one_mul] at hd0
    have hdiv := (orderOf_dvd_iff_zpow_eq_one).mpr hd0
    rw [hforder] at hdiv
    have hyk : y' ^ k = 1 := orderOf_dvd_iff_zpow_eq_one.mp (hyorder ▸ hdiv)
    have hykG : y ^ k = 1 := congrArg (fun x : N => (x : G)) hyk
    apply hdL
    change l * y ^ k = d at hdz
    rw [hykG, mul_one] at hdz
    exact hdz ▸ hlL
  · rw [ha]
    exact markedAction_realizes c ⟨d, hYL hdY⟩


end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.LocalCover
