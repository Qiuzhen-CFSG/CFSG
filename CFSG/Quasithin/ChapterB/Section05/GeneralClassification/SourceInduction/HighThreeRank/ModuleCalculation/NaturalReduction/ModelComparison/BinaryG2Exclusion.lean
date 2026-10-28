module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.HighThreeRank.ModuleCalculation.NaturalReduction.ModelComparison.KernelObstruction
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.HighThreeRank.ModuleCalculation.NaturalReduction.ModelComparison.BinaryG2Exclusion.MultiplierTable
public import Theory.SpecificGroups.SU3.Quasisimplicity
public import Theory.SpecificGroups.SU3.FixedFieldTwo
public import Theory.SpecificGroups.SL2.OddOrderDivisibility
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.BinaryAction
public import Theory.AtlasPort.LinearGroups.G2.BinaryDerivedSimplicity
public import Theory.Mathieu.M22.Properties.Order

/-!
# Excluding G₂(2)′ with the actual component lift

The supplied noncentral context forces three to divide the center of its
actual lifted component. The complete earlier multiplier table I.1.3 rules
out a three-part in every perfect central-cover kernel of this component
if it is isomorphic to the literal derived octonion group.

Indeed that group has order 6048. Only the degree-three, alternating-six or
-seven, M₂₂ and exceptional L₃(4) rows of I.1.3 could contribute a factor of
three. The cube of the defining-field order divides the degree-three group
order. Combined with the source congruences, this excludes every linear row
and leaves only PSU₃(2), whose actual projective order is 72. The proved
alternating and M₂₂ orders exclude the other rows. Order is used solely to
refute proposed equivalences; no group is recognized from its order.

Universality then maps the constructed Schur multiplier onto the kernel of
the literal restricted projection. Since the component is centerless, this
kernel is the lifted center, giving the contradiction. The final theorem
uses only `EarlierMultiplierInput` beyond the supplied component and
`NoncentralContext`. It does not assume an intrinsic kernel exclusion.
The universal table remains with its existing producer `qt-i-01` (including
`qt-i01-lie-a2`); no further earlier-source parameters are introduced.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
B.5.7, printed pp.105–106, and I.1.1–3, p.407. The octonion order and
simplicity proofs are inherited from the licensed ATLAS port; see
`LICENSES/ATLAS.txt` and `LICENSES/ATLAS-CITATION.cff`.
-/

@[expose] public section
open Subgroup Theory.GroupTheory PerfectCentralCovering BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterB.SourceInduction.HighThreeRank.ModuleCalculation.NaturalReduction.ModelComparison.BinaryG2Exclusion
universe u

private theorem cube_divisor_bound {q : ℕ} (hd : q ^ 3 ∣ 6048) : q ≤ 18 := by
  have hle := Nat.le_of_dvd (by decide : 0 < 6048) hd
  by_contra h
  have hq : 19 ≤ q := by omega
  have := Nat.pow_le_pow_left hq 3
  norm_num at this
  omega

private theorem not_linear_row {S : Type u} [Group S] (hc : Nat.card S = 6048)
    {q : ℕ} (hcong : q % 3 = 1) (hm : ClassicalGroup.IsPSL S 3 q) : False := by
  obtain ⟨F, hF, hfin, hq, ⟨e⟩⟩ := hm
  have hd := Matrix.ProjectiveSpecialLinearGroup.psl3_cube_dvd_card (F := F)
  rw [hq, ← Nat.card_congr e.toEquiv, hc] at hd
  have hqpos : 1 < q := hq ▸ Finite.one_lt_card
  have hb := cube_divisor_bound hd
  interval_cases q <;> omega

private theorem not_unitary_row {S : Type u} [Group S] (hc : Nat.card S = 6048)
    {p f : ℕ} (hp : p.Prime) (hf : 0 < f) (hcong : (p ^ f) % 3 = 2)
    (hm : ClassicalGroup.IsPSU S 3 (p ^ f)) : False := by
  obtain ⟨F, hF, hfin, J, hcard, hconj, ⟨e⟩⟩ := hm
  let : Fact p.Prime := ⟨hp⟩
  have hfixed := FiniteField.card_fixed_of_quadratic_frobenius J.conj p f hf hcard hconj
  have hd := J.cube_dvd_card_projective hcard hfixed
  rw [← Nat.card_congr e.toEquiv, hc] at hd
  have he : p ^ f = 2 := by
    generalize p ^ f = q at hd hcong ⊢
    have hb := cube_divisor_bound hd
    interval_cases q <;> omega
  have h72 := HermitianForm.FixedFieldTwo.card_projective J (he ▸ hcard) (he ▸ hconj)
  rw [← Nat.card_congr e.toEquiv, hc] at h72
  norm_num at h72

private theorem multiplier_three_free_of_card {S : Type u} [Group S] [Finite S]
    [Group.IsPerfect S] (h : MultiplierTable S) (hc : Nat.card S = 6048) :
    ¬ 3 ∣ Nat.card (schurMultiplier S) := by
  intro hd
  have hn : Nontrivial (schurMultiplier S) := Finite.one_lt_card_iff_nontrivial.mp
    (lt_of_lt_of_le (by decide : 1 < 3) (Nat.le_of_dvd Nat.card_pos hd))
  obtain ⟨r, hr⟩ := h.exhaustive.mp hn
  obtain ⟨e⟩ := h.values r hr
  have hdiv : 3 ∣ Nat.card r.Carrier := (Nat.card_congr e.toEquiv) ▸ hd
  cases r with
  | two => norm_num [MultiplierShape.Carrier] at hdiv
  | elementaryFour => norm_num [MultiplierShape.Carrier, Nat.card_prod] at hdiv
  | three =>
      obtain ⟨_, hlin | hunit⟩ := hr
      · obtain ⟨q, hq, he⟩ := hlin
        exact not_linear_row hc hq he
      · obtain ⟨p, f, hp, hf, hq, he⟩ := hunit
        exact not_unitary_row hc hp hf hq he
  | six =>
      change Nonempty (S ≃* alternatingGroup (Fin 6)) ∨
        Nonempty (S ≃* alternatingGroup (Fin 7)) at hr
      rcases hr with h6 | h7
      · obtain ⟨e6⟩ := h6
        have he := Nat.card_congr e6.toEquiv
        rw [hc, nat_card_alternatingGroup] at he
        norm_num at he
      · obtain ⟨e7⟩ := h7
        have he := Nat.card_congr e7.toEquiv
        rw [hc, nat_card_alternatingGroup] at he
        norm_num at he
  | twelve =>
      obtain ⟨e⟩ := hr
      have he := Nat.card_congr e.toEquiv
      rw [hc, Sporadic.Mathieu.m22_order] at he
      norm_num at he
  | exceptionalFortyEight =>
      exact not_linear_row hc (q := 4) (by decide) hr

private theorem kernel_card_dvd_schurMultiplier
    {S E : Type u} [Group S] [Finite S] [Group.IsPerfect S]
    [Group E] [Finite E] (f : Cover E S) :
    Nat.card f.toMonoidHom.ker ∣ Nat.card (schurMultiplier S) := by
  let := f.isPerfect
  obtain ⟨h, hh, _⟩ := (universalCover_isUniversal (G := S)) E f
  have hsurj : Function.Surjective h :=
    surjective_of_comp_surjective_of_ker_le_center_of_isPerfect
      f.toMonoidHom h (hh ▸ (universalCover S).surjective) f.ker_le_center
  let k : schurMultiplier S →* f.toMonoidHom.ker := {
    toFun x := ⟨h x, (DFunLike.congr_fun hh (x : UniversalGroup S)).trans x.property⟩
    map_one' := Subtype.ext h.map_one
    map_mul' := fun x y => Subtype.ext (h.map_mul x y) }
  apply card_dvd_of_surjective k
  intro z
  obtain ⟨x, hx⟩ := hsurj z
  have hker : x ∈ schurMultiplier S := by
    change (universalCover S).toMonoidHom x = 1
    rw [← hh]
    change f.toMonoidHom (h x) = 1
    rw [hx]
    exact z.property
  exact ⟨⟨x, hker⟩, Subtype.ext hx⟩

/-- The complete multiplier table implies that every perfect central cover
of an SQTK simple group of order 6048 has kernel prime to three.
The order is used only to exclude table rows, never to identify a group. -/
theorem threeFreePerfectKernels_of_table
    {S : Type u} [Group S] [Finite S] [Group.IsPerfect S]
    (h : MultiplierTable S) (hc : Nat.card S = 6048) :
    ThreeFreePerfectKernels.{u} S := by
  intro E _ _ f hd
  exact multiplier_three_free_of_card h hc (hd.trans (kernel_card_dvd_schurMultiplier f))

end CFSG.Quasithin.ChapterB.SourceInduction.HighThreeRank.ModuleCalculation.NaturalReduction.ModelComparison.BinaryG2Exclusion

namespace CFSG.Quasithin.ChapterB.SourceInduction.HighThreeRank.ModuleCalculation.NaturalReduction.ModelComparison
open BinaryG2Exclusion
universe u

/-- The literal derived octonion group cannot be the component in this
noncentral context. The sole earlier-source parameter is the complete
universal I.1.3 implication; the representation and rank hypotheses of
the B.5.7 consumer require no further use after this context is constructed. -/
theorem not_binaryG2_component
    {G : Type u} [Group G] [Finite G] {K : GroupClass.{u}}
    (earlier : EarlierMultiplierInput K)
    {L : Subgroup G} (hL : IsComponent G L) (d : NoncentralContext K G L) :
    ¬ Nonempty (L ≃* commutator (Atlas.G2.Model (ZMod 2))) := by
  rintro ⟨e⟩
  let := hL.2
  let : IsSimpleGroup (commutator (Atlas.G2.Model (ZMod 2))) :=
    Atlas.G2.isSimple_commutator_binary
  let : IsSimpleGroup L := e.isSimpleGroup
  have hz : center L = ⊥ := by
    rcases (inferInstance : (center L).Normal).eq_bot_or_eq_top with hb | ht
    · exact hb
    · exact (Group.IsPerfect.not_isMulCommutative L (center_eq_top_iff.mp ht)).elim
  have hc : Nat.card L = 6048 :=
    (Nat.card_congr e.toEquiv).trans Atlas.G2.LieAutomorphismExtensions.card_binaryDerived
  exact not_model_of_threeFreePerfectKernels hL d hz
    (threeFreePerfectKernels_of_table (earlier L d.component_sqtk) hc) (MulEquiv.refl L)

end CFSG.Quasithin.ChapterB.SourceInduction.HighThreeRank.ModuleCalculation.NaturalReduction.ModelComparison
