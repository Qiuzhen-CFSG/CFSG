module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SevenLifting.Inspection.BinaryLie.Obstructions
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SevenLifting.Inspection.BinaryLie.Ree.Parabolics
public import Theory.SpecificGroups.ReeF4.ConverseParabolics.Coverage
public import Theory.SpecificGroups.ReeF4.ConverseParabolics.Suzuki
public import Theory.GroupAction.InnerInvolutionGeometry
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.FieldAction
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.LargeAutomorphisms

/-!
# Seven-component inspection for the actual Ree fixed groups

Choose an involution in any nonidentity two-subgroup of automorphisms.
When this automorphism is inner, centerlessness gives an actual involution
representative in the original simple group. Transport it through the supplied
`S ≃* d.fixedGroup` and the matrix-preserving `d.modelEquiv`. The proved
normalizer coverage puts its centralizer in a conjugate full Ree parabolic.
A component of the common fixed group embeds there and remains perfect,
so the rank-one projection excludes A₇ and its perfect central three-cover.
The proof never promotes this component to a component of the larger
single-involution centralizer.

The final theorem `ree` discharges inner-times-field coverage using the proved
two-power automorphism theorem and supplies the constructed full
Suzuki-parabolic projection with two-group kernel. Both full-parabolic
branches therefore exclude the seven components without additional model
premises. No strongly-quasithin hypothesis is needed for this deduction;
the source consumer may retain it. The binary parameter and Tits group are
separate branches. The conditional reductions remain available below.

Source: Aschbacher–Smith, E.6.18, printed p.252, and Theorem C/Remark A.2.4,
printed p.33 of `refs/quasithin.pdf`. The parabolic coverage uses GLS3,
Theorem 3.1.3; the actual Levi and field calculations retain their own sources.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.BinaryLie
open ReeF4.ConverseParabolics

/-- The full common-fixed-component inspection, conditional only on
innerness of actor involutions and the Suzuki-side projection. The supplied
local-block witness is compared with the model by its actual `modelEquiv`. -/
theorem ree_of_involution_inner_and_suzuki_projection
    {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    (hnonab : ¬ IsMulCommutative S) {m : ℕ} (hm : 1 ≤ m)
    (hmodel : Chapter1.Section02.LocalModels.IsReeF4At S m)
    (hinner : ∀ a : MulAut (ReeF4.Model m), orderOf a = 2 →
      ∃ x : ReeF4.Model m, a = MulAut.conj x)
    (π : parabolic m .suzuki →*
      BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m × (ReeF4.CoefficientField m)ˣ)
    (hker : IsPGroup 2 π.ker) : SevenActionInspection S := by
  obtain ⟨d, ⟨e⟩⟩ := hmodel
  let em := e.trans d.modelEquiv
  have hcenter : center S = ⊥ := by
    rcases (inferInstance : (center S).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exact (hnonab (center_eq_top_iff.mp h)).elim
  intro P hP L hLF hLc hseven
  by_contra hPne
  obtain ⟨z, hz⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hPne
  have hd : 2 ∣ Nat.card P := (hP.dvd_orderOf hz).trans (orderOf_dvd_natCard z)
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := P) 2 hd
  have hao : orderOf (a : MulAut S) = 2 := (Subgroup.orderOf_coe a).trans ha
  have hia : ∃ x : S, (a : MulAut S) = MulAut.conj x := by
    apply (MulAut.congr_inner_iff em _).mp
    exact hinner _ (((MulAut.congr em).orderOf_eq _).trans hao)
  obtain ⟨x, hx, hax, hfix⟩ :=
    MulAut.inner_involution_representative hcenter a hao hia
  have hey : orderOf (em x) = 2 := (em.orderOf_eq x).trans hx
  have hy2 : em x ^ 2 = 1 := by
    simpa only [hey] using pow_orderOf_eq_one (em x)
  have hR : zpowers (em x) ≠ ⊥ := by
    intro he
    have hone : em x = 1 := by simpa only [he, mem_bot] using mem_zpowers (em x)
    simp only [hone, orderOf_one] at hey
    omega
  have hpR : IsPGroup 2 (zpowers (em x)) :=
    (IsElementaryAbelian.zpowers_of_pow_eq_one (p := 2) hy2).isPGroup 2 _
  obtain ⟨g, s, hcover⟩ := normalizer_cover hm (zpowers (em x)) hR hpR
  have hLnormalizer (l : L) :
      em l ∈ normalizer (zpowers (em x) : Set (ReeF4.Model m)) := by
    apply centralizer_le_normalizer
    rw [zpowers_eq_closure, centralizer_closure, mem_centralizer_singleton_iff]
    have hl : (l : S) ∈ (a : MulAut S).fixedSubgroup :=
      (MulAut.mem_fixedSubgroup _ _).mpr (hLF l.property a)
    rw [hfix, mem_centralizer_singleton_iff] at hl
    simpa only [map_mul] using congrArg em hl
  let f₀ : L →* ReeF4.Model m :=
    (MulAut.conj g).toMonoidHom.comp (em.toMonoidHom.comp L.subtype)
  let f : L →* parabolic m s := f₀.codRestrict _ (fun l =>
    hcover (mem_map_of_mem _ (hLnormalizer l)))
  have hf : Function.Injective f := by
    intro l k h
    exact Subtype.ext (em.injective ((MulAut.conj g).injective (congrArg Subtype.val h)))
  let : IsQuasisimple (L.subgroupOf (FixedPoints.subgroup P S)) := hLc.2
  let : Group.IsPerfect L := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hLF).toMonoidHom) (subgroupOfEquivOfLe hLF).surjective
  cases s with
  | linear => exact ree_linear_no_seven hm L f hf hseven
  | suzuki => exact ree_suzuki_no_seven_of_projection hm π hker L f hf hseven

/-- The existing two-power automorphism and Suzuki-parabolic tasks provide
exactly these remaining inputs. Odd field period proves involution innerness;
this conditional theorem does not assert that coverage or the projection exists. -/
theorem ree_of_twoPower_form_and_suzuki_projection
    {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    (hnonab : ¬ IsMulCommutative S) {m : ℕ} (hm : 1 ≤ m)
    (hmodel : Chapter1.Section02.LocalModels.IsReeF4At S m)
    (hform : ∀ (a : MulAut (ReeF4.Model m)) (n : ℕ), a ^ (2 ^ n) = 1 →
      ∃ (g : ReeF4.Model m) (k : ℕ),
        a = MulAut.conj g * ReeF4.Parabolics.OuterLocal.fieldAutomorphism m ^ k)
    (π : parabolic m .suzuki →*
      BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m × (ReeF4.CoefficientField m)ˣ)
    (hker : IsPGroup 2 π.ker) : SevenActionInspection S := by
  apply ree_of_involution_inner_and_suzuki_projection hnonab hm hmodel ?_ π hker
  intro a ha
  have hpow : a ^ (2 ^ 1) = 1 := by simpa only [pow_one, ← ha] using pow_orderOf_eq_one a
  obtain ⟨g, k, hgk⟩ := hform a 1 hpow
  obtain ⟨x, hx⟩ := ReeF4.Parabolics.OuterLocal.inner_of_twoPower_of_inner_field
    m a g k 1 hgk hpow
  exact ⟨x, hx.symm⟩

/-- The Ree branch of the Theorem C inspection in E.6.18: a two-subgroup of
automorphisms whose common fixed subgroup has an A₇ or perfect central
three-cover component is trivial. The actual local-block model witness is
retained, and every automorphism and parabolic premise is discharged. -/
theorem ree
    {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    (hnonab : ¬ IsMulCommutative S) {m : ℕ} (hm : 1 ≤ m)
    (hmodel : Chapter1.Section02.LocalModels.IsReeF4At S m) :
    SevenActionInspection S :=
  ree_of_twoPower_form_and_suzuki_projection hnonab hm hmodel
    (ReeF4.Parabolics.OuterLocal.LargeAutomorphisms.inner_field_of_twoPower hm)
    (suzukiProjection hm) (suzukiProjection_ker_isPGroup hm)

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.BinaryLie
