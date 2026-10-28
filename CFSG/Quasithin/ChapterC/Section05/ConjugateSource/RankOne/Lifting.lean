module

public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.Coordinates

/-!
# Passing intrinsic covering calculations to the Baumann action

For the L₂ case, choose an internal actor with the same parameter. Their
quotient centralizes the full U, so they have the same action. The kernel
of the plane projection is exactly C_U(L), and an intrinsic fixed-lifting
theorem for the block quotient therefore proves lifting for the S-action.
For A₃, a trivial block-fixed subgroup makes the projection injective.

The intrinsic assertions are proved in `Covers` and supplied by `Setup`.
No centerless L₂-cover is assumed.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.5.4(2),
printed p.155, C.5.6 (*), printed p.156, and I.2.3(1), printed p.413.
-/

public section
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
open Subgroup
universe u
variable {G : Type u} [Group G] {R L : Subgroup G}
variable {F : Type*} [Field F] (c : ActionCoordinates R L F)

private theorem same_action {s t : S R} (hst : c.parameter s = c.parameter t) (v : U L) :
    moduleConjugate c.normalizes s v = moduleConjugate c.normalizes t v := by
  have hk : c.parameter (t⁻¹ * s) = 1 := by simp [hst]
  have hc := (c.parameter_kernel (t⁻¹ * s)).mp hk
  have he := hc (v : G) v.property
  change (v : G) * ((t : G)⁻¹ * s) = ((t : G)⁻¹ * s) * v at he
  apply Subtype.ext
  change (s : G) * (v : G) * (s : G)⁻¹ = (t : G) * (v : G) * (t : G)⁻¹
  have he' := congrArg (fun z : G => (t : G) * z * (s : G)⁻¹) he
  simpa [mul_assoc] using he'.symm

/-- The intrinsic rank-one covering fact passes through the genuine central
quotient to every internal Baumann actor. -/
theorem fixedLift_of_linearCover (hcover : LinearCoverInput (G := G))
    {n : ℕ} (hL : ChapterC.IsL2EvenBlock L n) (hi : c.IsInternal) : c.FixedLift := by
  intro s u hfix
  obtain ⟨t, ht, hts⟩ := hi s
  have hsu := same_action c hts.symm u
  rw [hsu] at hfix
  have hc : ((moduleConjugate c.normalizes t u : U L) / u : U L) ∈ c.projection.ker := by
    change c.projection _ = 1
    rw [map_div, hfix, div_self']
  have hcL := (c.projection_kernel _).mp hc
  obtain ⟨v, hv, he⟩ := u.property
  change (v : G) = (u : G) at he
  let v₀ : ChapterC.blockU L := ⟨v, hv⟩
  let l : L := ⟨(t : G), ht⟩
  have hquot : QuotientGroup.mk' (ChapterC.blockFixed L) (ChapterC.blockConjugate L l v₀) =
      QuotientGroup.mk' (ChapterC.blockFixed L) v₀ := by
    apply QuotientGroup.eq_iff_div_mem.mpr
    change ((ChapterC.blockConjugate L l v₀ / v₀ : ChapterC.blockU L) : L) ∈ center L
    rw [mem_center_iff]
    intro y
    apply Subtype.ext
    have hh := hcL (y : G) y.property
    simpa only [moduleConjugate, ChapterC.blockConjugate, Subgroup.coe_div,
      Subgroup.coe_mk, Subgroup.coe_mul, Subgroup.coe_inv, l, v₀, he] using hh
  have hvfix := hcover L n hL l v₀ hquot
  rw [hsu]
  apply Subtype.ext
  have hh := congrArg (fun z : ChapterC.blockU L => ((z : L) : G)) hvfix
  simpa only [moduleConjugate, ChapterC.blockConjugate, Subgroup.coe_mk, Subgroup.coe_mul, Subgroup.coe_inv, l, v₀, he] using hh

/-- When the block's central layer is trivial, quotient fixed points lift
without any internal-actor hypothesis. This is the separate A₃ route. -/
theorem fixedLift_of_blockFixed_eq_bot (hz : ChapterC.blockFixed L = ⊥) : c.FixedLift := by
  have hp : c.projection.ker = ⊥ := by
    apply eq_bot_iff.mpr
    intro u hu
    have hc := (c.projection_kernel u).mp hu
    obtain ⟨v, hv, he⟩ := u.property
    change (v : G) = (u : G) at he
    have hvz : (⟨v, hv⟩ : ChapterC.blockU L) ∈ ChapterC.blockFixed L := by
      change v ∈ center L
      rw [mem_center_iff]
      intro y
      apply Subtype.ext
      simpa only [Subgroup.coe_mul, he] using hc (y : G) y.property
    rw [hz, mem_bot] at hvz
    apply mem_bot.mpr
    apply Subtype.ext
    have hh := congrArg (fun z : ChapterC.blockU L => ((z : L) : G)) hvz
    simpa only [Subgroup.coe_one, he] using hh
  have hinj : Function.Injective c.projection := (MonoidHom.ker_eq_bot_iff c.projection).mp hp
  intro s v hv
  exact hinj hv

end CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
end
