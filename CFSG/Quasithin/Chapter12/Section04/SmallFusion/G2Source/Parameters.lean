module
public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source.NormalizerAction
public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.Parameters
public import Theory.Representation.G2OrthogonalCover.BinaryOffenders
public import Theory.Representation.BinaryOffender.InvolutionRatio

/-!
# Numerical G₂ parameter bounds

The binary G₂ natural module has no involution with fixed codimension below two.
Transporting the full normalizer actor to the chosen module therefore gives
`2 ≤ localM V`; together with the hyperplane global-rank bound this yields
`1 < globalS V`, the numerical input used by the fixed-space endgame.

Source: Aschbacher--Smith 12.4.8, printed pp.815--816.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source
open Chapter12.Section02 ChapterB.QuasisimpleSource Atlas.G2.Natural ChapterE
local notation "F" => ZMod 2
local notation "E" => TraceZero F
local notation "σ" => traceZeroAction F
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}

private theorem involution_fixedCodim_ge_two (t : Atlas.G2.Model F) (ht : orderOf t = 2) :
    2 ≤ fixedCodim σ (zpowers t) := by
  obtain ⟨hA, hr, _, _⟩ := involution_actor_rank_and_fixedCodim σ t ht
  by_contra! hc
  have hoff : IsOffender σ (zpowers t) := ⟨hA, by omega⟩
  have hthree := OrthogonalCover.BinaryOffenders.offender_rank (zpowers t) hoff
  omega

theorem localM_ge_two
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : ActionEquiv D.quotientAction (OrthogonalCover.action F))
    (hne : fixedSubgroup L V ≠ ⊥) : letI := D.elementary; 2 ≤ localM V := by
  classical
  let _ := D.elementary
  obtain ⟨_, _, _, _, hMV, _, _⟩ := exists_fixed_involution_setup h D structural e hne
  obtain ⟨b, φ, hφ⟩ := exists_normalizer_full_g2_actor h D structural e hne
  let c : Additive V ≃ₗ[F] E := by
    let ca : Additive V ≃+ E := {
      toFun v := (b v.toMul).toAdd
      invFun w := Additive.ofMul (b.symm (Multiplicative.ofAdd w))
      left_inv v := congrArg Additive.ofMul (b.symm_apply_apply v.toMul)
      right_inv w := congrArg Multiplicative.toAdd (b.apply_symm_apply _)
      map_add' v w := congrArg Multiplicative.toAdd (map_mul b v.toMul w.toMul) }
    exact { ca with map_smul' := ZMod.map_smul ca }
  let ρ := automizerRepresentation V
  let τ : Representation F (Automizer V) E := c.conjRingEquiv.toMonoidHom.comp ρ
  have hτ : Function.Injective τ :=
    c.conjRingEquiv.injective.comp (automizerRepresentation_injective V)
  have hmark (a : Automizer V) : ∃ t : Atlas.G2.Model F, τ a = σ t := by
    obtain ⟨n, hn⟩ := a.property
    let m : normalizer (L : Set G) := ⟨n, hMV.symm.le n.property⟩
    refine ⟨φ m, ?_⟩
    apply LinearMap.ext
    intro x
    apply Multiplicative.ofAdd.injective
    apply b.symm.injective
    apply Subtype.ext
    rw [hφ]
    change (b.symm (b (a.val (b.symm (Multiplicative.ofAdd x)))) : G) = _
    rw [b.symm_apply_apply, ← hn]
    rfl
  have hcodim (a : Automizer V) :
      fixedCodim ρ (zpowers a) = fixedCodim τ (zpowers a) := by
    simpa only [Subgroup.map_id] using
      fixedCodim_map_equivariant ρ τ (MonoidHom.id _) c
        (fun a v => by change c (ρ a v) = c (ρ a (c.symm (c v))); rw [c.symm_apply_apply])
        (zpowers a)
  apply le_csInf ⟨_, Set.mem_insert _ _⟩
  rintro n (rfl | ⟨a, ha, rfl⟩)
  · rw [c.finrank_eq, OrthogonalCover.finrank_traceZero]
    decide
  · obtain ⟨t, ht⟩ := hmark a
    have ht1 : t ≠ 1 := by
      intro heq
      have ha1 : a = 1 := hτ (by rw [ht, heq, map_one, map_one])
      simp [ha1] at ha
    have ht2 : t ^ 2 = 1 := by
      apply traceZeroAction_injective_binary
      rw [map_pow, ← ht, ← map_pow, (orderOf_eq_prime_iff.mp ha).1, map_one, map_one]
    have htOrder : orderOf t = 2 := orderOf_eq_prime ht2 ht1
    change 2 ≤ fixedCodim ρ (zpowers a)
    rw [hcodim, fixedCodim_zpowers_eq_displacement_rank, ht,
      ← fixedCodim_zpowers_eq_displacement_rank]
    exact involution_fixedCodim_ge_two t htOrder

theorem globalS_gt_one_of_hyperplanes
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : ActionEquiv D.quotientAction (OrthogonalCover.action F))
    (hne : fixedSubgroup L V ≠ ⊥)
    (hyp : ∀ U ≤ V, subgroupCorank V U = 1 →
      centralizer (U : Set G) ≤ normalizer (V : Set G)) : letI := D.elementary;
    1 < globalS V := by
  let _ := D.elementary
  apply lt_min (SLThreeCommutatorSource.globalR_gt_one_of_hyperplanes V hyp)
  have hm := localM_ge_two h D structural e hne
  have hm' : 1 < localM V := by omega
  exact_mod_cast hm'

end CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source
