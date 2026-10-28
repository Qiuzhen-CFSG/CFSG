module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block.SourceTL
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block.Sections
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.NaturalSum

/-!
# Removing the central supplement in the original SL₃ block

The natural sum of 11.5.5(3) has no fixed vectors. The image of C_U(L)
is fixed by K=L₁, so this centralizer lies in V₁. The original natural
SL₃ action then kills it. The preceding central splittings yield U≤L,
O₂(L)=V and the source T_L splitting, before any order comparison.

The representation here is on the literal image in G₁/V₁, with the
original solvable residual as actor. The seed equality is supplied by
the three-dimensional flag in Flag.lean.
Source: Aschbacher--Smith, 11.5.7, printed p.782.
-/

@[expose] public noncomputable section
open Subgroup Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterG.Section02.LinearThree
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block.Multiplicity
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V} (E : Geometry D)

abbrev Space (f : E.ClosureFlag) :=
  f.Space E.G₁ le_rfl (sup_le E.L₁_le_G₁ f.sylow_normalizes_point)

abbrev action (f : E.ClosureFlag) (hK : E.K = E.L₁) :=
  f.quotientAction E.G₁ le_rfl (sup_le E.L₁_le_G₁ f.sylow_normalizes_point) hK

theorem fixed_eq_zero (f : E.ClosureFlag) (hK : E.K = E.L₁) {r : ℕ}
    (e : ActionEquiv (action E f hK) (repeated (linearNatural E.input.field 2) r))
    (v : Space E f) (hv : ∀ k, action E f hK k v = v) : v = 0 := by
  apply e.linearEquiv.injective
  rw [map_zero]
  funext i
  apply (show Representation.OneCohomology.fixed
    (specialLinearNatural (k := E.input.field.Carrier) 2) = ⊥ from
      Representation.OneCohomology.SLHigherNatural.fixed_eq_bot (by decide)).le
  intro g
  have h := e.intertwines (e.groupEquiv.symm g) v
  rw [hv, e.groupEquiv.apply_symm_apply] at h
  exact (congrFun h i).symm

theorem closure_fixed_eq_bot (f : E.ClosureFlag) (hK : E.K = E.L₁)
    (hseed : E.V₃ = V) {x y : G}
    (d : Hypothesis (setup E) E.input.field.Carrier E.input.field.degree x y)
    (hsum : ∃ r : ℕ, Nonempty (ActionEquiv (action E f hK)
      (repeated (linearNatural E.input.field 2) r))) :
    E.W ⊓ centralizer (L : Set G) = ⊥ := by
  obtain ⟨r, ⟨e⟩⟩ := hsum
  apply bot_unique
  intro u hu
  have huA : u ∈ E.localClosure E.G₁ := by
    change u ∈ conjugateSpanBy E.V₃ E.G₁
    rw [hseed]
    exact hu.1
  let a : E.localClosure E.G₁ := ⟨u, huA⟩
  let hA := Geometry.ClosureFlag.closure_le E.G₁
    (sup_le E.L₁_le_G₁ f.sylow_normalizes_point)
  let v : Space E f := Additive.ofMul (E.tildeProjection _ hA a)
  have hv : ∀ k, action E f hK k v = v := by
    intro k
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 E.K) k
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [Geometry.ClosureFlag.quotientAction_apply]
    let ki : E.G₁ := ⟨k, E.K_le_G₁ k.property⟩
    let ui : E.G₁ := ⟨u, hA huA⟩
    let q := QuotientGroup.mk' (E.V₁.subgroupOf E.G₁)
    change q ki * q ui * (q ki)⁻¹ = q ui
    have hc : ki * ui = ui * ki := by
      apply Subtype.ext
      exact hu.2 k (E.L₁_le (hK ▸ k.property))
    rw [← map_inv, ← map_mul, ← map_mul, hc, mul_inv_cancel_right]
  have hz : E.tildeProjection _ hA a = 1 :=
    congrArg Additive.toMul (fixed_eq_zero E f hK e v hv)
  have hp : u ∈ E.V₁ := by
    have hk : a ∈ (E.tildeProjection _ hA).ker := hz
    rwa [E.tildeProjection_kernel] at hk
  exact (chosen_fixed_eq_bot E d).le ⟨E.V₁_le hp, hu.2⟩

theorem original_core_and_split (f : E.ClosureFlag) (hK : E.K = E.L₁)
    (hseed : E.V₃ = V) {x y : G}
    (d : Hypothesis (setup E) E.input.field.Carrier E.input.field.degree x y)
    (hUT : E.W ≤ (T : Subgroup G))
    (hf : (frattini E.W).map E.W.subtype ≤ E.V₁)
    (hc : threeCore E x y = triple E x y)
    (hsum : ∃ r : ℕ, Nonempty (ActionEquiv (action E f hK)
      (repeated (linearNatural E.input.field 2) r))) :
    E.W ≤ L ∧ L.pCoreIn 2 = V ∧
      LocalGeometry.sourceTL T L = ((T : Subgroup G) ⊓ L) ⊔
        ((T : Subgroup G) ⊓ centralizer (L : Set G)) := by
  have hz := closure_fixed_eq_bot E f hK hseed d hsum
  have hUL : E.W ≤ L := by
    have hs := closure_split E d hUT hf hc
    rw [hz, sup_bot_eq] at hs
    exact hs.le.trans inf_le_right
  have hQW : L.pCoreIn 2 ≤ E.W :=
    (componentCore_le_threeCore E d hUT hf).trans
      (hc.le.trans (triple_le_closure E x y))
  have hQ : L.pCoreIn 2 = V := by
    have hC : L.pCoreIn 2 ⊓ centralizer (L : Set G) = ⊥ :=
      bot_unique ((inf_le_inf_right _ hQW).trans hz.le)
    simpa only [hC, sup_bot_eq] using componentCore_split E d hUT hf hc
  exact ⟨hUL, hQ, sourceTL_split E d hQ⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block.Multiplicity
