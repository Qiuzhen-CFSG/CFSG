module

public import CFSG.Quasithin.Chapter16.Section04To05.Bender.GeometryConstruction.TorusConstruction.Component
public import CFSG.Quasithin.Chapter16.Section01To02.Local
public import CFSG.Quasithin.Chapter16.Section04To05.Bender.GeometryConstruction.TorusConstruction.Linear.Model

/-!
# The center-free PSL₂ component torus

This constructs the actor required in the first and third paragraphs of
Proposition 16.5.1 for a component whose central quotient is PSL₂(2ⁿ) and
whose center is trivial. The quotient by that center gives a genuine model
isomorphism. Subnormal Sylow intersection and Sylow conjugacy align the
standard upper root group with the prescribed T ∩ L. The diagonal torus
is then mapped into L in the ambient group.

The model calculations give a cyclic actor of order 2ⁿ − 1, elementary
component omega, trivial fixed subgroup, full root displacement of order
2ⁿ, regular literal conjugation, and pointwise coverage of the component
omega normalizer. The center-free condition remains the explicit branch
hypothesis; this module does not assert its ambient discharge.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), Proposition
16.5.1, printed p.1194, first and third paragraphs.
-/

public section

open Subgroup BenderSuzuki.Converse
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter16.Intersections.Bender.GeometryConstruction.TorusConstruction
namespace Linear
open Matrix.ProjectiveSpecialLinearGroup.OddBorel
open Matrix.ProjectiveSpecialLinearGroup.EvenBorelResidual

private theorem regular_map {H K : Type*} [Group H] [Group K]
    (U X : Subgroup H) (f : H →* K) (hf : Function.Injective f)
    (hreg : ∀ v ∈ U, v ≠ 1 → ∀ w ∈ U, w ≠ 1 →
      ∃! x : X, MulAut.conj (x : H) v = w) :
    ∀ v ∈ U.map f, v ≠ 1 → ∀ w ∈ U.map f, w ≠ 1 →
      ∃! x : X.map f, MulAut.conj (x : K) v = w := by
  rintro _ ⟨v, hv, rfl⟩ hv1 _ ⟨w, hw, rfl⟩ hw1
  obtain ⟨x, hx, huniq⟩ := hreg v hv (fun h => hv1 (h ▸ f.map_one))
    w hw (fun h => hw1 (h ▸ f.map_one))
  refine ⟨⟨f x, ⟨x, x.property, rfl⟩⟩, ?_, ?_⟩
  · simpa only [MulAut.conj_apply, map_mul, map_inv] using congrArg f hx
  · rintro ⟨_, y, hy, rfl⟩ he
    apply Subtype.ext
    have hyx : (⟨y, hy⟩ : X) = x := huniq _ (hf (by
      simpa only [MulAut.conj_apply, map_mul, map_inv] using he))
    exact congrArg (fun z : X => f z) hyx

private theorem fixed_map {H K : Type*} [Group H] [Group K]
    (U X : Subgroup H) (f : H →* K) (hf : Function.Injective f)
    (hfix : U ⊓ centralizer (X : Set H) = ⊥) :
    U.map f ⊓ centralizer (X.map f : Set K) = ⊥ := by
  apply eq_bot_iff.mpr
  rintro _ ⟨⟨u, hu, rfl⟩, hc⟩
  have hu1 : u = 1 := by
    apply mem_bot.mp
    rw [← hfix]
    refine ⟨hu, mem_centralizer_iff.mpr fun x hx => ?_⟩
    apply hf
    simpa only [map_mul] using mem_centralizer_iff.mp hc (f x) ⟨x, hx, rfl⟩
  simp only [hu1, map_one, one_mem]

private theorem aligned_equiv {H F : Type*} [Group H] [Finite H]
    [Field F] [Finite F] [CharP F 2] (e : PSL(2,F) ≃* H) (S : Sylow 2 H) :
    ∃ f : PSL(2,F) ≃* H, (kernel F).map f.toMonoidHom = (S : Subgroup H) := by
  let P := (standardSylow F).mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H P S
  refine ⟨e.trans (MulAut.conj g), ?_⟩
  change (kernel F).map ((MulAut.conj g).toMonoidHom.comp e.toMonoidHom) = _
  rw [← map_map, ← coe_standardSylow]
  exact congrArg Sylow.toSubgroup hg

end Linear

open Matrix.ProjectiveSpecialLinearGroup.OddBorel
open Matrix.ProjectiveSpecialLinearGroup.EvenBorelResidual

/-- The center-free PSL₂ branch of the intrinsic torus calculation in 16.5.1.
The actor is the image of the actual diagonal torus in coordinates aligned
with the prescribed component Sylow subgroup. -/
theorem exists_componentTorus_psl2 {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {z : G} {L : Subgroup G} {n : ℕ}
    (hlocal : CentralComponentSetup T z L) (hZ : center L = ⊥)
    (hn : 2 ≤ n) (hmodel : ClassicalGroup.IsPSL (L ⧸ center L) 2 (2^n)) :
    ∃ d : ComponentTorus T L n, OmegaNormalizerAction T L d.actor := by
  classical
  obtain ⟨F, _, _, hF, ⟨e₀⟩⟩ := hmodel
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let eL : L ≃* PSL(2,F) :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans e₀
  obtain ⟨S, hS⟩ := hlocal.exists_component_sylow
  obtain ⟨e, he⟩ := Linear.aligned_equiv eL.symm S
  let f : PSL(2,F) →* G := L.subtype.comp e.toMonoidHom
  have hf : Function.Injective f := L.subtype_injective.comp e.injective
  have hroot : (kernel F).map f = componentSylow T L := by
    rw [show f = L.subtype.comp e.toMonoidHom from rfl, ← map_map, he, hS]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨hy, y.property⟩
    · intro hx
      exact ⟨⟨x, hx.2⟩, hx.1, rfl⟩
  -- The following local names keep all transported subgroups tied to f.
  let U := Matrix.ProjectiveSpecialLinearGroup.OddBorel.kernel F
  let X := Matrix.ProjectiveSpecialLinearGroup.OddBorel.complement F
  have hlarge : 2 < Nat.card F := by
    rw [hF]
    have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) hn
    omega
  have hU : IsElementaryAbelian 2 U := Linear.kernel_elementary F
  let := hU
  have hUm : IsElementaryAbelian 2 (componentSylow T L) := by
    rw [← hroot]
    exact IsElementaryAbelian.map f
  let := hUm
  have homega : omegaOneAmbient (componentSylow T L) = U.map f := by
    rw [omegaOneAmbient_eq_self, hroot]
  have hnorm : X.map f ≤ normalizer (componentSylow T L : Set G) := by
    rw [← hroot]
    exact (map_mono (Matrix.ProjectiveSpecialLinearGroup.OddBorel.complement_normalizes F)).trans
      (le_normalizer_map f)
  have hcomm : ⁅omegaOneAmbient (componentSylow T L), X.map f⁆ = U.map f := by
    rw [homega, ← map_commutator, Linear.kernel_commutator F hlarge]
  let d : ComponentTorus T L n := {
    actor := X.map f
    actor_le := le_inf (by
      rintro _ ⟨a, _, rfl⟩
      exact (e a).property) hnorm
    actor_cyclic := by
      let := Linear.complement_cyclic F
      exact isCyclic_of_surjective (f.subgroupMap X) (f.subgroupMap_surjective X)
    actor_card := by
      rw [card_map_of_injective hf, Matrix.ProjectiveSpecialLinearGroup.EvenBorelResidual.card_torus, hF]
    elementary := by rw [omegaOneAmbient_eq_self]; exact hUm
    fixed_le := by
      rw [homega, Linear.fixed_map U X f hf (Linear.kernel_fixed_eq_bot F hlarge)]
      exact bot_le
    moved_card := by
      rw [hcomm, card_map_of_injective hf, Matrix.ProjectiveSpecialLinearGroup.OddBorel.card_kernel, hF]
    regular := by
      rw [hcomm]
      exact Linear.regular_map U X f hf (fun _ hv hv1 _ hw hw1 =>
        Linear.complement_regular F hv hv1 hw hw1)
  }
  refine ⟨d, ?_⟩
  intro l hl hln
  let a : PSL(2,F) := e.symm ⟨l, hl⟩
  have hal : f a = l := congrArg Subtype.val (e.apply_symm_apply ⟨l, hl⟩)
  have ha : a ∈ normalizer (U : Set PSL(2,F)) := by
    apply mem_normalizer_iff.mpr
    intro u
    have hh := mem_normalizer_iff.mp hln (f u)
    rw [homega, ← hal, ← map_inv, ← map_mul, ← map_mul] at hh
    simpa only [mem_map_iff_mem hf] using hh
  obtain ⟨x, hx⟩ := Linear.normalizer_coverage F ha
  refine ⟨⟨f x, ⟨x, x.property, rfl⟩⟩, ?_⟩
  rw [homega]
  rintro _ ⟨u, hu, rfl⟩
  have hh := congrArg f (hx u hu)
  simpa only [MulAut.conj_apply, map_mul, map_inv, hal] using hh

end CFSG.Quasithin.Chapter16.Intersections.Bender.GeometryConstruction.TorusConstruction
