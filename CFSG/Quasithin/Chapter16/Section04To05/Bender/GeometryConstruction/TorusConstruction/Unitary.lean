module

public import CFSG.Quasithin.Chapter16.Section04To05.Bender.GeometryConstruction.TorusConstruction.Component
public import CFSG.Quasithin.Chapter16.Section01To02.Local
public import CFSG.Quasithin.Chapter16.Section04To05.Bender.GeometryConstruction.TorusConstruction.Unitary.Normalizer

/-!
# The center-free PSU₃ component torus

An actual Hermitian basis change identifies the model with the standard form
without changing the stored quadratic Frobenius. Sylow conjugacy then places
its root subgroup on the prescribed component Sylow T ∩ L. The fixed-field
diagonal torus transports to an actor of order 2ⁿ − 1 in L. The central root
calculation gives the elementary omega layer, its fixed subgroup and its full
displacement; the isotropic-point action gives normalizer coverage.

The parameter 2ⁿ is the fixed-field order, with matrices over (2ⁿ)² elements.
The center-free condition is the explicit branch assumption; its ambient
discharge belongs to the parent theorem.

Source: Aschbacher–Smith, Proposition 16.5.1, printed p.1194, first and third
paragraphs, combined manuscript of 1 March 2004.
-/

public section
open Subgroup BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.Chapter16.Intersections.Bender.GeometryConstruction.TorusConstruction
namespace Unitary

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

private theorem omega_map_injective {H K : Type*} [Group H] [Group K]
    (P : Subgroup H) (f : H →* K) (hf : Function.Injective f) :
    omegaOneAmbient (P.map f) = (omegaOneAmbient P).map f := by
  apply le_antisymm
  · apply (omegaOneAmbient_le_iff _ _).mpr
    rintro _ ⟨u, hu, rfl⟩ hp
    have hpu : u ^ 2 = 1 := hf (by simpa only [map_pow, map_one] using hp)
    exact ⟨u, (omegaOneAmbient_le_iff _ _).mp le_rfl u hu hpu, rfl⟩
  · apply map_le_iff_le_comap.mpr
    apply (omegaOneAmbient_le_iff _ _).mpr
    intro u hu hp
    apply (omegaOneAmbient_le_iff (P.map f) (omegaOneAmbient (P.map f))).mp
      le_rfl (f u) ⟨u, hu, rfl⟩
    rw [← map_pow, hp, map_one]

private theorem aligned_equiv {H K : Type*} [Group H] [Group K] [Finite H] [Finite K]
    (e : H ≃* K) (P : Sylow 2 H) (S : Sylow 2 K) :
    ∃ f : H ≃* K, (P : Subgroup H).map f.toMonoidHom = (S : Subgroup K) := by
  let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K Q S
  refine ⟨e.trans (MulAut.conj g), ?_⟩
  change (P : Subgroup H).map ((MulAut.conj g).toMonoidHom.comp e.toMonoidHom) = _
  rw [← map_map]
  exact congrArg Sylow.toSubgroup hg

end Unitary

open BenderSuzuki.MatrixGroups.HermitianForm
open BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport

/-- The center-free PSU₃ branch of the intrinsic component torus calculation.
Every action clause is proved for the explicit matrices and transported through
an equivalence aligned with the component's actual Sylow subgroup. -/
theorem exists_componentTorus_psu3 {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {z : G} {L : Subgroup G} {n : ℕ}
    (hlocal : CentralComponentSetup T z L) (hZ : center L = ⊥)
    (hn : 2 ≤ n) (hmodel : ClassicalGroup.IsPSU (L ⧸ center L) 3 (2^n)) :
    ∃ d : ComponentTorus T L n, OmegaNormalizerAction T L d.actor := by
  classical
  obtain ⟨E, _, _, J, hE, hconj, ⟨e₀⟩⟩ := hmodel
  let : Fintype E := Fintype.ofFinite E
  let : Finite (Matrix.ProjGenLinGroup (Fin 3) E) := Quotient.finite _
  let : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := n * 2) (by
    simpa only [Nat.card_eq_fintype_card, pow_mul] using hE)
  have hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n :=
    FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n (by omega) hE hconj
  obtain ⟨eJ⟩ := exists_projectiveEquiv J (2 ^ n) hE hfixed
  let J₀ := standardForm J
  have hJ₀ : J₀.form = !![0,0,1;0,1,0;1,0,0] := rfl
  let eL : L ≃* ProjectiveSpecialUnitaryMatrixGroup J₀ :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans
      (e₀.trans eJ)
  let P := EvenTwoRank.rootSylow J₀ hJ₀ (show 0 < n by omega) hE hfixed
  obtain ⟨S, hS⟩ := hlocal.exists_component_sylow
  obtain ⟨e, he⟩ := Unitary.aligned_equiv eL.symm P S
  change (BorelTorus.projectiveRoot J₀ hJ₀).map e.toMonoidHom = (S : Subgroup L) at he
  let f : ProjectiveSpecialUnitaryMatrixGroup J₀ →* G := L.subtype.comp e.toMonoidHom
  have hf : Function.Injective f := L.subtype_injective.comp e.injective
  have hroot : (BorelTorus.projectiveRoot J₀ hJ₀).map f = componentSylow T L := by
    rw [show f = L.subtype.comp e.toMonoidHom from rfl, ← map_map, he, hS]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨hy, y.property⟩
    · intro hx
      exact ⟨⟨x, hx.2⟩, hx.1, rfl⟩
  let U := Unitary.centralImage J₀ hJ₀
  let X := Unitary.splitImage J₀ hJ₀
  have hlarge : 2 < Nat.card (Unitary.fixedField J₀) := by
    change 2 < Nat.card {x : E // J.conj x = x}
    rw [hfixed]
    have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) hn
    omega
  have homega : omegaOneAmbient (componentSylow T L) = U.map f := by
    rw [← hroot, Unitary.omega_map_injective _ f hf, Unitary.omega_root]
  have hcomm : ⁅omegaOneAmbient (componentSylow T L), X.map f⁆ = U.map f := by
    rw [homega, ← map_commutator, Unitary.split_commutator J₀ hJ₀ hlarge]
  let d : ComponentTorus T L n := {
    actor := X.map f
    actor_le := le_inf (by
      rintro _ ⟨a, _, rfl⟩
      exact (e a).property) (by
      rw [← hroot]
      exact (map_mono (Unitary.split_normalizes_root J₀ hJ₀)).trans (le_normalizer_map f))
    actor_cyclic := by
      let := Unitary.splitImage_cyclic J₀ hJ₀
      exact isCyclic_of_surjective (f.subgroupMap X) (f.subgroupMap_surjective X)
    actor_card := by
      rw [card_map_of_injective hf]
      exact Unitary.splitImage_card J₀ hJ₀ hfixed
    elementary := by
      rw [homega]
      let := Unitary.centralImage_elementary J₀ hJ₀
      exact IsElementaryAbelian.map f
    fixed_le := by
      rw [homega, Unitary.fixed_map U X f hf (Unitary.split_fixed_eq_bot J₀ hJ₀ hlarge)]
      exact bot_le
    moved_card := by
      rw [hcomm, card_map_of_injective hf]
      exact Unitary.centralImage_card J₀ hJ₀ hfixed
    regular := by
      rw [hcomm]
      exact Unitary.regular_map U X f hf (fun _ hv hv1 _ hw hw1 =>
        Unitary.split_regular J₀ hJ₀ hv hv1 hw hw1)
  }
  refine ⟨d, ?_⟩
  intro l hl hln
  let a := e.symm ⟨l, hl⟩
  have hal : f a = l := congrArg Subtype.val (e.apply_symm_apply ⟨l, hl⟩)
  have ha : a ∈ normalizer (U : Set (ProjectiveSpecialUnitaryMatrixGroup J₀)) := by
    apply mem_normalizer_iff.mpr
    intro u
    have hh := mem_normalizer_iff.mp hln (f u)
    rw [homega, ← hal, ← map_inv, ← map_mul, ← map_mul] at hh
    simpa only [mem_map_iff_mem hf] using hh
  obtain ⟨x, hx⟩ := Unitary.normalizer_coverage J₀ hJ₀ hE hfixed ha
  refine ⟨⟨f x, ⟨x, x.property, rfl⟩⟩, ?_⟩
  rw [homega]
  rintro _ ⟨u, hu, rfl⟩
  have hh := congrArg f (hx u hu)
  simpa only [MulAut.conj_apply, map_mul, map_inv, hal] using hh

end CFSG.Quasithin.Chapter16.Intersections.Bender.GeometryConstruction.TorusConstruction
