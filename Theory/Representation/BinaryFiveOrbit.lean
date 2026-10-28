module
public import Theory.LinearAlgebra.BinaryPentagonQuadratic
public import Mathlib.GroupTheory.Complement
public import Mathlib.GroupTheory.Sylow
public import Mathlib.RepresentationTheory.Basic

/-!
# Binary quadratic forms on a five-element orbit

A Sylow two-subgroup of index five is complemented by an element of
order five. A vector fixed by the Sylow subgroup therefore has a
five-element spanning orbit. Its orbit map transports the cyclic
pentagon quadratic calculation to the original representation: an
invariant quadratic form vanishing on the seed and on a subspace of
codimension at most two is zero.

Source application: Aschbacher–Smith 14.2.20(1), printed p.987.
-/

public section
open Subgroup
namespace BinaryPentagon
variable {H W : Type*} [Group H] [Finite H] [AddCommGroup W] [Module (ZMod 2) W]
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

theorem exists_five_complement (S : Sylow 2 H) (hi : S.index = 5) :
    ∃ a : H, orderOf a = 5 ∧ (zpowers a).IsComplement' (S : Subgroup H) := by
  classical
  have hd : 5 ∣ Nat.card H := hi ▸ (S : Subgroup H).index_dvd_card
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' (G := H) 5 hd
  refine ⟨a,ha,isComplement'_of_card_mul_and_disjoint ?_ ?_⟩
  · rw [Nat.card_zpowers,ha]
    exact hi ▸ (S : Subgroup H).index_mul_card
  · apply disjoint_of_coprime_natCard
    rw [Nat.card_zpowers,ha]
    obtain ⟨k,hk⟩ := S.isPGroup'.exists_card_eq
    rw [hk]
    exact (by decide : Nat.Coprime 5 2).pow_right k

theorem exists_five_orbit_map
    (ρ : Representation (ZMod 2) H W) (S : Subgroup H)
    (a : H) (ha : orderOf a = 5) (hcomp : (zpowers a).IsComplement' S)
    (w : W) (hw : ∀ s : S, ρ s w = w)
    (hspan : Submodule.span (ZMod 2) (Set.range (fun h : H => ρ h w)) = ⊤) :
    ∃ f : Space →ₗ[ZMod 2] W, Function.Surjective f ∧
      (∀ i : Fin 5, f (vertex i) = ρ (a ^ i.val) w) ∧
      (∀ v, f (rotate v) = ρ a (f v)) := by
  classical
  let orbit (i : Fin 5) := ρ (a ^ i.val) w
  let f : Space →ₗ[ZMod 2] W := (Pi.basisFun (ZMod 2) (Fin 5)).constr (ZMod 2) orbit
  have hfvertex (i : Fin 5) : f (vertex i) = orbit i := by
    simpa only [f,vertex,Pi.basisFun_apply] using
      (Pi.basisFun (ZMod 2) (Fin 5)).constr_basis (ZMod 2) orbit i
  have horbit : Set.range (fun h : H => ρ h w) = Set.range orbit := by
    ext x
    constructor
    · rintro ⟨h,rfl⟩
      obtain ⟨⟨r,s⟩,hrs⟩ := hcomp.2 h
      obtain ⟨i,hi,hei⟩ := Finset.mem_image.mp (mem_zpowers_iff_mem_range_orderOf.mp r.property)
      let j : Fin 5 := ⟨i,by simpa [ha] using Finset.mem_range.mp hi⟩
      refine ⟨j,?_⟩
      rw [←hrs]
      change ρ (a ^ i) w = ρ ((r : H) * (s : H)) w
      rw [ρ.map_mul,Module.End.mul_apply,hw s]
      exact congrArg (fun g => ρ g w) hei
    · rintro ⟨i,rfl⟩
      exact ⟨a ^ i.val,rfl⟩
  have hf : Function.Surjective f := by
    apply LinearMap.range_eq_top.mp
    dsimp only [f]
    rw [(Pi.basisFun (ZMod 2) (Fin 5)).constr_range]
    rw [←horbit,hspan]
  refine ⟨f,hf,hfvertex,?_⟩
  have hnext (i : Fin 5) : orbit (i + 1) = ρ a (orbit i) := by
    fin_cases i
    all_goals simp only [orbit,Fin.reduceAdd,Fin.val_zero,Fin.val_one,
      Fin.reduceFinMk]
    all_goals rw [←Module.End.mul_apply,←ρ.map_mul,←pow_succ']
    all_goals first | rfl |
      change ρ (a ^ 0) w = ρ (a ^ 5) w
      have hp : a ^ 5 = 1 := ha ▸ pow_orderOf_eq_one a
      simp only [pow_zero,hp]
  intro v
  have hv : v = ∑ i : Fin 5, v i • vertex i := by
    exact pi_eq_sum_univ' v
  rw [hv]
  have hrotate_sum : rotate (∑ i : Fin 5, v i • vertex i) =
      ∑ i : Fin 5, v i • vertex (i + 1) := by
    ext j
    fin_cases j <;> simp [rotate,vertex,Fin.sum_univ_succ]
  rw [hrotate_sum]
  simp only [map_sum,map_smul,hfvertex,hnext]

theorem eq_zero_of_index_five_orbit [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) H W) (S : Sylow 2 H) (hi : S.index = 5)
    (w : W) (hw : ∀ s : S, ρ s w = w)
    (hspan : Submodule.span (ZMod 2) (Set.range (fun h : H => ρ h w)) = ⊤)
    (Q : QuadraticForm (ZMod 2) W) (hQ : Q w = 0)
    (hinv : ∀ (g : H) x, Q (ρ g x) = Q x)
    (E : Submodule (ZMod 2) W) (hE : ∀ x ∈ E, Q x = 0)
    (hcodim : Module.finrank (ZMod 2) (W ⧸ E) ≤ 2) : Q = 0 := by
  obtain ⟨a,ha,hcomp⟩ := exists_five_complement S hi
  obtain ⟨f,hf,hv,hr⟩ := exists_five_orbit_map ρ S a ha hcomp w hw hspan
  apply eq_zero_of_spanning_invariant_pentagon Q f hf
    (fun i => by rw [hv i,hinv,hQ]) (fun v => by rw [hr v,hinv]) E hE hcodim

end BinaryPentagon
