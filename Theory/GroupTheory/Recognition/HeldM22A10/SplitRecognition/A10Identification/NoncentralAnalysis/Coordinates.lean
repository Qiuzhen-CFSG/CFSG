module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.SourceChecks
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.ModelInvolutions

/-!
# Concrete coordinates for Held's A10 local group

The eight named elements are permutations in the actual centralizer of
(01)(23)(45)(67) in A10. They satisfy every displayed Section 1 relation and
generate the whole centralizer. The element `mu` is exactly the double
transposition used by `LocalData.a10NoncentralInvolution`.

Generation follows from 384 distinct normal forms: sixteen products of the
four generators of the pair-flip subgroup, followed by twenty-four pair permutations. Reading the action
on pairs recovers the latter factor, and reading individual letters recovers
the former. The known centralizer order makes these forms exhaustive. Counting
commuting normal forms gives the eight local centralizer orders in the source.
All finite calculations are checked by kernel reduction; A10 is not enumerated.

Transport proves generation of the entire ambient H and the order 64 of
H ∩ C_G(mu). This does not compute the order of C_G(mu) or control fusion in G.

Source: D. Held, "A Characterization of some multiply transitive permutation
groups, I", Illinois J. Math. 13 (1969), 224--240,
DOI 10.1215/ijm/1256053756, Section 1, pp.224--225. Coordinates follow the
checked probe in Scratch/HeldA10Identification/LocalCoordinates.lean of the
supplying identification workspace. The source convention x^g is g⁻¹*x*g.
-/

open Subgroup Equiv
namespace Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.Coordinates
public abbrev H := CentralizerModels.a10Centralizer
public abbrev pi : H := modelCentralInvolution
public abbrev mu : H := modelNoncentralInvolution

@[expose] public def mup : H := ⟨⟨swap 0 1 * swap 4 5, by rw [Perm.mem_alternatingGroup]; decide +kernel⟩,
  by apply mem_centralizer_singleton_iff.mpr; decide +kernel⟩
@[expose] public def tau : H := ⟨⟨swap 0 2 * swap 1 3 * swap 4 6 * swap 5 7,
  by rw [Perm.mem_alternatingGroup]; decide +kernel⟩,
  by apply mem_centralizer_singleton_iff.mpr; decide +kernel⟩
@[expose] public def taup : H := ⟨⟨swap 0 4 * swap 1 5 * swap 2 6 * swap 3 7,
  by rw [Perm.mem_alternatingGroup]; decide +kernel⟩,
  by apply mem_centralizer_singleton_iff.mpr; decide +kernel⟩
@[expose] public def rho : H := ⟨⟨swap 0 2 * swap 0 4 * swap 1 3 * swap 1 5,
  by rw [Perm.mem_alternatingGroup]; decide +kernel⟩,
  by apply mem_centralizer_singleton_iff.mpr; decide +kernel⟩
@[expose] public def lam : H := ⟨⟨swap 0 2 * swap 1 3, by rw [Perm.mem_alternatingGroup]; decide +kernel⟩,
  by apply mem_centralizer_singleton_iff.mpr; decide +kernel⟩
@[expose] public def xi : H := ⟨⟨swap 0 1 * swap 8 9, by rw [Perm.mem_alternatingGroup]; decide +kernel⟩,
  by apply mem_centralizer_singleton_iff.mpr; decide +kernel⟩

public abbrev BaseCode := Fin 2 × Fin 2 × Fin 2 × Fin 2
public abbrev ActorCode := Fin 2 × Fin 2 × Fin 3 × Fin 2
public abbrev Code := BaseCode × ActorCode

@[expose] public def baseWord (a : BaseCode) : H :=
  pi ^ a.1.val * mu ^ a.2.1.val * mup ^ a.2.2.1.val * xi ^ a.2.2.2.val
@[expose] public def actorWord (a : ActorCode) : H :=
  tau ^ a.1.val * taup ^ a.2.1.val * rho ^ a.2.2.1.val * lam ^ a.2.2.2.val
@[expose] public def word (a : Code) : H := baseWord a.1 * actorWord a.2

-- Recover the actor from its action on the four pairs, then recover the flips.
private def actorRead (g : H) : ℕ × ℕ × ℕ :=
  ⟨(g.1.1 0).val / 2, (g.1.1 2).val / 2, (g.1.1 4).val / 2⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem actorRead_injective : Function.Injective (fun a : ActorCode => actorRead (actorWord a)) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem actorRead_baseWord : ∀ (b : BaseCode) (a : ActorCode),
    actorRead (baseWord b * actorWord a) = actorRead (actorWord a) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem baseRead_injective : Function.Injective (fun a : BaseCode =>
    ((baseWord a).1.1 0, (baseWord a).1.1 2, (baseWord a).1.1 4, (baseWord a).1.1 6)) := by
  decide +kernel

public theorem word_injective : Function.Injective word := by
  intro a b hab
  have ha : a.2 = b.2 := by
    apply actorRead_injective
    simpa only [word, actorRead_baseWord] using congrArg actorRead hab
  have hb : a.1 = b.1 := by
    have hw : baseWord a.1 = baseWord b.1 := by
      apply mul_right_cancel (b := actorWord b.2)
      simpa only [word, ha] using hab
    apply baseRead_injective
    exact congrArg (fun g : H => (g.1.1 0, g.1.1 2, g.1.1 4, g.1.1 6)) hw
  exact Prod.ext hb ha

public theorem word_bijective : Function.Bijective word := by
  apply word_injective.bijective_of_nat_card_le
  rw [centralizer_central_card]
  simp [Code, BaseCode, ActorCode]

@[expose] public def generators : Fin 8 → H := ![pi, mu, mup, tau, taup, rho, lam, xi]

public theorem word_mem {K : Subgroup H} (h : ∀ i, generators i ∈ K) (a : Code) :
    word a ∈ K := by
  unfold word baseWord actorWord
  repeat' first | apply K.mul_mem | apply K.pow_mem
  all_goals first
    | exact h 0
    | exact h 1
    | exact h 2
    | exact h 3
    | exact h 4
    | exact h 5
    | exact h 6
    | exact h 7

public theorem generators_generate : closure (Set.range generators) = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨a, rfl⟩ := word_bijective.surjective x
  apply word_mem
  intro i
  exact subset_closure ⟨i, rfl⟩

/-- All displayed defining relations in Held Section 1, in source order. -/
public theorem relations :
    pi ^ 2 = 1 ∧ mu ^ 2 = 1 ∧ mup ^ 2 = 1 ∧ tau ^ 2 = 1 ∧ taup ^ 2 = 1 ∧
    rho ^ 3 = 1 ∧ lam ^ 2 = 1 ∧ xi ^ 2 = 1 ∧
    pi * mu = mu * pi ∧ pi * mup = mup * pi ∧ mu * mup = mup * mu ∧ tau * taup = taup * tau ∧
    rho⁻¹ * tau * rho = tau * taup ∧ rho⁻¹ * taup * rho = tau ∧ tau * lam = lam * tau ∧
    lam * taup * lam = tau * taup ∧ lam * rho * lam = rho⁻¹ ∧ pi * tau = tau * pi ∧
    taup * pi = pi * taup ∧ rho * pi = pi * rho ∧ lam * pi = pi * lam ∧
    tau * mu = mu * tau ∧ taup * mu * taup = pi * mu ∧ rho⁻¹ * mu * rho = mu * mup ∧
    lam * mu = mu * lam ∧ tau * mup * tau = pi * mup ∧ taup * mup = mup * taup ∧
    rho⁻¹ * mup * rho = mu ∧ lam * mup * lam = mu * mup ∧
    pi * xi = xi * pi ∧ mu * xi = xi * mu ∧ mup * xi = xi * mup ∧
    xi * tau * xi = mu * tau ∧ xi * taup * xi = taup * mup ∧
    xi * lam * xi = mu * lam ∧ xi * rho * xi = rho * mu := by
  repeat' apply And.intro
  all_goals decide +kernel

private theorem centralizer_card_eq_count (x : H) :
    Nat.card (centralizer ({x} : Set H)) =
      Fintype.card {a : Code // word a * x = x * word a} := by
  rw [← Nat.card_eq_fintype_card]
  apply Nat.card_congr
  apply Equiv.symm
  apply Equiv.subtypeEquiv (Equiv.ofBijective word word_bijective)
  intro a
  exact mem_centralizer_singleton_iff.symm

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
/-- The eight local centralizer orders listed on Held p.225. -/
public theorem involution_centralizer_cards :
    Nat.card (centralizer ({pi} : Set H)) = 384 ∧
    Nat.card (centralizer ({mu} : Set H)) = 64 ∧
    Nat.card (centralizer ({tau} : Set H)) = 32 ∧
    Nat.card (centralizer ({lam} : Set H)) = 32 ∧
    Nat.card (centralizer ({pi * lam} : Set H)) = 32 ∧
    Nat.card (centralizer ({xi} : Set H)) = 96 ∧
    Nat.card (centralizer ({pi * xi} : Set H)) = 96 ∧
    Nat.card (centralizer ({tau * lam * xi} : Set H)) = 16 := by
  refine ⟨?_, ?_⟩
  · have hc : centralizer ({pi} : Set H) = ⊤ := by
      apply top_unique
      intro x _
      exact mem_centralizer_singleton_iff.mpr
        (mem_center_iff.mp modelCentralInvolution_mem_center x)
    rw [hc, card_top]
    exact centralizer_central_card
  · repeat' apply And.intro
    all_goals rw [centralizer_card_eq_count]; decide +kernel

public theorem centralizer_mu_card : Nat.card (centralizer ({mu} : Set H)) = 64 :=
  involution_centralizer_cards.2.1

universe u
variable {G : Type u} [Group G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)

public theorem ambient_generators_generate :
    closure (Set.range (fun i => D.a10ModelEmbedding e (generators i))) = D.centralizer := by
  rw [Set.range_comp', ← MonoidHom.map_closure, generators_generate,
    ← MonoidHom.range_eq_map]
  exact D.a10ModelEmbedding_range e

public theorem ambient_centralizer_mu_map :
    (centralizer ({mu} : Set H)).map (D.a10ModelEmbedding e) =
      D.centralizer ⊓ centralizer ({D.a10NoncentralInvolution e} : Set G) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨(e.symm y).property, mem_centralizer_singleton_iff.mpr ?_⟩
    change D.a10ModelEmbedding e y * D.a10ModelEmbedding e mu =
      D.a10ModelEmbedding e mu * D.a10ModelEmbedding e y
    simpa only [map_mul] using
      congrArg (D.a10ModelEmbedding e) (mem_centralizer_singleton_iff.mp hy)
  · rintro ⟨hx, hmu⟩
    have hxrange : x ∈ (D.a10ModelEmbedding e).range := by
      rw [D.a10ModelEmbedding_range e]
      exact hx
    obtain ⟨y, rfl⟩ := hxrange
    refine ⟨y, mem_centralizer_singleton_iff.mpr ?_, rfl⟩
    apply D.a10ModelEmbedding_injective e
    simpa only [map_mul, LocalData.a10NoncentralInvolution, mu] using
      mem_centralizer_singleton_iff.mp hmu

public theorem ambient_intersection_card :
    Nat.card ↥(D.centralizer ⊓ centralizer ({D.a10NoncentralInvolution e} : Set G)) = 64 := by
  rw [← ambient_centralizer_mu_map, card_map_of_injective (D.a10ModelEmbedding_injective e)]
  exact centralizer_mu_card

end Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.Coordinates
