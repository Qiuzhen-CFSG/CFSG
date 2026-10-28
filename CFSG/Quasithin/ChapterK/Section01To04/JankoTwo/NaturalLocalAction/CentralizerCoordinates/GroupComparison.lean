module

public import CFSG.Quasithin.ChapterK.Section01To04.JankoTwo.NaturalLocalAction.Restriction
public import Theory.AtlasPort.LinearGroups.G2.ShortRootProducts.CentralizerCore.Coordinates

open Subgroup Atlas.G2 Atlas.G2.Explicit Atlas.SplitOctonion
open Atlas.G2.LieParabolicSetup Atlas.G2.PairStabilizer
open Atlas.G2.ShortRootProducts.CentralizerCore
open Sporadic.LeechRelated.J2.InnerInvolutionCores
open scoped MatrixGroups

/-!
# The actual A₅ block quotient of the marked centralizer

An injective E₄ × A₅ subgroup whose elements have the actual A/B/C-root and
SL₂-block factorization projects onto the SL₂ block. The projection kernel
has exponent two, so simplicity of A₅ makes its restriction injective.
Over a four-element field the group orders then give surjectivity. The E₄
factor projects into the trivial center of SL₂. Commutation with the upper
and lower transvections kills both remaining A/B coordinates, leaving C roots.

This is the group calculation used by CentralizerCoordinates for the actual
marked J₂ embedding. It does not identify a representation from group order:
the representation intertwiner is computed separately in RootSpace.
Source: Aschbacher–Smith, K.4.5, printed p.460/PDF p.471 and B.4.6(6).
The root and block formulas come from the attributed ATLAS imports above.
-/

@[expose] public noncomputable section

namespace CFSG.Quasithin.ChapterK.JankoTwo.NaturalLocalAction.CentralizerCoordinates.GroupComparison
variable {K : Type*} [Field K] [CharP K 2]

private theorem factor_mem_local (p : Multiplicative (K × K)) (r : K) (M : SL(2,K)) :
    longRootHom p * rootC r * blockHom M ∈ local₂ := by
  apply mul_mem
  · apply mul_mem
    · exact residualBlock_le_local (mem_sup_left ⟨p,rfl⟩)
    · exact unipotent_le_local₂ (shortRootGroup_le_unipotent ⟨Multiplicative.ofAdd r,rfl⟩)
  · exact block_mem_local₂ M

variable (f : E4 × A5 →* Model K)
variable (hf : ∀ x, ∃ (p : Multiplicative (K × K)) (r : K) (M : SL(2,K)),
  f x = longRootHom p * rootC r * blockHom M)

private def localHom : E4 × A5 →* local₂ (F := K) :=
  f.codRestrict local₂ (by
    intro x
    obtain ⟨p,r,M,h⟩ := hf x
    rw [h]
    exact factor_mem_local p r M)

private def projection : E4 × A5 →* SL(2,K) := longSLHom.comp (localHom f hf)

private def simpleProjection : A5 →* SL(2,K) :=
  (projection f hf).comp (MonoidHom.inr E4 A5)

private theorem projection_of_factor (x : E4 × A5) (p : Multiplicative (K × K)) (r : K)
    (M : SL(2,K)) (h : f x = longRootHom p * rootC r * blockHom M) :
    projection f hf x = M := by
  apply Subtype.ext
  change longMatrix (f x) = M.val
  rw [h]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [longMatrix, E, basisVector, longRootHom,
      rootA,rootAEquiv,rootALinear,rootAApply,
      rootB,rootBEquiv,rootBLinear,rootBApply,
      rootC,rootCEquiv,rootCLinear,rootCApply,
      blockHom,blockEquiv,blockLinear,CharTwo.neg_eq,CharTwo.sub_eq_add]

private theorem kernel_square (x : E4 × A5) (hx : projection f hf x = 1) : (f x)^2 = 1 := by
  obtain ⟨p,r,M,h⟩ := hf x
  have hM : M = 1 := (projection_of_factor f hf x p r M h).symm.trans hx
  rw [h, hM, map_one, mul_one]
  have hc : Commute (longRootHom p) (rootC r) :=
    mem_centralizer_singleton_iff.mp
      (residualBlock_le_centralizer_rootC r (mem_sup_left ⟨p,rfl⟩))
  rw [hc.mul_pow, ← map_pow]
  have hp : p^2 = 1 := by
    apply Multiplicative.toAdd.injective
    apply Prod.ext <;> simp [pow_two, CharTwo.add_self_eq_zero]
  rw [hp, map_one, one_mul, pow_two, Atlas.G2.rootC_add, CharTwo.add_self_eq_zero, rootC_zero]

private theorem simpleProjection_injective (hi : Function.Injective f) :
    Function.Injective (simpleProjection f hf) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rcases (simpleProjection f hf).normal_ker.eq_bot_or_eq_top with h | h
  · exact h
  · let e : A5 := ⟨Equiv.swap 0 1 * Equiv.swap 1 2, by simp⟩
    have hn : e^2 ≠ 1 := by decide +kernel
    have hk : simpleProjection f hf e = 1 :=
      MonoidHom.mem_ker.mp (h ▸ mem_top e)
    have hs : (f (1,e))^2 = 1 := kernel_square f hf (1,e) hk
    have he : (1,e)^2 = (1 : E4 × A5) := hi (by simpa only [map_pow, map_one] using hs)
    exact (hn (congrArg Prod.snd he)).elim

private theorem simpleProjection_bijective [Finite K] (hK : Nat.card K = 4)
    (hi : Function.Injective f) : Function.Bijective (simpleProjection f hf) := by
  apply (Nat.bijective_iff_injective_and_card _).mpr
  refine ⟨simpleProjection_injective f hf hi, ?_⟩
  rw [Atlas.card_sl_two, hK, nat_card_alternatingGroup]
  norm_num

private theorem projection_central (hs : Function.Surjective (simpleProjection f hf)) (c : E4) :
    projection f hf (c,1) = 1 := by
  have hc : projection f hf (c,1) ∈ center SL(2,K) := by
    apply mem_center_iff.mpr
    intro M
    obtain ⟨e,rfl⟩ := hs M
    change projection f hf (1,e) * projection f hf (c,1) =
      projection f hf (c,1) * projection f hf (1,e)
    rw [← map_mul, ← map_mul]
    simp
  simpa only [longSL_center_eq_bot, mem_bot] using hc

private theorem projection_snd (hs : Function.Surjective (simpleProjection f hf)) (x : E4 × A5) :
    projection f hf x = simpleProjection f hf x.2 := by
  have h : x = (x.1,1) * (1,x.2) := by simp
  rw [h, map_mul, projection_central f hf hs, one_mul]
  simp [simpleProjection]

private theorem central_parameter (p q : Multiplicative (K × K)) (r s : K) (M : SL(2,K))
    (hc : Commute (longRootHom p * rootC r)
      (longRootHom q * rootC s * blockHom M)) :
    M 0 0*p.toAdd.1+M 0 1*p.toAdd.2 = p.toAdd.1 ∧
      M 1 0*p.toAdd.1+M 1 1*p.toAdd.2 = p.toAdd.2 := by
  have h1 := congrArg (fun g : Model K => g.val (basisVector 7) 1) hc.eq
  have h2 := congrArg (fun g : Model K => g.val (basisVector 7) 2) hc.eq
  simp [longRootHom, rootA,rootAEquiv,rootALinear,rootAApply,
      rootB,rootBEquiv,rootBLinear,rootBApply, rootC,rootCEquiv,rootCLinear,rootCApply,
      blockHom,blockEquiv,blockLinear,basisVector,CharTwo.neg_eq,CharTwo.sub_eq_add] at h1 h2
  constructor
  · linear_combination -h1
  · linear_combination -h2



private theorem central_root (hs : Function.Surjective (simpleProjection f hf)) (c : E4) :
    ∃ r : K, f (c,1) = rootC r := by
  obtain ⟨p,r,M,h⟩ := hf (c,1)
  have hM : M = 1 := (projection_of_factor f hf (c,1) p r M h).symm.trans
    (projection_central f hf hs c)
  rw [hM, map_one, mul_one] at h
  have hp (N : SL(2,K)) :
      N 0 0*p.toAdd.1+N 0 1*p.toAdd.2 = p.toAdd.1 ∧
        N 1 0*p.toAdd.1+N 1 1*p.toAdd.2 = p.toAdd.2 := by
    obtain ⟨e,he⟩ := hs N
    obtain ⟨q,s,M,hm⟩ := hf (1,e)
    have hmn : M = N := (projection_of_factor f hf (1,e) q s M hm).symm.trans he
    have hc : Commute (f (c,1)) (f (1,e)) := by
      change f (c,1) * f (1,e) = f (1,e) * f (c,1)
      rw [← map_mul, ← map_mul]
      simp
    rw [h, hm, hmn] at hc
    exact central_parameter p q r s N hc
  let U : SL(2,K) := ⟨!![1,1;0,1], by simp⟩
  let L : SL(2,K) := ⟨!![1,0;1,1], by simp⟩
  have h2 : p.toAdd.2 = 0 := by simpa [U] using (hp U).1
  have h1 : p.toAdd.1 = 0 := by simpa [L] using (hp L).2
  refine ⟨r, ?_⟩
  simpa [longRootHom, h1, h2] using h

include hf in
private theorem block_factors [Finite K] (hK : Nat.card K = 4) (hi : Function.Injective f) :
    ∃ φ : A5 ≃* SL(2,K), ∀ x : E4 × A5,
      ∃ (p : Multiplicative (K × K)) (r : K),
        f x = longRootHom p * rootC r * blockHom (φ x.2) := by
  let φ := MulEquiv.ofBijective (simpleProjection f hf) (simpleProjection_bijective f hf hK hi)
  refine ⟨φ, ?_⟩
  intro x
  obtain ⟨p,r,M,h⟩ := hf x
  refine ⟨p,r,?_⟩
  have hM : M = φ x.2 := (projection_of_factor f hf x p r M h).symm.trans
    (projection_snd f hf (simpleProjection_bijective f hf hK hi).2 x)
  rwa [← hM]



include hf in
theorem comparison [Finite K] (hK : Nat.card K = 4) (hi : Function.Injective f) :
    ∃ φ : A5 ≃* SL(2,K),
      (∀ x : E4 × A5, ∃ (p : Multiplicative (K × K)) (r : K),
        f x = longRootHom p * rootC r * blockHom (φ x.2)) ∧
      (∀ c : E4, ∃ r : K, f (c,1) = rootC r) := by
  obtain ⟨φ,hφ⟩ := block_factors f hf hK hi
  exact ⟨φ,hφ,central_root f hf (simpleProjection_bijective f hf hK hi).2⟩

end CFSG.Quasithin.ChapterK.JankoTwo.NaturalLocalAction.CentralizerCoordinates.GroupComparison
