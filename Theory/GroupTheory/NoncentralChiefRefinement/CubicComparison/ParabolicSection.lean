module
public import Theory.GroupTheory.NoncentralChiefRefinement.CubicComparison.Displacement
public import Theory.GroupTheory.NoncentralChiefRefinement.CubicComparison.SmallQuotients
public import Theory.GroupTheory.PCoreImage
public import Theory.Representation.ElementaryPerfectSplit
public import Theory.Representation.FrattiniAction

/-!
# Cubic movement above a full parabolic kernel

A cubic in a parabolic whose quotient has self-centralizing two-core must
move the larger two-group above the full quotient kernel. Equality of
cubic lengths would centralize that quotient core, putting a surviving
cubic in a two-group. The companion identity translates binary fixed
codimension into the same literal conjugation cubic length.

The actual alternating amalgam application supplies the parabolic, its
full two-group kernel and the larger core. Source: Aschbacher–Smith
13.4.7(4), printed p.903.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
open NoncentralChiefRefinement.CubicComparison

namespace NoncentralChiefRefinement.CubicComparison
variable {G F : Type*} [Group G] [Finite G] [Group F] [Finite F]

/-- A surviving cubic moves the larger core above the full parabolic kernel. -/
theorem section_pos_of_selfCentralizing_core_image
    (E R N J : Subgroup G) (hE : Nat.card E = 3)
    (hR : IsPGroup 2 R) (hNR : N ≤ R)
    (hER : E ≤ normalizer (R : Set G)) (hEN : E ≤ normalizer (N : Set G))
    [(N.subgroupOf R).Normal]
    (hEJ : E ≤ J) (hJR : J.pCoreIn 2 ≤ R)
    (f : J →* F) (hf : Function.Surjective f)
    (hk : f.ker = N.subgroupOf J)
    (hself : centralizer (pCore 2 F : Set F) ≤ pCore 2 F) :
    1 ≤ sectionCubicLength E N R := by
  have hker : IsPGroup 2 f.ker := hk ▸ (hR.to_le hNR).comap_subtype
  by_contra hn
  have hz : conjugationCubicLength E N = conjugationCubicLength E R := by
    have hm := conjugationCubicLength_mono E hNR
    unfold sectionCubicLength at hn
    omega
  have hc := commutator_le_of_length_eq E R N
    (IsPGroup.of_card (n := 1) (by simpa using hE)) hR hNR hER hEN hz
  have hd : ⁅pCore 2 J,E.subgroupOf J⁆ ≤ f.ker := by
    rw [hk]
    apply map_le_iff_le_comap.mp
    rw [map_commutator,map_subgroupOf_eq_of_le hEJ]
    exact (commutator_mono hJR le_rfl).trans hc
  have hmap : (pCore 2 J).map f = pCore 2 F := by
    rw [←f.comap_pCore_of_ker_isPGroup hf hker,map_comap_eq_self]
    rw [MonoidHom.range_eq_top_of_surjective _ hf]
    exact le_top
  have hm := map_mono (f := f) hd
  have hmk : f.ker.map f = ⊥ := (map_eq_bot_iff f.ker).mpr le_rfl
  rw [map_commutator,hmap,hmk] at hm
  have hle : (E.subgroupOf J).map f ≤ pCore 2 F :=
    (le_centralizer_iff.mp
      (commutator_eq_bot_iff_le_centralizer.mp (le_bot_iff.mp hm))).trans hself
  have he : Nat.card (E.subgroupOf J) = 3 :=
    (Nat.card_congr (subgroupOfEquivOfLe hEJ).toEquiv).trans hE
  obtain ⟨n,hn⟩ := (pCore_isPGroup.to_le hle).exists_card_eq
  rw [GLS3.Chapter5.cubic_image_card_of_two_kernel f hker _ he] at hn
  have hdvd : 3 ∣ 2 ^ n := by rw [←hn]
  exact (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hdvd)
end NoncentralChiefRefinement.CubicComparison

namespace Representation
open BinaryOffender
variable {G : Type*} [Group G] [Finite G]
/-- Binary displacement computes the literal conjugation cubic length. -/
theorem conjugation_length_eq_log_fixedCodim
    (C U : Subgroup G) [IsElementaryAbelian 2 U]
    (hCU : C ≤ normalizer (U : Set G)) (E : Subgroup G) (hEC : E ≤ C) :
    let ρ := elementaryRepresentation (p := 2)
      (U.normalizerMonoidHom.comp (inclusion hCU))
    conjugationCubicLength E U = Nat.log 4 (2 ^ fixedCodim ρ (E.subgroupOf C)) := by
  let ρ := elementaryRepresentation (p := 2)
    (U.normalizerMonoidHom.comp (inclusion hCU))
  let := conjMulDistribMulActionOfLeNormalizer E U (hEC.trans hCU)
  let e : E ≃* E.subgroupOf C := (subgroupOfEquivOfLe hEC).symm
  have hh := BinaryFixedPoints.cubicLength_eq_of_equivariant
    (ρ.comp (E.subgroupOf C).subtype) e.toMonoidHom e.surjective
    (MulEquiv.refl U) (fun _ _ => rfl)
  rw [FrattiniAction.fixedIndex_eq_two_pow_fixedCodim] at hh
  exact (conjugationCubicLength_eq E U (hEC.trans hCU)).trans hh
end Representation
