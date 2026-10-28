module

public import CFSG.Quasithin.Chapter2.Section05.PSL2PairSource.InitialAction
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.ModelExclusion

/-!
# The two actual Sylow-rank witnesses for the crossing pair

Restrict the supplied Sylow of C_G(t) to its normal K, and use the actual
PSL₂ model to produce an elementary four-group. Its ambient image lies in
T ∩ K. Right conjugation by the original x ∈ T transports that witness to
T ∩ Kˣ. This requires neither a non-dihedral assumption nor an extra rank
hypothesis.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
2.5.21, printed p.567. The intrinsic rank calculation is the existing
`StrongClosure.ModelExclusion.linear_odd_sylow_rank`.
-/

public section

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter16.CounterexampleGeometry
open BenderSuzuki.PFchapter1section1
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter2.PSL2PairSource
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}}
variable {p : ℕ} [Fact p.Prime]

private theorem rank_of_sylow_model {D : Type*} [Group D] [Finite D]
    (P : Sylow 2 D) (e : D ≃* PSL(2, ZMod p)) (hp : 7 ≤ p) :
    TwoRankAtLeastTwo P := by
  apply StrongClosure.ModelExclusion.linear_odd_sylow_rank
    (Fact.out : p.Prime) ((Fact.out : p.Prime).odd_of_ne_two (by omega)) _ P
  exact ⟨ZMod p, inferInstance, inferInstance, by simp, ⟨e⟩⟩

namespace Incoming
variable (d : Incoming κ G p)

/-- The first actual Sylow intersection contains an elementary four-group.
The witness comes from the supplied Sylow of J, restricted to its normal K. -/
theorem left_sylow_rank : TwoRankAtLeastTwo ((d.T : Subgroup G) ⊓ d.K : Subgroup G) := by
  let J := centralizer ({d.t} : Set G)
  let KJ := d.K.subgroupOf J
  let : KJ.Normal := d.normalK
  have hKJ : d.K ≤ J := by
    rw [show J = _ from d.generated]
    exact le_sup_of_le_left le_sup_left
  obtain ⟨P, hP⟩ := d.sylow.exists_subgroupOf_eq_of_normal KJ
  let e : KJ ≃* PSL(2, ZMod p) := (subgroupOfEquivOfLe hKJ).trans d.model
  have hr := rank_of_sylow_model P e d.prime_ge
  let f0 : P →* G := J.subtype.comp (KJ.subtype.comp (P : Subgroup KJ).subtype)
  have hf0 : Function.Injective f0 :=
    J.subtype_injective.comp (KJ.subtype_injective.comp (P : Subgroup KJ).subtype_injective)
  have hmem : ∀ a : P, f0 a ∈ ((d.T : Subgroup G) ⊓ d.K : Subgroup G) := by
    intro a
    have ha : ((a : KJ) : J) ∈ (d.sylow : Subgroup J) := by
      have hh : (a : KJ) ∈ (P : Subgroup KJ) := a.property
      rw [hP] at hh
      exact hh
    have haS : f0 a ∈ d.S := by
      rw [← d.sylow_eq]
      exact mem_map_of_mem J.subtype ha
    exact ⟨d.s_le_t haS, (a : KJ).property⟩
  let f := f0.codRestrict ((d.T : Subgroup G) ⊓ d.K) hmem
  exact hr.map_of_injective f (by intro a b h; exact hf0 (congrArg (fun z : ((d.T : Subgroup G) ⊓ d.K : Subgroup G) => (z : G)) h))

/-- Right conjugation by the original x ∈ T transfers the first four-group
to the second actual Sylow intersection; no extra rank hypothesis is used. -/
theorem right_sylow_rank :
    TwoRankAtLeastTwo ((d.T : Subgroup G) ⊓ conjugate d.K d.x : Subgroup G) := by
  let A := (d.T : Subgroup G) ⊓ d.K
  let B := (d.T : Subgroup G) ⊓ conjugate d.K d.x
  let f0 : A →* G := (MulAut.conj d.x⁻¹).toMonoidHom.comp A.subtype
  have hmem : ∀ a : A, f0 a ∈ B := by
    intro a
    refine ⟨?_, mem_map_of_mem _ a.property.2⟩
    change d.x⁻¹ * (a : G) * (d.x⁻¹)⁻¹ ∈ (d.T : Subgroup G)
    rw [inv_inv]
    exact (d.T : Subgroup G).mul_mem
      ((d.T : Subgroup G).mul_mem ((d.T : Subgroup G).inv_mem d.x_mem) a.property.1) d.x_mem
  let f := f0.codRestrict B hmem
  exact d.left_sylow_rank.map_of_injective f (by
    intro a b h
    apply Subtype.ext
    apply (MulAut.conj d.x⁻¹).injective
    exact congrArg Subtype.val h)

end Incoming
end CFSG.Quasithin.Chapter2.PSL2PairSource

end
