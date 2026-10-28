module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.Escape.Fusion.Orbits

/-!
# Pure-factor involutions are not 2-central

The survivor's point-centralizer bound transports to the exchanged factor.
If a pure nonidentity vector centralized a Sylow subgroup of G, that Sylow
would lie in M. Sylow conjugacy inside M would make a pure nonidentity
vector T-fixed, contradicting the exchange of disjoint factors. Every
specified nonidentity vector in V ∩ Z(T) is diagonal, and diagonal
transitivity then excludes fusion between pure and diagonal vectors.

Source: Aschbacher--Smith, 10.3.2, first paragraph, printed p.756,
PDF p.773 of `refs/quasithin.pdf`.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.Escape.Fusion
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  (s : SourceLinearThreeSurvivor T D)

/-- Conjugation by an element of M transports point-centralizer containment. -/
theorem centralizer_conj_le {x g : G}
    (hx : centralizer ({x} : Set G) ≤ D.maximalLocal) (hg : g ∈ D.maximalLocal) :
    centralizer ({MulAut.conj g x} : Set G) ≤ D.maximalLocal := by
  intro c hc
  have hh : MulAut.conj g⁻¹ c ∈ centralizer ({x} : Set G) := by
    apply mem_centralizer_singleton_iff.mpr
    have h := congrArg (MulAut.conj g⁻¹) (mem_centralizer_singleton_iff.mp hc)
    simpa [map_mul, MulAut.conj_apply, mul_assoc] using h
  have hm := D.maximalLocal.mul_mem
    (D.maximalLocal.mul_mem hg (hx hh)) (D.maximalLocal.inv_mem hg)
  simpa [MulAut.conj_apply,mul_assoc] using hm

/-- This is the pure-factor centralizer bound, including the exchanged factor. -/
theorem pure_centralizer_le {x : G} (hx : Pure s x) (hne : x ≠ 1) :
    centralizer ({x} : Set G) ≤ D.maximalLocal := by
  obtain ⟨a,ha,m,hm,rfl⟩ := pure_rep s hx
  exact centralizer_conj_le (s.pointCentralizers a ha
    (fun h => hne (by simp [h]))) hm

/-- The exchange prevents a nonidentity pure vector from being T-fixed. -/
theorem pure_not_fixed
    (hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥)
    {x : G} (hx : Pure s x) (hne : x ≠ 1)
    (hfix : x ∈ centralizer (T : Set G)) : False := by
  have he : MulAut.conj s.exchange x = x := by
    change s.exchange * x * s.exchange⁻¹ = x
    rw [hfix s.exchange s.exchange_mem,mul_inv_cancel_right]
  have hd := (survivor_pair_disjoint s hz).eq_bot
  apply hne
  apply mem_bot.mp
  rw [← hd]
  rcases hx with hx | hx
  · exact ⟨hx,he ▸ mem_map_of_mem (MulAut.conj s.exchange).toMonoidHom hx⟩
  · obtain ⟨a,ha,hae⟩ := hx
    have hax : a = x := (MulAut.conj s.exchange).injective (hae.trans he.symm)
    exact ⟨hax ▸ ha,⟨a,ha,hae⟩⟩

/-- Every specified nonidentity T-central vector is diagonal. -/
theorem central_is_diagonal
    (hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥)
    {z : G} (hzV : z ∈ D.fullModule) (hzT : z ∈ centerIn (T : Subgroup G))
    (hzn : z ≠ 1) : Diagonal s z := by
  rcases pure_or_diagonal s hz hzV with hp | hd
  · exact (pure_not_fixed s hz hp hzn hzT.2).elim
  · exact hd

/-- A Sylow subgroup in a point centralizer can be moved to T inside M. -/
theorem centralizing_sylow_conjugate {x : G}
    (hc : centralizer ({x} : Set G) ≤ D.maximalLocal)
    (S : Sylow 2 G) (hS : (S : Subgroup G) ≤ centralizer ({x} : Set G)) :
    ∃ m ∈ D.maximalLocal, MulAut.conj m x ∈ centralizer (T : Set G) := by
  have hSM : (S : Subgroup G) ≤ D.maximalLocal := hS.trans hc
  have hTM : (T : Subgroup G) ≤ D.maximalLocal := le_normalizer_componentOrbit L T
  obtain ⟨m,hm⟩ := MulAction.exists_smul_eq D.maximalLocal (S.subtype hSM) (T.subtype hTM)
  have he : (m:G) • S = T :=
    Sylow.subtype_injective ((Sylow.smul_subtype hSM m).symm.trans hm)
  refine ⟨m,m.property,?_⟩
  intro t ht
  have ht' : t ∈ ((m:G) • S : Sylow 2 G) := he.symm ▸ ht
  change t ∈ (S : Subgroup G).map (MulAut.conj (m:G)).toMonoidHom at ht'
  obtain ⟨u,hu,rfl⟩ := ht'
  exact (map_mul (MulAut.conj (m:G)) u x).symm.trans
    ((congrArg (MulAut.conj (m:G)) (mem_centralizer_singleton_iff.mp (hS hu))).trans
      (map_mul (MulAut.conj (m:G)) x u))

/-- Pure involutions are not 2-central in G. The assertion uses the actual
Sylow subgroups, rather than an auxiliary fusion predicate. -/
theorem pure_not_two_central
    (hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥)
    {x : G} (hx : Pure s x) (hne : x ≠ 1)
    (S : Sylow 2 G) (hS : (S : Subgroup G) ≤ centralizer ({x} : Set G)) : False := by
  obtain ⟨m,hm,hfix⟩ := centralizing_sylow_conjugate (pure_centralizer_le s hx hne) S hS
  exact pure_not_fixed s hz (pure_conj s hx hm)
    (fun h => hne ((MulAut.conj m).injective (h.trans (map_one _).symm))) hfix

omit [Finite G] in
/-- A conjugate of a T-central element centralizes the conjugate Sylow. -/
theorem conjugate_sylow_centralizes {z : G}
    (hzT : z ∈ centralizer (T : Set G)) (g : G) :
    ((g • T : Sylow 2 G) : Subgroup G) ≤ centralizer ({MulAut.conj g z} : Set G) := by
  rintro _ ⟨t,ht,rfl⟩
  apply mem_centralizer_singleton_iff.mpr
  exact (map_mul (MulAut.conj g) t z).symm.trans
    ((congrArg (MulAut.conj g) (hzT t ht)).trans (map_mul (MulAut.conj g) z t))

/-- Pure and diagonal vectors cannot be fused in G. -/
theorem pure_diagonal_not_conjugate
    (hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥)
    {z : G} (hzV : z ∈ D.fullModule) (hzT : z ∈ centerIn (T : Subgroup G))
    (hzn : z ≠ 1) {x y : G} (hx : Pure s x) (hxn : x ≠ 1)
    (hy : Diagonal s y) (g : G) (hg : MulAut.conj g x = y) : False := by
  obtain ⟨l,_hl,he⟩ := diagonal_transitive s hz (central_is_diagonal s hz hzV hzT hzn) hy
  have hback : MulAut.conj (g⁻¹*l) z = x := by
    calc
      MulAut.conj (g⁻¹*l) z = MulAut.conj g⁻¹ (MulAut.conj l z) := by
        simp [MulAut.conj_apply,mul_assoc]
      _ = x := by rw [he,← hg]; simp [MulAut.conj_apply,mul_assoc]
  apply pure_not_two_central s hz hx hxn ((g⁻¹*l) • T)
  rw [← hback]
  exact conjugate_sylow_centralizes hzT.2 (g⁻¹*l)

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.Escape.Fusion
