module

public import Theory.GroupTheory.CComponent.SylowRadical
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.GroupTheory.IndexTwoConjugatePair
public import Theory.GroupTheory.QuotientIntersection
public import Theory.GroupTheory.ComponentLocalOrbitCore

/-!
# Normalization of the Sylow intersection with a component orbit

A full ambient Sylow intersects the commuting join of its conjugate ordinary
components in the join of the corresponding factor Sylows. If it normalizes
an actor X and X normalizes the first factor Sylow, X normalizes all those
conjugates and therefore their join. For a C-component with quasisimple
two-core quotient, apply this in the literal ambient two-core quotient and
pull back through the two-core contained in the original Sylow.

Source application: Aschbacher--Smith 6.1.4, printed p.665.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- An actor normalized by T preserves the whole component-orbit Sylow
as soon as it preserves the original component's Sylow intersection. -/
theorem IsComponent.normalizes_sylow_orbit {K X : Subgroup G}
    (hK : IsComponent G K) (T : Sylow 2 G)
    (hTX : (T : Subgroup G) ≤ normalizer (X : Set G))
    (hXU : X ≤ normalizer ((((T : Subgroup G) ⊓ K) : Subgroup G) : Set G)) :
    X ≤ normalizer ((((T : Subgroup G) ⊓ componentOrbit K (T : Subgroup G)) : Subgroup G) : Set G) := by
  classical
  let I := {J : Subgroup G // ∃ t : (T : Subgroup G), K.map (MulAut.conj (t : G)).toMonoidHom = J}
  let F : I → Subgroup G := fun i => i.val
  have hF (i : I) : IsComponent G (F i) := by
    obtain ⟨t,ht⟩ := i.property
    change IsComponent G i.val
    rw [←ht]
    exact hK.map_conj t
  have ho : componentOrbit K (T : Subgroup G) = ⨆ i, F i := by
    apply le_antisymm
    · exact iSup_le fun t => le_iSup F ⟨_,t,rfl⟩
    · apply iSup_le
      rintro ⟨J,t,rfl⟩
      exact le_iSup (fun t : (T : Subgroup G) => K.map (MulAut.conj (t : G)).toMonoidHom) t
  have hc : Pairwise fun i j => ∀ x y : G, x ∈ F i → y ∈ F j → Commute x y := by
    intro i j hne x y hx hy
    exact ((commutator_eq_bot_iff_le_centralizer.mp
      ((hF i).commutator_eq_bot_of_ne (hF j) (fun he => hne (Subtype.ext he)))) hx y hy).symm
  rw [ho,sylow_inf_iSup_of_commuting_subnormal T F (fun i => (hF i).1) hc]
  apply (le_iInf fun i => ?_).trans (iInf_normalizer_le_normalizer_iSup _)
  obtain ⟨t,ht⟩ := i.property
  have hnorm := normalizes_conjugate_of_normalizes (hTX t.property) hXU
  have he : (((T : Subgroup G) ⊓ K).map (MulAut.conj (t : G)).toMonoidHom) =
      (T : Subgroup G) ⊓ F i := by
    rw [Subgroup.map_inf _ _ _ (MulAut.conj (t : G)).injective]
    have hT := mem_normalizer_iff_map_conj_eq.mp ((T : Subgroup G).le_normalizer t.property)
    change (T : Subgroup G).map (MulAut.conj (t : G)).toMonoidHom = T at hT
    rw [hT,ht]
  change X ≤ normalizer ((((T : Subgroup G) ⊓ K).map
    (MulAut.conj (t : G)).toMonoidHom) : Set G) at hnorm
  rwa [he] at hnorm

/-- The same literal normalization lifts through the ambient two-core for a
C-component with quasisimple two-core quotient. -/
theorem cComponent_normalizes_sylow_orbit {K X : Subgroup G}
    (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (T : Sylow 2 G)
    (hTX : (T : Subgroup G) ≤ normalizer (X : Set G))
    (hXK : X ≤ normalizer (K : Set G))
    (hXU : X ≤ normalizer ((((T : Subgroup G) ⊓ K) : Subgroup G) : Set G)) :
    X ≤ normalizer ((((T : Subgroup G) ⊓ componentOrbit K (T : Subgroup G)) : Subgroup G) : Set G) := by
  let := hq
  let q := QuotientGroup.mk' (pCore 2 G)
  let B := K.map q
  let P := T.mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  have hB : IsComponent (G ⧸ pCore 2 G) B :=
    ⟨hK.subnormal.quotient,IsQuasisimple.of_mulEquiv (cComponentTwoCoreQuotientEquiv hK)⟩
  have hker : q.ker ≤ (T : Subgroup G) := by
    rw [show q.ker = pCore 2 G from QuotientGroup.ker_mk' _]
    exact pCore_isPGroup.le_sylow_of_normal T
  have hi (C : Subgroup G) : ((T : Subgroup G) ⊓ C).map q =
      (P : Subgroup (G ⧸ pCore 2 G)) ⊓ C.map q := by
    rw [inf_comm,map_inf_of_ker_le q C (T : Subgroup G) hker,inf_comm]
    rfl
  have hTq : (P : Subgroup (G ⧸ pCore 2 G)) ≤ normalizer (X.map q : Set _) :=
    (map_mono hTX).trans (X.le_normalizer_map q)
  have hXq : X.map q ≤ normalizer ((((P : Subgroup (G ⧸ pCore 2 G)) ⊓ B) : Subgroup (G ⧸ pCore 2 G)) : Set _) := by
    rw [←hi K]
    exact (map_mono hXU).trans (((T : Subgroup G) ⊓ K).le_normalizer_map q)
  have hn := hB.normalizes_sylow_orbit P hTq hXq
  have hXN : X ≤ normalizer (componentOrbit K (T : Subgroup G) : Set G) := by
    apply (le_iInf fun t : (T : Subgroup G) => ?_).trans (iInf_normalizer_le_normalizer_iSup _)
    exact normalizes_conjugate_of_normalizes (hTX t.property) hXK
  have horb : (componentOrbit K (T : Subgroup G)).map q =
      componentOrbit B (P : Subgroup (G ⧸ pCore 2 G)) := by
    rw [map_componentOrbit]
    rfl
  apply le_normalizer_iff.mpr
  intro x hx u hu
  have hqu : q u ∈ (P : Subgroup (G ⧸ pCore 2 G)) ⊓ componentOrbit B P :=
    ⟨mem_map_of_mem q hu.1,horb ▸ mem_map_of_mem q hu.2⟩
  have hqxu := le_normalizer_iff.mp hn (q x) (mem_map_of_mem q hx) (q u) hqu
  have hxT : x*u*x⁻¹ ∈ (T : Subgroup G) := by
    have hh : x*u*x⁻¹ ∈ ((T : Subgroup G).map q).comap q := by
      change q (x*u*x⁻¹) ∈ (T : Subgroup G).map q
      have hfirst := hqxu.1
      change q x*q u*(q x)⁻¹ ∈ (T : Subgroup G).map q at hfirst
      simpa only [map_mul,map_inv] using hfirst
    rwa [comap_map_eq_self hker] at hh
  exact ⟨hxT,le_normalizer_iff.mp hXN x hx u hu.2⟩

end Theory.GroupTheory
