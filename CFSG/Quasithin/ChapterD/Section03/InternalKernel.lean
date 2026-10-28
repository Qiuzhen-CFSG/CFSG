module

public import CFSG.Quasithin.ChapterD.Section03.InternalImage
public import CFSG.Quasithin.ChapterD.Section03.ActorKernel

/-!
# The original actor kernel in D.3.3

Quotienting the ambient group by the normal actor's intrinsic two-core
turns both internal actor alternatives into those of D.3.1. The proper
normal actor-subgroup bound then places the image kernel in the image
actor's Frattini subgroup. The first isomorphism theorem identifies its
pullback with the literal preimage of Φ(X/O₂(X)).

The final theorem applies this bound to C_X(W), where W is the global
orbit span of the original Irr⁺ seed. Nontrivial action on that seed makes
the kernel proper, while the reduced actor action makes it contain O₂(X).

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma D.3.3(2), printed p.193.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
namespace CFSG.Quasithin.ChapterD.Section03
universe u v w
variable {G : Type u} [Group G] {H : Type w} [Group H]

private theorem mem_coreFrattini_of_image_mem_frattini (f : G →* H) (X : Subgroup G)
    (hk : (f.subgroupMap X).ker = pCore 2 X) (x : X)
    (hx : f.subgroupMap X x ∈ frattini (X.map f)) : x ∈ coreFrattiniIn X := by
  let e := QuotientGroup.liftEquiv (pCore 2 X) (f.subgroupMap_surjective X) hk.symm
  have hm := frattini_le_comap_frattini_of_surjective
    (φ := e.symm.toMonoidHom) e.symm.surjective hx
  change e.symm (f.subgroupMap X x) ∈ frattini (X ⧸ pCore 2 X) at hm
  have he : e (QuotientGroup.mk' (pCore 2 X) x) = f.subgroupMap X x := rfl
  rw [← he, e.symm_apply_apply] at hm
  exact hm

/-- A proper normal actor subgroup containing the intrinsic two-core lies
in the preimage of the Frattini subgroup of the two-core quotient. -/
theorem InternalActorCases.proper_normal_le_coreFrattini [Finite G]
    {T : Sylow 2 G} {X N : Subgroup G} [X.Normal]
    {hTX : (T : Subgroup G) ≤ normalizer (X : Set G)}
    (hcases : InternalActorCases T X hTX) (hNX : N ≤ X)
    (hn : X ⊔ (T : Subgroup G) ≤ normalizer (N : Set G)) (hne : N ≠ X)
    (hON : X.pCoreIn 2 ≤ N) : N ≤ (coreFrattiniIn X).map X.subtype := by
  let O := X.pCoreIn 2
  let : O.Normal := by dsimp [O, pCoreIn]; infer_instance
  let q := QuotientGroup.mk' O
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective O
  have hk : q.ker = O := QuotientGroup.ker_mk' O
  have hkN : q.ker ≤ N := by rw [hk]; exact hON
  have hkX : q.ker ≤ X := hkN.trans hNX
  have hmapne : N.map q ≠ X.map q := by
    intro he
    exact hne (map_injective_of_ker_le q hkN hkX he)
  have hXne : X.map q ≠ ⊥ := by
    intro he
    have hn0 : N.map q = ⊥ := le_bot_iff.mp (he ▸ map_mono hNX)
    exact hmapne (hn0.trans he.symm)
  have hbar : (T.mapSurjective hq : Subgroup (G ⧸ O)) ≤
      normalizer (X.map q : Set (G ⧸ O)) :=
    (map_mono hTX).trans (X.le_normalizer_map q)
  have hc : ActorCases (T.mapSurjective hq) (X.map q) hbar := by
    rcases hcases with ⟨L, hL, hQ, hX⟩ | ⟨p, hp, ho, hP, hI⟩
    · exact Or.inl (component_internal_actor_image hL hQ hX q hq hk.ge hXne)
    · exact actorCases_of_internal_odd_image q hq T X hTX hk.ge hp ho hP hI hbar
  have hm : N.map q ≤ (frattini (X.map q)).map (X.map q).subtype :=
    hc.proper_normal_le_frattini (map_mono hNX) (by
      change X.map q ⊔ (T : Subgroup G).map q ≤ _
      rw [← Subgroup.map_sup]
      exact (map_mono hn).trans (N.le_normalizer_map q)) hmapne
  have hk' : (q.subgroupMap X).ker = pCore 2 X := by
    rw [ker_subgroupMap, hk]
    exact comap_map_eq_self_of_injective X.subtype_injective (pCore 2 X)
  intro n hnN
  obtain ⟨a, ha, hea⟩ := hm (mem_map_of_mem q hnN)
  have ha' : q.subgroupMap X ⟨n, hNX hnN⟩ ∈ frattini (X.map q) := by
    have he : a = q.subgroupMap X ⟨n, hNX hnN⟩ := Subtype.ext hea
    rwa [← he]
  exact ⟨⟨n, hNX hnN⟩, mem_coreFrattini_of_image_mem_frattini q X hk' _ ha', rfl⟩

variable [Finite G] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {K : GroupClass.{u}}
  {T : Sylow 2 G} {X : Subgroup G} {I : Submodule (ZMod 2) V}

/-- D.3.3(2): the original actor kernel on the global orbit span lies in
its intrinsic two-core--Frattini preimage. -/
theorem InternalModuleHypotheses.orbit_actorKernel_le_coreFrattini
    (h : InternalModuleHypotheses K ρ T X I) :
    subspaceKernel ρ (orbitSpan ρ ⊤ I) X ≤ (coreFrattiniIn X).map X.subtype := by
  let := h.normal
  let W := orbitSpan ρ ⊤ I
  let N := subspaceKernel ρ W X
  have hW : (⊤ : Subgroup G) ≤ subspaceStabilizer ρ W := orbitSpan_invariant ρ ⊤ I
  apply h.cases.proper_normal_le_coreFrattini (subspaceKernel_le ρ W X)
  · apply le_normalizer_iff.mpr
    intro g hg n hn
    refine ⟨h.normal.conj_mem n hn.1 g, ?_⟩
    intro w hw
    have hi : ρ g⁻¹ w ∈ W := (hW (mem_top _) w).2 hw
    have hh := congrArg (ρ g) (hn.2 _ hi)
    simpa only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      Module.End.one_apply, mul_assoc] using hh
  · intro he
    apply h.seed.not_le_fixedSpace ρ
    intro v hv x
    have hx : (x : G) ∈ N := by
      rw [show N = X from he]
      exact x.property
    exact hx.2 v (le_orbitSpan ρ ⊤ I hv)
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨x.property, fun v _ => h.actorCore_fixes x hx v⟩

end CFSG.Quasithin.ChapterD.Section03
