module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Triality.ParabolicTransport
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SporadicExclusions.Interface
public import Theory.SpecificGroups.Triality.FullParabolicActions
public import Theory.SpecificGroups.Triality.OuterOddSubgroups.Coverage.RootGeometry.SimpleRecognition.ParabolicIntersections
public import Theory.GroupTheory.ComponentLocalOrbitEmbedding

/-!
# Invariant triality parabolics and their relative local overgroups

Conjugating a genuine model equivalence aligns the root unipotent Sylow
subgroup with S ∩ L. Every automorphism preserving this Sylow subgroup
preserves its Borel and permutes the two root parabolics. Their distinct
Borel indices q³ + 1 and q + 1 force it to fix each parabolic. Hence the
transported parabolics are invariant under N_S(L).

The genuine root radicals are the full parabolics' self-centralizing two-cores.
Transport gives characteristic two for each component parabolic. The relative
component-orbit theorem then gives characteristic two for its join with all
of S, including when S permutes components. The involution in LocalSetup
supplies nontriviality of the resulting two-core and full HeOver membership.

All positive binary exponents, including q = 2, are covered. The different
node indices retain the cubic root-field convention. This construction uses
only the component and Sylow data of the source setup; the additional inner
action supplied by 1.1.5(3)(a) is not needed for this geometric step.

Sources: Aschbacher–Smith 1.1.5(3)(a), printed p.501, and the invariant
parabolic step of 2.3.9(7), printed p.526 (`refs/quasithin.pdf`). Root geometry
and radical calculations use GLS3 §§2.3–2.6 (`refs/KGroup/GLS3/chapter2.tex`).
-/

public section

open Subgroup
open _root_.Triality.Standard
open Theory.GroupTheory
open scoped Pointwise

namespace CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.TrialityCase

private theorem parabolic_invariant (P : Parameters) (hp : P.prime = 2)
    (σ : MulAut (Carrier P))
    (hU : (Parabolics.unipotent P).map σ.toMonoidHom = Parabolics.unipotent P)
    (a : Parabolics.Node) :
    (Parabolics.parabolic P a).map σ.toMonoidHom = Parabolics.parabolic P a := by
  obtain ⟨n, hn, rfl⟩ := (exists_binaryParameters_iff P).mpr hp
  have hB := OuterOdd.Coverage.map_borel_eq_of_unipotent_invariant _ rfl σ hU
  obtain ⟨b, hb⟩ := OuterOdd.Coverage.RootGeometry.SimpleRecognition.map_parabolic_eq_of_borel_invariant
    n hn σ hB a
  have hi := Subgroup.relIndex_map_map_of_injective (f := σ.toMonoidHom)
    (Parabolics.borel (binaryParameters n hn))
    (Parabolics.parabolic (binaryParameters n hn) a) σ.injective
  rw [hB, hb,
    OuterOdd.Coverage.RootGeometry.SimpleRecognition.borel_relIndex_parabolic,
    OuterOdd.Coverage.RootGeometry.SimpleRecognition.borel_relIndex_parabolic] at hi
  have hq := (binaryParameters n hn).q_ge_two
  have hneq : (binaryParameters n hn).q ^ 3 ≠ (binaryParameters n hn).q := by
    have hlt := pow_lt_pow_right₀ (show 1 < (binaryParameters n hn).q by omega)
      (show 1 < (3 : ℕ) by decide)
    simpa only [pow_one] using ne_of_gt hlt
  have hab : b = a := by
    cases a <;> cases b
    · rfl
    · exact (hneq (Nat.add_right_cancel hi).symm).elim
    · exact (hneq (Nat.add_right_cancel hi)).elim
    · rfl
  exact hab ▸ hb

variable {G : Type*} [Group G] {H L M : Subgroup G} {S : Sylow 2 H} {z : G}
    {P : Parameters}

/-- Conjugate the supplied genuine equivalence to align the actual component
Sylow intersection with the standard positive subgroup. -/
theorem exists_sylow_aligned_equiv (h : LocalSetup H L M S z)
    (hp : P.prime = 2) (e₀ : L ≃* Carrier P) :
    ∃ e : L ≃* Carrier P,
      (Parabolics.unipotent P).comap e.toMonoidHom =
        ((S : Subgroup H).map H.subtype).subgroupOf L := by
  let := h.finite
  obtain ⟨R, hR⟩ := h.exists_component_sylow
  have hR' : (R : Subgroup L) = ((S : Subgroup H).map H.subtype).subgroupOf L := by
    apply Subgroup.map_injective L.subtype_injective
    rw [hR, subgroupOf_map_subtype, inf_comm]
  let R' := R.mapSurjective (f := e₀.toMonoidHom) e₀.surjective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Carrier P) R' (Parabolics.unipotentSylow P hp)
  let e := e₀.trans (MulAut.conj g)
  have he : (R : Subgroup L).map e.toMonoidHom = Parabolics.unipotent P := by
    have hs := congrArg (fun T : Sylow 2 (Carrier P) => (T : Subgroup (Carrier P))) hg
    change ((R : Subgroup L).map e₀.toMonoidHom).map (MulAut.conj g).toMonoidHom = _ at hs
    rw [Subgroup.map_map] at hs
    exact hs
  refine ⟨e, ?_⟩
  rw [← he, Subgroup.comap_map_eq_self_of_injective e.injective, hR']

private theorem intersection_invariant (A : Subgroup G)
    (s : normalizer (L : Set G)) (hs : (s : G) ∈ A) :
    (A.subgroupOf L).map (L.normalizerMonoidHom s).toMonoidHom = A.subgroupOf L := by
  have hf (u : normalizer (L : Set G)) (hu : (u : G) ∈ A) {x : L}
      (hx : x ∈ A.subgroupOf L) : L.normalizerMonoidHom u x ∈ A.subgroupOf L := by
    change (L.normalizerMonoidHom u x : G) ∈ A
    rw [normalizerMonoidHom_apply_apply_coe]
    exact A.mul_mem (A.mul_mem hu hx) (A.inv_mem hu)
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hf s hs hy
  · intro hx
    refine ⟨L.normalizerMonoidHom s⁻¹ x, hf s⁻¹ (A.inv_mem hs) hx, ?_⟩
    rw [map_inv]
    exact (L.normalizerMonoidHom s).apply_symm_apply x

/-- Both aligned root parabolics are normalized by the component stabilizer
in A. Only A ∩ N_G(L), rather than all of A, acts on L. -/
theorem componentParabolic_normalized (hp : P.prime = 2)
    (e : L ≃* Carrier P) (A : Subgroup G)
    (he : (Parabolics.unipotent P).comap e.toMonoidHom = A.subgroupOf L)
    (a : Parabolics.Node) :
    A ⊓ normalizer (L : Set G) ≤ normalizer (componentParabolic e a : Set G) := by
  intro s hs
  let n : normalizer (L : Set G) := ⟨s, hs.2⟩
  let α := L.normalizerMonoidHom n
  let σ : MulAut (Carrier P) := e.symm.trans (α.trans e)
  have hσα : σ.toMonoidHom.comp e.toMonoidHom = e.toMonoidHom.comp α.toMonoidHom := by
    ext x
    exact congrArg (fun y => e (α y)) (e.symm_apply_apply x)
  have hA : (A.subgroupOf L).map e.toMonoidHom = Parabolics.unipotent P := by
    rw [← he, Subgroup.map_comap_eq_self_of_surjective e.surjective]
  have hU : (Parabolics.unipotent P).map σ.toMonoidHom = Parabolics.unipotent P := by
    rw [← hA, Subgroup.map_map, hσα, ← Subgroup.map_map,
      intersection_invariant A n hs.1]
  have hK : ((Parabolics.parabolic P a).comap e.toMonoidHom).map α.toMonoidHom =
      (Parabolics.parabolic P a).comap e.toMonoidHom := by
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [Subgroup.map_map, ← hσα, ← Subgroup.map_map,
      Subgroup.map_comap_eq_self_of_surjective e.surjective,
      parabolic_invariant P hp σ hU a]
  apply mem_normalizer_iff_map_conj_eq.mpr
  have hc : ((MulAut.conj s : MulAut G) : G →* G).comp L.subtype =
      L.subtype.comp α.toMonoidHom := by
    ext x
    rfl
  rw [componentParabolic, Subgroup.map_map, hc, ← Subgroup.map_map, hK]

/-- Transport the genuine full-parabolic radical centralizer calculation. -/
theorem componentParabolic_mem_He (hp : P.prime = 2)
    (e : L ≃* Carrier P) (a : Parabolics.Node) : componentParabolic e a ∈ Chapter1.He G := by
  let ι := L.subtype.comp e.symm.toMonoidHom
  have hι : Function.Injective ι := L.subtype_injective.comp e.symm.injective
  have hK : componentParabolic e a = (Parabolics.parabolic P a).map ι := by
    rw [componentParabolic, Subgroup.comap_equiv_eq_map_symm', Subgroup.map_map]
  have hc : Parabolics.parabolic P a ⊓ centralizer
      ((Parabolics.parabolic P a).pCoreIn 2 : Set (Carrier P)) ≤
        (Parabolics.parabolic P a).pCoreIn 2 := by
    change Parabolics.parabolic P a ⊓ centralizer
      (((pCore 2 (Parabolics.parabolic P a)).map (Parabolics.parabolic P a).subtype) :
        Set (Carrier P)) ≤ (pCore 2 (Parabolics.parabolic P a)).map (Parabolics.parabolic P a).subtype
    rw [Parabolics.parabolic_twoCore_map P hp a]
    exact Parabolics.parabolic_centralizer_radical_le P hp a
  change componentParabolic e a ⊓ centralizer
    ((componentParabolic e a).pCoreIn 2 : Set G) ≤ (componentParabolic e a).pCoreIn 2
  rw [hK, ← map_pCoreIn_of_injective 2 _ ι hι]
  exact (inf_centralizer_map_le_iff _ _ ι hι).mpr hc

/-- Apply characteristic-two inheritance to the actual S-orbit of the
component parabolic, with component subnormality relative to H. -/
theorem parabolicOvergroup_mem_He (h : LocalSetup H L M S z)
    (hp : P.prime = 2) (e : L ≃* Carrier P)
    (he : (Parabolics.unipotent P).comap e.toMonoidHom =
      ((S : Subgroup H).map H.subtype).subgroupOf L)
    (a : Parabolics.Node) :
    parabolicOvergroup e ((S : Subgroup H).map H.subtype) a ∈ Chapter1.He G := by
  let := h.finite
  apply h.component.relative_local_adjoin_centralizer h.component_le
    (componentParabolic_le e a)
    (Subgroup.map_subtype_le (S : Subgroup H)) (S.isPGroup'.map H.subtype)
    (componentParabolic_normalized hp e _ he a)
    (componentParabolic_mem_He hp e a)

/-- The invariant pair required in 2.3.9(7), with the literal Sylow pullback
and both full HeOver memberships. No geometric or local-core premise remains. -/
theorem exists_relative_overgroups (h : LocalSetup H L M S z)
    (hp : P.prime = 2) (e₀ : L ≃* Carrier P) :
    ∃ e : L ≃* Carrier P,
      (Parabolics.unipotent P).comap e.toMonoidHom =
        ((S : Subgroup H).map H.subtype).subgroupOf L ∧
      (∀ a, (S : Subgroup H).map H.subtype ⊓ normalizer (L : Set G) ≤
        normalizer (componentParabolic e a : Set G)) ∧
      (∀ a, parabolicOvergroup e ((S : Subgroup H).map H.subtype) a ∈ Chapter1.He G) ∧
      (∀ a, parabolicOvergroup e ((S : Subgroup H).map H.subtype) a ∈
        Chapter1.HeOver G ((S : Subgroup H).map H.subtype : Set G)) := by
  obtain ⟨e, he⟩ := exists_sylow_aligned_equiv h hp e₀
  refine ⟨e, he, componentParabolic_normalized hp e _ he, ?_, ?_⟩
  · exact parabolicOvergroup_mem_He h hp e he
  · intro a
    exact parabolicOvergroup_mem_HeOver h e a (parabolicOvergroup_mem_He h hp e he a)

end CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.TrialityCase

end
