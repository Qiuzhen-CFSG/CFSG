module

public import CFSG.Quasithin.ChapterD.Section03.InternalSetup

/-!
# The odd-prime actor alternative under the faithful quotient

Killing the original two-core gives a surjection from `X/O₂(X)` onto
the literal image of `X`. Frattini functoriality then gives a surjection
from `X/O₂,Φ(X)` to that image's Frattini quotient. On representatives it
intertwines the two original conjugation actions. Pullback of invariant
subgroups proves irreducibility of the target action, including the case
of a trivial target. The odd-prime group property descends through the
same two-core quotient map.

The final result supplies the actual odd-prime alternative in D.3.1 for
the image actor and the image Sylow subgroup.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Hypothesis D.3.2(ii) and Lemma D.3.3, printed p.193.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterD.Section03
variable {G H : Type*} [Group G] [Group H]

private theorem core_le_subgroupMap_ker (f : G →* H) (X : Subgroup G)
    (hkill : X.pCoreIn 2 ≤ f.ker) : pCore 2 X ≤ (f.subgroupMap X).ker := by
  intro x hx
  apply Subtype.ext
  exact hkill (mem_map_of_mem X.subtype hx)

/-- Killing the two-core carries an odd-prime actor quotient to a
p-group image; the descent itself works for every prime parameter. -/
theorem isPGroup_map_of_core_killed (f : G →* H) (X : Subgroup G)
    (hkill : X.pCoreIn 2 ≤ f.ker) {p : ℕ} (hP : IsPGroup p (X ⧸ pCore 2 X)) :
    IsPGroup p (X.map f) := by
  let a := QuotientGroup.lift (pCore 2 X) (f.subgroupMap X)
    (core_le_subgroupMap_ker f X hkill)
  exact hP.of_surjective a (QuotientGroup.lift_surjective_of_surjective _ _
    (f.subgroupMap_surjective X) _)

private theorem coreFrattini_le_comap_frattini_map (f : G →* H) (X : Subgroup G)
    (hkill : X.pCoreIn 2 ≤ f.ker) :
    coreFrattiniIn X ≤ (frattini (X.map f)).comap (f.subgroupMap X) := by
  let a := QuotientGroup.lift (pCore 2 X) (f.subgroupMap X)
    (core_le_subgroupMap_ker f X hkill)
  have ha : Function.Surjective a := QuotientGroup.lift_surjective_of_surjective _ _
    (f.subgroupMap_surjective X) _
  have hphi := frattini_le_comap_frattini_of_surjective ha
  intro x hx
  exact hphi hx

private theorem coreFrattiniAction_mk (T X : Subgroup G)
    (hTX : T ≤ normalizer (X : Set G)) (t : T) (x : X) :
    coreFrattiniAction T X hTX t (QuotientGroup.mk' (coreFrattiniIn X) x) =
      QuotientGroup.mk' (coreFrattiniIn X)
        (X.normalizerMonoidHom ⟨t, hTX t.property⟩ x) := by
  change quotientAut (coreFrattiniIn X) (X.normalizerMonoidHom (inclusion hTX t))
    (QuotientGroup.mk' (coreFrattiniIn X) x) = _
  rw [quotientAut_apply_mk]
  rfl

private theorem frattiniAction_mk (T X : Subgroup G)
    (hTX : T ≤ normalizer (X : Set G)) (t : T) (x : X) :
    frattiniAction T X hTX t (QuotientGroup.mk' (frattini X) x) =
      QuotientGroup.mk' (frattini X) (X.normalizerMonoidHom ⟨t, hTX t.property⟩ x) := by
  change quotientAut (frattini X) (X.normalizerMonoidHom (inclusion hTX t))
    (QuotientGroup.mk' (frattini X) x) = _
  rw [quotientAut_apply_mk]
  rfl

/-- The original irreducible action above the two-core and Frattini
subgroup descends to the literal Frattini action on the actor image. -/
theorem CoreFrattiniIrreducible.map {T X : Subgroup G}
    {hTX : T ≤ normalizer (X : Set G)} (hI : CoreFrattiniIrreducible T X hTX)
    (f : G →* H) (hkill : X.pCoreIn 2 ≤ f.ker)
    (hbar : T.map f ≤ normalizer (X.map f : Set H)) :
    FrattiniIrreducible (T.map f) (X.map f) hbar := by
  let q := (QuotientGroup.mk' (frattini (X.map f))).comp (f.subgroupMap X)
  have hq : Function.Surjective q :=
    (QuotientGroup.mk'_surjective _).comp (f.subgroupMap_surjective X)
  have hker : coreFrattiniIn X ≤ q.ker := by
    intro x hx
    exact (QuotientGroup.eq_one_iff _).mpr (coreFrattini_le_comap_frattini_map f X hkill hx)
  let a := QuotientGroup.lift (coreFrattiniIn X) q hker
  have ha : Function.Surjective a := QuotientGroup.lift_surjective_of_surjective _ _ hq _
  have hequiv (t : T) (v : X ⧸ coreFrattiniIn X) :
      a (coreFrattiniAction T X hTX t v) =
        frattiniAction (T.map f) (X.map f) hbar (f.subgroupMap T t) (a v) := by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (coreFrattiniIn X) v
    rw [coreFrattiniAction_mk]
    change QuotientGroup.mk' (frattini (X.map f))
        (f.subgroupMap X (X.normalizerMonoidHom ⟨t, hTX t.property⟩ x)) =
      frattiniAction (T.map f) (X.map f) hbar (f.subgroupMap T t)
        (QuotientGroup.mk' (frattini (X.map f)) (f.subgroupMap X x))
    rw [frattiniAction_mk]
    congr 1
    apply Subtype.ext
    change f ((t : G) * (x : G) * (t : G)⁻¹) =
      f t * f x * (f t)⁻¹
    simp only [map_mul, map_inv]
  intro B hB
  have hpre : ∀ t : T, ∀ v ∈ B.comap a, coreFrattiniAction T X hTX t v ∈ B.comap a := by
    intro t v hv
    change a (coreFrattiniAction T X hTX t v) ∈ B
    rw [hequiv]
    exact hB (f.subgroupMap T t) (a v) hv
  rcases hI (B.comap a) hpre with hb | ht
  · left
    have hm := congrArg (Subgroup.map a) hb
    simpa only [Subgroup.map_comap_eq_self_of_surjective ha, Subgroup.map_bot] using hm
  · right
    have hm := congrArg (Subgroup.map a) ht
    simpa only [Subgroup.map_comap_eq_self_of_surjective ha, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top_of_surjective a ha] using hm

/-- Both group and module assertions for the original actor image and
the actual surjective image of the Sylow subgroup. -/
theorem odd_actor_image_data [Finite G] (f : G →* H) (hf : Function.Surjective f)
    (T : Sylow 2 G) (X : Subgroup G)
    (hTX : (T : Subgroup G) ≤ normalizer (X : Set G))
    (hkill : X.pCoreIn 2 ≤ f.ker) {p : ℕ} (hP : IsPGroup p (X ⧸ pCore 2 X))
    (hI : CoreFrattiniIrreducible (T : Subgroup G) X hTX)
    (hbar : (T.mapSurjective hf : Subgroup H) ≤ normalizer (X.map f : Set H)) :
    IsPGroup p (X.map f) ∧
      FrattiniIrreducible (T.mapSurjective hf : Subgroup H) (X.map f) hbar := by
  refine ⟨isPGroup_map_of_core_killed f X hkill hP, ?_⟩
  exact hI.map f hkill hbar

/-- The internal odd-prime alternative yields the source D.3.1 odd-prime
alternative after the two-core is killed. -/
theorem actorCases_of_internal_odd_image [Finite G]
    (f : G →* H) (hf : Function.Surjective f) (T : Sylow 2 G) (X : Subgroup G)
    (hTX : (T : Subgroup G) ≤ normalizer (X : Set G))
    (hkill : X.pCoreIn 2 ≤ f.ker) {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hP : IsPGroup p (X ⧸ pCore 2 X))
    (hI : CoreFrattiniIrreducible (T : Subgroup G) X hTX)
    (hbar : (T.mapSurjective hf : Subgroup H) ≤ normalizer (X.map f : Set H)) :
    ActorCases (T.mapSurjective hf) (X.map f) hbar := by
  exact Or.inr ⟨p, hp, ho, odd_actor_image_data f hf T X hTX hkill hP hI hbar⟩

end CFSG.Quasithin.ChapterD.Section03
