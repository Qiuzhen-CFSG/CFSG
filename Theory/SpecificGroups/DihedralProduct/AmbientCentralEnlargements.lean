module
public import Theory.SpecificGroups.DihedralProduct.CentralEnlargementModel

/-!
# The normalizer action on actual dihedral central enlargements

Transport the four canonical enlargements through a supplied isomorphism
of an ambient subgroup with D₈⁴. Conjugation by its normalizer gives the
literal permutation action, whose kernel consists exactly of elements
normalizing all four enlargements.

Source: Aschbacher–Smith, 10.2.1, printed p.743.
-/

@[expose] public noncomputable section
open Subgroup
namespace DihedralProductCanonical
variable {G : Type*} [Group G]

def ambientGamma (S : Subgroup G) (e : S ≃* (Fin 4 → D)) (i : Fin 4) : Subgroup G :=
  (transportedGamma e i).map S.subtype

def ambientGammaEquiv (S : Subgroup G) (e : S ≃* (Fin 4 → D)) (i : Fin 4) :
    ambientGamma S e i ≃* D × Remainder i :=
  ((transportedGamma e i).equivMapOfInjective S.subtype S.subtype_injective).symm.trans
    (transportedGammaEquiv e i)

theorem ambientGamma_injective (S : Subgroup G) (e : S ≃* (Fin 4 → D)) :
    Function.Injective (ambientGamma S e) := by
  intro i j h
  exact transportedGamma_injective e (map_injective S.subtype_injective h)

theorem ambientGamma_le (S : Subgroup G) (e : S ≃* (Fin 4 → D)) (i : Fin 4) :
    ambientGamma S e i ≤ S := map_subtype_le _

def normalizerFactorAction (S : Subgroup G) (e : S ≃* (Fin 4 → D)) :
    normalizer (S : Set G) →* Equiv.Perm (Fin 4) :=
  (transportedFactorAction e).comp S.normalizerMonoidHom

theorem map_ambientGamma (S : Subgroup G) (e : S ≃* (Fin 4 → D))
    (n : normalizer (S : Set G)) (i : Fin 4) :
    (ambientGamma S e i).map (MulAut.conj (n : G)).toMonoidHom =
      ambientGamma S e (normalizerFactorAction S e n i) := by
  change ((transportedGamma e i).map S.subtype).map (MulAut.conj (n : G)).toMonoidHom = _
  rw [map_map]
  have hcomp : (MulAut.conj (n : G)).toMonoidHom.comp S.subtype =
      S.subtype.comp (S.normalizerMonoidHom n).toMonoidHom := by
    ext x
    rfl
  rw [hcomp, ←map_map, map_transportedGamma]
  rfl

theorem normalizerFactorAction_eq_one_iff (S : Subgroup G) (e : S ≃* (Fin 4 → D))
    (n : normalizer (S : Set G)) :
    normalizerFactorAction S e n = 1 ↔
      ∀ i, (n : G) ∈ normalizer (ambientGamma S e i : Set G) := by
  constructor
  · intro hn i
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (ambientGamma S e i).map (MulAut.conj (n : G)).toMonoidHom = _
    rw [map_ambientGamma, hn]
    rfl
  · intro hn
    apply Equiv.ext
    intro i
    apply ambientGamma_injective S e
    change ambientGamma S e (normalizerFactorAction S e n i) = ambientGamma S e i
    rw [←map_ambientGamma]
    exact mem_normalizer_iff_map_conj_eq.mp (hn i)

end DihedralProductCanonical
