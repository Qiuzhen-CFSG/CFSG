module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.OddCore
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleCore
/-!
# Centralizer consequences in the diagonal-outer argument

Conjugation gives an actual isomorphism of element centralizers and of their
odd cores. A component in one centralizer cannot be transported into a
centralizer with `F* = O₂`: it would be a nontrivial perfect two-group.
This is the group-theoretic step excluding the `z` fusion class.

The TI odd-core bound transports along fusion to an injection into the
specified local odd-core model (the source model is `E₉`). The last lemma
retains the two alternatives in A.3.18: a 3′ centralizer, or a unique
subgroup of order three. Neither can contain an exponent-three group of
order divisible by three and greater than three. In particular this applies
to E₉. `SourceObstruction` separately audits the incompatible order-27
construction printed in the source.

These are conditional consequences, not model classifications. Existence of
the component, the local odd-core identification, and the A.3.18 alternatives
remain inputs. Source: Aschbacher--Smith, combined manuscript (1 March 2004),
proof of 15.3.38, printed p.1137.
-/

public section

namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter
open Subgroup Theory.GroupTheory CFSG.Quasithin.ChapterI.Section06To08
variable {G : Type*} [Group G]
private def centralizerTransport {H : Type*} [Group H]
    (e : G ≃* H) (x : G) :
    centralizer ({x} : Set G) ≃* centralizer ({e x} : Set H) where
  toFun y := ⟨e y, mem_centralizer_singleton_iff.mpr (by
    simpa only [map_mul] using congrArg e (mem_centralizer_singleton_iff.mp y.property))⟩
  invFun y := ⟨e.symm y, mem_centralizer_singleton_iff.mpr (by
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using
      mem_centralizer_singleton_iff.mp y.property)⟩
  left_inv y := Subtype.ext (e.symm_apply_apply y)
  right_inv y := Subtype.ext (e.apply_symm_apply y)
  map_mul' y z := Subtype.ext (e.map_mul y z)

private def centralizerFusionEquiv {x y : G} (g : G)
    (hg : (MulAut.conj g) x = y) :
    centralizer ({x} : Set G) ≃* centralizer ({y} : Set G) :=
  (centralizerTransport (MulAut.conj g) x).trans
    (MulEquiv.subgroupCongr (congrArg (fun a => centralizer ({a} : Set G)) hg))

/-- The component supplied by the graph-centralizer argument excludes fusion
with an element whose centralizer has generalized Fitting subgroup `O₂`. -/
theorem not_fused_of_component_centralizer [Finite G] {x z : G}
    (K : Subgroup (centralizer ({x} : Set G)))
    (hK : IsComponent (centralizer ({x} : Set G)) K)
    (hz : generalizedFitting (centralizer ({z} : Set G)) =
      pCore 2 (centralizer ({z} : Set G))) : ¬ IsConj x z := by
  rintro hconj
  obtain ⟨g, hg⟩ := isConj_iff.mp hconj
  let e := centralizerFusionEquiv g hg
  let D := K.map e.toMonoidHom
  have hD : IsComponent (centralizer ({z} : Set G)) D := hK.map_equiv e
  let : IsQuasisimple D := hD.2
  have hle : D ≤ pCore 2 (centralizer ({z} : Set G)) :=
    hz ▸ component_le_generalizedFitting _ D hD
  have hp : IsPGroup 2 D := pCore_isPGroup.to_le hle
  let : Group.IsNilpotent D := hp.isNilpotent
  let : IsSimpleGroup (D ⧸ center D) := IsQuasisimple.simple
  let : Nontrivial D := Function.Surjective.nontrivial
    (QuotientGroup.mk'_surjective (center D))
  exact Group.IsPerfect.not_isSolvable D inferInstance


/-- The odd core of a fused element centralizer embeds in the actual local
odd-core model. Instantiating `E` with `E₉` gives the source rank/exponent bound. -/
theorem centralizer_oddCore_embeds_of_fusion [Finite G] (V I : Subgroup G) [IsKleinFour V]
    (hV : IsTISubgroup V) (hI : I = normalizer (V : Set G)) {w f : G}
    (hw : w ∈ centralizer (V : Set G)) (hfusion : IsConj w f)
    {E : Type*} [Group E]
    (e : pPrimeCore 2 ↥(I ⊓ centralizer ({w} : Set G)) ≃* E) :
    ∃ ι : pPrimeCore 2 (centralizer ({f} : Set G)) →* E, Function.Injective ι := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hfusion
  let ec := (centralizerFusionEquiv g hg).symm
  let er := (ec.subgroupMap (pPrimeCore 2 (centralizer ({f} : Set G)))).trans
    (MulEquiv.subgroupCongr (pPrimeCore_map_iso 2 ec))
  let C := centralizer ({w} : Set G)
  let D := I ⊓ C
  let R := (pPrimeCore 2 C).map C.subtype
  let Q := (pPrimeCore 2 D).map D.subtype
  have hRQ : R ≤ Q := centralizer_oddCore_le_local_oddCore V I hV hI hw
  let er' := (pPrimeCore 2 C).equivMapOfInjective C.subtype C.subtype_injective
  let eq' := (pPrimeCore 2 D).equivMapOfInjective D.subtype D.subtype_injective
  let ι : pPrimeCore 2 (centralizer ({f} : Set G)) →* E :=
    e.toMonoidHom.comp (eq'.symm.toMonoidHom.comp
      ((inclusion hRQ).comp (er'.toMonoidHom.comp er.toMonoidHom)))
  refine ⟨ι, ?_⟩
  exact e.injective.comp (eq'.symm.injective.comp
    ((inclusion_injective hRQ).comp (er'.injective.comp er.injective)))

/-- An exponent-three group of order greater than three cannot lie in
a 3′ group or in a group with a unique subgroup of order three. -/
theorem exponent_three_not_le [Finite G] (B C Z : Subgroup G)
    (hthree : 3 ∣ Nat.card B) (hB : 3 < Nat.card B) (hexp : ∀ b : B, b ^ 3 = 1)
    (hC : Nat.Coprime 3 (Nat.card C) ∨
      (Nat.card Z = 3 ∧ ∀ P : Subgroup G, P ≤ C → Nat.card P = 3 → P = Z)) :
    ¬ B ≤ C := by
  intro hBC
  rcases hC with hcop | ⟨hZ, huniq⟩
  · have hd : 3 ∣ Nat.card C := hthree.trans (card_dvd_of_le hBC)
    exact (by decide : ¬ Nat.Coprime 3 3) (hcop.of_dvd_right hd)
  · have hBZ : B ≤ Z := by
      intro b hb
      by_cases he : b = 1
      · simp [he]
      have hb3 : b ^ 3 = 1 := congrArg Subtype.val (hexp ⟨b, hb⟩)
      have hbo : orderOf b = 3 := (orderOf_eq_prime_iff).mpr ⟨hb3, he⟩
      have hP : zpowers b ≤ C := (zpowers_le.mpr hb).trans hBC
      have hPc : Nat.card (zpowers b) = 3 := (Nat.card_zpowers b).trans hbo
      rw [← huniq (zpowers b) hP hPc]
      exact mem_zpowers b
    have hc := Nat.le_of_dvd (Nat.card_pos (α := Z)) (card_dvd_of_le hBZ)
    omega

/-- The original order-27 specialization, retained as a conditional helper. -/
theorem exponent_three_order_27_not_le [Finite G] (B C Z : Subgroup G)
    (hB : Nat.card B = 27) (hexp : ∀ b : B, b ^ 3 = 1)
    (hC : Nat.Coprime 3 (Nat.card C) ∨
      (Nat.card Z = 3 ∧ ∀ P : Subgroup G, P ≤ C → Nat.card P = 3 → P = Z)) :
    ¬ B ≤ C :=
  exponent_three_not_le B C Z (by omega) (by omega) hexp hC

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter
