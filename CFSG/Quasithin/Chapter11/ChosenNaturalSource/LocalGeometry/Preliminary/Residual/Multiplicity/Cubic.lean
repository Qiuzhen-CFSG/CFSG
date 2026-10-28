module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.Residual.CubicMultiplicity
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.Residual.Multiplicity

/-!
# The triple-multiplicity obstruction on the original chosen module

The literal full normalizer orbit has coordinates consisting of s natural
copies, all with the original L/O₂(L) marking. The constituent-count theorem
places every cubic in L whenever three does not divide s. Conversely, an
escaping cubic forces s = 3k with k positive and dim(V_M) = 9nk. Thus the
source application can use nondivisibility of the full dimension by 9n in
place of the stronger strict dimension bound from Multiplicity.

No multiplicity, faithfulness or splitting premise is added to the
necessary obstruction. The sufficient containment theorems keep their
dimension premise explicit. Excluding the remaining multiples of three
from the full ambient hypotheses remains with
qt-d-1222-natural-preliminary-source, before final discharge by
qt-d-1222-natural-local-geometry.

Source: the invariant-constituent argument of Aschbacher--Smith A.3.19,
printed pp.54--55, applied to 11.0.4, printed p.760.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups IsMulCommutative
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

/-- The cubic clause on the full orbit once its genuine repeated-natural marking
is supplied. No seed-invariance, constituent-selection or kernel premise remains. -/
theorem sl3_orderThree_mem_of_fullModule_copies
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (heven : Even S.field.degree) {s : ℕ} (hs : ¬ 3 ∣ s)
    (hcopies : FullModuleNaturalCopies D S m s)
    {x : G} (hxM : x ∈ normalizer (L : Set G)) (hx : orderOf x = 3) : x ∈ L := by
  let := fullModule_elementary D S
  let M := normalizer (L : Set G)
  let K := L.subgroupOf M
  let : K.Normal := normal_subgroupOf_of_le_normalizer le_rfl
  let a : K ≃* L := subgroupOfEquivOfLe L.le_normalizer
  let η : K →* SL(3,S.field.Carrier) :=
    m.groupEquiv.toMonoidHom.comp ((QuotientGroup.mk' (pCore 2 L)).comp a.toMonoidHom)
  have hη : Function.Surjective η := m.groupEquiv.surjective.comp
    ((QuotientGroup.mk'_surjective _).comp a.surjective)
  have hηker : Nat.Coprime 3 (Nat.card η.ker) := by
    have hk : η.ker = (pCore 2 L).comap a.toMonoidHom := by
      ext k
      change m.groupEquiv (QuotientGroup.mk' (pCore 2 L) (a k)) = 1 ↔ a k ∈ pCore 2 L
      rw [m.groupEquiv.map_eq_one_iff]
      exact QuotientGroup.eq_one_iff (a k)
    have hp : IsPGroup 2 η.ker := hk ▸ pCore_isPGroup.comap_of_injective
      a.toMonoidHom a.injective
    obtain ⟨n,hn⟩ := hp.exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  obtain ⟨e,he⟩ := hcopies
  have hd : 3 ∣ Nat.card S.field.Carrier - 1 := by
    rw [S.field.card_eq]
    exact (Nat.BinaryTorusParity.three_dvd_sub_one_iff S.field.degree).mpr heven
  exact CubicNatural.cubic_mem_of_repeated_coordinates S.field K η hη hηker
    (fullModuleConjugation D S) hs e (fun k v => he (a k) v) hd
    ((normalizer_sqtk D S).stronglyQuasithin 3 Nat.prime_three (by decide))
    ⟨x,hxM⟩ (Subtype.ext (hx ▸ pow_orderOf_eq_one x))


/-- Any cubic outside the original component forces every marked natural
multiplicity of the actual full orbit to be divisible by three. -/
theorem FullModuleNaturalCopies.three_dvd_of_cubic_outside
    {m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3)}
    (heven : Even S.field.degree) {s : ℕ} (h : FullModuleNaturalCopies D S m s)
    {x : G} (hxM : x ∈ normalizer (L : Set G)) (hx : orderOf x = 3)
    (hxL : x ∉ L) : 3 ∣ s := by
  by_contra hn
  exact hxL (sl3_orderThree_mem_of_fullModule_copies D S m heven hn h hxM hx)

/-- The exact remaining obstruction on the original input: an escaping
cubic requires a positive multiple of three copies and dimension 9nk. -/
theorem fullModule_sl3_triple_multiplicity_of_cubic_outside
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (heven : Even S.field.degree) {x : G}
    (hxM : x ∈ normalizer (L : Set G)) (hx : orderOf x = 3) (hxL : x ∉ L) :
    letI := fullModule_elementary D S
    ∃ k : ℕ, 0 < k ∧ FullModuleNaturalCopies D S m (3 * k) ∧
      Module.finrank (ZMod 2) (Additive (componentOrbit V (normalizer (L : Set G)))) =
        9 * S.field.degree * k := by
  let := fullModule_elementary D S
  obtain ⟨s,hs,h⟩ := fullModule_sl3_natural_copies D S m
  obtain ⟨k,hk⟩ := h.three_dvd_of_cubic_outside D S heven hxM hx hxL
  subst s
  refine ⟨k,by omega,h,?_⟩
  rw [h.finrank]
  ring

/-- Cubic containment can use a dimension divisibility obstruction instead
of the stronger strict bound below 9n. The preliminary source owner must
still discharge this premise from the ambient hypotheses. -/
theorem sl3_orderThree_mem_of_fullModule_finrank_not_dvd
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (heven : Even S.field.degree)
    (hd : letI := fullModule_elementary D S
      ¬ 9 * S.field.degree ∣ Module.finrank (ZMod 2)
        (Additive (componentOrbit V (normalizer (L : Set G)))))
    {x : G} (hxM : x ∈ normalizer (L : Set G)) (hx : orderOf x = 3) : x ∈ L := by
  by_contra hn
  obtain ⟨k,_,_,hk⟩ := fullModule_sl3_triple_multiplicity_of_cubic_outside D S m
    heven hxM hx hn
  exact hd ⟨k,hk⟩

/-- The elementary-three subgroup conclusion used in §§11.1--11.2, under
the same exact full-orbit dimension premise. -/
theorem sl3_elementaryThreeSubgroup_le_of_fullModule_finrank_not_dvd
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (heven : Even S.field.degree)
    (hd : letI := fullModule_elementary D S
      ¬ 9 * S.field.degree ∣ Module.finrank (ZMod 2)
        (Additive (componentOrbit V (normalizer (L : Set G)))))
    (P : Subgroup G) [IsElementaryAbelian 3 P]
    (hPM : P ≤ normalizer (L : Set G)) : P ≤ L := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro x hx
  by_cases hx1 : x = 1
  · exact hx1 ▸ L.one_mem
  · exact sl3_orderThree_mem_of_fullModule_finrank_not_dvd D S m heven hd (hPM hx)
      (orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian x hx) hx1)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary
