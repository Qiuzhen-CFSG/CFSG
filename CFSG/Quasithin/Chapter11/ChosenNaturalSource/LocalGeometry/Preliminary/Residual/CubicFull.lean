module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.Residual.CubicDouble
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.Residual.CubicSeed

/-!
# Cubic containment on the original full chosen-natural module

The action here is conjugation on V_M = ⟨V^{N_G(L)}⟩. A doubled natural
marking records a binary-linear isomorphism and its equations for the
original map L → L/O₂(L) → SL₃. CubicDouble supplies a preserved natural
constituent, without assuming that the original chosen seed is preserved.
The full-module elementary structure, quotient kernel and ambient rank
bound are all discharged from the original chosen input.

The final entry point joins this case with the proved V_M = V case.
Its multiplicity alternative remains explicit: source 11.0.3 homogeneity
alone does not prove it. Its discharge belongs to
qt-d-1222-natural-preliminary-source, before the final application in
qt-d-1222-natural-local-geometry.
Source: Aschbacher--Smith A.3.19, pp.54--55, and 11.0.4, p.760.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups IsMulCommutative
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

/-- Conjugation on the literal full normalizer orbit. -/
@[expose] def fullModuleConjugation :
    letI := fullModule_elementary D S
    Representation (ZMod 2) (normalizer (L : Set G))
      (Additive (componentOrbit V (normalizer (L : Set G)))) := by
  letI := fullModule_elementary D S
  let U := componentOrbit V (normalizer (L : Set G))
  let a := U.normalizerMonoidHom.comp (inclusion (le_normalizer_componentOrbit V _))
  exact {
    toFun g := (a g).toMonoidHom.toAdditive.toZModLinearMap 2
    map_one' := by
      apply LinearMap.ext
      intro v
      exact congrArg (fun b : MulAut U => Additive.ofMul (b v.toMul)) a.map_one
    map_mul' g h := by
      apply LinearMap.ext
      intro v
      exact congrArg (fun b : MulAut U => Additive.ofMul (b v.toMul)) (a.map_mul g h) }

/-- The actual two-copy marking used in A.3.19, with the component quotient
and both binary-linear intertwining equations specified. -/
@[expose] def FullModuleDoubleNatural
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3)) : Prop :=
  letI := fullModule_elementary D S
  ∃ e : Additive (componentOrbit V (normalizer (L : Set G))) ≃ₗ[ZMod 2]
      (Fin 3 → S.field.Carrier) × (Fin 3 → S.field.Carrier),
    ∀ (l : L) v, e (fullModuleConjugation D S (inclusion L.le_normalizer l) v) =
      ((m.groupEquiv (QuotientGroup.mk' (pCore 2 L) l)).val.mulVec (e v).1,
        (m.groupEquiv (QuotientGroup.mk' (pCore 2 L) l)).val.mulVec (e v).2)

/-- The cubic clause on the full orbit once its genuine two-copy marking
is supplied. No seed-invariance, constituent-selection or kernel premise remains. -/
theorem sl3_orderThree_mem_of_fullModule_double
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (heven : Even S.field.degree) (hdouble : FullModuleDoubleNatural D S m)
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
  obtain ⟨e,he⟩ := hdouble
  have hd : 3 ∣ Nat.card S.field.Carrier - 1 := by
    rw [S.field.card_eq]
    exact (Nat.BinaryTorusParity.three_dvd_sub_one_iff S.field.degree).mpr heven
  exact CubicNatural.cubic_mem_of_double_coordinates S.field K η hη hηker
    (fullModuleConjugation D S) e (fun k v => he (a k) v) hd
    ((normalizer_sqtk D S).stronglyQuasithin 3 Nat.prime_three (by decide))
    ⟨x,hxM⟩ (Subtype.ext (hx ▸ pow_orderOf_eq_one x))

/-- The one-copy and two-copy applications have the same literal source
conclusion. Establishing the multiplicity alternative remains with the
chosen-natural preliminary source owner. -/
theorem sl3_orderThree_mem_of_fullModule_multiplicity
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (heven : Even S.field.degree)
    (hmult : componentOrbit V (normalizer (L : Set G)) = V ∨
      FullModuleDoubleNatural D S m)
    {x : G} (hxM : x ∈ normalizer (L : Set G)) (hx : orderOf x = 3) : x ∈ L := by
  rcases hmult with heq | hd
  · exact sl3_orderThree_mem_of_fullModule_eq D S m heven heq hxM hx
  · exact sl3_orderThree_mem_of_fullModule_double D S m heven hd hxM hx

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary
