module
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.Marking.EarlierCore.NaturalSetup
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.NaturalSix.Normalizer

/-!
# Extend the literal natural L-action to LT

Conjugation on V gives a linear action in the prescribed coordinates.
Normality of L in LT makes its image normalize the marked natural A₆.
The proved linear normalizer is S₆, so the entire action lifts uniquely
to permutations, retaining the given quotient marking of L.

Source: Aschbacher–Smith, setup preceding Notation 13.2.1, pp.876–877.
Only the intrinsic natural-module normalizer calculation is used.
-/

@[expose] public section
open Subgroup BinaryPermutation
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionParabolic.EarlierCore
variable {G : Type*} [Group G]

private def coordinateAction (X V : Subgroup G) (hXV : X ≤ normalizer (V : Set G))
    (e : V ≃* Multiplicative Natural) : Representation (ZMod 2) X Natural where
  toFun g := (AddMonoidHom.toMultiplicative.symm
    (e.toMonoidHom.comp ((V.normalizerMonoidHom (inclusion hXV g)).toMonoidHom.comp
      e.symm.toMonoidHom))).toZModLinearMap 2
  map_one' := by
    apply LinearMap.ext
    intro w
    change (e (V.normalizerMonoidHom (inclusion hXV 1)
      (e.symm (Multiplicative.ofAdd w)))).toAdd = w
    rw [map_one, map_one]
    exact congrArg Multiplicative.toAdd (e.apply_symm_apply _)
  map_mul' g h := by
    apply LinearMap.ext
    intro w
    change (e (V.normalizerMonoidHom (inclusion hXV (g * h))
      (e.symm (Multiplicative.ofAdd w)))).toAdd =
      (e (V.normalizerMonoidHom (inclusion hXV g)
        (e.symm (e (V.normalizerMonoidHom (inclusion hXV h)
          (e.symm (Multiplicative.ofAdd w))))))).toAdd
    rw [e.symm_apply_apply, map_mul, map_mul]
    rfl

/-- The full compatible LT permutation action follows from the prescribed
natural L-action. Thus that field of `NaturalSetup` need not be an extra
representation-theorem hypothesis. -/
theorem exists_permutation_extension (L T V : Subgroup G)
    (hTL : T ≤ normalizer (L : Set G))
    (hXV : L ⊔ T ≤ normalizer (V : Set G))
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (eV : V ≃* Multiplicative Natural)
    (he : ∀ (l : L) (v : V),
      (eV (V.normalizerMonoidHom
        ⟨l.val, hXV (show l.val ∈ L ⊔ T from (show L ≤ L ⊔ T from le_sup_left) l.property)⟩ v)).toAdd =
      alternatingNaturalRepresentation (Fin 6) (eL (QuotientGroup.mk' (pCore 2 L) l))
        (eV v).toAdd) :
    ∃ f : (L ⊔ T : Subgroup G) →* Equiv.Perm (Fin 6),
      (∀ l : L, f (inclusion le_sup_left l) = (eL (QuotientGroup.mk' (pCore 2 L) l)).val) ∧
      (∀ (g : (L ⊔ T : Subgroup G)) (v : V),
        (eV (V.normalizerMonoidHom ⟨g.val, hXV g.property⟩ v)).toAdd =
          naturalRepresentation (Fin 6) (f g) (eV v).toAdd) := by
  let ρ := coordinateAction (L ⊔ T) V hXV eV
  let γ := ρ.asGroupHom
  let K := L.subgroupOf (L ⊔ T)
  let : K.Normal := normal_subgroupOf_of_le_normalizer (sup_le L.le_normalizer hTL)
  have hγL (l : L) : γ (inclusion le_sup_left l) =
      ComponentSieve.SixAndG2.NaturalSix.alternatingHom (eL (QuotientGroup.mk' (pCore 2 L) l)) := by
    apply Units.ext
    apply LinearMap.ext
    intro w
    obtain ⟨v, rfl⟩ := eV.surjective (Multiplicative.ofAdd w)
    change (eV (V.normalizerMonoidHom _ (eV.symm (eV v)))).toAdd = _
    rw [eV.symm_apply_apply]
    exact he l v
  have hmap : K.map γ = ComponentSieve.SixAndG2.NaturalSix.alternatingImage := by
    apply le_antisymm
    · rintro _ ⟨l, hl, rfl⟩
      let lL : L := ⟨l.val, hl⟩
      exact ⟨eL (QuotientGroup.mk' (pCore 2 L) lL), (hγL lL).symm⟩
    · rintro _ ⟨a, rfl⟩
      obtain ⟨q, rfl⟩ := eL.surjective a
      obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) q
      exact ⟨inclusion le_sup_left l, l.property, hγL l⟩
  have hγmem (g : (L ⊔ T : Subgroup G)) :
      γ g ∈ ComponentSieve.SixAndG2.NaturalSix.symmetricImage := by
    rw [← ComponentSieve.SixAndG2.NaturalSix.normalizer_alternatingImage, ← hmap]
    apply K.le_normalizer_map γ
    exact ⟨g, by rw [K.normalizer_eq_top]; trivial, rfl⟩
  let γ' := γ.codRestrict ComponentSieve.SixAndG2.NaturalSix.symmetricImage hγmem
  let E := MonoidHom.ofInjective ComponentSieve.SixAndG2.NaturalSix.symmetricHom_injective
  let f := E.symm.toMonoidHom.comp γ'
  have hf (g : (L ⊔ T : Subgroup G)) :
      ComponentSieve.SixAndG2.NaturalSix.symmetricHom (f g) = γ g :=
    congrArg Subtype.val (E.apply_symm_apply (γ' g))
  refine ⟨f, ?_, ?_⟩
  · intro l
    apply ComponentSieve.SixAndG2.NaturalSix.symmetricHom_injective
    rw [hf, hγL]
    rfl
  · intro g v
    have hh := congrArg (fun u : ComponentSieve.SixAndG2.NaturalSix.LinearGroup =>
      u.val (eV v).toAdd) (hf g)
    change naturalRepresentation (Fin 6) (f g) (eV v).toAdd =
      (eV (V.normalizerMonoidHom _ (eV.symm (eV v)))).toAdd at hh
    rw [eV.symm_apply_apply] at hh
    exact hh.symm

end CFSG.Quasithin.Chapter13.Section08.TransvectionParabolic.EarlierCore
