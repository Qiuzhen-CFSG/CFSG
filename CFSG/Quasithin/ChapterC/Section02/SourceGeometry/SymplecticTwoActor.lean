module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.MarkedConjugation
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.MovedNormalizerAction
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.CoreStarAction
public import Theory.SpecificGroups.SymplecticFour.Binary.DerivedSylowAction
/-!
# A marked transposition on the literal component core

The binary symplectic row identifies the whole actor with Sp4(2) and its
component with the derived A6. Lift a transposition through that actor and
the actual star quotient. Compatibility of the subgroup marking and the
core-to-star map gives its precise permutation action on the A6 quotient.

Source: Aschbacher–Smith B.4.2(3), C.2.7 and 15.3.21.
-/
public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterB.QuasisimpleSource
open Theory.SpecificGroups.SymplecticFour
variable {G : Type*} [Group G] (K R : Subgroup G)

theorem symplecticTwo_core_swap_actor (hR : R ≤ normalizer (K : Set G)) :
    let C := starImage K R K
    let J := offenderSubgroup (starRepresentation K R)
    ∀ (hCJ : C ≤ J)
      (s : MovedSection ((starRepresentation K R).comp J.subtype) (C.subgroupOf J))
      (H : Subgroup J)
      (e : MarkedActionEquiv s.action H (C.subgroupOf J)
        (symplecticNatural (k := ZMod 2) 2) (commutator (Sp (ZMod 2)))),
    let f := (((subgroupOfEquivOfLe hCJ).symm.trans e.subgroupEquiv).trans
      (Binary.derivedEquivAlternatingSix (F := ZMod 2) (by simp))).toMonoidHom.comp
        (coreToStar hR)
    ∃ r : normalizer (K : Set G), ∃ _hr : (r : G) ∈ K ⊔ R,
      ∀ x : K ⧸ pCore 2 K,
        f (quotientAut (pCore 2 K) (K.normalizerMonoidHom r) x) =
          AlternatingSix.ShadowLocal.permutationAction (Equiv.swap (0 : Fin 6) 1) (f x) := by
  intro C J hCJ s H e f
  let δ := Binary.derivedEquivAlternatingSix (F := ZMod 2) (by simp)
  let τ : Equiv.Perm (Fin 6) := Equiv.swap 0 1
  let a : Sp (ZMod 2) := (Binary.fieldEquivSp
    (Binary.fieldEquivZModTwo (ZMod 2) (by simp))).symm (Binary.symmetricSixEquiv τ)
  let h : H := e.action.groupEquiv.symm a
  let q := QuotientGroup.mk' (starKernel K R)
  obtain ⟨g,hg⟩ := QuotientGroup.mk'_surjective (starKernel K R) (h.val.val)
  let r : normalizer (K : Set G) := ⟨g, (sup_le K.le_normalizer hR) g.property⟩
  refine ⟨r,g.property,?_⟩
  intro x
  let l : C.subgroupOf J := (subgroupOfEquivOfLe hCJ).symm (coreToStar hR x)
  let y := AlternatingSix.ShadowLocal.permutationAction τ (δ (e.subgroupEquiv l))
  let l' : C.subgroupOf J := e.subgroupEquiv.symm (δ.symm y)
  have hh : e.action.groupEquiv h = a := e.action.groupEquiv.apply_symm_apply a
  have hd : δ.symm y = Binary.derivedPermutationAction (F := ZMod 2) (by simp) τ
      (e.subgroupEquiv l) := by
    apply δ.injective
    rw [δ.apply_symm_apply]
    apply Subtype.ext
    exact (Binary.derivedPermutationAction_apply (by simp) τ (e.subgroupEquiv l)).symm
  have hc : (δ.symm y : Sp (ZMod 2)) = a * (e.subgroupEquiv l : Sp (ZMod 2)) * a⁻¹ := by
    rw [hd]
    exact Binary.derivedPermutationAction_matrix (by simp) τ (e.subgroupEquiv l)
  have hm : MulAut.conjNormal (e.action.groupEquiv h) (e.subgroupEquiv l) = δ.symm y := by
    apply Subtype.ext
    rw [MulAut.conjNormal_apply,hh]
    exact hc.symm
  have he : (l' : J) = h.val * l.val * h.val⁻¹ := by
    have h' := e.marked_conjugation h l
    rw [hm] at h'
    exact h'
  have he' : l'.val.val = h.val.val * l.val.val * h.val.val⁻¹ := congrArg Subtype.val he
  have hproj : ((coreToStar hR (quotientAut (pCore 2 K) (K.normalizerMonoidHom r) x) : C) :
      StarQuotient K R) = l'.val.val := by
    rw [coreToStar_normalizer_action hR r g.property]
    change q g * (coreToStar hR x : StarQuotient K R) * (q g)⁻¹ = l'.val.val
    rw [hg,he']
    rfl
  have hp : (subgroupOfEquivOfLe hCJ).symm
      (coreToStar hR (quotientAut (pCore 2 K) (K.normalizerMonoidHom r) x)) = l' := by
    apply Subtype.ext
    apply Subtype.ext
    exact hproj
  change δ (e.subgroupEquiv ((subgroupOfEquivOfLe hCJ).symm
    (coreToStar hR (quotientAut (pCore 2 K) (K.normalizerMonoidHom r) x)))) = y
  rw [hp]
  change δ (e.subgroupEquiv (e.subgroupEquiv.symm (δ.symm y))) = y
  rw [e.subgroupEquiv.apply_symm_apply,δ.apply_symm_apply]
end CFSG.Quasithin.ChapterC.C27Source
