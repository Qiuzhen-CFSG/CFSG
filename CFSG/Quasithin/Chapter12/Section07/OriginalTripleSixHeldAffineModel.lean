module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixHeldScalarComplement
public import Theory.AtlasPort.OtherSporadic.Mathieu.SextetStabilizer
import Theory.GroupTheory.SplitExtensionGivenComplement

/-!
# Marked affine coordinates on the original Held normalizer

The actual scalar-cubic complement and the full original conjugation action
identify the entire normalizer with the appropriate affine hexacode group.
The equivalence preserves every vector of the original U, the prescribed
K-action, and the whole normalizer of the actual scalar subgroup. Its actor
is either the even triple cover or the full hexacode group.

Source: Aschbacher--Smith12.7.7, printed p.841.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource Atlas.Codes
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- Affine coordinates retain the same original module, component action,
and actual scalar-cubic complement, in both possible actor groups. -/
theorem original_tripleSix_held_affine_model
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K)
    (hB : let H := centralizer ({(t : G)} : Set G)
      let Lt := (pResidual 2 (K ⊓ H : Subgroup G)).map (K ⊓ H).subtype
      IsComponent H ((conjugateSpanBy Lt H).subgroupOf H))
    (hcenter :
      let Lt := (pResidual 2 (K ⊓ centralizer ({(t : G)} : Set G) : Subgroup G)).map
        (K ⊓ centralizer ({(t : G)} : Set G)).subtype
      centerIn (conjugateSpanBy Lt (centralizer ({(t : G)} : Set G))) = tripleSixPoint D a t)
    (e :
      let Lt := (pResidual 2 (K ⊓ centralizer ({(t : G)} : Set G) : Subgroup G)).map
        (K ⊓ centralizer ({(t : G)} : Set G)).subtype
      let B := conjugateSpanBy Lt (centralizer ({(t : G)} : Set G))
      B ⧸ center B ≃* Matrix.PSL3Four.PSL) :
    let M := normalizer (K : Set G)
    ∃ R : Subgroup HexAutomorphisms, (R = hexSign.ker ∨ R = ⊤) ∧
      ∃ Y : Subgroup M, Nat.card Y = 3 ∧
        Y.map M.subtype ≤ tripleSixScalarResidual K ∧
        ∃ E : M ≃* Multiplicative hexacode ⋊[hexAffineAction.comp R.subtype] R,
          (∀ u : U, E (inclusion (D.le_component.trans K.le_normalizer) u) =
            SemidirectProduct.inl (tripleSixPointCoordinates D a u)) ∧
          (∀ k : K, ((E (inclusion K.le_normalizer k)).right : HexAutomorphisms) =
            (a.groupEquiv (QuotientGroup.mk' (pCore 2 K) k)).val) ∧
          (normalizer (Y : Set M)).map E.toMonoidHom =
            (SemidirectProduct.inr : R →*
              Multiplicative hexacode ⋊[hexAffineAction.comp R.subtype] R).range := by
  obtain ⟨f,hker,hcases,hmark,hact,_⟩ := original_tripleSix_held_local_model
    h structural D a t ht heven hB hcenter e
  obtain ⟨Y,hY,hYX,hcomp,_⟩ := original_tripleSix_held_scalar_complement
    h structural D a t ht heven hB hcenter e
  obtain ⟨_,_,hM,_,_⟩ := original_tripleSix_held_core_recovery
    h structural D a t ht heven hB hcenter e
  let M := normalizer (K : Set G)
  have hUM : U ≤ M := D.le_component.trans K.le_normalizer
  let q := f.rangeRestrict
  have hk : q.ker = U.subgroupOf M := by
    rw [show q = f.rangeRestrict from rfl,MonoidHom.ker_rangeRestrict,hker]
    apply map_injective M.subtype_injective
    rw [map_subgroupOf_eq_of_le hUM]
    exact hM
  let c := tripleSixPointCoordinates D a
  let v : q.ker ≃* U :=
    (MulEquiv.subgroupCongr hk).trans (subgroupOfEquivOfLe hUM)
  let w := v.trans c
  let ρ := hexAffineAction.comp f.range.subtype
  have hw (m : M) (u : q.ker) :
      w (MulAut.conjNormal m u) = ρ (q m) (w u) := by
    have hv : v (MulAut.conjNormal m u) = c.symm
        (Multiplicative.ofAdd (Hexacode.action (f m) (c (v u)).toAdd)) := by
      apply Subtype.ext
      exact (hact m (v u)).symm
    change c (v (MulAut.conjNormal m u)) = _
    rw [hv,c.apply_symm_apply]
    rfl
  obtain ⟨E,hEq,hEu,_,hEY⟩ := exists_marked_semidirect_equiv_of_given_complement
    q f.rangeRestrict_surjective w ρ hw (normalizer (Y : Set M)) (hk.symm ▸ hcomp)
  refine ⟨f.range,hcases,Y,hY,hYX,E,?_,?_,hEY⟩
  · intro u
    let u' : q.ker := ⟨inclusion hUM u,hk.symm ▸ u.property⟩
    exact hEu u'
  · intro k
    exact (congrArg Subtype.val (hEq (inclusion K.le_normalizer k))).trans (hmark k)

end CFSG.Quasithin.Chapter12.Section07
