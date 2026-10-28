module
public import Theory.Representation.BinaryAlternatingFiveExtension.Splitting
public import Theory.Representation.BinaryAlternatingFiveExtension.BorelModel
public import Theory.GroupTheory.SplitExtensionCoordinates

/-!
# Marked splitting of the natural binary A₅ extension

The natural extension splitting theorem supplies a complement. Its restriction
of the original quotient identifies that complement with A₅. Combining it with
the given kernel coordinates constructs the split isomorphism while retaining
both the literal quotient and kernel maps.

Source: Aschbacher–Smith, the single alternating case of 2.4.29.
-/

@[expose] public section
namespace BinaryPermutation.AlternatingFiveExtension
open Subgroup
local notation "A5" => alternatingGroup (Fin 5)
local notation "S5" => Equiv.Perm (Fin 5)

abbrev alternatingAction : A5 →* MulAut V := coreAction.comp (alternatingGroup (Fin 5)).subtype
abbrev AlternatingModel := V ⋊[alternatingAction] A5

theorem exists_marked_equiv {G : Type*} [Group G] [Finite G]
    (q : G →* A5) (hq : Function.Surjective q) (e : q.ker ≃* V)
    (he : ∀ (g : G) (v : q.ker), e (MulAut.conjNormal g v) =
      Multiplicative.ofAdd (coreRepresentation (Fin 5) (q g).val (e v).toAdd)) :
    ∃ E : G ≃* AlternatingModel,
      (∀ g, (E g).right = q g) ∧
      (∀ v : q.ker, E (v : G) = SemidirectProduct.inl (e v)) := by
  obtain ⟨K, hK⟩ := exists_complement q hq e he
  let eA := QuotientGroup.quotientKerEquivOfSurjective q hq
  let eK := hK.symm.QuotientMulEquiv.symm.trans eA
  have heK (k : K) : eK k = q k := by
    change eA (hK.symm.QuotientMulEquiv.symm k) = q k
    have hk : hK.symm.QuotientMulEquiv.symm k = QuotientGroup.mk' q.ker k := by
      apply hK.symm.QuotientMulEquiv.injective
      rw [MulEquiv.apply_symm_apply, quotientMulEquiv_mk_apply_of_isComplement']
    rw [hk]
    rfl
  let γ : K →* MulAut q.ker := q.ker.normalizerMonoidHom.comp
    (inclusion (q.ker.normalizer_eq_top ▸ le_top))
  have hc (k : K) : (γ k).trans e = e.trans (alternatingAction (eK k)) := by
    apply MulEquiv.ext
    intro v
    change e (MulAut.conjNormal (k : G) v) =
      Multiplicative.ofAdd (coreRepresentation (Fin 5) (eK k).val (e v).toAdd)
    rw [he, heK]
  let m := SemidirectProduct.mulEquivSubgroup hK
  let c := SemidirectProduct.congr e eK hc
  refine ⟨m.symm.trans c, ?_, ?_⟩
  · intro g
    obtain ⟨x, rfl⟩ := m.surjective g
    change (c (m.symm (m x))).right = q (m x)
    rw [m.symm_apply_apply]
    change eK x.right = q ((x.left : G) * (x.right : G))
    rw [map_mul, show q (x.left : G) = 1 from x.left.property, one_mul, heK]
  · intro v
    have hm : m (SemidirectProduct.inl v) = (v : G) := by
      change (v : G) * 1 = v
      exact mul_one _
    rw [← hm]
    change c (m.symm (m (SemidirectProduct.inl v))) = _
    rw [m.symm_apply_apply]
    ext <;> simp [c]

end BinaryPermutation.AlternatingFiveExtension
