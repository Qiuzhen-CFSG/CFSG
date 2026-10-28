module
public import Theory.GroupTheory.SplitExtensionCoordinates

/-!
# Split coordinates retaining a given complement

Equivariant kernel coordinates and the original quotient map identify an
extension with a semidirect product. The supplied complement is retained
literally: its image is exactly the standard actor subgroup, while both
the quotient and the full kernel coordinates keep their original maps.
-/

public noncomputable section
namespace Subgroup
variable {G A W : Type*} [Group G] [Group A] [Group W]

/-- Mark the split extension using the given actual complement, preserving
the quotient, the full kernel coordinates, and the entire complement image. -/
theorem exists_marked_semidirect_equiv_of_given_complement
    (q : G →* A) (hq : Function.Surjective q) (e : q.ker ≃* W)
    (ρ : A →* MulAut W)
    (he : ∀ (g : G) (v : q.ker), e (MulAut.conjNormal g v) = ρ (q g) (e v))
    (K : Subgroup G) (hK : q.ker.IsComplement' K) :
    ∃ E : G ≃* W ⋊[ρ] A,
      (∀ g, (E g).right = q g) ∧
      (∀ v : q.ker, E (v : G) = SemidirectProduct.inl (e v)) ∧
      (∀ k : K, E (k : G) = SemidirectProduct.inr (q k)) ∧
      K.map E.toMonoidHom = (SemidirectProduct.inr : A →* W ⋊[ρ] A).range := by
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
  have hc (k : K) : (γ k).trans e = e.trans (ρ (eK k)) := by
    apply MulEquiv.ext
    intro v
    change e (MulAut.conjNormal (k : G) v) = ρ (eK k) (e v)
    rw [he, heK]
  let m := SemidirectProduct.mulEquivSubgroup hK
  let c := SemidirectProduct.congr e eK hc
  let E := m.symm.trans c
  have hcomp (k : K) : E (k : G) = SemidirectProduct.inr (q k) := by
    have hm : m (SemidirectProduct.inr k) = (k : G) := by
      change 1 * (k : G) = k
      exact one_mul _
    conv_lhs => rw [←hm]
    change c (m.symm (m (SemidirectProduct.inr k))) = _
    rw [m.symm_apply_apply]
    apply SemidirectProduct.ext
    · exact e.map_one
    · exact heK k
  refine ⟨E, ?_, ?_, hcomp, ?_⟩
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
    rw [←hm]
    change c (m.symm (m (SemidirectProduct.inl v))) = _
    rw [m.symm_apply_apply]
    ext <;> simp [c]
  · apply le_antisymm
    · rintro x ⟨k,hk,rfl⟩
      exact ⟨q k, (hcomp ⟨k,hk⟩).symm⟩
    · rintro x ⟨a,rfl⟩
      refine ⟨eK.symm a, (eK.symm a).property, ?_⟩
      exact (hcomp _).trans (congrArg SemidirectProduct.inr
        ((heK _).symm.trans (eK.apply_symm_apply a)))

end Subgroup
