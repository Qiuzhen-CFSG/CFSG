module
public import Theory.Representation.BinaryAlternatingFiveExtension.Borel

/-!
# Kernel-preserving coordinates on the standard point Borel

The complement of the natural binary A₅ kernel restricts to the stabilizer
of the fifth point. Reconstructing this split extension preserves the given
kernel coordinates pointwise. Thus its vector flags can be transported
without imposing compatibility on an arbitrary abstract Borel equivalence.

Source: Aschbacher--Smith, the natural alternating-five extension in 2.4.29
and the marked point centralizers used in 14.6.9.
-/

public section
namespace BinaryPermutation.AlternatingFiveExtension
open Subgroup AlternatingFiveBorel

private theorem split_equiv_marked {G A W : Type*} [Group G] [Group A] [Group W]
    (Q K : Subgroup G) [Q.Normal] (hK : Q.IsComplement' K)
    (eA : (G ⧸ Q) ≃* A) (eQ : Q ≃* W) (ρ : A →* MulAut W)
    (he : ∀ (g : G) (u : Q), eQ (MulAut.conjNormal g u) =
      ρ (eA (QuotientGroup.mk' Q g)) (eQ u)) :
    ∃ e : G ≃* W ⋊[ρ] A, ∀ w : W,
      e.symm (SemidirectProduct.inl w) = (eQ.symm w : G) := by
  let eK := hK.symm.QuotientMulEquiv.symm.trans eA
  have heK (k : K) : eK k = eA (QuotientGroup.mk' Q k) := by
    apply congrArg eA
    change hK.symm.QuotientMulEquiv.symm k = QuotientGroup.mk' Q k
    apply hK.symm.QuotientMulEquiv.injective
    rw [MulEquiv.apply_symm_apply,quotientMulEquiv_mk_apply_of_isComplement']
  let γ : K →* MulAut Q := Q.normalizerMonoidHom.comp (inclusion (Q.normalizer_eq_top ▸ le_top))
  have hc (k : K) : (γ k).trans eQ = eQ.trans (ρ (eK k)) := by
    apply MulEquiv.ext
    intro u
    change eQ (MulAut.conjNormal (k:G) u) = ρ (eK k) (eQ u)
    rw [he,heK]
  refine ⟨(SemidirectProduct.mulEquivSubgroup hK).symm.trans
    (SemidirectProduct.congr eQ eK hc), ?_⟩
  intro w
  simp [SemidirectProduct.congr, SemidirectProduct.mulEquivSubgroup,
    SemidirectProduct.monoidHomSubgroup, SemidirectProduct.lift]

/-- The standard point-Borel equivalence preserves the given kernel coordinates. -/
theorem standard_borel_equiv_marked {G : Type*} [Group G] [Finite G]
    (q : G →* alternatingGroup (Fin 5)) (hq : Function.Surjective q) (e : q.ker ≃* V)
    (he : ∀ (g : G) (v : q.ker), e (MulAut.conjNormal g v) =
      Multiplicative.ofAdd (coreRepresentation (Fin 5) (q g).val (e v).toAdd)) :
    ∃ eb : (B.comap q) ≃* BorelModel, ∀ v : V,
      (eb.symm (SemidirectProduct.inl v) : G) = (e.symm v : G) := by
  obtain ⟨K, hK⟩ := exists_complement q hq e he
  let H := B.comap q
  let f : H →* B :=
    { toFun := fun g => ⟨q g, g.property⟩
      map_one' := Subtype.ext (map_one q)
      map_mul' := fun g h => Subtype.ext (map_mul q (g : G) (h : G)) }
  have hf : Function.Surjective f := by
    intro b
    obtain ⟨g, hg⟩ := hq b
    exact ⟨⟨g, show q g ∈ B from hg.symm ▸ b.property⟩, Subtype.ext hg⟩
  have hker : f.ker = q.ker.subgroupOf H := by
    ext g
    change (⟨q g, g.property⟩ : B) = 1 ↔ q g = 1
    exact Subtype.ext_iff
  have hle : q.ker ≤ H := by
    intro g hg
    change q g ∈ B
    rw [show q g = 1 from hg]
    exact B.one_mem
  let ek : f.ker ≃* q.ker := (MulEquiv.subgroupCongr hker).trans (subgroupOfEquivOfLe hle)
  have hKB : f.ker.IsComplement' (K.subgroupOf H) :=
    hker.symm ▸ hK.subgroupOf_overgroup hle
  obtain ⟨eb,heb⟩ := split_equiv_marked f.ker (K.subgroupOf H) hKB
    (QuotientGroup.quotientKerEquivOfSurjective f hf) (ek.trans e) borelAction (by
      intro g u
      change e (ek (MulAut.conjNormal g u)) =
        Multiplicative.ofAdd (coreRepresentation (Fin 5) (q g).val (e (ek u)).toAdd)
      have hh : ek (MulAut.conjNormal g u) = MulAut.conjNormal (g : G) (ek u) := by
        apply Subtype.ext
        rfl
      rw [hh]
      exact he g (ek u))
  refine ⟨eb, fun v => ?_⟩
  exact congrArg Subtype.val (heb v)
end BinaryPermutation.AlternatingFiveExtension
