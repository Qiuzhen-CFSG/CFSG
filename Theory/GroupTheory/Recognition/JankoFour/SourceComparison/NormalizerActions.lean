module
public import Theory.GroupTheory.Recognition.JankoFour.SourceComparison.SixCover
public import Theory.GroupTheory.PerfectCentralCoverAutomorphisms
public import Theory.GroupTheory.SylowThreeNormalizerSection

/-!
# Full normalizer actions on the original perfect six-cover

Every automorphism of a finite perfect M₂₂ cover lifts uniquely from its
simple quotient. In the original type-J₄ centralizer, the cubic normalizer
acts on the full six-cover and covers Aut(M₂₂) through the original map.
Perfectness makes the earlier six-cover comparison equivariant for every
pair of actors with matching projections. Such a target actor always exists.

The map N_H(A) → H/Q has kernel exactly Z(H), retaining the marked central
involution until it is explicitly quotiented. This supplies the action and
central-kernel steps of AS91 (8.3), p.606. Actor selection here is elementwise;
a multiplicative selection and an isomorphism of the original normalizers
are not yet asserted.
-/

@[expose] public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceComparison
open Subgroup SourceRecognition LocalGeometry Sporadic.Mathieu PerfectCentralCovering

/-- Every automorphism of M22 lifts uniquely to a genuine finite perfect cover. -/
theorem m22_cover_existsUnique_aut {E : Type*} [Group E] [Finite E]
    (f : Cover E M22) (a : MulAut M22) :
    ∃! b : MulAut E, ∀ x, f.toMonoidHom (b x) = a (f.toMonoidHom x) := by
  let g : Cover E M22 := {
    toMonoidHom := a.toMonoidHom.comp f.toMonoidHom
    surjective := a.surjective.comp f.surjective
    isPerfect := f.isPerfect
    ker_le_center := by
      rw [MonoidHom.ker_comp_of_injective _ _ a.injective]
      exact f.ker_le_center }
  obtain ⟨b,hb⟩ := exists_m22_cover_equiv_over g f (by
    change Nat.card (a.toMonoidHom.comp f.toMonoidHom).ker = _
    rw [MonoidHom.ker_comp_of_injective _ _ a.injective])
  refine ⟨b,hb,?_⟩
  intro c hc
  let := f.isPerfect
  apply MulEquiv.toMonoidHom_injective
  apply monoidHom_eq_of_isPerfect_of_comp_eq f.toMonoidHom f.ker_le_center
  apply MonoidHom.ext
  intro x
  exact (hc x).trans (hb x).symm

variable {G : Type*} [Group G] [Finite G] {z : G}
variable (h : IsTypeJ4 z)
variable (e : CubicAutomorphismQuotient (centralizer z ⧸ core z))
variable (X : Sylow 3 (CubicLift.subgroup e))

/-- The action of the original normalizer on the original six-cover. -/
noncomputable def cubicNormalizerAction :
    cubicNormalizerInH e X →* MulAut (cubicCentralizerInH e X) :=
  (cubicCentralizerInH e X).normalizerMonoidHom.comp
    (inclusion (normalizer_le_normalizer_centralizer (cubicSylowImage e X)))

theorem cubicNormalizerAction_apply (n : cubicNormalizerInH e X)
    (c : cubicCentralizerInH e X) :
    (cubicNormalizerAction e X n c : centralizer z) = n.val * c.val * n.val⁻¹ := rfl

/-- The original projection on the full normalizer. -/
noncomputable def cubicNormalizerProjection : cubicNormalizerInH e X →* MulAut M22 :=
  (CubicLift.projection e).comp (cubicNormalizerInH e X).subtype

theorem cubicCentralizerProjection_conj (c : cubicCentralizerInH e X) :
    MulAut.conj (cubicCentralizerProjection h e X c) = CubicLift.projection e c.val :=
  innerProjection_conj e (cubicCentralizerToInner h e X c)

/-- Equivariance uses the original quotient, rather than a separately chosen marking. -/
theorem cubicNormalizerAction_projection (n : cubicNormalizerInH e X)
    (c : cubicCentralizerInH e X) :
    cubicCentralizerProjection h e X (cubicNormalizerAction e X n c) =
      cubicNormalizerProjection e X n (cubicCentralizerProjection h e X c) := by
  apply conj_injective_of_center_eq_bot m22_center_eq_bot
  rw [cubicCentralizerProjection_conj]
  change CubicLift.projection e (n.val * c.val * n.val⁻¹) = _
  rw [map_mul,map_mul,map_inv,← cubicCentralizerProjection_conj h e X c]
  ext y
  simp [cubicNormalizerProjection]

include h in
theorem cubicNormalizerToCore_surjective : Function.Surjective
    ((QuotientGroup.mk' (core z)).comp (cubicNormalizerInH e X).subtype) := by
  intro y
  obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective (core z) y
  obtain ⟨q,n,he⟩ := exists_core_mul_cubicNormalizer e h X g
  refine ⟨n,?_⟩
  change QuotientGroup.mk' (core z) n.val = QuotientGroup.mk' (core z) g
  rw [← he,map_mul,show QuotientGroup.mk' (core z) q.val = 1 from
    (QuotientGroup.eq_one_iff q.val).mpr q.property,one_mul]

include h in
/-- The full normalizer still covers the entire specified automorphism group. -/
theorem cubicNormalizerProjection_surjective : Function.Surjective (cubicNormalizerProjection e X) :=
  e.surjective.comp (cubicNormalizerToCore_surjective h e X)

variable (hp : Group.IsPerfect (cubicCentralizerInH e X))

include h hp in
/-- Every automorphism of the six-cover is induced by its original normalizer. -/
theorem cubicNormalizerAction_surjective : Function.Surjective (cubicNormalizerAction e X) := by
  let f := cubicCentralizerCover h e X hp
  have hk : f.toMonoidHom.ker = center (cubicCentralizerInH e X) :=
    (cubicCentralizerProjection_ker h e X).trans (cubicCentralizer_center h e X hp).symm
  intro a
  obtain ⟨n,hn⟩ := cubicNormalizerProjection_surjective h e X (f.autMap hk a)
  refine ⟨n,?_⟩
  apply (f.autMap_injective hk)
  apply MulEquiv.ext
  intro x
  obtain ⟨c,rfl⟩ := f.surjective x
  rw [f.autMap_apply,f.autMap_apply]
  exact (cubicNormalizerAction_projection h e X n c).trans
    (by rw [hn]; exact f.autMap_apply hk a c)


include h in
/-- Normalizing the cubic inside Q already centralizes it. -/
theorem core_inf_cubicNormalizer :
    core z ⊓ cubicNormalizerInH e X = center (centralizer z) := by
  have hd : Disjoint (core z) (cubicSylowImage e X) := by
    apply disjoint_of_coprime_natCard
    rw [h.core_card,cubicSylowImage_card h e X]
    norm_num
  rw [SylowThreeNormalizer.normalizer_inf_eq_centralizer_inf (core z)
    (cubicSylowImage e X) (by rw [(core z).normalizer_eq_top]; exact le_top) hd]
  apply le_antisymm
  · intro n hn
    rw [← core_center_eq_centralizer_center h]
    exact mem_map_of_mem (core z).subtype
      ((core_cubic_centralizer h e X).le (show
        (⟨n,hn.1⟩ : core z) ∈ (cubicCentralizerInH e X).subgroupOf (core z) from hn.2))
  · exact le_inf (centralizer_center_le_core h) (center_le_centralizer _)

/-- The literal map to H/Q on the original normalizer. -/
noncomputable def cubicNormalizerToCore :
    cubicNormalizerInH e X →* centralizer z ⧸ core z :=
  (QuotientGroup.mk' (core z)).comp (cubicNormalizerInH e X).subtype

include h in
theorem cubicNormalizerToCore_ker :
    (cubicNormalizerToCore e X).ker =
      (center (centralizer z)).subgroupOf (cubicNormalizerInH e X) := by
  ext n
  change QuotientGroup.mk' (core z) n.val = 1 ↔ n.val ∈ center (centralizer z)
  change (QuotientGroup.mk n.val : centralizer z ⧸ core z) = 1 ↔ _
  rw [QuotientGroup.eq_one_iff]
  constructor
  · intro hn
    exact (core_inf_cubicNormalizer h e X).le ⟨hn,n.property⟩
  · exact fun hn => centralizer_center_le_core h hn

/-- Only the marked central involution is removed in passing from N to H/Q. -/
noncomputable def cubicNormalizerCentralQuotientEquiv :
    (cubicNormalizerInH e X ⧸
      (center (centralizer z)).subgroupOf (cubicNormalizerInH e X)) ≃*
        centralizer z ⧸ core z :=
  (QuotientGroup.quotientMulEquivOfEq (cubicNormalizerToCore_ker h e X).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (cubicNormalizerToCore e X)
      (cubicNormalizerToCore_surjective h e X))

variable {G' : Type*} [Group G'] [Finite G'] {z' : G'}
variable (h' : IsTypeJ4 z')
variable (e' : CubicAutomorphismQuotient (centralizer z' ⧸ core z'))
variable (X' : Sylow 3 (CubicLift.subgroup e'))

include hp in
/-- The constructed cover comparison intertwines every pair of normalizer
actors with the same original M22 automorphism. -/
theorem cubicCentralizerEquiv_intertwines
    (φ : cubicCentralizerInH e X ≃* cubicCentralizerInH e' X')
    (hφ : ∀ c, cubicCentralizerProjection h' e' X' (φ c) =
      cubicCentralizerProjection h e X c)
    (n : cubicNormalizerInH e X) (n' : cubicNormalizerInH e' X')
    (hn : cubicNormalizerProjection e' X' n' = cubicNormalizerProjection e X n)
    (c : cubicCentralizerInH e X) :
    φ (cubicNormalizerAction e X n c) = cubicNormalizerAction e' X' n' (φ c) := by
  let := hp
  have he : φ.toMonoidHom.comp (cubicNormalizerAction e X n).toMonoidHom =
      (cubicNormalizerAction e' X' n').toMonoidHom.comp φ.toMonoidHom := by
    apply monoidHom_eq_of_isPerfect_of_comp_eq
      (cubicCentralizerProjection h' e' X') (cubicCentralizerProjection_ker_le_center h' e' X')
    apply MonoidHom.ext
    intro x
    change cubicCentralizerProjection h' e' X' (φ (cubicNormalizerAction e X n x)) =
      cubicCentralizerProjection h' e' X' (cubicNormalizerAction e' X' n' (φ x))
    rw [hφ,cubicNormalizerAction_projection,cubicNormalizerAction_projection,hφ,hn]
  exact DFunLike.congr_fun he c


variable (hp' : Group.IsPerfect (cubicCentralizerInH e' X'))

include hp hp' in
/-- Comparison of the six-covers together with their full normalizer actions.
Every source actor has a target actor with the same original projection. -/
theorem exists_cubicCentralizer_equiv_equivariant :
    ∃ φ : cubicCentralizerInH e X ≃* cubicCentralizerInH e' X',
      (∀ c, cubicCentralizerProjection h' e' X' (φ c) = cubicCentralizerProjection h e X c) ∧
      ((cubicSylowImage e X).subgroupOf (cubicCentralizerInH e X)).map φ.toMonoidHom =
        (cubicSylowImage e' X').subgroupOf (cubicCentralizerInH e' X') ∧
      φ (cubicMarker e X) = cubicMarker e' X' ∧
      (∀ n : cubicNormalizerInH e X, ∃ n' : cubicNormalizerInH e' X',
        cubicNormalizerProjection e' X' n' = cubicNormalizerProjection e X n ∧
        ∀ c, φ (cubicNormalizerAction e X n c) = cubicNormalizerAction e' X' n' (φ c)) := by
  obtain ⟨φ,hφ,ha,hz⟩ := exists_cubicCentralizer_equiv h e X hp h' e' X' hp'
  refine ⟨φ,hφ,ha,hz,?_⟩
  intro n
  obtain ⟨n',hn⟩ := cubicNormalizerProjection_surjective h' e' X' (cubicNormalizerProjection e X n)
  exact ⟨n',hn,cubicCentralizerEquiv_intertwines h e X hp h' e' X' φ hφ n n' hn⟩

end Theory.GroupTheory.Recognition.JankoFour.SourceComparison
