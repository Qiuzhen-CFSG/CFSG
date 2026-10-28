module
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.SourceModule
public import Theory.Mathieu.M22.TripleCover.ScalarAutomorphisms
public import Theory.GroupTheory.CoprimeSubgroupCentralizer

/-!
# The actual cubic centralizer in H/⟨z⟩

The full inner inverse image in H/Q is the perfect triple cover. An
automorphism fixing its central cubic scalar is inner, so its centralizer
in H/Q is exactly that inverse image. Coprime centralizer lifting through
Q and through Z(H) identifies C_{H/Z(H)}(X) with this same cover. The
kernel vanishes by the proved identity C_Q(X) = Z(Q) = Z(H).

Every map is induced by the original quotient H/Z(H) → H/Q. The earlier
`IsTypeJ4.centralizer_center_image` identifies Z(H) with the marked ⟨z⟩.
Thus this constructs the quasisimple centralizer in Aschbacher–Segev,
*The uniqueness of groups of type J₄*, Invent. Math. 105 (1991), (4.1),
printed p.597, DOI 10.1007/BF01232280, rather than substituting a cover
inside a different quotient. Its module action is retained in `CubicModule`.
-/

@[expose] public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
open Subgroup LocalGeometry Sporadic.Mathieu Representation

section Extension
variable {H : Type*} [Group H] (e : CubicAutomorphismQuotient H)

instance innerPreimage_normal : (innerPreimage e).Normal := by
  change ((MulAut.innerSubgroup M22).comap e.projection).Normal
  infer_instance

private theorem projection_conjugation (g : H) (x : innerPreimage e) :
    innerProjection e (MulAut.conjNormal g x) = e.projection g (innerProjection e x) := by
  apply conj_injective_of_center_eq_bot m22_center_eq_bot
  rw [innerProjection_conj]
  change e.projection (g * x * g⁻¹) = _
  rw [map_mul, map_mul, map_inv, ← innerProjection_conj e x]
  ext y
  simp

private theorem innerPreimage_center_le_kernel (x : innerPreimage e)
    (hx : x ∈ center (innerPreimage e)) : (x : H) ∈ e.projection.ker := by
  apply (innerProjection_ker_iff e x).mp
  change innerProjection e x = 1
  apply mem_bot.mp
  rw [← m22_center_eq_bot]
  apply mem_center_iff.mpr
  intro y
  obtain ⟨w,rfl⟩ := innerProjection_surjective e y
  rw [← map_mul, ← map_mul]
  exact congrArg (innerProjection e) (mem_center_iff.mp hx w)

private theorem kernel_le_innerPreimage : e.projection.ker ≤ innerPreimage e := by
  intro x hx
  change e.projection x ∈ MulAut.innerSubgroup M22
  rw [hx]
  exact one_mem _

private theorem centralizer_innerPreimage_le_kernel :
    Subgroup.centralizer (innerPreimage e : Set H) ≤ e.projection.ker := by
  intro g hg
  change e.projection g = 1
  apply MulEquiv.ext
  intro y
  obtain ⟨x,rfl⟩ := innerProjection_surjective e y
  change e.projection g (innerProjection e x) = innerProjection e x
  rw [← projection_conjugation]
  apply congrArg (innerProjection e)
  apply Subtype.ext
  change g * (x : H) * g⁻¹ = x
  rw [← hg x x.property, mul_inv_cancel_right]

/-- Fixing the central cubic scalar forces an inner automorphism of the
actual cover; the remaining centralizer is already in the cubic kernel. -/
theorem centralizer_cubicKernel_of_triple (ec : innerPreimage e ≃* M22TripleCover) :
    Subgroup.centralizer (e.projection.ker : Set H) = innerPreimage e := by
  apply le_antisymm
  · intro g hg
    let α : MulAut M22TripleCover := MulAut.congr ec (MulAut.conjNormal g)
    have hscalar : α M22TripleCover.scalar = M22TripleCover.scalar := by
      have hfix : MulAut.conjNormal g (ec.symm M22TripleCover.scalar) =
          ec.symm M22TripleCover.scalar := by
        apply Subtype.ext
        change g * (ec.symm M22TripleCover.scalar : H) * g⁻¹ = ec.symm M22TripleCover.scalar
        have hc := innerPreimage_center_le_kernel e _ (M22TripleCover.scalar_mem_center_of_equiv ec)
        rw [← hg _ hc, mul_inv_cancel_right]
      exact (congrArg ec hfix).trans (ec.apply_symm_apply M22TripleCover.scalar)
    obtain ⟨x,hx⟩ := M22TripleCover.ScalarAutomorphisms.inner_of_fixes_scalar α hscalar
    have hi : MulAut.conjNormal g = MulAut.conj (ec.symm x) := by
      apply (MulAut.congr ec).injective
      rw [MulAut.congr_conj, ec.apply_symm_apply]
      exact hx
    have hm : g ∈ (MulAut.innerSubgroup (innerPreimage e)).comap
        (MulAut.conjNormal : H →* MulAut (innerPreimage e)) := ⟨ec.symm x,hi.symm⟩
    rw [MulAut.conjNormal_comap_innerSubgroup] at hm
    exact (sup_le le_rfl ((centralizer_innerPreimage_le_kernel e).trans
      (kernel_le_innerPreimage e))) hm
  · intro g hg k hk
    let k' : innerPreimage e := ⟨k,kernel_le_innerPreimage e hk⟩
    have hc := innerProjection_kernel_central e ((innerProjection_ker_iff e k').mpr hk)
    exact (congrArg Subtype.val (mem_center_iff.mp hc (⟨g,hg⟩ : innerPreimage e))).symm
end Extension

variable {G : Type*} [Group G] [Finite G] {z : G} (h : IsTypeJ4 z)
variable (e : CubicAutomorphismQuotient ((centralizer z) ⧸ core z))
variable (X : Sylow 3 (CubicLift.subgroup e))
include h

/-- In the source extension the cubic kernel centralizer is the full inner preimage. -/
theorem centralizer_cubicKernel :
    Subgroup.centralizer (e.projection.ker : Set ((centralizer z) ⧸ core z)) = innerPreimage e :=
  centralizer_cubicKernel_of_triple e (innerPreimageTripleEquiv h e)

/-- The source Sylow maps onto the retained cubic kernel under the original quotient. -/
theorem cubicSylow_map_coreQuotient :
    (cubicSylowImage e X).map (QuotientGroup.mk' (core z)) = e.projection.ker := by
  ext y
  constructor
  · rintro ⟨x,⟨w,hw,rfl⟩,rfl⟩
    exact (cubicKernelEquiv e h X ⟨w,hw⟩).property
  · intro hy
    obtain ⟨x,hx⟩ := (cubicKernelEquiv e h X).surjective ⟨y,hy⟩
    exact ⟨x.val,mem_map_of_mem (CubicLift.subgroup e).subtype x.property,
      congrArg Subtype.val hx⟩

/-- Coprime lifting identifies the image of the original cubic centralizer. -/
theorem cubicCentralizer_map_coreQuotient :
    (Subgroup.centralizer (cubicSylowImage e X : Set (centralizer z))).map
      (QuotientGroup.mk' (core z)) = innerPreimage e := by
  have hc : Nat.Coprime 3 (Nat.card (QuotientGroup.mk' (core z)).ker) := by
    rw [QuotientGroup.ker_mk', h.core_card]
    norm_num
  rw [map_centralizer_eq_of_isPGroup_of_surjective_coprime 3 (cubicSylowImage e X)
    (X.isPGroup'.map (CubicLift.subgroup e).subtype) _ (QuotientGroup.mk'_surjective _) hc,
    cubicSylow_map_coreQuotient h e X, centralizer_cubicKernel h e]

theorem centralizer_center_card : Nat.card (center (centralizer z)) = 2 := by
  have hc := congrArg (fun S : Subgroup G => Nat.card S) h.centralizer_center_image
  rw [card_map_of_injective (centralizer z).subtype_injective,
    Nat.card_zpowers,h.involution] at hc
  exact hc

theorem centralizer_center_le_core : center (centralizer z) ≤ core z := by
  rw [← core_center_eq_centralizer_center h]
  exact map_subtype_le _

/-- The source H/⟨z⟩, with the center identified with the marked line. -/
abbrev CenterQuotient := centralizer z ⧸ center (centralizer z)

/-- The literal quotient map from H/⟨z⟩ to H/Q. -/
noncomputable def centerToCoreProjection : CenterQuotient (z := z) →* centralizer z ⧸ core z :=
  QuotientGroup.map _ _ (MonoidHom.id _) (centralizer_center_le_core h)

@[simp] theorem centerToCoreProjection_mk (g : centralizer z) :
    centerToCoreProjection h (QuotientGroup.mk' (center (centralizer z)) g) =
      QuotientGroup.mk' (core z) g := rfl

/-- The literal source centralizer of the cubic image in H/⟨z⟩. -/
noncomputable def cubicCentralizer : Subgroup (CenterQuotient (z := z)) :=
  Subgroup.centralizer ((cubicSylowImage e X).map
    (QuotientGroup.mk' (center (centralizer z))) : Set (CenterQuotient (z := z)))

theorem cubicCentralizer_map_centerQuotient :
    (Subgroup.centralizer (cubicSylowImage e X : Set (centralizer z))).map
      (QuotientGroup.mk' (center (centralizer z))) = cubicCentralizer e X := by
  have hc : Nat.Coprime 3 (Nat.card (QuotientGroup.mk' (center (centralizer z))).ker) := by
    rw [QuotientGroup.ker_mk', centralizer_center_card h]
    decide
  exact map_centralizer_eq_of_isPGroup_of_surjective_coprime 3 (cubicSylowImage e X)
    (X.isPGroup'.map (CubicLift.subgroup e).subtype) _ (QuotientGroup.mk'_surjective _) hc

/-- Restriction of the original quotient map to the source centralizer. -/
noncomputable def cubicCentralizerProjection : cubicCentralizer e X →* innerPreimage e :=
  ((centerToCoreProjection h).comp (cubicCentralizer e X).subtype).codRestrict
    (innerPreimage e) (fun c => by
      have hc := (cubicCentralizer_map_centerQuotient h e X).ge c.property
      obtain ⟨g,hg,hgc⟩ := hc
      change centerToCoreProjection h c.val ∈ innerPreimage e
      rw [← hgc,centerToCoreProjection_mk]
      exact (cubicCentralizer_map_coreQuotient h e X).le (mem_map_of_mem _ hg))

@[simp] theorem cubicCentralizerProjection_apply (c : cubicCentralizer e X) :
    (cubicCentralizerProjection h e X c : centralizer z ⧸ core z) =
      centerToCoreProjection h c.val := rfl

theorem cubicCentralizerProjection_injective : Function.Injective (cubicCentralizerProjection h e X) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_bot_iff.mp
  intro c hc
  have hlift := (cubicCentralizer_map_centerQuotient h e X).ge c.property
  obtain ⟨g,hg,hgc⟩ := hlift
  have hq : QuotientGroup.mk' (core z) g = 1 := by
    have he := congrArg Subtype.val hc
    change centerToCoreProjection h c.val = 1 at he
    rwa [← hgc, centerToCoreProjection_mk] at he
  have hgQ : g ∈ core z := (QuotientGroup.eq_one_iff g).mp hq
  have hgZ : g ∈ center (centralizer z) := by
    rw [← core_center_eq_centralizer_center h]
    apply mem_map_of_mem (core z).subtype (x := (⟨g,hgQ⟩ : core z))
    exact (core_cubic_centralizer h e X).le hg
  apply Subtype.ext
  exact hgc.symm.trans ((QuotientGroup.eq_one_iff g).mpr hgZ)

theorem cubicCentralizerProjection_surjective : Function.Surjective (cubicCentralizerProjection h e X) := by
  intro y
  obtain ⟨g,hg,hgy⟩ := (cubicCentralizer_map_coreQuotient h e X).ge y.property
  refine ⟨⟨QuotientGroup.mk' (center (centralizer z)) g,
    (cubicCentralizer_map_centerQuotient h e X).le (mem_map_of_mem _ hg)⟩, ?_⟩
  exact Subtype.ext hgy

/-- The centralizer in H/⟨z⟩ is identified through its original projection. -/
noncomputable def cubicCentralizerEquiv : cubicCentralizer e X ≃* innerPreimage e :=
  MulEquiv.ofBijective (cubicCentralizerProjection h e X)
    ⟨cubicCentralizerProjection_injective h e X,cubicCentralizerProjection_surjective h e X⟩

/-- The native marking of the source centralizer, with its full cubic center retained. -/
noncomputable def cubicCentralizerTripleEquiv : cubicCentralizer e X ≃* M22TripleCover :=
  (cubicCentralizerEquiv h e X).trans (innerPreimageTripleEquiv h e)

/-- The quasisimplicity clause of AS91 (4.1) for its literal centralizer. -/
theorem cubicCentralizer_quasisimple : IsQuasisimple (cubicCentralizer e X) :=
  IsQuasisimple.of_mulEquiv (cubicCentralizerTripleEquiv h e X).symm

end Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
end
