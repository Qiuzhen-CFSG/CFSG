module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.PlaneMovement.NativeBounds

/-!
# The whole replacement cover before orbit recognition

The alternating component makes the whole moved subgroup a perfect central
cover of the natural four-space. The universal augmentation cover surjects
onto it. Any failure of equivariance for the larger actor lands in the
component-fixed kernel and vanishes on alternating commutators. Thus the
surjection is equivariant for the literal replacement projection even when
that projection has not yet been proved onto S₆.

The constant line is retained. This construction removes the orbit-selection
premise from the whole-cover transport needed to exclude the order-four
critical image. Source: MS93 (3.3), (3.6), printed pp.866--871; Aschbacher--Smith
I.1.5--6, printed p.408. The equivariance proof is adapted from
Theory/Representation/BinaryPermutationSixCover.lean.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender BinaryPermutation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.LocalImages
open LargeDistance PlaneMovement
private lemma core_map_equivariant
    {H U : Type*} [Group H] [AddCommGroup U] [Module (ZMod 2) U]
    (ρ : Representation (ZMod 2) H U) (eH : H →* Equiv.Perm (Fin 6)) (hinj : Function.Injective eH) (K : Subgroup H)
    (a : alternatingGroup (Fin 6) →* H)
    (ha : ∀ k, a k ∈ K) (hae : ∀ k, eH (a k) = k.val)
    (p : U →ₗ[ZMod 2] natural (Fin 6))
    (hp : ∀ g u, p (ρ g u) = naturalRepresentation (Fin 6) (eH g) (p u))
    (hker : p.ker ≤ fixedSpace ρ K)
    (f : core (Fin 6) →ₗ[ZMod 2] U)
    (hpf : ∀ v, p (f v) = coreToNatural (Fin 6) v)
    (hfa : ∀ g : alternatingGroup (Fin 6), ∀ v,
      f (coreRepresentation (Fin 6) g.val v) = ρ (a g) (f v))
    (g : H) (v : core (Fin 6)) :
    f (coreRepresentation (Fin 6) (eH g) v) = ρ g (f v) := by
  let d : core (Fin 6) →ₗ[ZMod 2] U :=
    f.comp (coreRepresentation (Fin 6) (eH g)) - (ρ g).comp f
  have hdker (v : core (Fin 6)) : d v ∈ p.ker := by
    change p (f (coreRepresentation (Fin 6) (eH g) v) - ρ g (f v)) = 0
    rw [map_sub, hpf, hp, hpf, coreToNatural_equivariant, sub_self]
  have hd (k : alternatingGroup (Fin 6)) (v : core (Fin 6)) :
      d (alternatingCoreRepresentation (Fin 6) k v) = d v := by
    let l : alternatingGroup (Fin 6) := ⟨eH g * k.val * (eH g)⁻¹,
      (inferInstance : (alternatingGroup (Fin 6)).Normal).conj_mem _ k.property _⟩
    have hal : a l = g * a k * g⁻¹ := by
      apply hinj
      simp only [map_mul, map_inv, hae]
      rfl
    have he : coreRepresentation (Fin 6) (eH g) (coreRepresentation (Fin 6) k.val v) =
        coreRepresentation (Fin 6) l.val (coreRepresentation (Fin 6) (eH g) v) := by
      simp [l, ← Module.End.mul_apply, ← map_mul]
    change f (coreRepresentation (Fin 6) (eH g) (coreRepresentation (Fin 6) k.val v)) -
      ρ g (f (coreRepresentation (Fin 6) k.val v)) = d v
    rw [he, hfa, hfa]
    have hh : ρ (a l) (ρ g (f v)) = ρ g (ρ (a k) (f v)) := by
      rw [hal]
      simp [← Module.End.mul_apply, ← map_mul]
    rw [← hh, ← map_sub]
    exact hker (hdker v) ⟨a l, ha l⟩
  have hz : Coinvariants.ker (alternatingCoreRepresentation (Fin 6)) ≤ d.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨k, v⟩, rfl⟩
    change d (_ - _) = 0
    rw [map_sub, hd, sub_self]
  rw [alternatingSix_core_generated] at hz
  exact sub_eq_zero.mp (hz (Submodule.mem_top : v ∈ ⊤))


private theorem core_surjection_on_image
    {H U : Type*} [Group H] [AddCommGroup U] [Module (ZMod 2) U]
    [FiniteDimensional (ZMod 2) U]
    (ρ : Representation (ZMod 2) H U)
    (e : H →* Equiv.Perm (Fin 6)) (hinj : Function.Injective e) (K : Subgroup H)
    (a : alternatingGroup (Fin 6) →* H)
    (ha : ∀ k, a k ∈ K) (hae : ∀ k, e (a k) = k.val)
    (hag : ∀ k ∈ K, ∃ g, a g = k)
    (p : U →ₗ[ZMod 2] natural (Fin 6))
    (hp : ∀ g u, p (ρ g u) = naturalRepresentation (Fin 6) (e g) (p u))
    (hsur : Function.Surjective p)
    (hker : p.ker ≤ fixedSpace ρ K)
    (hgen : Coinvariants.ker (ρ.comp K.subtype) = ⊤) :
    ∃ f : core (Fin 6) →ₗ[ZMod 2] U, Function.Surjective f ∧
      ∀ g v, f (coreRepresentation (Fin 6) (e g) v) = ρ g (f v) := by
  let σ : Representation (ZMod 2) (alternatingGroup (Fin 6)) U := ρ.comp a
  let P : σ.IntertwiningMap (alternatingNaturalRepresentation (Fin 6)) :=
    p.intertwiningMap_of_isIntertwiningMap _ _ (fun g u => by
      change p (ρ (a g) u) = naturalRepresentation (Fin 6) g.val (p u)
      rw [hp,hae])
  have hcoin : Coinvariants.ker σ = Coinvariants.ker (ρ.comp K.subtype) := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨⟨g,v⟩,rfl⟩
      exact Coinvariants.sub_mem_ker (⟨a g,ha g⟩ : K) v
    · apply Submodule.span_le.mpr
      rintro _ ⟨⟨k,v⟩,rfl⟩
      obtain ⟨g,hg⟩ := hag k k.property
      change ρ k.val v - v ∈ Coinvariants.ker σ
      rw [←hg]
      exact Coinvariants.sub_mem_ker g v
  have hP : Representation.OneCohomology.IsCover P :=
    ⟨hsur,fun v hv g => hker hv ⟨a g,ha g⟩,hcoin.trans hgen⟩
  obtain ⟨f,hf,hfa,hpf⟩ := SixCover.core_quotient_of_alternating_cover σ P hP
  exact ⟨f,hf,core_map_equivariant ρ e hinj K a ha hae p hp hker f hpf hfa⟩

universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : center (L ⧸ pCore 2 L) = ⊥) (hn : InitialNatural h e hz)
  (d : Replacement L R)

include h e hz hn in
theorem moved_cover_surjection :
    letI := replacementMoved_normal h d
    letI := moved_elementary h d
    ∃ f : core (Fin 6) →ₗ[ZMod 2] Additive (replacementMoved d),
      Function.Surjective f ∧
      ∀ g v, (f (coreRepresentation (Fin 6) (Recognition.sourceProjection h e hz hn d g) v)).toMul =
        MulAut.conjNormal g (f v).toMul := by
  let := replacementMoved_normal h d
  let := moved_elementary h d
  let W := replacementMoved d
  let K := replacementComponent d
  let q := Recognition.sourceProjection h e hz hn d
  let q' : d.overgroup →* q.range := q.rangeRestrict
  let hk : q'.ker = centralizer (W : Set d.overgroup) := by
    rw [MonoidHom.ker_rangeRestrict]
    exact (Recognition.sourceProjection_kernel h e hz hn d).trans
      (moved_centralizer h e hz hn d).symm
  let ρ : Representation (ZMod 2) q.range (Additive W) := NormalElementaryQuotient.representation W q' q.rangeRestrict_surjective hk
  let C := K.map q'
  have hAC : alternatingGroup (Fin 6) ≤ q.range := by
    rw [←Recognition.sourceProjection_component h e hz hn d]
    exact map_le_range _ _
  let a : alternatingGroup (Fin 6) →* q.range :=
    (alternatingGroup (Fin 6)).subtype.codRestrict q.range (fun g => hAC g.property)
  let p : Additive W →ₗ[ZMod 2] natural (Fin 6) :=
    (coverProjection h e hz hn d).toAdditiveLeft.toZModLinearMap 2
  have hp (g : q.range) (v : Additive W) :
      p (ρ g v) = naturalRepresentation (Fin 6) g.val (p v) := by
    obtain ⟨x,rfl⟩ := q.rangeRestrict_surjective g
    have hw := NormalElementaryQuotient.representation_apply W q' q.rangeRestrict_surjective hk x v
    have he := coverProjection_conjugate h e hz hn d x v.toMul (ρ (q' x) v).toMul hw
    change p (ρ (q' x) v) = replacementAction h e hz hn d x (p v) at he
    change p (ρ (q' x) v) = naturalRepresentation (Fin 6) (q x) (p v)
    rw [Recognition.sourceProjection_action]
    exact he
  have hsur : Function.Surjective p := by
    intro v
    obtain ⟨w,hw⟩ := coverProjection_surjective h e hz hn d (Multiplicative.ofAdd v)
    exact ⟨Additive.ofMul w,congrArg Multiplicative.toAdd hw⟩
  have hK : K.map q = alternatingGroup (Fin 6) := by
    change ((L.subgroupOf (L ⊔ R)).subgroupOf d.overgroup).map q = _
    rw [←replacement_residual h d]
    exact Recognition.sourceProjection_component h e hz hn d
  have hC : C = (alternatingGroup (Fin 6)).subgroupOf q.range := by
    apply map_injective q.range.subtype_injective
    rw [map_map,MonoidHom.subtype_comp_rangeRestrict,map_subgroupOf_eq_of_le hAC]
    exact hK
  have hfix : p.ker ≤ fixedSpace ρ C := by
    intro v hv g
    obtain ⟨k,hkK,he⟩ := g.property
    change ρ g.val v = v
    rw [←he]
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [NormalElementaryQuotient.representation_apply]
    have hvc : v.toMul ∈ (coverProjection h e hz hn d).ker := hv
    rw [coverProjection_kernel] at hvc
    exact mul_inv_eq_iff_eq_mul.mpr (hvc k hkK)
  have hWK : W ≤ K := by
    let := h.relative_normal
    intro w hw
    exact commutator_le_right (centralOmega L R) (L.subgroupOf (L ⊔ R)) hw
  have hc := NormalElementaryQuotient.coinvariants_image_eq_top W q'
    q.rangeRestrict_surjective hk K hWK (replacementMoved_idempotent h d)
  obtain ⟨f,hf,hfull⟩ := core_surjection_on_image ρ q.range.subtype
    q.range.subtype_injective C a (fun k => by rw [hC];exact k.property)
    (fun _ => rfl) (fun k hk => by
      have he : k.val ∈ alternatingGroup (Fin 6) := by
        have hh : k ∈ (alternatingGroup (Fin 6)).subgroupOf q.range := hC ▸ hk
        exact hh
      exact ⟨⟨k.val,he⟩,Subtype.ext rfl⟩) p hp hsur hfix hc
  refine ⟨f,hf,?_⟩
  intro g v
  change (f (coreRepresentation (Fin 6) (q.range.subtype (q' g)) v)).toMul = _
  rw [hfull (q' g)]
  apply Subtype.ext
  exact NormalElementaryQuotient.representation_apply W q' q.rangeRestrict_surjective hk g (f v)
end AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.LocalImages
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
