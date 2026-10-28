module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.NaturalSix.MultiplicativeNormalizer
public import Theory.Representation.BinaryPermutationSixCover.Universal
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AutomorphismAction
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AlternatingSixCoverCoordinates
public import Theory.GroupTheory.LocalNormalizerUniqueness

/-!
# The full six-letter action in the rank-five source branch

An order-32 alternating-six block has the full augmentation module. Its
normalizer action on the natural quotient comes from S₆. That permutation
lifts uniquely to the full core: the difference of two lifts lands in the
fixed line and vanishes on all alternating commutators. The final interface
retains the original ambient module and literal conjugation action.

Source: Aschbacher–Smith B.3 and 14.6.10(5), printed pp.1029–1030.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.OneCohomology BinaryPermutation
namespace CFSG.Quasithin.Chapter14.Section06.RankFiveNaturalSix
open Chapter13.Section08.ComponentSieve.SixAndG2.NaturalSix

private theorem core_lift_eq
    (F : core (Fin 6) →ₗ[ZMod 2] core (Fin 6))
    (φ : alternatingGroup (Fin 6) →* alternatingGroup (Fin 6))
    (g : Equiv.Perm (Fin 6))
    (hF : ∀ k u, F (coreRepresentation (Fin 6) k.val u) =
      coreRepresentation (Fin 6) (φ k).val (F u))
    (hp : ∀ u, coreToNatural (Fin 6) (F u) =
      naturalRepresentation (Fin 6) g (coreToNatural (Fin 6) u)) :
    ∀ u, F u = coreRepresentation (Fin 6) g u := by
  have hactor (k : alternatingGroup (Fin 6)) : (φ k).val * g = g * k.val := by
    apply symmetricAction_injective
    apply LinearMap.ext
    intro v
    obtain ⟨u,rfl⟩ := coreToNatural_surjective v
    calc
      _ = naturalRepresentation (Fin 6) (φ k).val (naturalRepresentation (Fin 6) g
        (coreToNatural (Fin 6) u)) := by rw [map_mul,Module.End.mul_apply]
      _ = coreToNatural (Fin 6) (coreRepresentation (Fin 6) (φ k).val (F u)) := by
        rw [coreToNatural_equivariant,hp]
      _ = coreToNatural (Fin 6) (F (coreRepresentation (Fin 6) k.val u)) := by rw [hF]
      _ = _ := by rw [hp,coreToNatural_equivariant,map_mul,Module.End.mul_apply]
  let d : core (Fin 6) →ₗ[ZMod 2] core (Fin 6) := F - coreRepresentation (Fin 6) g
  have hker (v : core (Fin 6)) : coreToNatural (Fin 6) (d v) = 0 := by
    change coreToNatural (Fin 6) (F v - coreRepresentation (Fin 6) g v) = 0
    rw [map_sub,hp,coreToNatural_equivariant,sub_self]
  have hfixed (v : core (Fin 6)) (k : alternatingGroup (Fin 6)) :
      coreRepresentation (Fin 6) k.val (d v) = d v := by
    exact alternatingSix_coreProjection_isCover.2.1 (hker v) k
  have hd (k : alternatingGroup (Fin 6)) (v : core (Fin 6)) :
      d (alternatingCoreRepresentation (Fin 6) k v) = d v := by
    change F (coreRepresentation (Fin 6) k.val v) -
      coreRepresentation (Fin 6) g (coreRepresentation (Fin 6) k.val v) = d v
    rw [hF]
    have he : coreRepresentation (Fin 6) g (coreRepresentation (Fin 6) k.val v) =
        coreRepresentation (Fin 6) (φ k).val (coreRepresentation (Fin 6) g v) := by
      rw [←Module.End.mul_apply,←map_mul,←hactor, map_mul,Module.End.mul_apply]
    rw [he,←map_sub]
    exact hfixed v (φ k)
  have hz : Coinvariants.ker (alternatingCoreRepresentation (Fin 6)) ≤ d.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨k,v⟩,rfl⟩
    change d (_ - _) = 0
    rw [map_sub,hd,sub_self]
  rw [alternatingSix_core_generated] at hz
  intro u
  exact sub_eq_zero.mp (hz (Submodule.mem_top : u ∈ ⊤))

open ChapterC
variable {L : Type*} [Group L]
private theorem moduleAction_normalizes (m : BlockModuleModel L AlternatingSixCover.action) (a : MulAut L) :
    m.moduleAction a ∈ normalizer (AlternatingSixCover.action.range : Set (MulAut (Multiplicative (natural (Fin 6))))) := by
  apply mem_normalizer_iff.mpr
  intro u
  constructor
  · rintro ⟨g,rfl⟩
    refine ⟨m.quotientAction a g,?_⟩
    ext v : 1
    have he := m.actions_compatible a g ((m.moduleAction a).symm v)
    simpa only [MulEquiv.apply_symm_apply,MulAut.mul_apply,MulAut.inv_apply] using he.symm
  · intro hu
    obtain ⟨g,hg⟩ := hu
    refine ⟨(m.quotientAction a).symm g,?_⟩
    apply (MulAut.conj (m.moduleAction a)).injective
    have he : (m.moduleAction a) * AlternatingSixCover.action ((m.quotientAction a).symm g) *
        (m.moduleAction a)⁻¹ = AlternatingSixCover.action g := by
      ext v : 1
      have hh := m.actions_compatible a ((m.quotientAction a).symm g)
        ((m.moduleAction a).symm v)
      simpa only [MulEquiv.apply_symm_apply,MulAut.mul_apply,MulAut.inv_apply] using hh
    exact he.trans hg

/-- Every block automorphism acts on the full core by a permutation of the same six letters. -/
theorem automorphism_core_coordinates
    (m : BlockModuleModel L AlternatingSixCover.action)
    (E : blockU L ≃* Multiplicative (core (Fin 6)))
    (hE : ∀ l u, (E (blockConjugate L l u)).toAdd =
      coreRepresentation (Fin 6) (m.quotientIso (QuotientGroup.mk' (pCore 2 L) l)).val (E u).toAdd)
    (hq : ∀ u, coreToNatural (Fin 6) (E u).toAdd =
      (m.moduleIso (QuotientGroup.mk' (blockFixed L) u)).toAdd)
    (a : MulAut L) :
    ∃ g : Equiv.Perm (Fin 6), ∀ u,
      (E (MulAut.characteristic (blockU L) a u)).toAdd =
        coreRepresentation (Fin 6) g (E u).toAdd := by
  obtain ⟨g,hg⟩ := exists_permutation_of_normalizes_alternatingMulImage
    (m.moduleAction a) (moduleAction_normalizes m a)
  let δ : MulAut (Multiplicative (core (Fin 6))) :=
    (MulAut.congr E) (MulAut.characteristic (blockU L) a)
  let F : core (Fin 6) →ₗ[ZMod 2] core (Fin 6) :=
    (AddEquiv.toMultiplicative.symm δ).toAddMonoidHom.toZModLinearMap 2
  have hf (u : blockU L) : F (E u).toAdd =
      (E (MulAut.characteristic (blockU L) a u)).toAdd := by
    change (E (MulAut.characteristic (blockU L) a (E.symm (E u)))).toAdd = _
    rw [E.symm_apply_apply]
  let φ : MulAut (alternatingGroup (Fin 6)) :=
    (MulAut.congr m.quotientIso) (quotientAut (pCore 2 L) a)
  have hF (k : alternatingGroup (Fin 6)) (v : core (Fin 6)) :
      F (coreRepresentation (Fin 6) k.val v) =
        coreRepresentation (Fin 6) (φ k).val (F v) := by
    obtain ⟨l,rfl⟩ := m.quotientIso.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 L)) k
    obtain ⟨u,hu⟩ := E.surjective (Multiplicative.ofAdd v)
    have hv : (E u).toAdd = v := congrArg Multiplicative.toAdd hu
    change F (coreRepresentation (Fin 6) (m.quotientIso (QuotientGroup.mk' (pCore 2 L) l)).val v) = _
    have hφ : φ (m.quotientIso (QuotientGroup.mk' (pCore 2 L) l)) =
        m.quotientIso (QuotientGroup.mk' (pCore 2 L) (a l)) := by
      change m.quotientIso (quotientAut (pCore 2 L) a (m.quotientIso.symm (m.quotientIso _))) = _
      rw [m.quotientIso.symm_apply_apply,quotientAut_apply_mk]
    simp only [Function.comp_apply]
    rw [←hv,hφ,←hE,hf,hf]
    have he : MulAut.characteristic (blockU L) a (blockConjugate L l u) =
        blockConjugate L (a l) (MulAut.characteristic (blockU L) a u) := by
      apply Subtype.ext
      change a (l * (u : L) * l⁻¹) = a l * a (u : L) * (a l)⁻¹
      simp only [map_mul,map_inv]
    rw [he,hE]
  have hp (v : core (Fin 6)) : coreToNatural (Fin 6) (F v) =
      naturalRepresentation (Fin 6) g (coreToNatural (Fin 6) v) := by
    obtain ⟨u,hu⟩ := E.surjective (Multiplicative.ofAdd v)
    have hv : (E u).toAdd = v := congrArg Multiplicative.toAdd hu
    rw [←hv,hf,hq,hq,←m.moduleAction_mk,←hg]
    rfl
  refine ⟨g,fun u => ?_⟩
  rw [←hf]
  exact core_lift_eq F φ.toMonoidHom g hF hp _


/-- The unique six-letter actions assemble to a homomorphism on the block automorphism group. -/
theorem exists_automorphism_actor
    (m : BlockModuleModel L AlternatingSixCover.action)
    (E : blockU L ≃* Multiplicative (core (Fin 6)))
    (hE : ∀ l u, (E (blockConjugate L l u)).toAdd =
      coreRepresentation (Fin 6) (m.quotientIso (QuotientGroup.mk' (pCore 2 L) l)).val (E u).toAdd)
    (hq : ∀ u, coreToNatural (Fin 6) (E u).toAdd =
      (m.moduleIso (QuotientGroup.mk' (blockFixed L) u)).toAdd) :
    ∃ f : MulAut L →* Equiv.Perm (Fin 6), ∀ a u,
      (E (MulAut.characteristic (blockU L) a u)).toAdd =
        coreRepresentation (Fin 6) (f a) (E u).toAdd := by
  choose g hg using automorphism_core_coordinates m E hE hq
  have hsur : Function.Surjective (fun u : blockU L => (E u).toAdd) :=
    Multiplicative.toAdd.surjective.comp E.surjective
  refine ⟨{ toFun := g, map_one' := ?_, map_mul' := ?_ },hg⟩
  · apply coreAction_injective
    ext v
    obtain ⟨u,rfl⟩ := hsur v
    rw [←hg]
    simp
  · intro a b
    apply coreAction_injective
    ext v
    obtain ⟨u,rfl⟩ := hsur v
    rw [map_mul,Module.End.mul_apply,←hg,←hg,←hg]
    rfl
end CFSG.Quasithin.Chapter14.Section06.RankFiveNaturalSix

namespace CFSG.Quasithin.Chapter14.Section06.RankFiveNaturalSix
open ChapterC
variable {G : Type*} [Group G] (K : Subgroup G)
abbrev sourceModule : Subgroup G := (blockU K).map K.subtype

/-- Original ambient core coordinates extend to its full normalizer, and the component has exactly the alternating image. -/
theorem source_core_coordinates (hK : IsAlternatingBlock K 6)
    (hc : Nat.card (sourceModule K) = 32) :
    ∃ E : sourceModule K ≃* Multiplicative (core (Fin 6)),
    ∃ f : normalizer (K : Set G) →* Equiv.Perm (Fin 6),
      (∀ (n : normalizer (K : Set G)) (u : sourceModule K)
        (hu : n.val * u.val * n.val⁻¹ ∈ sourceModule K),
        (E ⟨n.val * u.val * n.val⁻¹,hu⟩).toAdd =
          coreRepresentation (Fin 6) (f n) (E u).toAdd) ∧
      (K.subgroupOf (normalizer (K : Set G))).map f = alternatingGroup (Fin 6) := by
  have hcard : Nat.card (blockU K) = 32 := by
    rw [sourceModule,card_map_of_injective K.subtype_injective] at hc
    exact hc
  obtain ⟨m,E0,hE0,hq⟩ := hK.six_core_coordinates hcard
  obtain ⟨f0,hf0⟩ := exists_automorphism_actor m E0 hE0 hq
  let j : blockU K ≃* sourceModule K := (blockU K).equivMapOfInjective K.subtype K.subtype_injective
  let E : sourceModule K ≃* Multiplicative (core (Fin 6)) := j.symm.trans E0
  let f : normalizer (K : Set G) →* Equiv.Perm (Fin 6) := f0.comp K.normalizerMonoidHom
  have he (n : normalizer (K : Set G)) (u : sourceModule K)
      (hu : n.val * u.val * n.val⁻¹ ∈ sourceModule K) :
      j.symm ⟨n.val*u.val*n.val⁻¹,hu⟩ =
        MulAut.characteristic (blockU K) (K.normalizerMonoidHom n) (j.symm u) := by
    apply j.injective
    rw [j.apply_symm_apply]
    apply Subtype.ext
    change n.val*u.val*n.val⁻¹ = n.val * (((j.symm u : blockU K) : K) : G) * n.val⁻¹
    congr 2
    exact (congrArg Subtype.val (j.apply_symm_apply u)).symm
  have hfg (l : K) : f ⟨l.val,K.le_normalizer l.property⟩ =
      (m.quotientIso (QuotientGroup.mk' (pCore 2 K) l)).val := by
    let n : normalizer (K : Set G) := ⟨l.val,K.le_normalizer l.property⟩
    apply Chapter13.Section08.ComponentSieve.SixAndG2.NaturalSix.coreAction_injective
    apply LinearMap.ext
    intro v
    obtain ⟨u,hu⟩ := E0.surjective (Multiplicative.ofAdd v)
    have hv : (E0 u).toAdd = v := congrArg Multiplicative.toAdd hu
    change coreRepresentation (Fin 6) (f0 (K.normalizerMonoidHom n)) v = _
    rw [←hv,←hf0]
    have hconj : MulAut.characteristic (blockU K) (K.normalizerMonoidHom n) u = blockConjugate K l u := by
      apply Subtype.ext
      apply Subtype.ext
      rfl
    rw [hconj,hE0]
  refine ⟨E,f,?_,?_⟩
  · intro n u hu
    change (E0 (j.symm _)).toAdd = coreRepresentation (Fin 6) (f0 _) (E0 (j.symm u)).toAdd
    rw [he]
    exact hf0 _ _
  · apply le_antisymm
    · rintro _ ⟨n,hn,rfl⟩
      have hh := hfg ⟨n.val,hn⟩
      simpa only [hh] using (m.quotientIso (QuotientGroup.mk' (pCore 2 K) ⟨n.val,hn⟩)).property
    · intro g hg
      obtain ⟨l,hl⟩ := m.quotientIso.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 K)) ⟨g,hg⟩
      refine ⟨⟨l.val,K.le_normalizer l.property⟩,l.property,?_⟩
      exact (hfg l).trans (congrArg Subtype.val hl)

/-- The kernel of a literal six-letter action is exactly the centralizer
of the full source module. -/
theorem source_action_kernel
    (E : sourceModule K ≃* Multiplicative (core (Fin 6)))
    (f : normalizer (K : Set G) →* Equiv.Perm (Fin 6))
    (he : ∀ (n : normalizer (K : Set G)) (u : sourceModule K)
      (hu : n.val * u.val * n.val⁻¹ ∈ sourceModule K),
      (E ⟨n.val*u.val*n.val⁻¹,hu⟩).toAdd =
        coreRepresentation (Fin 6) (f n) (E u).toAdd) :
    f.ker = (centralizer (sourceModule K : Set G)).subgroupOf (normalizer (K : Set G)) := by
  have hn := normalizer_le_normalizer_characteristic_image K (blockU K)
  have hu (n : normalizer (K : Set G)) (u : sourceModule K) :
      n.val*u.val*n.val⁻¹ ∈ sourceModule K :=
    (mem_normalizer_iff.mp (hn n.property) u.val).mp u.property
  ext n
  constructor
  · intro h
    apply mem_centralizer_iff.mpr
    intro w hw
    let u : sourceModule K := ⟨w,hw⟩
    have hv := he n u (hu n u)
    rw [MonoidHom.mem_ker.mp h,map_one,Module.End.one_apply] at hv
    have hc := congrArg Subtype.val (E.injective (Multiplicative.toAdd.injective hv))
    exact (mul_inv_eq_iff_eq_mul.mp hc).symm
  · intro h
    apply MonoidHom.mem_ker.mpr
    apply Chapter13.Section08.ComponentSieve.SixAndG2.NaturalSix.coreAction_injective
    apply LinearMap.ext
    intro v
    obtain ⟨u,heuv⟩ := E.surjective (Multiplicative.ofAdd v)
    have hv : (E u).toAdd = v := congrArg Multiplicative.toAdd heuv
    rw [←hv,←he n u (hu n u),map_one,Module.End.one_apply]
    congr 2
    apply Subtype.ext
    have hc := mem_centralizer_iff.mp h u.val u.property
    change n.val*u.val*n.val⁻¹ = u.val
    change u.val*n.val = n.val*u.val at hc
    rw [←hc,mul_inv_cancel_right]
end CFSG.Quasithin.Chapter14.Section06.RankFiveNaturalSix
