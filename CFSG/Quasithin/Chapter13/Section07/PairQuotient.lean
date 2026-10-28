module

public import CFSG.Quasithin.Chapter13.Section07.CoreImage
public import CFSG.Quasithin.Chapter13.Section07.ChosenConjugator
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.TransvectionPair
public import Theory.GroupTheory.SymmetricThreeTwoCore


/-!
# The actual S₃ quotient of the source two-conjugate span

The actual VH image is a transposition fixing V₁-perpendicular. The
chosen conjugate point lies outside this hyperplane, so the two natural
transpositions generate S₃. Restricting the original LT action keeps its
two-group kernel; the S₃ quotient identifies that kernel with O₂(I), where
I is the literal join of VH and its chosen conjugate.

The final theorem constructs the original g∈L, its square modulo O₂(LT),
the point escape and the actual core/quotient conclusion. No S₃ image or
core identity is supplied by the caller. The further factorization of the
core requires the source internal-conjugator argument and is separate.
Source: Aschbacher–Smith,13.7.10(1–2), printed pp.941–942.
-/

@[expose] public section

open Subgroup BinaryPermutation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section07
open Section08.SourceCompletion NaturalAction ChapterF.Section09.Setup
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalPairing
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d

omit d [Finite G] in
private theorem conjugate_le_LT (A : Subgroup G) (hA : A ≤ L ⊔ (T : Subgroup G))
    (g : (L ⊔ (T : Subgroup G) : Subgroup G)) : conjugate A (g:G) ≤ L ⊔ (T : Subgroup G) := by
  rintro _ ⟨a,ha,rfl⟩
  change (g:G)⁻¹*a*((g:G)⁻¹)⁻¹∈_
  rw [inv_inv]
  exact mul_mem (mul_mem ((L ⊔ (T : Subgroup G)).inv_mem g.property) (hA ha)) g.property

private theorem conjugate_permutation_image (A : Subgroup G) (hA : A ≤ L ⊔ (T : Subgroup G))
    (g : (L ⊔ (T : Subgroup G) : Subgroup G)) :
    ((conjugate A (g:G)).subgroupOf (L ⊔ (T : Subgroup G))).map (permutation d) =
      ((A.subgroupOf (L ⊔ (T : Subgroup G))).map (permutation d)).map
        (MulAut.conj (permutation d g)⁻¹).toMonoidHom := by
  have he : (conjugate A (g:G)).subgroupOf (L ⊔ (T : Subgroup G)) =
      (A.subgroupOf (L ⊔ (T : Subgroup G))).map (MulAut.conj g⁻¹).toMonoidHom := by
    apply map_injective (L ⊔ (T : Subgroup G)).subtype_injective
    rw [map_subgroupOf_eq_of_le (conjugate_le_LT A hA g),map_map]
    have hc : (L ⊔ (T : Subgroup G)).subtype.comp (MulAut.conj g⁻¹).toMonoidHom =
        (MulAut.conj (g:G)⁻¹).toMonoidHom.comp (L ⊔ (T : Subgroup G)).subtype := by
      apply MonoidHom.ext
      intro x
      rfl
    rw [hc,←map_map,map_subgroupOf_eq_of_le hA]
    rfl

  rw [he,map_map,map_map]
  congr 1
  apply MonoidHom.ext
  intro x
  simp only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,
    MulAut.conj_inv_apply,map_mul,map_inv]

theorem natural_image_conjugate (A : Subgroup G) (hA : A ≤ V)
    (g : (L ⊔ (T : Subgroup G) : Subgroup G)) :
    image d (conjugate A (g:G)) = (image d A).map (naturalRepresentation (Fin 6) (permutation d g⁻¹)) := by
  apply le_antisymm
  · intro w hw
    obtain ⟨v,hv,rfl⟩ := (mem_image d _ _).mp hw
    obtain ⟨a,ha,he⟩ := hv
    let aV : V := ⟨a,hA ha⟩
    refine ⟨(d.coordinate aV).toAdd,(mem_image d A _).mpr ⟨aV,ha,rfl⟩,?_⟩
    rw [←conjugation d g⁻¹ aV]
    apply congrArg (fun v:V=>(d.coordinate v).toAdd)
    exact Subtype.ext he
  · rintro _ ⟨w,hw,rfl⟩
    obtain ⟨v,hv,rfl⟩ := (mem_image d A _).mp hw
    rw [←conjugation d g⁻¹ v]
    apply (mem_image d _ _).mpr
    exact ⟨_,⟨v.val,hv,rfl⟩,rfl⟩

/-- The literal two-conjugate image is S₃, forced by the original point escape. -/
theorem pair_image_symmetricThree
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V))
    (g : (L ⊔ (T : Subgroup G) : Subgroup G))
    (hout : ¬ conjugate V₁ (g:G) ≤ Section08.Source.UH H V₃) :
    Nonempty ((((Section08.Source.VH H V ⊔ conjugate (Section08.Source.VH H V) (g:G)).subgroupOf
      (L ⊔ (T : Subgroup G))).map (permutation d)) ≃* Equiv.Perm (Fin 3)) := by
  let A := Section08.Source.VH H V
  have hAX : A ≤ L ⊔ (T : Subgroup G) := (VH_le_core d h hU).trans (h.QH_le_T.trans le_sup_right)
  have hPgV : conjugate V₁ (g:G) ≤ V := by
    have hv : conjugate V (g:G)=V := mem_normalizer_iff_map_conj_eq.mp
      ((normalizer (V:Set G)).inv_mem (d.normalizes_V g.property))
    exact (map_mono (h.point_lt.le.trans h.plus_le)).trans hv.le
  obtain ⟨t,ht,htA,_⟩ := nonabelian_transposition_images d h hU hV
  have htf : ∀ w ∈ form.orthogonal (image d V₁), naturalRepresentation (Fin 6) t w=w := by
    intro w hw
    rw [←seed_perpendicular d] at hw
    obtain ⟨v,hv,rfl⟩ := (mem_image d V₃ _).mp hw
    have htm : t ∈ (A.subgroupOf (L ⊔ (T : Subgroup G))).map (permutation d) :=
      htA.symm ▸ mem_zpowers t
    obtain ⟨a,ha,hat⟩:=htm
    rw [←hat,←conjugation d a v]
    apply congrArg (fun v:V=>(d.coordinate v).toAdd)
    apply Subtype.ext
    have hc := (VH_centralizes_UH d h hU) ha
    have hh := (centralizer_le (le_conjugateSpanBy V₃ H)) hc.2
    change a.val*v.val*a.val⁻¹=v.val
    have hh' : v.val*a.val=a.val*v.val := hh v.val hv
    rw [←hh',mul_inv_cancel_right]
  have hcross : ¬ (image d V₁).map (naturalRepresentation (Fin 6) (permutation d g)⁻¹) ≤
      form.orthogonal (image d V₁) := by
    intro hc
    have him : image d (conjugate V₁ (g:G)) ≤ image d V₃ := by
      rw [natural_image_conjugate d V₁ (h.point_lt.le.trans h.plus_le),seed_perpendicular d,map_inv]
      exact hc
    apply hout
    intro a ha
    have hh := him ((mem_image d _ _).mpr ⟨⟨a,hPgV ha⟩,ha,rfl⟩)
    obtain ⟨v,hv,he⟩ := (mem_image d V₃ _).mp hh
    have hea : v=(⟨a,hPgV ha⟩:V) := d.coordinate.injective he
    have hea' : v.val=a := congrArg Subtype.val hea
    have hv' : a∈V₃ := hea' ▸ hv
    exact le_conjugateSpanBy V₃ H hv'
  have hp := Theory.SpecificGroups.SymmetricSix.BinaryFlags.TransvectionPair.conjugate_pair
    (image d V₁) (image_dim d V₁ (h.point_lt.le.trans h.plus_le) 1 d.line_card)
    (permutation d g)⁻¹ t ht htf hcross
  have he : ((A ⊔ conjugate A (g:G)).subgroupOf (L ⊔ (T : Subgroup G))).map (permutation d) =
      zpowers t ⊔ zpowers ((permutation d g)⁻¹*t*((permutation d g)⁻¹)⁻¹) := by
    rw [subgroupOf_sup hAX (conjugate_le_LT A hAX g),Subgroup.map_sup,
      conjugate_permutation_image d A hAX g,htA,MonoidHom.map_zpowers]
    rfl
  exact he.symm ▸ hp

/-- The original two-conjugate subgroup has S₃ quotient by its actual two-core,
and that core is its intersection with the original O₂(LT). -/
theorem pair_twoCore_quotient
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V))
    (g : (L ⊔ (T : Subgroup G) : Subgroup G))
    (hout : ¬ conjugate V₁ (g:G) ≤ Section08.Source.UH H V₃) :
    let I := Section08.Source.VH H V ⊔ conjugate (Section08.Source.VH H V) (g:G)
    I.pCoreIn 2 = I ⊓ (L ⊔ (T : Subgroup G) : Subgroup G).pCoreIn 2 ∧
      Nonempty ((I ⧸ pCore 2 I) ≃* Equiv.Perm (Fin 3)) := by
  dsimp only
  let X := L ⊔ (T : Subgroup G)
  let A := Section08.Source.VH H V
  let I := A ⊔ conjugate A (g:G)
  have hAX : A ≤ X := (VH_le_core d h hU).trans (h.QH_le_T.trans le_sup_right)
  have hIX : I ≤ X := sup_le hAX (conjugate_le_LT A hAX g)
  let k : I →* Equiv.Perm (Fin 6) := (permutation d).comp (inclusion hIX)
  have hr : k.range = (I.subgroupOf X).map (permutation d) := by
    rw [MonoidHom.range_comp,inclusion_range]
  obtain ⟨e⟩:=pair_image_symmetricThree d h hU hV g hout
  let j := (MulEquiv.subgroupCongr hr).trans e
  let f : I →* Equiv.Perm (Fin 3) := j.toMonoidHom.comp k.rangeRestrict
  have hf : Function.Surjective f := j.surjective.comp k.rangeRestrict_surjective
  have hk : f.ker=k.ker := (MonoidHom.ker_comp_of_injective k.rangeRestrict
    j.toMonoidHom j.injective).trans (MonoidHom.ker_rangeRestrict k)
  have hkG : IsPGroup 2 k.ker := by
    change IsPGroup 2 ((permutation d).ker.comap (inclusion hIX))
    rw [nonabelian_permutation_kernel d h hU hV]
    exact pCore_isPGroup.comap_of_injective (inclusion hIX) (inclusion_injective hIX)
  have hcore : f.ker=pCore 2 I := ker_eq_twoCore_of_surjective_perm_three f hf (hk.symm ▸ hkG)
  have hki : k.ker=(X.pCoreIn 2).subgroupOf I := by
    ext x
    constructor
    · intro hx
      have hx' : inclusion hIX x∈(permutation d).ker:=hx
      rw [nonabelian_permutation_kernel d h hU hV] at hx'
      exact mem_map_of_mem X.subtype hx'
    · intro hx
      obtain ⟨y,hy,he⟩:=hx
      have he' : y=inclusion hIX x := Subtype.ext he
      have hx' : inclusion hIX x∈pCore 2 X:=he' ▸ hy
      rw [←nonabelian_permutation_kernel d h hU hV] at hx'
      exact hx'
  have hm : ((X.pCoreIn 2).subgroupOf I).map I.subtype = I.pCoreIn 2 :=
    congrArg (Subgroup.map I.subtype) (hki.symm.trans (hk.symm.trans hcore))
  rw [Subgroup.subgroupOf_map_subtype] at hm
  refine ⟨?_,?_⟩
  · exact hm.symm.trans (inf_comm _ _)
  · exact ⟨(QuotientGroup.quotientMulEquivOfEq hcore.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)⟩

/-- Construct the source conjugator and the actual S₃ quotient simultaneously. -/
theorem exists_pair_twoCore_quotient
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V)) :
    ∃ g : L,
      (QuotientGroup.mk' (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G))
        (inclusion le_sup_left g))^2=1 ∧
      ¬conjugate V₁ (g:G) ≤ Section08.Source.UH H V₃ ∧
      let I := Section08.Source.VH H V ⊔ conjugate (Section08.Source.VH H V) (g:G)
      I.pCoreIn 2 = I ⊓ (L ⊔ (T : Subgroup G) : Subgroup G).pCoreIn 2 ∧
        Nonempty ((I ⧸ pCore 2 I) ≃* Equiv.Perm (Fin 3)) := by
  obtain ⟨g,hs,hout,_⟩:=exists_source_intersections d h hU hV
  exact ⟨g,hs,hout,pair_twoCore_quotient d h hU hV (inclusion le_sup_left g) hout⟩
end CFSG.Quasithin.Chapter13.Section07
