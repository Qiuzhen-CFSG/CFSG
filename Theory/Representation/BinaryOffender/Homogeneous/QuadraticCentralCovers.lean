module
public import Theory.Representation.BinaryOffender.QuadraticHomogeneousOrbit
public import Theory.Representation.BinaryOffender.QuadraticQuotient

/-!
# Quadratic orbits of homogeneous central covers

Work in the literal quotient by component-fixed vectors. Homogeneity makes
its orbit independent. If an elementary quadratic actor moves a cover,
its seed stabilizer fixes that quotient pointwise. Faithfulness forces
this stabilizer to centralize the component; full commutator generation
then makes it fix the entire original cover. Consequently the actor's
faithful image on the original orbit span has order two.

Central kernels may be nonzero and may intersect across different covers.
No direct-sum assertion about the original covers is used. The minimum-ratio
consumer in Chapter D applies this to exclude movement of covers with
central quotient dimension greater than two.

Source: Aschbacher--Smith, A.1.40--42, D.2.5 and the quadratic orbit argument
of D.3.5, printed pp.31--32,179,195--196; used in14.6.22, p.1038.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace Representation.BinaryOffender.Homogeneous
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- Faithfulness of the central quotient makes a pointwise kernel on its
image centralize the original component, even when the cover is nonsplit. -/
theorem centralizes_of_fixed_central_image
    {K : Subgroup G} {I : Submodule (ZMod 2) V} (hI : IsIrrPlus ρ K I)
    (hf : Function.Injective (centralQuotientRepresentation ρ K I hI.choose))
    {b : G} (hbN : b ∈ normalizer (K : Set G))
    (hb : ∀ v ∈ I, ρ b v-v ∈ fixedSpace ρ K) : b ∈ centralizer (K : Set G) := by
  let N := normalizer (K : Set G)
  let L := K.subgroupOf N
  let q := (fixedSpace ρ K).mkQ
  let J := I.map q
  let σ := normalizerQuotientRepresentation ρ K
  let : L.Normal := (normal_subgroupOf_iff_le_normalizer K.le_normalizer).mpr le_rfl
  have hL : L ≤ subspaceStabilizer σ J := by
    apply le_subspaceStabilizer
    rintro k hk w ⟨v,hv,rfl⟩
    exact ⟨ρ k.val v,(hI.choose hk v).2 hv,rfl⟩
  have hLf : ∀ k ∈ L, (∀ w ∈ J, σ k w = w) → k = 1 := by
    intro k hk hh
    have he : (⟨k.val,hk⟩ : K) = 1 := by
      apply hf
      rw [map_one]
      apply LinearMap.ext
      intro v
      apply (centralQuotientImageEquiv ρ K I).injective
      induction v using Submodule.Quotient.induction_on with
      | _ v =>
        apply Subtype.ext
        change q (ρ k.val v.val) = q v.val
        exact hh (q v.val) ⟨v,v.property,rfl⟩
    exact Subtype.ext (congrArg (fun x : K => (x : G)) he)
  have hb' : ∀ w ∈ J, σ ⟨b,hbN⟩ w = w := by
    rintro w ⟨v,hv,rfl⟩
    change q (ρ b v) = q v
    apply sub_eq_zero.mp
    rw [←map_sub]
    exact (Submodule.Quotient.mk_eq_zero _).mpr (hb v hv)
  have hc := centralizes_of_fixes_faithful_section σ L J hL hLf
    (show (⟨b,hbN⟩ : N) ∈ normalizer (L : Set N) from
      le_normalizer_of_normal (mem_top _)) hb'
  intro k hk
  exact congrArg Subtype.val (mem_centralizer_iff.mp hc ⟨k,K.le_normalizer hk⟩ hk)


/-- Fixing the faithful central image fixes the full commutator-generated cover. -/
theorem fixes_of_fixed_central_image
    {K : Subgroup G} {I : Submodule (ZMod 2) V} (hI : IsIrrPlus ρ K I)
    (hf : Function.Injective (centralQuotientRepresentation ρ K I hI.choose))
    {b : G} (hbN : b ∈ normalizer (K : Set G))
    (hb : ∀ v ∈ I, ρ b v-v ∈ fixedSpace ρ K) : ∀ v ∈ I, ρ b v = v := by
  have hc := centralizes_of_fixed_central_image ρ hI hf hbN hb
  have hle : subspaceCommutator ρ I K ≤ LinearMap.ker (ρ b - LinearMap.id) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨k,hk,w,hw,rfl⟩
    change ρ b (ρ k w-w) - (ρ k w-w) = 0
    apply sub_eq_zero.mpr
    have hbk : ρ b (ρ k w) = ρ k (ρ b w) := by
      change (ρ b * ρ k) w = (ρ k * ρ b) w
      rw [←map_mul,←map_mul,(mem_centralizer_iff.mp hc k hk).symm]
    have hd := hb w hw ⟨k,hk⟩
    rw [map_sub] at hd ⊢
    rw [hbk]
    exact sub_eq_sub_iff_sub_eq_sub.mp hd
  rw [hI.choose_spec.1] at hle
  exact fun v hv => sub_eq_zero.mp (hle hv)

/-- Every subgroup of the prescribed normalizer has an independent orbit on
the actual central image, with the original covering kernel retained. -/
theorem IsIrrPlusWith.independent_central_orbit
    {K T A : Subgroup G} {I : Submodule (ZMod 2) V}
    (hI : IsIrrPlusWith ρ K T I) (hAT : A ≤ T) :
    sSupIndep (subspaceOrbit ((normalizerQuotientRepresentation ρ K).comp
      (inclusion (hAT.trans hI.normalizes))) ⊤ (I.map (fixedSpace ρ K).mkQ)) := by
  let q := (fixedSpace ρ K).mkQ
  let J := I.map q
  let σ := (normalizerQuotientRepresentation ρ K).comp
    (inclusion (hAT.trans hI.normalizes))
  let S := quotientImage ρ K I hI.invariant
  let Ω := centralOrbit ρ K T hI.normalizes S
  change sSupIndep (subspaceOrbit σ ⊤ J)
  classical
  let f : subspaceOrbit σ ⊤ J → Ω := fun L =>
    ⟨centralRightConjugate ρ K T hI.normalizes S
      ⟨(Classical.choose L.property).val.val⁻¹,
        T.inv_mem (hAT (Classical.choose L.property).val.property)⟩,
     ⟨_,rfl⟩⟩
  have hf (L : subspaceOrbit σ ⊤ J) : (f L).val.toSubmodule = L.val := by
    rw [show (f L).val = centralRightConjugate ρ K T hI.normalizes S
      ⟨(Classical.choose L.property).val.val⁻¹,
        T.inv_mem (hAT (Classical.choose L.property).val.property)⟩ from rfl,
      centralRightConjugate_toSubmodule]
    change J.map (normalizerQuotientRepresentation ρ K
      ⟨(Classical.choose L.property).val.val⁻¹⁻¹,_⟩) = L.val
    simp only [inv_inv]
    exact Classical.choose_spec L.property
  have hfi : Function.Injective f := by
    intro L N h
    exact Subtype.ext ((hf L).symm.trans
      ((congrArg (fun U : Ω => U.val.toSubmodule) h).trans (hf N)))
  have hh := (hI.orbit_decomposition ρ).1.comp hfi
  change iSupIndep (fun L : subspaceOrbit σ ⊤ J => (f L).val.toSubmodule) at hh
  simp only [hf] at hh
  exact (sSupIndep_iff _).mpr hh

private theorem restricted_card_two_of_moving_orbit
    (I : Submodule (ZMod 2) V) (A : Subgroup G) [IsMulCommutative A]
    {a : G} (ha : a ∈ A) (ha2 : a*a = 1) (haI : I.map (ρ a) ≠ I)
    (hfixI : ∀ b ∈ A, I.map (ρ b) = I → ∀ v ∈ I, ρ b v = v)
    (horbit : ∀ b ∈ A, I.map (ρ b) = I ∨ I.map (ρ b) = I.map (ρ a)) :
    Nat.card (restrictedSubgroup ρ (orbitSpan ρ A I) A) = 2 := by
  classical
  let W := orbitSpan ρ A I
  have hW := orbitSpan_invariant ρ A I
  let f := subgroupActionHom ρ W A hW
  have hfix {b : G} (hb : b ∈ A) (hbI : I.map (ρ b) = I) : f ⟨b,hb⟩ = 1 := by
    have hfW : W ≤ (ρ b - LinearMap.id).ker := by
      apply iSup_le
      rintro t _ ⟨v,hv,rfl⟩
      change ρ b (ρ t v)-ρ t v = 0
      have hbt : b*(t:G) = (t:G)*b := congrArg Subtype.val (mul_comm (⟨b,hb⟩ : A) t)
      rw [←Module.End.mul_apply,←map_mul,hbt,map_mul,Module.End.mul_apply,hfixI b hb hbI v hv,sub_self]
    apply subspaceImageRepresentation_injective ρ W
    ext w
    exact sub_eq_zero.mp (hfW w.property)
  have hfa : f ⟨a,ha⟩ ≠ 1 := by
    intro he
    apply haI
    apply (subspace_map_eq_iff ρ I a).mpr
    intro v
    have hfI : ∀ w ∈ I, ρ a w = w := by
      intro w hw
      exact congrArg (fun x => (subspaceImageRepresentation ρ W x
        ⟨w,le_orbitSpan ρ A I hw⟩ : V)) he
    constructor
    · intro hv
      have hev := hfI (ρ a v) hv
      rw [←Module.End.mul_apply,←map_mul,ha2,map_one,Module.End.one_apply] at hev
      exact hev ▸ hv
    · intro hv
      rwa [hfI v hv]
  have htwo (b : A) : f b = 1 ∨ f b = f ⟨a,ha⟩ := by
    rcases horbit b b.property with hb | hb
    · exact Or.inl (hfix b.property hb)
    · right
      have hab : I.map (ρ (a*b)) = I := by
        rw [subspace_map_mul,hb,←subspace_map_mul,ha2]
        simp only [map_one,Module.End.one_eq_id,Submodule.map_id]
      have hh := hfix (A.mul_mem ha b.property) hab
      change f (⟨a,ha⟩*b) = 1 at hh
      rw [map_mul] at hh
      have hh2 : f ⟨a,ha⟩*f ⟨a,ha⟩ = 1 := by
        rw [←map_mul,show (⟨a,ha⟩ : A)*(⟨a,ha⟩ : A) = 1 from Subtype.ext ha2,map_one]
      exact mul_left_cancel (hh.trans hh2.symm)
  rw [←subgroupActionHom_range ρ W A hW]
  apply Nat.card_eq_two_iff.mpr
  refine ⟨1,f.rangeRestrict ⟨a,ha⟩,?_,?_⟩
  · intro he
    exact hfa (congrArg Subtype.val he).symm
  · apply Set.eq_univ_of_forall
    rintro ⟨b,c,rfl⟩
    rcases htwo c with hc | hc
    · exact Or.inl (show f.rangeRestrict c = 1 from Subtype.ext hc)
    · exact Or.inr (show f.rangeRestrict c = f.rangeRestrict ⟨a,ha⟩ from Subtype.ext hc)

/-- If a quadratic elementary actor moves a homogeneous central cover, its
faithful action on the full orbit span has order two. -/
theorem IsIrrPlusWith.quadratic_moving_cover_image_card
    {K T A : Subgroup G} {I : Submodule (ZMod 2) V}
    (hI : IsIrrPlusWith ρ K T I) (hAT : A ≤ T)
    (hA : IsElementaryTwo A) (hq : IsQuadratic ρ A)
    (hf : Function.Injective (centralQuotientRepresentation ρ K I hI.isIrrPlus.choose))
    {a : G} (ha : a ∈ A) (haI : I.map (ρ a) ≠ I) :
    Nat.card (restrictedSubgroup ρ (orbitSpan ρ A I) A) = 2 := by
  classical
  let : IsElementaryAbelian 2 A := hA.2
  let q := (fixedSpace ρ K).mkQ
  let J := I.map q
  let σ := (normalizerQuotientRepresentation ρ K).comp
    (inclusion (hAT.trans hI.normalizes))
  have hmap (b : A) : J.map (σ b) = (I.map (ρ b.val)).map q :=
    (quotientImage_map_normalizer ρ K I ⟨b,hI.normalizes (hAT b.property)⟩).symm
  have hlift (b : A) (hh : J.map (σ b) = J) : I.map (ρ b.val) = I := by
    rw [hmap] at hh
    have hbI := hI.isIrrPlus.map_normalizer ρ (hI.normalizes (hAT b.property))
    exact le_antisymm
      (le_of_quotientImage_le ρ hbI.choose_spec.1 hI.invariant hh.le)
      (le_of_quotientImage_le ρ hI.isIrrPlus.choose_spec.1 hbI.choose hh.ge)
  have hJ : J ≠ ⊥ := by
    intro hh
    apply hI.isIrrPlus.not_le_fixedSpace ρ
    intro v hv
    apply (Submodule.Quotient.mk_eq_zero _).mp
    have hh' : q v ∈ J := ⟨v,hv,rfl⟩
    rwa [hh] at hh'
  have hq' : IsQuadratic σ ⊤ := by
    apply quadratic_of_equivariant_surjection (ρ.comp A.subtype) σ q
      (Submodule.mkQ_surjective _) (fun _ _ => rfl) ⊤
    intro b _ c _ v
    exact hq b.val b.property c.val c.property v
  have hind := hI.independent_central_orbit ρ hAT
  have haJ : J.map (σ ⟨a,ha⟩) ≠ J := fun hh => haI (hlift ⟨a,ha⟩ hh)
  have ha2 : a*a = 1 := by
    simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) a ha
  have haa : (⟨a,ha⟩ : A)*(⟨a,ha⟩ : A) = 1 := Subtype.ext ha2
  have hdis : Disjoint J (J.map (σ ⟨a,ha⟩)) := by
    rw [hmap]
    exact hI.isIrrPlus.disjoint_quotientImages ρ
      (hI.isIrrPlus.map_normalizer ρ (hI.normalizes (hAT ha))) haI.symm
  apply restricted_card_two_of_moving_orbit ρ I A ha ha2 haI
  · intro b hb hbI
    have hbJ : J.map (σ ⟨b,hb⟩) = J := by rw [hmap,hbI]
    have hbs := (subspace_map_eq_iff σ J ⟨b,hb⟩).mp hbJ
    have hfJ := quadratic_fixes_disjoint_summand σ J hq' (mem_top _) (mem_top _) hdis
      (fun v hv => (hbs v).2 hv)
    apply fixes_of_fixed_central_image ρ hI.isIrrPlus hf (hI.normalizes (hAT hb))
    intro v hv
    apply (Submodule.Quotient.mk_eq_zero _).mp
    change q (ρ b v-v) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr (hfJ (q v) ⟨v,hv,rfl⟩)
  · intro b hb
    rcases quadratic_orbit_eq_self_or_moving σ J hJ ⊤ hq' hind (mem_top _) haa haJ
      (mem_top (⟨b,hb⟩ : A)) with hh | hh
    · exact Or.inl (hlift ⟨b,hb⟩ hh)
    · right
      rw [hmap,hmap] at hh
      have hbI := hI.isIrrPlus.map_normalizer ρ (hI.normalizes (hAT hb))
      have haI' := hI.isIrrPlus.map_normalizer ρ (hI.normalizes (hAT ha))
      exact le_antisymm
        (le_of_quotientImage_le ρ hbI.choose_spec.1 haI'.choose hh.le)
        (le_of_quotientImage_le ρ haI'.choose_spec.1 hbI.choose hh.ge)

end Representation.BinaryOffender.Homogeneous
