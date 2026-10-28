module
public import Theory.Representation.BinaryAlternatingFiveExtension.PointCoreGeometry.Transport
public import Theory.GroupTheory.DisjointCommutingProduct
public import Theory.Representation.BinaryAlternatingFiveFlag.PairedFourQuotient

/-!
# The paired four-group quotient of two binary Borel factors

For two commuting disjoint subgroups marked by the binary A₄ extension,
project each two-core V ⋊ V₄ onto its regular four-group. Multiplication
identifies their core product with the literal joined subgroup, and the
kernel is the join of the two marked vector groups. The complements supply
independent A₄ actors. An element exchanging the Borel factors exchanges
the supported quotient preimages whenever it normalizes the kernel.

Consequently the joined core modulo the vector join is irreducible for
any stated actor containing both factors and such an exchanger. The actor
normalizes both endpoints; no larger Sylow action or compatibility between
the two coordinate markings is imposed.

Source: Aschbacher--Smith, 14.6.9(l), printed p.1027.
-/

public section
open Subgroup
namespace BinaryPermutation.AlternatingFiveExtension.PairedCoreQuotient
open AlternatingFiveFlag AlternatingFiveBorel PointCoreGeometry

private def projection : outerCore →* four where
  toFun x := ⟨x.val.right.val.val,x.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

private theorem four_fixes (x : four) : x.val 4 = 4 := by
  rcases x.property with h|h|h|h <;> rw [h] <;> decide +kernel

private def liftFour (x : four) : outerCore :=
  ⟨SemidirectProduct.inr ⟨⟨x.val,four_even x.property⟩,four_fixes x⟩,x.property⟩

private theorem projection_ker : projection.ker.map outerCore.subtype = vectors := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    change y.val.right = 1
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : four => z.val) (show projection y = 1 from hy)
  · intro hx
    refine ⟨⟨x,vectors_le_outerCore hx⟩,?_,rfl⟩
    apply Subtype.ext
    exact congrArg (fun b : B => b.val.val) (show x.right = 1 from hx)

variable {G : Type*} [Group G]

private def modelMap (H : Subgroup G) (e : H ≃* BorelModel) : BorelModel →* G :=
  H.subtype.comp e.symm.toMonoidHom

private theorem modelMap_injective (H : Subgroup G) (e : H ≃* BorelModel) :
    Function.Injective (modelMap H e) := H.subtype_injective.comp e.symm.injective

private theorem modelMap_core (H : Subgroup G) (e : H ≃* BorelModel) :
    outerCore.map (modelMap H e) = H.pCoreIn 2 := by
  rw [←pCore_eq_outerCore]
  change (pCore 2 BorelModel).map (H.subtype.comp e.symm.toMonoidHom) = _
  rw [←map_map,pCore_map_iso]
  rfl

private def pairMap {H₁ H₂ : Subgroup G} (e₁ : H₁ ≃* BorelModel)
    (e₂ : H₂ ≃* BorelModel) (hc : H₁ ≤ centralizer (H₂ : Set G)) :
    BorelModel × BorelModel →* G :=
  (modelMap H₁ e₁).noncommCoprod (modelMap H₂ e₂) (fun x y =>
    (hc (e₁.symm x).property (e₂.symm y) (e₂.symm y).property).symm)

private theorem pairMap_injective {H₁ H₂ : Subgroup G} (e₁ : H₁ ≃* BorelModel)
    (e₂ : H₂ ≃* BorelModel) (hc : H₁ ≤ centralizer (H₂ : Set G))
    (hd : Disjoint H₁ H₂) : Function.Injective (pairMap e₁ e₂ hc) := by
  intro x y hxy
  have he : (e₁.symm x.1,e₂.symm x.2) = (e₁.symm y.1,e₂.symm y.2) :=
    mul_injective_of_disjoint hd hxy
  exact Prod.ext (e₁.symm.injective (congrArg Prod.fst he))
    (e₂.symm.injective (congrArg Prod.snd he))

private theorem pairMap_prod {H₁ H₂ : Subgroup G} (e₁ : H₁ ≃* BorelModel)
    (e₂ : H₂ ≃* BorelModel) (hc : H₁ ≤ centralizer (H₂ : Set G))
    (P Q : Subgroup BorelModel) :
    (P.prod Q).map (pairMap e₁ e₂ hc) =
      P.map (modelMap H₁ e₁) ⊔ Q.map (modelMap H₂ e₂) := by
  apply le_antisymm
  · rintro x ⟨⟨a,b⟩,⟨ha,hb⟩,rfl⟩
    exact mul_mem_sup (mem_map_of_mem _ ha) (mem_map_of_mem _ hb)
  · apply sup_le
    · rintro x ⟨a,ha,rfl⟩
      exact ⟨(a,1),⟨ha,Q.one_mem⟩,by change _ * modelMap H₂ e₂ 1 = _; rw [map_one,mul_one]⟩
    · rintro x ⟨b,hb,rfl⟩
      exact ⟨(1,b),⟨P.one_mem,hb⟩,by change modelMap H₁ e₁ 1 * _ = _; rw [map_one,one_mul]⟩

private def coreMap {H₁ H₂ : Subgroup G} (e₁ : H₁ ≃* BorelModel)
    (e₂ : H₂ ≃* BorelModel) (hc : H₁ ≤ centralizer (H₂ : Set G)) :
    outerCore × outerCore →* G :=
  (pairMap e₁ e₂ hc).comp (outerCore.subtype.prodMap outerCore.subtype)

private theorem coreMap_injective {H₁ H₂ : Subgroup G} (e₁ : H₁ ≃* BorelModel)
    (e₂ : H₂ ≃* BorelModel) (hc : H₁ ≤ centralizer (H₂ : Set G))
    (hd : Disjoint H₁ H₂) : Function.Injective (coreMap e₁ e₂ hc) := by
  intro x y h
  have he := pairMap_injective e₁ e₂ hc hd h
  exact Prod.ext (Subtype.ext (congrArg Prod.fst he)) (Subtype.ext (congrArg Prod.snd he))

private theorem coreMap_range {H₁ H₂ : Subgroup G} (e₁ : H₁ ≃* BorelModel)
    (e₂ : H₂ ≃* BorelModel) (hc : H₁ ≤ centralizer (H₂ : Set G)) :
    (coreMap e₁ e₂ hc).range = H₁.pCoreIn 2 ⊔ H₂.pCoreIn 2 := by
  rw [←modelMap_core H₁ e₁,←modelMap_core H₂ e₂,←pairMap_prod e₁ e₂ hc]
  ext x
  constructor
  · rintro ⟨⟨a,b⟩,rfl⟩
    exact ⟨(a.val,b.val),⟨a.property,b.property⟩,rfl⟩
  · rintro ⟨⟨a,b⟩,⟨ha,hb⟩,rfl⟩
    exact ⟨(⟨a,ha⟩,⟨b,hb⟩),rfl⟩

private noncomputable def coreEquiv {H₁ H₂ : Subgroup G} (e₁ : H₁ ≃* BorelModel)
    (e₂ : H₂ ≃* BorelModel) (hc : H₁ ≤ centralizer (H₂ : Set G))
    (hd : Disjoint H₁ H₂) : outerCore × outerCore ≃* ↥(H₁.pCoreIn 2 ⊔ H₂.pCoreIn 2) :=
  (MonoidHom.ofInjective (coreMap_injective e₁ e₂ hc hd)).trans
    (MulEquiv.subgroupCongr (coreMap_range e₁ e₂ hc))

private noncomputable def pairProjection {H₁ H₂ : Subgroup G} (e₁ : H₁ ≃* BorelModel)
    (e₂ : H₂ ≃* BorelModel) (hc : H₁ ≤ centralizer (H₂ : Set G))
    (hd : Disjoint H₁ H₂) : ↥(H₁.pCoreIn 2 ⊔ H₂.pCoreIn 2) →* four × four :=
  (projection.prodMap projection).comp (coreEquiv e₁ e₂ hc hd).symm.toMonoidHom

private theorem pairProjection_apply {H₁ H₂ : Subgroup G} (e₁ : H₁ ≃* BorelModel)
    (e₂ : H₂ ≃* BorelModel) (hc : H₁ ≤ centralizer (H₂ : Set G))
    (hd : Disjoint H₁ H₂) (x : outerCore × outerCore) :
    pairProjection e₁ e₂ hc hd (coreEquiv e₁ e₂ hc hd x) =
      (projection x.1,projection x.2) := by
  change (projection.prodMap projection) ((coreEquiv e₁ e₂ hc hd).symm
    (coreEquiv e₁ e₂ hc hd x)) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

private theorem pairProjection_surjective {H₁ H₂ : Subgroup G} (e₁ : H₁ ≃* BorelModel)
    (e₂ : H₂ ≃* BorelModel) (hc : H₁ ≤ centralizer (H₂ : Set G))
    (hd : Disjoint H₁ H₂) : Function.Surjective (pairProjection e₁ e₂ hc hd) := by
  intro x
  exact ⟨coreEquiv e₁ e₂ hc hd (liftFour x.1,liftFour x.2),
    pairProjection_apply e₁ e₂ hc hd _⟩

private theorem projection_eq_one (x : outerCore) : projection x = 1 ↔ x.val ∈ vectors := by
  constructor
  · intro h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : four => z.val) h
  · intro h
    apply Subtype.ext
    exact congrArg (fun z : B => z.val.val) (show x.val.right = 1 from h)

private theorem pairProjection_ker {H₁ H₂ : Subgroup G} (e₁ : H₁ ≃* BorelModel)
    (e₂ : H₂ ≃* BorelModel) (hc : H₁ ≤ centralizer (H₂ : Set G))
    (hd : Disjoint H₁ H₂) :
    (pairProjection e₁ e₂ hc hd).ker.map (H₁.pCoreIn 2 ⊔ H₂.pCoreIn 2).subtype =
      vectors.map (modelMap H₁ e₁) ⊔ vectors.map (modelMap H₂ e₂) := by
  rw [←pairMap_prod e₁ e₂ hc]
  ext x
  constructor
  · rintro ⟨a,ha,rfl⟩
    obtain ⟨a,rfl⟩ := (coreEquiv e₁ e₂ hc hd).surjective a
    change pairProjection e₁ e₂ hc hd (coreEquiv e₁ e₂ hc hd a) = 1 at ha
    rw [pairProjection_apply] at ha
    refine ⟨(a.1.val,a.2.val),⟨?_,?_⟩,rfl⟩
    · exact (projection_eq_one _).mp (congrArg Prod.fst ha)
    · exact (projection_eq_one _).mp (congrArg Prod.snd ha)
  · rintro ⟨⟨a,b⟩,⟨ha,hb⟩,rfl⟩
    let ab : outerCore × outerCore :=
      (⟨a,vectors_le_outerCore ha⟩,⟨b,vectors_le_outerCore hb⟩)
    refine ⟨coreEquiv e₁ e₂ hc hd ab,?_,rfl⟩
    change pairProjection e₁ e₂ hc hd (coreEquiv e₁ e₂ hc hd ab) = 1
    rw [pairProjection_apply]
    exact Prod.ext ((projection_eq_one _).mpr ha) ((projection_eq_one _).mpr hb)

private theorem pairProjection_preimage {H₁ H₂ : Subgroup G} (e₁ : H₁ ≃* BorelModel)
    (e₂ : H₂ ≃* BorelModel) (hc : H₁ ≤ centralizer (H₂ : Set G))
    (hd : Disjoint H₁ H₂) (P Q : Subgroup four) :
    ((P.prod Q).comap (pairProjection e₁ e₂ hc hd)).map
        (H₁.pCoreIn 2 ⊔ H₂.pCoreIn 2).subtype =
      ((P.comap projection).map outerCore.subtype).map (modelMap H₁ e₁) ⊔
      ((Q.comap projection).map outerCore.subtype).map (modelMap H₂ e₂) := by
  rw [←pairMap_prod e₁ e₂ hc]
  ext x
  constructor
  · rintro ⟨a,ha,rfl⟩
    obtain ⟨a,rfl⟩ := (coreEquiv e₁ e₂ hc hd).surjective a
    change pairProjection e₁ e₂ hc hd (coreEquiv e₁ e₂ hc hd a) ∈ P.prod Q at ha
    rw [pairProjection_apply] at ha
    exact ⟨(a.1.val,a.2.val),⟨⟨a.1,ha.1,rfl⟩,⟨a.2,ha.2,rfl⟩⟩,rfl⟩
  · rintro ⟨⟨a,b⟩,⟨⟨a,ha,rfl⟩,⟨b,hb,rfl⟩⟩,rfl⟩
    refine ⟨coreEquiv e₁ e₂ hc hd (a,b),?_,rfl⟩
    change pairProjection e₁ e₂ hc hd (coreEquiv e₁ e₂ hc hd (a,b)) ∈ P.prod Q
    rw [pairProjection_apply]
    exact ⟨ha,hb⟩

private theorem pairProjection_first {H₁ H₂ : Subgroup G} (e₁ : H₁ ≃* BorelModel)
    (e₂ : H₂ ≃* BorelModel) (hc : H₁ ≤ centralizer (H₂ : Set G))
    (hd : Disjoint H₁ H₂) :
    (((⊤ : Subgroup four).prod ⊥).comap (pairProjection e₁ e₂ hc hd)).map
        (H₁.pCoreIn 2 ⊔ H₂.pCoreIn 2).subtype =
      H₁.pCoreIn 2 ⊔ (vectors.map (modelMap H₁ e₁) ⊔ vectors.map (modelMap H₂ e₂)) := by
  rw [pairProjection_preimage,comap_top,←MonoidHom.range_eq_map,range_subtype,
    show (⊥ : Subgroup four).comap projection = projection.ker from rfl,
    projection_ker,modelMap_core,←sup_assoc]
  rw [sup_eq_left.mpr (show vectors.map (modelMap H₁ e₁) ≤ H₁.pCoreIn 2 from
    modelMap_core H₁ e₁ ▸ map_mono vectors_le_outerCore)]

private theorem pairProjection_second {H₁ H₂ : Subgroup G} (e₁ : H₁ ≃* BorelModel)
    (e₂ : H₂ ≃* BorelModel) (hc : H₁ ≤ centralizer (H₂ : Set G))
    (hd : Disjoint H₁ H₂) :
    (((⊥ : Subgroup four).prod ⊤).comap (pairProjection e₁ e₂ hc hd)).map
        (H₁.pCoreIn 2 ⊔ H₂.pCoreIn 2).subtype =
      H₂.pCoreIn 2 ⊔ (vectors.map (modelMap H₁ e₁) ⊔ vectors.map (modelMap H₂ e₂)) := by
  rw [pairProjection_preimage,comap_top,←MonoidHom.range_eq_map,range_subtype,
    show (⊥ : Subgroup four).comap projection = projection.ker from rfl,
    projection_ker,modelMap_core,sup_left_comm]
  rw [sup_eq_left.mpr (show vectors.map (modelMap H₂ e₂) ≤ H₂.pCoreIn 2 from
    modelMap_core H₂ e₂ ▸ map_mono vectors_le_outerCore)]

private def coreConj (b : B) : MulAut outerCore :=
  MulAut.conjNormal (SemidirectProduct.inr b : BorelModel)

private theorem coreMap_conj_first {H₁ H₂ : Subgroup G} (e₁ : H₁ ≃* BorelModel)
    (e₂ : H₂ ≃* BorelModel) (hc : H₁ ≤ centralizer (H₂ : Set G))
    (b : B) (x : outerCore × outerCore) :
    coreMap e₁ e₂ hc (coreConj b x.1,x.2) =
      modelMap H₁ e₁ (SemidirectProduct.inr b) * coreMap e₁ e₂ hc x *
        (modelMap H₁ e₁ (SemidirectProduct.inr b))⁻¹ := by
  have he : ((coreConj b x.1 : BorelModel),(x.2 : BorelModel)) =
      (SemidirectProduct.inr b,1) * ((x.1 : BorelModel),(x.2 : BorelModel)) *
        (SemidirectProduct.inr b,1)⁻¹ := by
    apply Prod.ext
    · rfl
    · simp
  change pairMap e₁ e₂ hc ((coreConj b x.1 : BorelModel),(x.2 : BorelModel)) = _
  rw [he,map_mul,map_mul,map_inv]
  have hunit : pairMap e₁ e₂ hc (SemidirectProduct.inr b,1) =
      modelMap H₁ e₁ (SemidirectProduct.inr b) := by
    change _ * modelMap H₂ e₂ 1 = _
    rw [map_one,mul_one]
  rw [hunit]
  rfl

private theorem coreMap_conj_second {H₁ H₂ : Subgroup G} (e₁ : H₁ ≃* BorelModel)
    (e₂ : H₂ ≃* BorelModel) (hc : H₁ ≤ centralizer (H₂ : Set G))
    (b : B) (x : outerCore × outerCore) :
    coreMap e₁ e₂ hc (x.1,coreConj b x.2) =
      modelMap H₂ e₂ (SemidirectProduct.inr b) * coreMap e₁ e₂ hc x *
        (modelMap H₂ e₂ (SemidirectProduct.inr b))⁻¹ := by
  have he : ((x.1 : BorelModel),(coreConj b x.2 : BorelModel)) =
      (1,SemidirectProduct.inr b) * ((x.1 : BorelModel),(x.2 : BorelModel)) *
        (1,SemidirectProduct.inr b)⁻¹ := by
    apply Prod.ext
    · simp
    · rfl
  change pairMap e₁ e₂ hc ((x.1 : BorelModel),(coreConj b x.2 : BorelModel)) = _
  rw [he,map_mul,map_mul,map_inv]
  have hunit : pairMap e₁ e₂ hc (1,SemidirectProduct.inr b) =
      modelMap H₂ e₂ (SemidirectProduct.inr b) := by
    change modelMap H₁ e₁ 1 * _ = _
    rw [map_one,one_mul]
  rw [hunit]
  rfl

private theorem projection_coreConj (b : B) (x : outerCore) :
    projection (coreConj b x) = fourConj b (projection x) := rfl

/-- Independent Borel factors construct the literal paired four-group quotient.
The exchanger preserves the lower subgroup as a whole; no compatibility of
its action with either chosen vector marking is required. -/
noncomputable def pairedFourQuotient
    (J H₁ H₂ A C : Subgroup G) (e₁ : H₁ ≃* BorelModel) (e₂ : H₂ ≃* BorelModel)
    (hd : Disjoint H₁ H₂) (hc : H₁ ≤ centralizer (H₂ : Set G))
    (h₁ : H₁ ≤ J) (h₂ : H₂ ≤ J)
    (hA : A = vectors.map (H₁.subtype.comp e₁.symm.toMonoidHom) ⊔
      vectors.map (H₂.subtype.comp e₂.symm.toMonoidHom))
    (hC : C = H₁.pCoreIn 2 ⊔ H₂.pCoreIn 2)
    (hJA : J ≤ normalizer (A : Set G)) (hJC : J ≤ normalizer (C : Set G))
    (hex : ∃ t ∈ J, H₁.map (MulAut.conj t).toMonoidHom = H₂) :
    PairedFourQuotient J A C := by
  subst A
  subst C
  refine
    { q := pairProjection e₁ e₂ hc hd
      surjective := pairProjection_surjective e₁ e₂ hc hd
      kernel := pairProjection_ker e₁ e₂ hc hd
      normalizes := hJC
      first_actor := ?_
      second_actor := ?_
      exchange := ?_ }
  · intro b
    let g : G := modelMap H₁ e₁ (SemidirectProduct.inr b)
    have hg : g ∈ J := h₁ (e₁.symm (SemidirectProduct.inr b)).property
    refine ⟨⟨g,hg⟩,?_⟩
    intro x
    obtain ⟨y,rfl⟩ := (coreEquiv e₁ e₂ hc hd).surjective x
    have he : (⟨g * coreEquiv e₁ e₂ hc hd y * g⁻¹,
        (hJC hg _).mp (coreEquiv e₁ e₂ hc hd y).property⟩ :
        ↥(H₁.pCoreIn 2 ⊔ H₂.pCoreIn 2)) =
        coreEquiv e₁ e₂ hc hd (coreConj b y.1,y.2) := by
      apply Subtype.ext
      exact (coreMap_conj_first e₁ e₂ hc b y).symm
    rw [he,pairProjection_apply,pairProjection_apply,projection_coreConj]
  · intro b
    let g : G := modelMap H₂ e₂ (SemidirectProduct.inr b)
    have hg : g ∈ J := h₂ (e₂.symm (SemidirectProduct.inr b)).property
    refine ⟨⟨g,hg⟩,?_⟩
    intro x
    obtain ⟨y,rfl⟩ := (coreEquiv e₁ e₂ hc hd).surjective x
    have he : (⟨g * coreEquiv e₁ e₂ hc hd y * g⁻¹,
        (hJC hg _).mp (coreEquiv e₁ e₂ hc hd y).property⟩ :
        ↥(H₁.pCoreIn 2 ⊔ H₂.pCoreIn 2)) =
        coreEquiv e₁ e₂ hc hd (y.1,coreConj b y.2) := by
      apply Subtype.ext
      exact (coreMap_conj_second e₁ e₂ hc b y).symm
    rw [he,pairProjection_apply,pairProjection_apply,projection_coreConj]
  · obtain ⟨t,ht,he⟩ := hex
    refine ⟨⟨t,ht⟩,?_⟩
    rw [pairProjection_first,pairProjection_second,Subgroup.map_sup,
      map_pCoreIn_of_injective 2 H₁ _ (MulAut.conj t).injective,he]
    exact congrArg (fun P : Subgroup G => H₂.pCoreIn 2 ⊔ P)
      (mem_normalizer_iff_map_conj_eq.mp (hJA ht))

/-- The core of two commuting disjoint Borel factors has an irreducible
paired four-group quotient under their independent actors and an exchanger. -/
theorem paired_borel_core_irreducible
    (J H₁ H₂ A C : Subgroup G) (e₁ : H₁ ≃* BorelModel) (e₂ : H₂ ≃* BorelModel)
    (hd : Disjoint H₁ H₂) (hc : H₁ ≤ centralizer (H₂ : Set G))
    (h₁ : H₁ ≤ J) (h₂ : H₂ ≤ J)
    (hA : A = vectors.map (H₁.subtype.comp e₁.symm.toMonoidHom) ⊔
      vectors.map (H₂.subtype.comp e₂.symm.toMonoidHom))
    (hC : C = H₁.pCoreIn 2 ⊔ H₂.pCoreIn 2)
    (hJA : J ≤ normalizer (A : Set G)) (hJC : J ≤ normalizer (C : Set G))
    (hex : ∃ t ∈ J, H₁.map (MulAut.conj t).toMonoidHom = H₂) :
    Stellmacher.IsIrreducibleSection J A C :=
  (pairedFourQuotient J H₁ H₂ A C e₁ e₂ hd hc h₁ h₂ hA hC hJA hJC hex).irreducible

end BinaryPermutation.AlternatingFiveExtension.PairedCoreQuotient
