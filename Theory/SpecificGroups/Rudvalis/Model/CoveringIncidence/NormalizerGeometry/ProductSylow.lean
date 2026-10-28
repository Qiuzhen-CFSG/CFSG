module

public import Theory.SpecificGroups.Rudvalis.Model.Basic
public import Theory.SpecificGroups.Suzuki.RootOmega
public import Theory.GroupTheory.EmbeddedCenterMap
public import Theory.ElementaryAbelian.Quotient
public import Mathlib.GroupTheory.Abelianization.Defs

/-!
# The four-group times Suzuki Sylow inside the actual Rudvalis model

An injective map from E₄ × Sz(8) determines a two-subgroup of order 256.
Its derived subgroup has order eight, is centralized by the two-subgroup,
and the literal abelianization is elementary of order 32. A split-torus
actor of order seven normalizes it and fixes no nonidentity derived element.
The final application uses the inclusion of an actual involution centralizer.

Source: GLS3, Table 5.3r and printed pp.291–292; Huppert–Blackburn III,
XI.3.1 and XI.3.10. These intrinsic calculations do not assert that the
subgroup is Sylow in a Rudvalis component normalizer or place it in max4.
-/

namespace Rudvalis.CoveringIncidence.NormalizerGeometry
open Subgroup BenderSuzuki.MatrixGroups BenderSuzuki.PFAppendixIII
open scoped IsMulCommutative

variable {E : Type} [Group E]

/-- The root product, before applying the centralizer embedding. -/
@[expose] public noncomputable def rootProduct (E : Type) [Group E] :
    Subgroup (E × SuzukiMatrixGroup 1) :=
  (⊤ : Subgroup E).prod (SuzukiRootSubgroup 1)

/-- The embedded Suzuki root center, with trivial four-group coordinate. -/
@[expose] public noncomputable def rootDerived (E : Type) [Group E] :
    Subgroup (E × SuzukiMatrixGroup 1) :=
  (⊥ : Subgroup E).prod
    ((center (SuzukiRootSubgroup 1)).map (SuzukiRootSubgroup 1).subtype)

private theorem root_commutator :
    _root_.commutator (SuzukiRootSubgroup 1) = center (SuzukiRootSubgroup 1) := by
  let F := BinaryGaloisField 3
  let σ : F ≃+* F := iterateFrobeniusEquiv F 2 2
  have hc := (BenderSuzuki.External.huppert_blackburn_XI_3_1 1 (by decide) σ
    (BenderSuzuki.External.binaryGaloisField_tits_formula_sq 1 σ
      (iterateFrobeniusEquiv_def F 2 2))).2.2.2.2.2.2.2.2.2.1
  change _root_.commutator (SuzukiRootClosure 1) = center (SuzukiRootClosure 1) at hc
  let e : SuzukiRootClosure 1 ≃* SuzukiRootSubgroup 1 :=
    (subgroupOfEquivOfLe (suzukiRootClosure_le 1)).symm
  have hm := congrArg (fun H : Subgroup (SuzukiRootClosure 1) => H.map e.toMonoidHom) hc
  rw [_root_.commutator_def, map_commutator, map_top_of_surjective e.toMonoidHom e.surjective] at hm
  change _root_.commutator (SuzukiRootSubgroup 1) = _ at hm
  rw [hm]
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (centerCongr e ⟨z, hz⟩).property
  · intro hx
    exact ⟨e.symm x, (centerCongr e.symm ⟨x, hx⟩).property, e.apply_symm_apply x⟩

public theorem rootProduct_derived [IsElementaryAbelian 2 E] :
    ⁅rootProduct E, rootProduct E⁆ = rootDerived E := by
  rw [rootProduct, commutator_prod_prod]
  change (_root_.commutator E).prod _ = _
  rw [commutator_eq_bot, ← map_subtype_commutator, root_commutator]
  rfl

public theorem rootDerived_le_rootProduct : rootDerived E ≤ rootProduct E :=
  prod_mono bot_le (map_subtype_le _)

public theorem rootProduct_centralizes_derived :
    rootProduct E ≤ centralizer (rootDerived E : Set (E × SuzukiMatrixGroup 1)) := by
  intro x hx
  apply mem_centralizer_iff.mpr
  rintro y ⟨hy, z, hz, hzy⟩
  apply Prod.ext
  · have hy1 : y.1 = 1 := hy
    simp [hy1]
  · have he := congrArg Subtype.val (mem_center_iff.mp hz ⟨x.2, hx.2⟩)
    change y.2 * x.2 = x.2 * y.2
    change x.2 * (z : SuzukiMatrixGroup 1) = (z : SuzukiMatrixGroup 1) * x.2 at he
    rw [← hzy]
    exact he.symm

public theorem rootProduct_card (hE : Nat.card E = 4) : Nat.card (rootProduct E) = 256 := by
  rw [rootProduct, Nat.card_congr ((⊤ : Subgroup E).prodEquiv (SuzukiRootSubgroup 1)).toEquiv,
    Nat.card_prod, Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup E) ≃* E).toEquiv,
    hE, suzukiRootSubgroup_card 1 (by decide)]
  norm_num

/-- The root product is Sylow in the full centralizer product. -/
@[expose] public noncomputable def rootProductSylow (hE : Nat.card E = 4) :
    Sylow 2 (E × SuzukiMatrixGroup 1) :=
  (IsPGroup.of_card (n := 8) (rootProduct_card hE)).toSylow (by
    rw [rootProduct, index_prod, index_top, one_mul]
    obtain ⟨P, hP⟩ := suzukiRootSubgroup_isSylow 1 (by decide)
    rw [← hP]
    exact P.not_dvd_index)

public theorem rootDerived_card : Nat.card (rootDerived E) = 8 := by
  rw [rootDerived, Nat.card_congr ((⊥ : Subgroup E).prodEquiv
      ((center (SuzukiRootSubgroup 1)).map (SuzukiRootSubgroup 1).subtype)).toEquiv,
    Nat.card_prod, card_bot, one_mul, card_map_of_injective (SuzukiRootSubgroup 1).subtype_injective,
    suzukiRootSubgroup_center_card 1 (by decide)]
  norm_num

/-- The actual ambient image of E₄ times the standard Suzuki Sylow. -/
@[expose] public noncomputable def sylowImage (f : E × SuzukiMatrixGroup 1 →* Model) :
    Subgroup Model := (rootProduct E).map f

/-- This isomorphism identifies the subgroup with the actual root group
factor, rather than only identifying its order. -/
public noncomputable def sylowImageEquiv
    (f : E × SuzukiMatrixGroup 1 →* Model) (hf : Function.Injective f) :
    sylowImage f ≃* E × SuzukiRootSubgroup 1 :=
  ((rootProduct E).equivMapOfInjective f hf).symm.trans
    (((⊤ : Subgroup E).prodEquiv (SuzukiRootSubgroup 1)).trans
      (MulEquiv.prodCongr Subgroup.topEquiv (MulEquiv.refl _)))

/-- The eight-group in that same ambient embedding. -/
@[expose] public noncomputable def derivedImage (f : E × SuzukiMatrixGroup 1 →* Model) :
    Subgroup Model := (rootDerived E).map f

public theorem sylowImage_derived [IsElementaryAbelian 2 E] (f : E × SuzukiMatrixGroup 1 →* Model) :
    ⁅sylowImage f, sylowImage f⁆ = derivedImage f := by
  rw [sylowImage, ← map_commutator, rootProduct_derived, derivedImage]

public theorem derivedImage_le (f : E × SuzukiMatrixGroup 1 →* Model) :
    derivedImage f ≤ sylowImage f := map_mono rootDerived_le_rootProduct

public theorem sylowImage_card (hE : Nat.card E = 4)
    (f : E × SuzukiMatrixGroup 1 →* Model) (hf : Function.Injective f) :
    Nat.card (sylowImage f) = 256 := by
  rw [sylowImage, card_map_of_injective hf, rootProduct_card hE]

public theorem derivedImage_card
    (f : E × SuzukiMatrixGroup 1 →* Model) (hf : Function.Injective f) :
    Nat.card (derivedImage f) = 8 := by
  rw [derivedImage, card_map_of_injective hf, rootDerived_card]

public theorem sylowImage_isPGroup (hE : Nat.card E = 4)
    (f : E × SuzukiMatrixGroup 1 →* Model) (hf : Function.Injective f) :
    IsPGroup 2 (sylowImage f) := IsPGroup.of_card (n := 8) (sylowImage_card hE f hf)

public theorem sylowImage_centralizes_derived (f : E × SuzukiMatrixGroup 1 →* Model) :
    sylowImage f ≤ centralizer (derivedImage f : Set Model) := by
  rintro _ ⟨x, hx, rfl⟩
  apply mem_centralizer_iff.mpr
  rintro _ ⟨y, hy, rfl⟩
  simpa only [map_mul] using congrArg f
    (mem_centralizer_iff.mp (rootProduct_centralizes_derived hx) y hy)

public theorem sylowImage_square_mem_derived [IsElementaryAbelian 2 E] (f : E × SuzukiMatrixGroup 1 →* Model)
    (x : Model) (hx : x ∈ sylowImage f) : x ^ 2 ∈ derivedImage f := by
  obtain ⟨x, hx, rfl⟩ := hx
  rw [← map_pow]
  apply mem_map_of_mem
  refine ⟨?_, ?_⟩
  · exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 E) x.1
  · refine ⟨(⟨x.2, hx.2⟩ : SuzukiRootSubgroup 1) ^ 2, ?_, rfl⟩
    apply (suzukiRootSubgroup_square_iff_center 1 (by decide) _).mp
    rw [← pow_mul]
    exact suzukiRootSubgroup_pow_four 1 (by decide) _

public theorem sylowImage_abelianization_elementary [IsElementaryAbelian 2 E]
    (f : E × SuzukiMatrixGroup 1 →* Model) :
    IsElementaryAbelian 2 (Abelianization (sylowImage f)) := by
  refine { exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_ }
  intro q
  induction q using QuotientGroup.induction_on with | H x => ?_
  change (Abelianization.of x) ^ 2 = 1
  rw [← map_pow, ← MonoidHom.mem_ker, Abelianization.ker_of]
  have hx := sylowImage_square_mem_derived f x x.property
  rw [← sylowImage_derived, ← map_subtype_commutator] at hx
  obtain ⟨y, hy, he⟩ := hx
  exact (Subtype.ext he : y = x ^ 2) ▸ hy

public theorem sylowImage_abelianization_card [IsElementaryAbelian 2 E] (hE : Nat.card E = 4)
    (f : E × SuzukiMatrixGroup 1 →* Model) (hf : Function.Injective f) :
    Nat.card (Abelianization (sylowImage f)) = 32 := by
  have hd : Nat.card (_root_.commutator (sylowImage f)) = 8 := by
    rw [← card_map_of_injective (sylowImage f).subtype_injective,
      map_subtype_commutator, sylowImage_derived, derivedImage_card f hf]
  have hc := (_root_.commutator (sylowImage f)).index_mul_card
  rw [index_eq_card, hd, sylowImage_card hE f hf] at hc
  change Nat.card (Abelianization (sylowImage f)) * 8 = 256 at hc
  omega

/-- The ambient derived subgroup restricts to the intrinsic commutator. -/
public theorem derivedImage_subgroupOf [IsElementaryAbelian 2 E]
    (f : E × SuzukiMatrixGroup 1 →* Model) :
    (derivedImage f).subgroupOf (sylowImage f) = _root_.commutator (sylowImage f) := by
  rw [← sylowImage_derived, ← map_subtype_commutator, subgroupOf,
    comap_map_eq_self_of_injective (sylowImage f).subtype_injective]

public instance derivedImage_normal [IsElementaryAbelian 2 E]
    (f : E × SuzukiMatrixGroup 1 →* Model) :
    ((derivedImage f).subgroupOf (sylowImage f)).Normal := by
  rw [derivedImage_subgroupOf]
  infer_instance

/-- Elementary structure on the literal quotient by the ambient eight-group. -/
public theorem sylowImage_quotient_elementary [IsElementaryAbelian 2 E]
    (f : E × SuzukiMatrixGroup 1 →* Model) :
    IsElementaryAbelian 2 (sylowImage f ⧸ (derivedImage f).subgroupOf (sylowImage f)) := by
  let e : (sylowImage f ⧸ (derivedImage f).subgroupOf (sylowImage f)) ≃*
      Abelianization (sylowImage f) :=
    QuotientGroup.quotientMulEquivOfEq (derivedImage_subgroupOf f)
  let := sylowImage_abelianization_elementary f
  exact IsElementaryAbelian.of_surjective e.symm.toMonoidHom e.symm.surjective

/-- Order of the literal quotient used in the covering incidence. -/
public theorem sylowImage_quotient_card [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 4) (f : E × SuzukiMatrixGroup 1 →* Model)
    (hf : Function.Injective f) :
    Nat.card (sylowImage f ⧸ (derivedImage f).subgroupOf (sylowImage f)) = 32 := by
  rw [derivedImage_subgroupOf]
  exact sylowImage_abelianization_card hE f hf

/-- A genuine order-seven actor in the image normalizes the two-subgroup and
has no nonidentity fixed point on its derived eight-group. -/
public theorem exists_seven_actor
    (f : E × SuzukiMatrixGroup 1 →* Model) (hf : Function.Injective f) :
    ∃ a : Model, a ∈ f.range ∧ orderOf a = 7 ∧
      a ∈ normalizer (sylowImage f : Set Model) ∧
      ∀ v ∈ derivedImage f, Commute a v → v = 1 := by
  let := suzukiSplitTorus_isCyclic 1 (by decide)
  obtain ⟨t, ht⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := SuzukiSplitTorus 1)
  rw [suzukiSplitTorus_card 1 (by decide)] at ht
  have ht7 : orderOf (t : SuzukiMatrixGroup 1) = 7 := by
    exact (orderOf_injective (SuzukiSplitTorus 1).subtype
      (SuzukiSplitTorus 1).subtype_injective t).trans ht
  have htne : (t : SuzukiMatrixGroup 1) ≠ 1 := by
    intro he
    rw [he, orderOf_one] at ht7
    omega
  let a : E × SuzukiMatrixGroup 1 := (1, t)
  have ha7 : orderOf a = 7 := by
    exact (orderOf_injective (MonoidHom.inr E (SuzukiMatrixGroup 1))
      (fun _ _ h => congrArg Prod.snd h) (t : SuzukiMatrixGroup 1)).trans ht7
  have hn : a ∈ normalizer (rootProduct E : Set (E × SuzukiMatrixGroup 1)) := by
    rw [mem_normalizer_iff]
    intro x
    simpa only [rootProduct, a, mem_prod, mem_top, true_and, Prod.snd_mul, Prod.snd_inv] using
      (mem_normalizer_iff.mp (suzukiSplitTorus_le_normalizer_root 1 t.property) x.2)
  refine ⟨f a, ⟨a, rfl⟩, (orderOf_injective f hf a).trans ha7, ?_, ?_⟩
  · exact le_normalizer_map f (mem_map_of_mem f hn)
  · rintro v ⟨x, hx, rfl⟩ hv
    have hx1 : x.1 = 1 := hx.1
    have hr : x.2 ∈ SuzukiRootSubgroup 1 := map_subtype_le _ hx.2
    have hc : Commute (t : SuzukiMatrixGroup 1) x.2 := by
      have he : a * x = x * a := hf (by simpa only [map_mul] using hv.eq)
      exact congrArg Prod.snd he
    have he := suzukiRootSubgroup_eq_one_of_commute_split 1 (by decide)
      t x.2 t.property htne hr hc
    rw [show x = 1 from Prod.ext hx1 he, map_one]

/-- Literal embedding supplied by a centralizer identification. -/
@[expose] public noncomputable def centralizerEmbedding (C : Subgroup Model)
    (e : C ≃* E × SuzukiMatrixGroup 1) : E × SuzukiMatrixGroup 1 →* Model :=
  C.subtype.comp e.symm.toMonoidHom

public theorem centralizerEmbedding_injective (C : Subgroup Model)
    (e : C ≃* E × SuzukiMatrixGroup 1) : Function.Injective (centralizerEmbedding C e) :=
  C.subtype_injective.comp e.symm.injective

/-- The actual centralizer Sylow obtained from its given identification. -/
@[expose] public noncomputable def centralizerSylow (C : Subgroup Model)
    (e : C ≃* E × SuzukiMatrixGroup 1) (hE : Nat.card E = 4) : Sylow 2 C := by
  let : Finite (E × SuzukiMatrixGroup 1) := Finite.of_equiv C e.toEquiv
  exact (rootProductSylow hE).mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective

public theorem centralizerSylow_image (C : Subgroup Model)
    (e : C ≃* E × SuzukiMatrixGroup 1) (hE : Nat.card E = 4) :
    ((centralizerSylow C e hE : Sylow 2 C) : Subgroup C).map C.subtype =
      sylowImage (centralizerEmbedding C e) := by
  change ((rootProduct E).map e.symm.toMonoidHom).map C.subtype = _
  rw [map_map]
  rfl

/-- An odd relative-index normalizer extension preserves this exact Sylow image. -/
public theorem exists_overgroupSylow (C N : Subgroup Model)
    (e : C ≃* E × SuzukiMatrixGroup 1) (hE : Nat.card E = 4)
    (hCN : C ≤ N) (hodd : ¬ 2 ∣ C.relIndex N) :
    ∃ R : Sylow 2 N, (R : Subgroup N).map N.subtype =
      sylowImage (centralizerEmbedding C e) := by
  let f := centralizerEmbedding C e
  let S := centralizerSylow C e hE
  have hRC : sylowImage f ≤ C := by
    rintro _ ⟨x, _, rfl⟩
    exact (e.symm x).property
  have hRN := hRC.trans hCN
  have hi : ¬ 2 ∣ (sylowImage f).relIndex C := by
    have he : (sylowImage f).subgroupOf C = (S : Subgroup C) := by
      rw [← centralizerSylow_image C e hE, subgroupOf,
        comap_map_eq_self_of_injective C.subtype_injective]
    change ¬ 2 ∣ ((sylowImage f).subgroupOf C).index
    rw [he]
    exact S.not_dvd_index
  have hn : ¬ 2 ∣ (sylowImage f).relIndex N := by
    rw [← relIndex_mul_relIndex _ C N hRC hCN]
    intro h
    exact (Nat.prime_two.dvd_mul.mp h).elim hi hodd
  let hp := (sylowImage_isPGroup hE f (centralizerEmbedding_injective C e)).comap_subtype
    (K := N)
  exact ⟨hp.toSylow hn, map_subgroupOf_eq_of_le hRN⟩

/-- Application to the actual centralizer: this constructs the intrinsic
order-256 subgroup and its order-seven actor, without any incidence premise. -/
public theorem centralizer_sylow_geometry [IsElementaryAbelian 2 E] (C : Subgroup Model)
    (e : C ≃* E × SuzukiMatrixGroup 1) (hE : Nat.card E = 4) :
    let f := centralizerEmbedding C e
    Nat.card (sylowImage f) = 256 ∧
    Nat.card (derivedImage f) = 8 ∧
    Nat.card (Abelianization (sylowImage f)) = 32 ∧
    IsElementaryAbelian 2 (Abelianization (sylowImage f)) ∧
    ∃ a : Model, a ∈ C ∧ orderOf a = 7 ∧
      a ∈ normalizer (sylowImage f : Set Model) ∧
      ∀ v ∈ derivedImage f, Commute a v → v = 1 := by
  let f := centralizerEmbedding C e
  have hf := centralizerEmbedding_injective C e
  refine ⟨sylowImage_card hE f hf, derivedImage_card f hf,
    sylowImage_abelianization_card hE f hf, sylowImage_abelianization_elementary f, ?_⟩
  obtain ⟨a, ⟨x, rfl⟩, ha, hn, hv⟩ := exists_seven_actor f hf
  exact ⟨f x, (e.symm x).property, ha, hn, hv⟩

end Rudvalis.CoveringIncidence.NormalizerGeometry
