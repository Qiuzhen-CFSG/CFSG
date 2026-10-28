module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.TwoBlock.Factor

/-!
# The natural factor family modulo a central covering kernel

Every quotient of F=UUˣ whose kernel lies in D has exactly the two maximum
elementary images U and Uˣ. Fixed points lift through this kernel by the
original natural-cover theorem, so the full-cover B.2.21 argument applies.
This includes the actual factor images in S/C_S(K₁K₂).

Source: Aschbacher–Smith, C.5.6(7), printed p.159.
-/
@[expose] public section
open Subgroup
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
variable {G : Type*} [Group G] {R K : Subgroup G} {𝔽 : Type*} [Field 𝔽]
variable {T : Type*} [Group T] {x : G}

noncomputable abbrev factor (K : Subgroup G) (x : G) : Subgroup G :=
  U K ⊔ (U K).map (MulAut.conj x⁻¹).toMonoidHom

noncomputable def factorImage (f : factor K x →* T) (B : Subgroup G) : Subgroup T :=
  (B.subgroupOf (factor K x)).map f

private theorem image_mem (f : factor K x →* T) (B : Subgroup G)
    (hk : f.ker ≤ B.subgroupOf (factor K x)) (s : factor K x) :
    f s ∈ factorImage f B ↔ (s : G) ∈ B := by
  change f s ∈ (B.subgroupOf (factor K x)).map f ↔ _
  rw [← mem_comap, comap_map_eq, sup_eq_left.mpr hk]
  rfl

private theorem fixed_lift (h : Setup R K 𝔽)
    (f : factor K x →* T) (hk : f.ker ≤ (D R K).subgroupOf (factor K x))
    (hAS : factor K x ≤ S R) (s : factor K x) (u : U K)
    (hu : f (s * inclusion (show U K ≤ factor K x from le_sup_left) u * s⁻¹) =
      f (inclusion (show U K ≤ factor K x from le_sup_left) u)) :
    moduleConjugate h.coordinates.normalizes (inclusion hAS s) u = u := by
  apply h.fixedLift
  have hdiff : moduleConjugate h.coordinates.normalizes (inclusion hAS s) u / u ∈
      h.coordinates.projection.ker := by
    apply (h.coordinates.projection_kernel _).mpr
    let uA : factor K x := inclusion (show U K ≤ factor K x from le_sup_left) u
    have hd : s * uA * s⁻¹ / uA ∈ f.ker := by
      change f _ = 1
      rw [map_div, hu, div_self']
    exact (hk hd).2
  have he : h.coordinates.projection (moduleConjugate h.coordinates.normalizes (inclusion hAS s) u) /
      h.coordinates.projection u = 1 := by simpa only [MonoidHom.mem_ker, map_div] using hdiff
  exact div_eq_one.mp he

variable [Finite G]

theorem Setup.factor_quotient_family (h : Setup R K 𝔽)
    (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (U K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U K : Set G))
    (f : factor K x →* T) (hf : Function.Surjective f)
    (hk : f.ker ≤ (D R K).subgroupOf (factor K x)) :
    Stellmacher.elementaryAbelianMaxSubgroups (⊤ : Subgroup T) =
      {factorImage f (U K), factorImage f ((U K).map (MulAut.conj x⁻¹).toMonoidHom)} := by
  let : Finite T := Finite.of_surjective f hf
  let A := factor K x
  let V := (U K).map (MulAut.conj x⁻¹).toMonoidHom
  let U₀ := (U K).subgroupOf A
  let V₀ := V.subgroupOf A
  let B := factorImage f (U K)
  let C := factorImage f V
  have hUA : U K ≤ A := le_sup_left
  have hVA : V ≤ A := le_sup_right
  have hAS : A ≤ S R := sup_le h.module_le (h.conjugate_le hx)
  have hd := h.conjugate_factor_structure hx hnc
  have hNU : f.ker ≤ U₀ := by
    intro a ha
    exact (hd.2.2.2.1.le ⟨a.property, hk ha⟩).1
  have hNV : f.ker ≤ V₀ := by
    intro a ha
    have hu : (a : G) ∈ U K := hNU ha
    have hv : (a : G) ∈ U K ⊓ centralizer (V : Set G) :=
      ⟨hu, (h.factorization hx hnc).centralizes (hk ha)⟩
    rw [← (h.commutator_eq_fixed hx hnc).1, (h.commutator_eq_fixed hx hnc).2] at hv
    exact hv.2
  let := h.elementary
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.map (MulAut.conj x⁻¹).toMonoidHom
  let : IsElementaryAbelian 2 U₀ := IsElementaryAbelian.subgroupOf hUA
  let : IsElementaryAbelian 2 V₀ := IsElementaryAbelian.subgroupOf hVA
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map f
  let : IsElementaryAbelian 2 C := IsElementaryAbelian.map f
  let : U₀.Normal := normal_subgroupOf_of_le_normalizer (hAS.trans h.coordinates.normalizes)
  let : B.Normal := Subgroup.Normal.map (inferInstance : U₀.Normal) f hf
  have hspan : B ⊔ C = ⊤ := by
    change U₀.map f ⊔ V₀.map f = ⊤
    rw [← Subgroup.map_sup, ← subgroupOf_sup hUA hVA, subgroupOf_self, map_top_of_surjective f hf]
  have hself : centralizer (B : Set T) = B := by
    apply le_antisymm
    · intro t ht
      obtain ⟨s,rfl⟩ := hf t
      apply (image_mem f _ hNU s).mpr
      apply (hd.2.2.1.le ⟨s.property, ?_⟩)
      rw [h.core]
      refine ⟨hAS s.property, ?_⟩
      intro u hu
      let u₀ : U K := ⟨u,hu⟩
      have hm : f (inclusion hUA u₀) ∈ B := mem_map_of_mem f hu
      have he : f (s * inclusion hUA u₀ * s⁻¹) = f (inclusion hUA u₀) := by
        rw [map_mul,map_mul,map_inv,← ht _ hm,mul_inv_cancel_right]
      have he' := congrArg Subtype.val (fixed_lift h f hk hAS s u₀ he)
      exact (mul_inv_eq_iff_eq_mul.mp he').symm
    · exact le_centralizer _
  have hne : ¬ C ≤ B := by
    intro he
    apply hnc
    intro v hv
    have hh := he (mem_map_of_mem f (show (⟨v,hVA hv⟩ : A) ∈ V₀ from hv))
    have hu := (image_mem f _ hNU ⟨v,hVA hv⟩).mp hh
    exact le_centralizer (U K) hu
  have hfix (t : T) (ht : t ∉ B) : B ⊓ centralizer ({t} : Set T) = B ⊓ C := by
    obtain ⟨s,rfl⟩ := hf t
    have hsQ : (s : G) ∉ Q R K := by
      intro hs
      exact ht (mem_map_of_mem f (hd.2.2.1.le ⟨s.property,hs⟩))
    apply le_antisymm
    · rintro z ⟨⟨u,hu,rfl⟩,hufix⟩
      refine ⟨mem_map_of_mem f hu, ?_⟩
      let u₀ : U K := ⟨u,hu⟩
      have he : f (s * inclusion hUA u₀ * s⁻¹) = f (inclusion hUA u₀) := by
        change f (s * u * s⁻¹) = f u
        rw [map_mul,map_mul,map_inv,← mem_centralizer_singleton_iff.mp hufix,mul_inv_cancel_right]
      have hv := h.fixed_module_mem_conjugate hx hnc (inclusion hAS s) hsQ u₀
        (fixed_lift h f hk hAS s u₀ he)
      exact mem_map_of_mem f hv
    · rintro z ⟨hzB,hzC⟩
      refine ⟨hzB,?_⟩
      have hc : z ∈ centralizer ((B ⊔ C : Subgroup T) : Set T) := by
        rw [sup_eq_closure,centralizer_closure]
        rintro a (ha | ha)
        · exact le_centralizer B hzB a ha
        · exact le_centralizer C hzC a ha
      rw [hspan] at hc
      exact fun a _ => hc a (mem_top a)
  have hcard : Nat.card B = Nat.card C := by
    have hc : Nat.card U₀ = Nat.card V₀ := by
      rw [Nat.card_congr (subgroupOfEquivOfLe hUA).toEquiv,
        Nat.card_congr (subgroupOfEquivOfLe hVA).toEquiv,
        card_map_of_injective (MulAut.conj x⁻¹).injective]
    have h1 := relIndex_mul_relIndex (⊥ : Subgroup A) f.ker U₀ bot_le hNU
    have h2 := relIndex_mul_relIndex (⊥ : Subgroup A) f.ker V₀ bot_le hNV
    rw [relIndex_bot_left,relIndex_bot_left] at h1 h2
    have hi : f.ker.relIndex U₀ = f.ker.relIndex V₀ := by
      have hp : 0 < Nat.card f.ker := Nat.card_pos
      nlinarith
    simpa only [B,C,factorImage,← relIndex_ker] using hi
  exact family_pair B C hself hspan hne hfix hcard
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne

public section
open Subgroup
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
variable {G T : Type*} [Group G] [Finite G] [Group T]
variable {R K : Subgroup G} {𝔽 : Type*} [Field 𝔽] {x : G}

/-- The theorem on the literal factor image under a homomorphism on S. -/
theorem Setup.factor_image_family (h : Setup R K 𝔽)
    (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (U K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U K : Set G))
    (f : S R →* T) (hk : f.ker ≤ (D R K).subgroupOf (S R)) :
    Stellmacher.elementaryAbelianMaxSubgroups (((factor K x).subgroupOf (S R)).map f) =
      {((U K).subgroupOf (S R)).map f,
        (((U K).map (MulAut.conj x⁻¹).toMonoidHom).subgroupOf (S R)).map f} := by
  let A := factor K x
  let B := (A.subgroupOf (S R)).map f
  have hAS : A ≤ S R := sup_le h.module_le (h.conjugate_le hx)
  let g : A →* B := (f.comp (inclusion hAS)).codRestrict B (fun a => mem_map_of_mem f a.property)
  have hg : Function.Surjective g := by
    rintro ⟨b,s,hs,rfl⟩
    exact ⟨⟨s,hs⟩,rfl⟩
  have hgk : g.ker ≤ (D R K).subgroupOf A := by
    intro a ha
    apply hk (show inclusion hAS a ∈ f.ker from ?_)
    change f (inclusion hAS a) = 1
    exact congrArg Subtype.val (show g a = 1 from ha)
  have hfamily := h.factor_quotient_family hx hnc g hg hgk
  have him (W : Subgroup G) (hWA : W ≤ A) :
      (factorImage g W).map B.subtype = (W.subgroupOf (S R)).map f := by
    ext t
    constructor
    · rintro ⟨_,⟨a,ha,rfl⟩,rfl⟩
      exact ⟨inclusion hAS a,ha,rfl⟩
    · rintro ⟨s,hs,rfl⟩
      exact ⟨g ⟨s,hWA hs⟩,⟨⟨s,hWA hs⟩,hs,rfl⟩,rfl⟩
  ext W
  constructor
  · intro hW
    have hh := (max_restrict hW.1).mpr hW
    rw [hfamily] at hh
    rcases Set.mem_insert_iff.mp hh with hh | hh
    · have he := congrArg (map B.subtype) hh
      rw [map_subgroupOf_eq_of_le hW.1,him _ le_sup_left] at he
      exact Set.mem_insert_iff.mpr (Or.inl he)
    · have he := congrArg (map B.subtype) (Set.mem_singleton_iff.mp hh)
      rw [map_subgroupOf_eq_of_le hW.1,him _ le_sup_right] at he
      exact Set.mem_insert_of_mem _ (Set.mem_singleton_iff.mpr he)
  · intro hW
    have hmax (C : Subgroup B) (hC : C ∈ Stellmacher.elementaryAbelianMaxSubgroups (⊤ : Subgroup B)) :
        C.map B.subtype ∈ Stellmacher.elementaryAbelianMaxSubgroups B := by
      apply (max_restrict (map_subtype_le C)).mp
      have he : (C.map B.subtype).subgroupOf B = C := by
        ext c
        constructor
        · rintro ⟨d,hd,he⟩
          exact (B.subtype_injective he) ▸ hd
        · intro hc
          exact ⟨c,hc,rfl⟩
      rwa [he]
    rcases Set.mem_insert_iff.mp hW with rfl | hW
    · rw [← him _ le_sup_left]
      apply hmax
      rw [hfamily]
      exact Set.mem_insert _ _
    · obtain rfl := Set.mem_singleton_iff.mp hW
      rw [← him _ le_sup_right]
      apply hmax
      rw [hfamily]
      exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
