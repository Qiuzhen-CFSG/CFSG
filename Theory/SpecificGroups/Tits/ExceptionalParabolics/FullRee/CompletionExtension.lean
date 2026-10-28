module
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.CompletionPresentation
public import Mathlib.GroupTheory.SemidirectProduct
/-!
# Extending the marked Tits embedding to the full binary Ree completion

The actual full model is the product of its simple derived subgroup and its
Borel. Their literal conjugation action gives a surjective semidirect-product
map. Compatible maps on those two factors descend through its kernel; agreement
on the actual intersection is enough.

For a faithful completion satisfying the canonical braid, the checked Tits
embedding agrees on both derived parabolics. Those local equations prove
conjugation compatibility with the original Borel and agreement on the whole
intersection. The descended full-model map agrees with both original endpoint
inclusions, hence is surjective. It is injective because conjugation on the
Tits carrier is faithful. Thus the resulting equivalence retains every mark.

The only additional input is the explicitly named canonical braid; geometric
smallness and pointed local selection supply it in the final source assembly.
No classification, ambient finiteness, or source group-order premise is used.

Source: Aschbacher--Smith F.4.8 and F.4.15--17, pp.278 and281--283;
Parrott (1972), p.683.
-/

@[expose] public section
noncomputable section
namespace Tits.ExceptionalParabolics.FullRee.CompletionExtension

/-- The derived subgroup together with the actual Borel generates the full Ree group. -/
theorem derived_sup_borel : commutator (ReeF4.Model 0) ⊔ FullRee.B = ⊤ := by
  let H := commutator (ReeF4.Model 0) ⊔ FullRee.B
  have hd : H.index ∣ 2 := by
    simpa only [derived_index] using Subgroup.index_dvd_of_le
      (show commutator (ReeF4.Model 0) ≤ H from le_sup_left)
  rcases (Nat.dvd_prime (by decide : Nat.Prime 2)).mp hd with h1 | h2
  · exact Subgroup.index_eq_one.mp h1
  · have hc := H.card_mul_index
    rw [h2, group_card] at hc
    have hc' : Nat.card H = 17971200 := by omega
    have hb := Subgroup.card_dvd_of_le (show FullRee.B ≤ H from le_sup_right)
    rw [borel_card, hc'] at hb
    norm_num at hb

/-- The original conjugation action of the Borel on the simple derived carrier. -/
def borelAction : FullRee.B →* MulAut Atlas1600Group := atlasAction.comp FullRee.B.subtype

theorem model_compatibility (b : FullRee.B) :
    atlasEmbedding.comp (borelAction b).toMonoidHom =
      (MulAut.conj (b : ReeF4.Model 0)).toMonoidHom.comp atlasEmbedding := by
  apply MonoidHom.ext
  intro n
  exact atlasAction_apply b n

/-- Multiplication from the literal semidirect product onto the full model. -/
def productMap : Atlas1600Group ⋊[borelAction] FullRee.B →* ReeF4.Model 0 :=
  SemidirectProduct.lift atlasEmbedding FullRee.B.subtype model_compatibility

theorem productMap_surjective : Function.Surjective productMap := by
  intro g
  have hg : g ∈ commutator (ReeF4.Model 0) ⊔ FullRee.B := by rw [derived_sup_borel]; trivial
  obtain ⟨d, hd, b, hb, hdb⟩ := Subgroup.mem_sup_of_normal_left.mp hg
  rw [← atlasEmbedding_range] at hd
  obtain ⟨n, rfl⟩ := hd
  exact ⟨⟨n, ⟨b, hb⟩⟩, hdb⟩

variable {G : Type*} [Group G] (f : Atlas1600Group →* G) (j : FullRee.B →* G)
variable (ha : ∀ b, f.comp (borelAction b).toMonoidHom = (MulAut.conj (j b)).toMonoidHom.comp f)
variable (hc : ∀ n (hn : atlasEmbedding n ∈ FullRee.B), f n = j ⟨atlasEmbedding n, hn⟩)

def sourceProduct : Atlas1600Group ⋊[borelAction] FullRee.B →* G :=
  SemidirectProduct.lift f j ha

include hc in
theorem product_kernel_le : productMap.ker ≤ (sourceProduct f j ha).ker := by
  intro a ha'
  have he : atlasEmbedding a.left * (a.right : ReeF4.Model 0) = 1 := ha'
  have he' : atlasEmbedding a.left = (a.right : ReeF4.Model 0)⁻¹ :=
    eq_inv_iff_mul_eq_one.mpr he
  have hm : atlasEmbedding a.left ∈ FullRee.B := by rw [he']; exact FullRee.B.inv_mem a.right.property
  change f a.left * j a.right = 1
  rw [hc a.left hm, ← map_mul]
  have hz : (⟨atlasEmbedding a.left, hm⟩ : FullRee.B) * a.right = 1 := Subtype.ext he
  rw [hz, map_one]

/-- Compatible maps on the derived group and Borel descend to the actual full model. -/
def modelLift : ReeF4.Model 0 →* G :=
  productMap.liftOfSurjective productMap_surjective
    ⟨sourceProduct f j ha, product_kernel_le f j ha hc⟩

theorem modelLift_comp : (modelLift f j ha hc).comp productMap = sourceProduct f j ha := by
  exact congrArg Subtype.val
    ((productMap.liftOfSurjective productMap_surjective).symm_apply_apply
      ⟨sourceProduct f j ha, product_kernel_le f j ha hc⟩)

@[simp] theorem modelLift_atlas (n : Atlas1600Group) :
    modelLift f j ha hc (atlasEmbedding n) = f n := by
  have he := DFunLike.congr_fun (modelLift_comp f j ha hc) (SemidirectProduct.inl n)
  have hp : productMap (SemidirectProduct.inl n) = atlasEmbedding n :=
    SemidirectProduct.lift_inl atlasEmbedding FullRee.B.subtype model_compatibility n
  rw [MonoidHom.comp_apply, hp] at he
  simpa only [sourceProduct, SemidirectProduct.lift_inl] using he

@[simp] theorem modelLift_borel (b : FullRee.B) :
    modelLift f j ha hc b = j b := by
  have he := DFunLike.congr_fun (modelLift_comp f j ha hc) (SemidirectProduct.inr b)
  have hp : productMap (SemidirectProduct.inr b) = (b : ReeF4.Model 0) :=
    SemidirectProduct.lift_inr atlasEmbedding FullRee.B.subtype model_compatibility b
  rw [MonoidHom.comp_apply, hp] at he
  simpa only [sourceProduct, SemidirectProduct.lift_inr] using he

/-- A map of the full Ree group is faithful as soon as its restriction to the
simple derived subgroup is faithful. -/
theorem hom_injective_of_atlas (F : ReeF4.Model 0 →* G)
    (hf : Function.Injective (F.comp atlasEmbedding)) : Function.Injective F := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply (Subgroup.eq_bot_iff_forall _).mpr
  intro g hg
  have hact : atlasAction g = 1 := by
    apply MulEquiv.ext
    intro n
    apply hf
    change F (atlasEmbedding (atlasAction g n)) = F (atlasEmbedding n)
    rw [atlasAction_apply, map_mul, map_mul, map_inv, MonoidHom.mem_ker.mp hg,
      inv_one, one_mul, mul_one]
  exact atlasAction_injective (hact.trans atlasAction.map_one.symm)

theorem modelLift_injective (hf : Function.Injective f) : Function.Injective (modelLift f j ha hc) := by
  apply hom_injective_of_atlas
  have he : (modelLift f j ha hc).comp atlasEmbedding = f := MonoidHom.ext (modelLift_atlas f j ha hc)
  rwa [he]

end Tits.ExceptionalParabolics.FullRee.CompletionExtension

namespace Tits.ExceptionalParabolics.FullRee.CompletionPresentation
open Theory.GroupTheory
open CompletionExtension
variable {G : Type*} [Group G] (c : RankTwoAmalgam.FaithfulCompletion FullRee.amalgam (G := G))

private theorem first_preimage {x : Atlas1600Group} (hx : atlasEmbedding x ∈ FullRee.first) :
    x ∈ ExceptionalParabolics.first := by
  have hm : atlasEmbedding x ∈ ExceptionalParabolics.first.map atlasEmbedding := by
    rw [atlas_first_map]
    exact ⟨hx, atlasEmbedding_range ▸ (show atlasEmbedding x ∈ atlasEmbedding.range from ⟨x, rfl⟩)⟩
  obtain ⟨y, hy, he⟩ := hm
  exact atlasEmbedding_injective he ▸ hy

private theorem second_preimage {x : Atlas1600Group} (hx : atlasEmbedding x ∈ FullRee.second) :
    x ∈ ExceptionalParabolics.second := by
  have hm : atlasEmbedding x ∈ ExceptionalParabolics.second.map atlasEmbedding := by
    rw [atlas_second_map]
    exact ⟨hx, atlasEmbedding_range ▸ (show atlasEmbedding x ∈ atlasEmbedding.range from ⟨x, rfl⟩)⟩
  obtain ⟨y, hy, he⟩ := hm
  exact atlasEmbedding_injective he ▸ hy

private theorem atlasLift_conj_left (hbraid : CanonicalBraid c) (b : FullRee.first)
    (x : Atlas1600Group) (hx : x ∈ ExceptionalParabolics.first) :
    atlasLift c hbraid (atlasAction b x) =
      c.left b * atlasLift c hbraid x * (c.left b)⁻¹ := by
  have hxm : atlasEmbedding x ∈ FullRee.first := atlas_first_map_le ⟨x, hx, rfl⟩
  have hym : atlasEmbedding (atlasAction b x) ∈ FullRee.first := by
    rw [atlasAction_apply]
    exact FullRee.first.mul_mem (FullRee.first.mul_mem b.property hxm)
      (FullRee.first.inv_mem b.property)
  rw [atlasLift_left c hbraid _ (first_preimage hym), atlasLift_left c hbraid x hx,
    ← map_inv, ← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (atlasAction_apply b x)

private theorem atlasLift_conj_right (hbraid : CanonicalBraid c) (b : FullRee.second)
    (x : Atlas1600Group) (hx : x ∈ ExceptionalParabolics.second) :
    atlasLift c hbraid (atlasAction b x) =
      c.right b * atlasLift c hbraid x * (c.right b)⁻¹ := by
  have hxm : atlasEmbedding x ∈ FullRee.second := atlas_second_map_le ⟨x, hx, rfl⟩
  have hym : atlasEmbedding (atlasAction b x) ∈ FullRee.second := by
    rw [atlasAction_apply]
    exact FullRee.second.mul_mem (FullRee.second.mul_mem b.property hxm)
      (FullRee.second.inv_mem b.property)
  rw [atlasLift_right c hbraid _ (second_preimage hym), atlasLift_right c hbraid x hx,
    ← map_inv, ← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (atlasAction_apply b x)

/-- The marked Tits embedding intertwines the original Borel action. -/
theorem atlasLift_borel_action (hbraid : CanonicalBraid c) (b : FullRee.B) :
    (atlasLift c hbraid).comp (borelAction b).toMonoidHom =
      (MulAut.conj (c.middle b)).toMonoidHom.comp (atlasLift c hbraid) := by
  apply MonoidHom.eq_of_eqOn_dense atlas1600ParrottAssignment_generates
  rintro x ⟨i, rfl⟩
  change atlasLift c hbraid (atlasAction b (atlas1600ParrottAssignment i)) =
    c.middle b * atlasLift c hbraid (atlas1600ParrottAssignment i) * (c.middle b)⁻¹
  by_cases hi : i = .r8
  · have hb : c.middle b = c.right ⟨b, borel_le_second b.property⟩ :=
      DFunLike.congr_fun c.compatible b
    rw [hb]
    exact atlasLift_conj_right c hbraid ⟨b, borel_le_second b.property⟩ _
      (second_preimage (modelGenerator_mem_second i (by rw [hi]; decide)))
  · exact atlasLift_conj_left c hbraid ⟨b, borel_le_first b.property⟩ _
      (first_preimage (modelGenerator_mem_first i hi))

/-- The two maps already agree on their full actual intersection. -/
theorem atlasLift_borel_agrees (hbraid : CanonicalBraid c) (n : Atlas1600Group)
    (hn : atlasEmbedding n ∈ FullRee.B) :
    atlasLift c hbraid n = c.middle ⟨atlasEmbedding n, hn⟩ := by
  exact atlasLift_left c hbraid n (first_preimage (borel_le_first hn))

/-- The actual full Ree model maps to the original completion, with no extension certificate input. -/
def fullLift (hbraid : CanonicalBraid c) : ReeF4.Model 0 →* G :=
  modelLift (atlasLift c hbraid) c.middle (atlasLift_borel_action c hbraid)
    (atlasLift_borel_agrees c hbraid)

@[simp] theorem fullLift_atlas (hbraid : CanonicalBraid c) (n : Atlas1600Group) :
    fullLift c hbraid (atlasEmbedding n) = atlasLift c hbraid n := modelLift_atlas ..

@[simp] theorem fullLift_borel (hbraid : CanonicalBraid c) (b : FullRee.B) :
    fullLift c hbraid b = c.middle b := modelLift_borel ..

/-- The full map retains the exact first inclusion. -/
@[simp] theorem fullLift_left (hbraid : CanonicalBraid c) (x : FullRee.first) :
    fullLift c hbraid x = c.left x := by
  obtain ⟨a, ha⟩ := productMap_surjective (x : ReeF4.Model 0)
  have he : atlasEmbedding a.left * (a.right : ReeF4.Model 0) = x := ha
  have hm : atlasEmbedding a.left ∈ FullRee.first := by
    have hh : atlasEmbedding a.left = (x : ReeF4.Model 0) * (a.right : ReeF4.Model 0)⁻¹ :=
      (eq_mul_inv_iff_mul_eq).mpr he
    rw [hh]
    exact FullRee.first.mul_mem x.property (FullRee.first.inv_mem (borel_le_first a.right.property))
  rw [← he, map_mul, fullLift_atlas, fullLift_borel,
    atlasLift_left c hbraid _ (first_preimage hm)]
  change c.left ⟨atlasEmbedding a.left, _⟩ * c.left ⟨a.right, borel_le_first a.right.property⟩ = _
  rw [← map_mul]
  exact congrArg c.left (Subtype.ext he)

/-- The full map also retains the exact second inclusion. -/
@[simp] theorem fullLift_right (hbraid : CanonicalBraid c) (x : FullRee.second) :
    fullLift c hbraid x = c.right x := by
  obtain ⟨a, ha⟩ := productMap_surjective (x : ReeF4.Model 0)
  have he : atlasEmbedding a.left * (a.right : ReeF4.Model 0) = x := ha
  have hm : atlasEmbedding a.left ∈ FullRee.second := by
    have hh : atlasEmbedding a.left = (x : ReeF4.Model 0) * (a.right : ReeF4.Model 0)⁻¹ :=
      (eq_mul_inv_iff_mul_eq).mpr he
    rw [hh]
    exact FullRee.second.mul_mem x.property (FullRee.second.inv_mem (borel_le_second a.right.property))
  rw [← he, map_mul, fullLift_atlas, fullLift_borel,
    atlasLift_right c hbraid _ (second_preimage hm)]
  have hb : c.middle a.right = c.right ⟨a.right, borel_le_second a.right.property⟩ :=
    DFunLike.congr_fun c.compatible a.right
  rw [hb, ← map_mul]
  exact congrArg c.right (Subtype.ext he)

theorem fullLift_surjective (hbraid : CanonicalBraid c) : Function.Surjective (fullLift c hbraid) := by
  apply MonoidHom.range_eq_top.mp
  apply top_unique
  rw [← c.generated]
  apply sup_le
  · rintro y ⟨x, rfl⟩
    exact ⟨x, fullLift_left c hbraid x⟩
  · rintro y ⟨x, rfl⟩
    exact ⟨x, fullLift_right c hbraid x⟩

theorem fullLift_injective (hbraid : CanonicalBraid c) : Function.Injective (fullLift c hbraid) :=
  modelLift_injective _ _ _ _ (atlasLift_injective c hbraid)

/-- Canonical braid plus the original faithful inclusions gives compatible full Ree recognition. -/
def fullEquiv (hbraid : CanonicalBraid c) : ReeF4.Model 0 ≃* G :=
  MulEquiv.ofBijective (fullLift c hbraid)
    ⟨fullLift_injective c hbraid, fullLift_surjective c hbraid⟩

@[simp] theorem fullEquiv_left (hbraid : CanonicalBraid c) (x : FullRee.first) :
    fullEquiv c hbraid x = c.left x := fullLift_left c hbraid x

@[simp] theorem fullEquiv_right (hbraid : CanonicalBraid c) (x : FullRee.second) :
    fullEquiv c hbraid x = c.right x := fullLift_right c hbraid x

@[simp] theorem fullEquiv_middle (hbraid : CanonicalBraid c) (x : FullRee.B) :
    fullEquiv c hbraid x = c.middle x := fullLift_borel c hbraid x

end Tits.ExceptionalParabolics.FullRee.CompletionPresentation

namespace Tits.ExceptionalParabolics.FullRee.CompletionPresentation
open ReeF4.Parabolics.Binary.FixedGeometry

/-- The first canonical presentation mark is the actual Suzuki Weyl lift. -/
theorem modelGenerator_r1 : modelGenerator .r1 = weylLift 0 .suzuki := by
  change atlasEmbedding (atlas1600ParrottAssignment .r1) = _
  apply ReeF4.toSplitGroup_injective 0
  rw [atlasEmbedding_generator_matrix, toSplitGroup_weylLift]
  rfl

/-- The second canonical presentation mark is the actual linear Weyl lift. -/
theorem modelGenerator_r8 : modelGenerator .r8 = weylLift 0 .linear := by
  change atlasEmbedding (atlas1600ParrottAssignment .r8) = _
  apply ReeF4.toSplitGroup_injective 0
  rw [atlasEmbedding_generator_matrix, toSplitGroup_weylLift]
  rfl

end Tits.ExceptionalParabolics.FullRee.CompletionPresentation

namespace Tits.ExceptionalParabolics.FullRee.CompletionPresentation
open Theory.GroupTheory ReeF4.Parabolics.Binary.FixedGeometry
variable {G : Type*} [Group G] (c : RankTwoAmalgam.FaithfulCompletion FullRee.amalgam (G := G))

theorem sourceGenerator_r1 : sourceGenerator c .r1 =
    c.left ⟨weylLift 0 .suzuki, weylLift_mem_seed 0 .suzuki⟩ := by
  rw [sourceGenerator_left c .r1 (by decide)]
  change c.left ⟨modelGenerator .r1, _⟩ = _
  exact congrArg c.left (Subtype.ext modelGenerator_r1)

theorem sourceGenerator_r8 : sourceGenerator c .r8 =
    c.right ⟨weylLift 0 .linear, weylLift_mem_seed 0 .linear⟩ := by
  rw [sourceGenerator_right c .r8 (by decide)]
  change c.right ⟨modelGenerator .r8, _⟩ = _
  exact congrArg c.right (Subtype.ext modelGenerator_r8)

/-- The presentation's sole mixed relation is exactly the original Weyl-marked braid. -/
theorem canonicalBraid_iff_weyl : CanonicalBraid c ↔
    (c.left ⟨weylLift 0 .suzuki, weylLift_mem_seed 0 .suzuki⟩ *
      c.right ⟨weylLift 0 .linear, weylLift_mem_seed 0 .linear⟩) ^ 8 = 1 := by
  rw [CanonicalBraid, sourceGenerator_r1, sourceGenerator_r8]

end Tits.ExceptionalParabolics.FullRee.CompletionPresentation
