module

public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankTwoUpper.LinearThreeCover
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankTwoUpper.LinearThree.LocalMembers
public import CFSG.Quasithin.ChapterE.Section01.Inheritance
public import Theory.SpecificGroups.PSL3.LinearThreeFlags.LocalGeneration

/-!
# The actual local pair in an aligned ambient PSL₃ extension

The two local images use exactly `linearThreeEmbedding`; their cores are
the images of their intrinsic two-cores. Alignment with the standard Sylow
determines the full pullback of the ambient Sylow, by Sylow maximality.
Consequently the intrinsic nonbinary E-members transport to the ambient
group as soon as the actual ambient tau lies in the selected local.

These results do not assert that tau has this property, or classify the
action of the ambient Sylow on the pair. Those are the model calculations
needed by the inner-family assembly. Source: Aschbacher--Smith E.1.1--5,
pp.209--210, E.1.14(1), p.214, and F.1.12, pp.263--264.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Matrix.PSL3.LinearThree
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterE.ValuesEvenClassical.RankTwoUpper.LinearThree.InnerFamilies
variable {G F : Type*} [Group G] [Field F] [Finite F]

/-- `true` is the actual point local; `false` is the actual line local. -/
def localModel (F : Type*) [Field F] (b : Bool) : Subgroup PSL(3,F) :=
  if b then pointLocal F else lineLocal F

/-- The selected local, embedded through the original socle equivalence. -/
noncomputable def localImage (L : Subgroup G) (e : L ≃* PSL(3,F)) (b : Bool) :
    Subgroup G := (localModel F b).map (linearThreeEmbedding L e)

/-- The embedded intrinsic two-core of the selected local. -/
noncomputable def coreImage (L : Subgroup G) (e : L ≃* PSL(3,F)) (b : Bool) :
    Subgroup G := (pCore 2 (localImage L e b)).map (localImage L e b).subtype

omit [Finite F] in
theorem embedding_injective (L : Subgroup G) (e : L ≃* PSL(3,F)) :
    Function.Injective (linearThreeEmbedding L e) :=
  Subtype.val_injective.comp e.symm.injective

omit [Finite F] in
theorem unipotent_le_localModel (b : Bool) : unipotent F ≤ localModel F b := by
  cases b
  · exact unipotent_le_lineLocal F
  · exact unipotent_le_pointLocal F

/-- Both local images together are exactly the given socle subgroup. -/
theorem localImages_sup (L : Subgroup G) (e : L ≃* PSL(3,F)) :
    localImage L e true ⊔ localImage L e false = L := by
  change (pointLocal F).map _ ⊔ (lineLocal F).map _ = L
  rw [← Subgroup.map_sup, locals_sup_eq_top, ← MonoidHom.range_eq_map,
    linearThreeEmbedding_range]

variable [Finite G]

omit [Finite G] in
/-- Alignment determines the entire Sylow pullback, not just its inclusion. -/
theorem sylow_comap_eq (L : Subgroup G) (e : L ≃* PSL(3,F))
    (T : Sylow 2 G) {f : ℕ} (hf : 0 < f) (hF : Nat.card F = 2^f)
    (halign : (unipotent F).map (linearThreeEmbedding L e) ≤ (T : Subgroup G)) :
    (T : Subgroup G).comap (linearThreeEmbedding L e) = unipotent F :=
  (unipotentSylow F hf hF).is_maximal'
    (T.isPGroup'.comap_of_injective _ (embedding_injective L e))
    (map_le_iff_le_comap.mp halign)

omit [Finite G] in
/-- The ambient intersection with a local is its actual Sylow two-subgroup. -/
theorem localImage_sylow (L : Subgroup G) (e : L ≃* PSL(3,F))
    (T : Sylow 2 G) {f : ℕ} (hf : 0 < f) (hF : Nat.card F = 2^f)
    (halign : (unipotent F).map (linearThreeEmbedding L e) ≤ (T : Subgroup G))
    (b : Bool) :
    ∃ S : Sylow 2 (localImage L e b),
      (S : Subgroup (localImage L e b)) = (T : Subgroup G).subgroupOf (localImage L e b) := by
  let E : localModel F b ≃* localImage L e b :=
    (localModel F b).equivMapOfInjective (linearThreeEmbedding L e)
    (embedding_injective L e)
  let S := (unipotentSylow F hf hF).subtype (unipotent_le_localModel (F := F) b)
  refine ⟨S.mapSurjective (f := E.toMonoidHom) E.surjective, ?_⟩
  change ((unipotent F).subgroupOf (localModel F b)).map E.toMonoidHom = _
  ext x
  obtain ⟨y, rfl⟩ := E.surjective x
  change E.toMonoidHom y ∈ ((unipotent F).subgroupOf (localModel F b)).map E.toMonoidHom ↔ _
  rw [mem_map_iff_mem E.injective]
  change (y : PSL(3,F)) ∈ unipotent F ↔ linearThreeEmbedding L e y ∈ T
  rw [← sylow_comap_eq L e T hf hF halign]
  rfl

omit [Finite G] in
theorem coreImage_le_sylow (L : Subgroup G) (e : L ≃* PSL(3,F))
    (T : Sylow 2 G) {f : ℕ} (hf : 0 < f) (hF : Nat.card F = 2^f)
    (halign : (unipotent F).map (linearThreeEmbedding L e) ≤ (T : Subgroup G))
    (b : Bool) : coreImage L e b ≤ (T : Subgroup G) := by
  obtain ⟨S, hS⟩ := localImage_sylow L e T hf hF halign b
  have h := (pCore_isPGroup (p := 2) (G := localImage L e b)).le_sylow_of_normal S
  rw [hS] at h
  exact (map_mono h).trans (by rw [subgroupOf_map_subtype]; exact inf_le_left)

omit [Finite F] [Finite G] in
/-- Normality is relative to the local, and then mapped into the common ambient group. -/
theorem localImage_le_coreImage_normalizer (L : Subgroup G)
    (e : L ≃* PSL(3,F)) (b : Bool) :
    localImage L e b ≤ normalizer (coreImage L e b : Set G) := by
  intro x hx
  apply Subgroup.le_normalizer_map (localImage L e b).subtype
  exact ⟨⟨x,hx⟩, by rw [normalizer_eq_top]; trivial, rfl⟩

/-- The nonbinary E-member in an arbitrary aligned ambient extension.
Only the necessary ambient tau containment remains explicit. -/
theorem localImage_isEMemberAt [CharP F 2]
    (L : Subgroup G) (e : L ≃* PSL(3,F))
    (T : Sylow 2 G) {f : ℕ} (hf : 0 < f) (hF : Nat.card F = 2^f)
    (hcard : 4 ≤ Nat.card F)
    (halign : (unipotent F).map (linearThreeEmbedding L e) ≤ (T : Subgroup G))
    (b : Bool) (A : Subgroup G) (hA : IsElementaryAbelian 2 A)
    (hAT : A ≤ (T : Subgroup G)) (hAK : A ≤ localImage L e b)
    (htau : tau (T : Subgroup G) A ≤ localImage L e b)
    (hne : ¬ A ≤ coreImage L e b) :
    IsEMemberAt f (T : Subgroup G) A (localImage L e b) := by
  let E : localModel F b ≃* localImage L e b :=
    (localModel F b).equivMapOfInjective (linearThreeEmbedding L e)
    (embedding_injective L e)
  have hp : Group.IsPerfect (localModel F b) := by
    cases b
    · exact lineLocal_isPerfect F hcard
    · exact pointLocal_isPerfect F hcard
  let := hp
  let : Group.IsPerfect (localImage L e b) :=
    Group.IsPerfect.ofSurjective (f := E.toMonoidHom) E.surjective
  have eq : Nonempty ((localModel F b ⧸ pCore 2 (localModel F b)) ≃* SL(2,F)) := by
    cases b
    · exact ⟨lineLocalCoreQuotientEquiv F⟩
    · exact ⟨pointLocalCoreQuotientEquiv F⟩
  obtain ⟨eq⟩ := eq
  let eq' := (QuotientGroup.congr _ _ E (pCore_map_iso 2 E)).symm.trans eq
  apply isEMemberAt_of_perfect_sl2_quotient (T : Subgroup G) A (localImage L e b)
    hcard eq' hF hA hAT hAK htau (localImage_sylow L e T hf hF halign b)
  intro h
  apply hne
  rw [← map_subgroupOf_eq_of_le hAK]
  exact map_mono h

end CFSG.Quasithin.ChapterE.ValuesEvenClassical.RankTwoUpper.LinearThree.InnerFamilies
