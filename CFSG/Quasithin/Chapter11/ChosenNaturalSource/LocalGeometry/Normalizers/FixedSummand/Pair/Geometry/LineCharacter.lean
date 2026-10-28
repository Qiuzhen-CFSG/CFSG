module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.ScalarGeometry.Coordinates
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.ScalarGeometry.Normalizer
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.ScalarGeometry.Orbit

/-!
# The Cartan character on the original quotient line

The supplied coordinate projection V₁ → f.space 0 is surjective, including
when C_V(L) is nontrivial. Every element of L preserving V₁ therefore has a
unique field scalar on this line. The original Cartan normalizer is transitive
on its nonzero vectors, and its odd Hall Cartan has the same action image.
This yields a surjective scalar character of the actual Cartan subgroup.
The companion splitting module uses its action equation to mark Z₁.

Source: Aschbacher–Smith, 11.1.5, printed p.766, using the flag and Cartan
geometry of 11.0.2 and the opening of §11.1, printed pp.759–761.
-/

open Subgroup Representation
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.Pair
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} {F : BinaryField}
    {c : Coordinates D F} (f : InvariantFlag c)

private theorem exists_line_scalar (l : L)
    (hl : (l : G) ∈ normalizer (f.Vi 0 : Set G)) :
    ∃ a : F.Carrierˣ, ∀ v : Additive (f.Vi 0),
      lineProjection f (lineAction f ⟨l,hl⟩ v) = (a : F.Carrier) • lineProjection f v := by
  let A : f.space 0 →ₗ[F.Carrier] f.space 0 :=
    ((c.modelAction (c.quotientMap l)).comp (f.space 0).subtype).codRestrict _ (by
      intro v
      exact ((c.mem_normalizer_preimage_iff _ l).mp hl v.val).mpr v.property)
  obtain ⟨r,hr,_⟩ := A.existsUnique_eq_smul_id_of_finrank_eq_one (f.dimension 0)
  have he (v : Additive (f.Vi 0)) :
      lineProjection f (lineAction f ⟨l,hl⟩ v) = r • lineProjection f v := by
    apply Subtype.ext
    exact (lineProjection_component f l hl v).trans
      (congrArg Subtype.val (LinearMap.congr_fun hr (lineProjection f v)))
  have hr0 : r ≠ 0 := by
    intro h
    obtain ⟨v,hv,hv0⟩ := (Submodule.ne_bot_iff _).mp (f.space_ne_bot 0)
    obtain ⟨w,hw⟩ := lineProjection_surjective f ⟨v,hv⟩
    have hh := he ((lineAction f ⟨l,hl⟩).symm w)
    rw [LinearEquiv.apply_symm_apply, h, zero_smul, hw] at hh
    exact hv0 (congrArg Subtype.val hh)
  exact ⟨Units.mk0 r hr0, he⟩

private theorem line_scalar_unique {a b : F.Carrierˣ}
    (h : ∀ v : Additive (f.Vi 0),
      (a : F.Carrier) • lineProjection f v = (b : F.Carrier) • lineProjection f v) : a = b := by
  obtain ⟨v,hv,hv0⟩ := (Submodule.ne_bot_iff _).mp (f.space_ne_bot 0)
  obtain ⟨w,hw⟩ := lineProjection_surjective f ⟨v,hv⟩
  apply Units.ext
  apply smul_left_injective F.Carrier (show (⟨v,hv⟩ : f.space 0) ≠ 0 from
    fun he => hv0 (congrArg Subtype.val he))
  simpa only [hw] using h w

/-- The scalar character on the original Cartan normalizer's marked quotient line.
The central kernel of V₁ is retained. -/
@[irreducible] def normalizerLineCharacter
    (hfixed : f.Vi 0 = V ⊓ centralizer (sourceTL T L : Set G)) :
    cartanNormalizer T L →* F.Carrierˣ := by
  let hn := cartanNormalizer_normalizes_line f hfixed
  let s := fun n : cartanNormalizer T L =>
    (exists_line_scalar f ⟨n,n.property.1⟩ (hn n.property)).choose
  have hs (n : cartanNormalizer T L) (v : Additive (f.Vi 0)) :
      lineProjection f (lineAction f (inclusion hn n) v) =
        (s n : F.Carrier) • lineProjection f v :=
    (exists_line_scalar f ⟨n,n.property.1⟩ (hn n.property)).choose_spec v
  refine { toFun := s, map_one' := ?_, map_mul' := ?_ }
  · apply line_scalar_unique f
    intro v
    have hh := hs 1 v
    simp only [map_one] at hh
    change lineProjection f v = (s 1 : F.Carrier) • lineProjection f v at hh
    exact hh.symm.trans (one_smul F.Carrier (lineProjection f v)).symm
  · intro a b
    apply line_scalar_unique f
    intro v
    have hab := hs (a*b) v
    simp only [map_mul, LinearEquiv.mul_apply] at hab
    have ha := hs a (lineAction f (inclusion hn b) v)
    have hb := hs b v
    exact hab.symm.trans (ha.trans ((congrArg (fun w => (s a : F.Carrier) • w) hb).trans
      (mul_smul (s a : F.Carrier) (s b : F.Carrier) (lineProjection f v)).symm))

theorem normalizerLineCharacter_apply
    (hfixed : f.Vi 0 = V ⊓ centralizer (sourceTL T L : Set G))
    (n : cartanNormalizer T L) (v : Additive (f.Vi 0)) :
    lineProjection f (lineAction f (inclusion (cartanNormalizer_normalizes_line f hfixed) n) v) =
      (normalizerLineCharacter f hfixed n : F.Carrier) • lineProjection f v := by
  unfold normalizerLineCharacter
  exact (exists_line_scalar f ⟨n,n.property.1⟩ _).choose_spec v

theorem normalizerLineCharacter_surjective
    (hfixed : f.Vi 0 = V ⊓ centralizer (sourceTL T L : Set G)) :
    Function.Surjective (normalizerLineCharacter f hfixed) := by
  intro a
  obtain ⟨v,hv,hv0⟩ := (Submodule.ne_bot_iff _).mp (f.space_ne_bot 0)
  let w : f.space 0 := ⟨v,hv⟩
  have hw : w ≠ 0 := fun h => hv0 (congrArg Subtype.val h)
  have haw : (a : F.Carrier) • w ≠ 0 := smul_ne_zero (Units.ne_zero a) hw
  obtain ⟨n,hn⟩ := normalizer_line_transitive f hfixed w ((a : F.Carrier) • w) hw haw
  obtain ⟨u,hu⟩ := lineProjection_surjective f w
  refine ⟨n, ?_⟩
  apply Units.ext
  apply smul_left_injective F.Carrier hw
  have he := normalizerLineCharacter_apply f hfixed n u
  rw [hu] at he
  exact he.symm.trans (Subtype.ext ((lineProjection_component f
    ⟨n,n.property.1⟩ (cartanNormalizer_normalizes_line f hfixed n.property) u).trans
      (by simpa only [hu] using hn)))

/-- The original odd Hall Cartan has the full field scalar character even when
V₁ → f.space 0 has a nontrivial kernel. -/
@[irreducible] def cartanLineCharacter {X : Subgroup G} (hX : IsCartan T L X)
    (hfixed : f.Vi 0 = V ⊓ centralizer (sourceTL T L : Set G)) : X →* F.Carrierˣ :=
  (normalizerLineCharacter f hfixed).comp (inclusion hX.1)

theorem cartanLineCharacter_apply {X : Subgroup G} (hX : IsCartan T L X)
    (hfixed : f.Vi 0 = V ⊓ centralizer (sourceTL T L : Set G))
    (x : X) (v : Additive (f.Vi 0)) :
    lineProjection f (lineAction f
      (inclusion (hX.1.trans (cartanNormalizer_normalizes_line f hfixed)) x) v) =
      (cartanLineCharacter f hX hfixed x : F.Carrier) • lineProjection f v := by
  have hi : inclusion (cartanNormalizer_normalizes_line f hfixed) (inclusion hX.1 x) =
      inclusion (hX.1.trans (cartanNormalizer_normalizes_line f hfixed)) x := by
    apply Subtype.ext
    rfl
  have he := normalizerLineCharacter_apply f hfixed (inclusion hX.1 x) v
  rw [hi] at he
  rw [cartanLineCharacter, MonoidHom.comp_apply]
  exact he

attribute [local irreducible] lineAction

theorem cartanLineCharacter_surjective {X : Subgroup G} (hX : IsCartan T L X)
    (hfixed : f.Vi 0 = V ⊓ centralizer (sourceTL T L : Set G)) :
    Function.Surjective (cartanLineCharacter f hX hfixed) := by
  intro a
  obtain ⟨n,hn⟩ := normalizerLineCharacter_surjective f hfixed a
  let n' := inclusion (cartanNormalizer_normalizes_line f hfixed) n
  have hmem : lineAction f n' ∈ lineImage f X := by
    rw [lineImage_cartan_eq_normalizer f hX hfixed]
    exact mem_map_of_mem _ n.property
  obtain ⟨x,hx,he⟩ := hmem
  refine ⟨⟨x,hx⟩, ?_⟩
  rw [← hn]
  apply line_scalar_unique f
  intro v
  have hi : inclusion (hX.1.trans (cartanNormalizer_normalizes_line f hfixed))
      (⟨x,hx⟩ : X) = x := by
    apply Subtype.ext
    rfl
  have h1 := cartanLineCharacter_apply f hX hfixed (⟨x,hx⟩ : X) v
  rw [hi] at h1
  have h2 := normalizerLineCharacter_apply f hfixed n v
  have hv : lineProjection f (lineAction f x v) = lineProjection f (lineAction f n' v) :=
    congrArg (fun A : Additive (f.Vi 0) ≃ₗ[ZMod 2] Additive (f.Vi 0) =>
      lineProjection f (A v)) he
  exact h1.symm.trans (hv.trans h2)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.Pair
