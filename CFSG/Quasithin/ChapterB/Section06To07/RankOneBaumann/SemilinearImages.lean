module

public import CFSG.Quasithin.ChapterB.Section02.UniqueOffender
public import Theory.Representation.BinaryOffender.FixedQuotientEquality
public import Theory.Representation.SL2NaturalOffenders.PointwiseFixer
/-!
# Thompson and Baumann images in a semilinear natural extension

Every moving maximum elementary subgroup is an offender on the original
module and on its natural quotient. Natural-module recognition identifies its
image with the Sylow intersection with the marked normal SL₂ layer. The sharp
rank inequality forces equality of the original and quotient fixed codimensions,
so all natural fixed vectors lift to actual fixed vectors. Consequently B.2.20's
literal pointwise centralizer lies in the natural layer, giving both images.

The quotient map retains exactly the centralizer of the original elementary
abelian subgroup as its kernel. No splitting of the module or restriction to a
purely linear ambient action is assumed.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.2.20 and
B.6.10, printed pp.82 and 117.
-/

public section
open Subgroup Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterB.RankOneBaumann
variable {G H F : Type*} [Group G] [Finite G] [Group H] [Finite H]
  [Field F] [Finite F] [Algebra (ZMod 2) F]
/-- A natural quotient with a marked normal SL₂ layer identifies the actual
Thompson and Baumann images, including ambient field automorphisms. -/
theorem thompson_baumann_images_of_semilinear_quotient
    (T : Sylow 2 G) (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G))
    (hUT : U ≤ T)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (L : Subgroup H) [L.Normal]
    (e : L ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (ρ : Representation (ZMod 2) H (Fin 2 → F)) (hfaith : Function.Injective ρ)
    (hnat : ∀ (g : L) (v : Fin 2 → F), ρ (g : H) v = Matrix.mulVec (e g).val v)
    (hF : 2 < Nat.card F)
    (f : Additive U →ₗ[ZMod 2] (Fin 2 → F)) (hf : Function.Surjective f)
    (he : ∀ g v, f (NormalElementaryQuotient.representation U q hq hker g v) = ρ g (f v)) :
    (elementaryAbelianMaxJ (T : Subgroup G)).map q = (T : Subgroup G).map q ⊓ L ∧
      (baumann (T : Subgroup G)).map q = (T : Subgroup G).map q ⊓ L := by
  let α := NormalElementaryQuotient.representation U q hq hker
  let P : Sylow 2 H := T.mapSurjective hq
  let S : Subgroup H := (P : Subgroup H) ⊓ L
  have hJ' : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ q.ker := hker ▸ hJ
  have hbest (B : Subgroup G) (hB : B ∈ elementaryAbelianMaxSubgroups (T : Subgroup G))
      (hne : B.map q ≠ ⊥) : IsOffender α (B.map q) :=
    (Chapter15.Section03.CharacteristicTwo.StarSelection.maxElementary_isBestOffender
      U q hq hker (T : Subgroup G) B hUT hB hne).isOffender
  have hunique (B : Subgroup G) (hB : B ∈ elementaryAbelianMaxSubgroups (T : Subgroup G))
      (hne : B.map q ≠ ⊥) : B.map q = S := by
    have hb := hbest B hB hne
    exact (SL2NaturalOffenders.Ratios.offender_iff_eq_sylowInf L e ρ hnat hF hfaith P
      (map_mono hB.1)).mp ⟨hb.1,
        (fixedCodim_le_of_equivariant_surjection α ρ f hf he _).trans hb.2⟩
  have hex : ∃ B ∈ elementaryAbelianMaxSubgroups (T : Subgroup G), B.map q ≠ ⊥ := by
    by_contra! hn
    exact hJ' (sSup_le fun B hB => (map_eq_bot_iff B).mp (hn B hB))
  obtain ⟨B, hB, hne⟩ := hex
  have hS : IsOffender α S := hunique B hB hne ▸ hbest B hB hne
  obtain ⟨Q, hQ⟩ := P.exists_sylow_map_eq_inf_of_normal L
  have hcod : fixedCodim ρ S = rank S := by
    change fixedCodim ρ ((P : Subgroup H) ⊓ L) = rank ((P : Subgroup H) ⊓ L)
    rw [← hQ, SL2NaturalOffenders.Ratios.sylowImage_fixedCodim L e ρ hnat Q,
      SL2NaturalOffenders.Ratios.sylowImage_rank L e Q]
  have hsharp : fixedCodim α S = fixedCodim ρ S :=
    le_antisymm (hS.2.trans_eq hcod.symm)
      (fixedCodim_le_of_equivariant_surjection α ρ f hf he S)
  have hfixed := fixedSpace_eq_comap_of_fixedCodim_eq α ρ f hf he S hsharp
  apply thompson_baumann_image_of_unique_maximum_image U (T : Subgroup G) q S hUT hJ' hunique
  intro a ha
  obtain ⟨x, hx, rfl⟩ := ha
  refine ⟨mem_map_of_mem q hx.1, ?_⟩
  apply SL2NaturalOffenders.mem_layer_of_sylow_fixedSpace L e ρ hfaith hnat P
    (mem_map_of_mem q hx.1)
  intro v hv
  obtain ⟨u, rfl⟩ := hf v
  have hu : u ∈ fixedSpace α S := by rw [hfixed]; exact hv
  have huC : (u.toMul : G) ∈ centralizer (S.comap q : Set G) := by
    apply (NormalElementaryQuotient.mem_fixedSpace_image U q hq hker (S.comap q) u).mp
    rwa [map_comap_eq_self_of_surjective hq]
  have hxu : α (q x) u = u := by
    apply Additive.toMul.injective
    apply Subtype.ext
    change ((NormalElementaryQuotient.representation U q hq hker (q x) u).toMul : G) = u.toMul
    rw [NormalElementaryQuotient.representation_apply]
    rw [← hx.2 u.toMul ⟨u.toMul.property, huC⟩, mul_inv_cancel_right]
  rw [← he, hxu]
end CFSG.Quasithin.ChapterB.RankOneBaumann
