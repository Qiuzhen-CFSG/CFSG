module
public import CFSG.Quasithin.ChapterB.Section02.UniqueOffender
public import CFSG.Quasithin.ChapterB.Section02.Baumann.ActionQuotient
public import Theory.Representation.SL2NaturalOffenders.NoStrong
public import Theory.Representation.SL2NaturalOffenders.Ratios

/-!
# Thompson and Baumann images on an actual natural quotient

A surjective equivariant map to the natural binary SL₂ module bounds fixed
codimensions. Every moving maximum elementary subgroup therefore fills the
mapped Sylow subgroup, yielding both Thompson and Baumann image equalities.
The same quotient inequality supplies B.2.18(c), with no splitting of the
original module and no two-group assumption on its centralizer.
Source: Aschbacher–Smith B.2.20 and B.6.10, printed pp.82 and117.
-/

open Subgroup Stellmacher Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterB.RankOneBaumann
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F]
  [Algebra (ZMod 2) F]
local notation "D" => Matrix.SpecialLinearGroup (Fin 2) F
local notation "N" => SL2NaturalOffenders.NoStrong.natural (F := F)

private theorem sylow_card (P : Sylow 2 D) : Nat.card P = Nat.card F := by
  let : CharP F 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) F).injective 2
  exact (Nat.card_congr (P.equiv (Matrix.SpecialLinearGroup.upperUnipotentSylow F 2)).toEquiv).trans
    (Matrix.SpecialLinearGroup.card_upperUnipotent F)

public theorem offender_eq_sylow_of_natural_quotient
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V)
    (f : V →ₗ[ZMod 2] (Fin 2 → F)) (hf : Function.Surjective f)
    (he : ∀ g v, f (ρ g v) = N g (f v))
    (P : Sylow 2 D) (E : Subgroup D) (hEP : E ≤ P)
    (hE : BinaryOffender.IsOffender ρ E) : E = P := by
  have hnat : BinaryOffender.IsOffender N E := ⟨hE.1,
    (BinaryOffender.fixedCodim_le_of_equivariant_surjection ρ N f hf he E).trans hE.2⟩
  obtain ⟨Q,hQ⟩ := SL2NaturalOffenders.exists_sylow_of_le
    ⊤ Subgroup.topEquiv N (fun _ _ => rfl) hnat le_top
  have hcard : Nat.card E = Nat.card F := by
    rw [← hQ, card_map_of_injective (⊤ : Subgroup D).subtype_injective]
    exact SL2NaturalOffenders.sylow_card ⊤ Subgroup.topEquiv Q
  exact eq_of_le_of_card_ge hEP (by rw [hcard,sylow_card])

public theorem thompson_baumann_images_of_natural_quotient
    (T : Sylow 2 G) (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (q : G →* D) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G))
    (hUT : U ≤ T)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (f : Additive U →ₗ[ZMod 2] (Fin 2 → F)) (hf : Function.Surjective f)
    (he : ∀ g v, f (NormalElementaryQuotient.representation U q hq hker g v) = N g (f v)) :
    (elementaryAbelianMaxJ (T : Subgroup G)).map q = (T : Subgroup G).map q ∧
      (baumann (T : Subgroup G)).map q = (T : Subgroup G).map q := by
  have hJ' : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ q.ker := hker ▸ hJ
  have hj := thompson_image_of_unique_maximum_image (T : Subgroup G) q
    ((T : Subgroup G).map q) hJ' (by
      intro B hB hne
      exact offender_eq_sylow_of_natural_quotient _ f hf he (T.mapSurjective hq)
        (B.map q) (map_mono hB.1)
        (Chapter15.Section03.CharacteristicTwo.StarSelection.maxElementary_isBestOffender
          U q hq hker (T : Subgroup G) B hUT hB hne).isOffender)
  refine ⟨hj,le_antisymm (map_mono inf_le_left) ?_⟩
  rw [← hj]
  exact map_mono (elementaryAbelianMaxJ_le_baumann _)

omit [Finite F] [Algebra (ZMod 2) F] in
public theorem fixedCodim_eq_quotient_representation
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (q : G →* D) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G)) (A : Subgroup G) :
    BaumannArgument.fixedCodim U A = BinaryOffender.fixedCodim
      (NormalElementaryQuotient.representation U q hq hker) (A.map q) :=
  BaumannArgument.fixedCodim_eq_centralizer_quotient U q hq hker A

public theorem noStrong_of_natural_quotient
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (q : G →* D) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G))
    (f : Additive U →ₗ[ZMod 2] (Fin 2 → F)) (hf : Function.Surjective f)
    (he : ∀ g v, f (NormalElementaryQuotient.representation U q hq hker g v) = N g (f v))
    (R : Subgroup G) : BaumannArgument.NoStrongOffenders U R := by
  apply BaumannArgument.noStrong_of_centralizer_quotient U q hq hker _ R
  exact SL2NaturalOffenders.NoStrong.not_strong_of_natural_quotient
    _ (MonoidHom.id D) Function.injective_id f hf he
end CFSG.Quasithin.ChapterB.RankOneBaumann
