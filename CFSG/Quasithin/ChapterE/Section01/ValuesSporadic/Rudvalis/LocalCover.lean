module

public import CFSG.Quasithin.ChapterE.Section01.ValuesSporadic.Rudvalis.LocalModels
public import CFSG.Quasithin.ChapterE.Section01.ValuesSporadic.Rudvalis.LocalGeneration
public import CFSG.Quasithin.ChapterE.Section01.ValuesSporadic.Rudvalis.LocalCover.ActionImage
public import CFSG.Quasithin.ChapterE.Section01.ValuesSporadic.Rudvalis.LocalCover.Generation
public import CFSG.Quasithin.Defs
public import Theory.SpecificGroups.Rudvalis.Model.SylowInvariantPair
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# Transporting the Rudvalis local pair through all normal two-extensions

Intersect the ambient Sylow subgroup with the normal Rudvalis copy, then
 align the fixed model Sylow by an inner conjugation. Model automorphisms
 induced by the ambient Sylow now preserve both locals. Their images are
 normal in their joins with the Sylow subgroup. The actual quotient-action
 calculations supply a faithful simple normal subgroup, a two-group quotient
 and two-rank at most two in each join modulo its own two-core. Mapping the
 pair's generation equality proves that the two joins generate the ambient
 group.

The concrete pair's generation follows from simplicity of the normal copy,
 transported to the model, and its automorphism invariance is unconditional.
 `exists_local_cover` discharges both geometric premises in the source
 application. Only the intrinsic quotient models remain as the independent
 input `LocalQuotientModels`; the E.1.14(5) assembly must supply that input.

Source: Aschbacher–Smith E.1.14(5), printed p.214, citing Asc82a, Lemma 4.9;
 GLS3 Table 5.3r, printed p.279. The transport follows the general
 `Theory.GroupTheory.InvariantLocalPairCover`, while retaining the additional
 faithful simple subgroup required by the Rudvalis E-generation criterion.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Rudvalis
variable {G : Type*} [Group G] [Finite G]

local notation "P" => _root_.Rudvalis.SylowInvariantPair.locals
local notation "S" => _root_.Rudvalis.SylowInvariantPair.sylow

/-- Given the two concrete geometric facts, every normal Rudvalis copy with
 a Sylow supplement has the required structural generating cover. -/
theorem exists_local_cover_of_invariant_pair
    (hmodels : LocalQuotientModels) (L : Subgroup G) [L.Normal] (T : Sylow 2 G)
    (e : L ≃* _root_.Rudvalis.Model) (hLT : L ⊔ (T : Subgroup G) = ⊤)
    (hgen : P 0 ⊔ P 1 = ⊤)
    (hinv : ∀ i (β : MulAut _root_.Rudvalis.Model),
      (S : Subgroup _root_.Rudvalis.Model).map β.toMonoidHom = S →
      (P i).map β.toMonoidHom = P i) :
    ∃ Δ : Set (Subgroup G), sSup Δ = ⊤ ∧
      ∀ H ∈ Δ, (T : Subgroup G) ≤ H ∧ HasRankTwoLocalQuotient H := by
  classical
  obtain ⟨R, hR⟩ := T.exists_subgroupOf_eq_of_normal L
  let S' := (S).mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq L S' R
  let f : _root_.Rudvalis.Model ≃* L := e.symm.trans (MulAut.conj g)
  have hf : (S : Subgroup _root_.Rudvalis.Model).map f.toMonoidHom = (R : Subgroup L) := by
    have hh := congrArg Sylow.toSubgroup hg
    change ((S : Subgroup _root_.Rudvalis.Model).map e.symm.toMonoidHom).map (MulAut.conj g).toMonoidHom = R at hh
    have he : f.toMonoidHom = (MulAut.conj g).toMonoidHom.comp e.symm.toMonoidHom := rfl
    rw [he, ← Subgroup.map_map]
    exact hh
  let ι : _root_.Rudvalis.Model →* G := L.subtype.comp f.toMonoidHom
  have hι : Function.Injective ι := L.subtype_injective.comp f.injective
  let K : Fin 2 → Subgroup G := fun i => (P i).map ι
  have hK : ∀ i, (T : Subgroup G) ≤ normalizer (K i : Set G) := by
    intro i t ht
    let α : MulAut L := MulAut.conjNormal t
    let β : MulAut _root_.Rudvalis.Model := MulAut.congr f.symm α
    have hα : (R : Subgroup L).map α.toMonoidHom = R := by
      rw [hR]
      apply Subgroup.eq_of_le_of_card_ge
      · rintro x ⟨y, hy, rfl⟩
        change t * (y : G) * t⁻¹ ∈ (T : Subgroup G)
        exact (T : Subgroup G).mul_mem ((T : Subgroup G).mul_mem ht hy)
          ((T : Subgroup G).inv_mem ht)
      · exact le_of_eq (Nat.card_congr (α.subgroupMap _).toEquiv)
    have hβ : (S : Subgroup _root_.Rudvalis.Model).map β.toMonoidHom = S := by
      apply map_injective (f := f.toMonoidHom) f.injective
      rw [Subgroup.map_map]
      have he : f.toMonoidHom.comp β.toMonoidHom = α.toMonoidHom.comp f.toMonoidHom := by
        apply MonoidHom.ext
        intro x
        change f (f.symm (α (f x))) = α (f x)
        exact f.apply_symm_apply _
      rw [he, ← Subgroup.map_map, hf, hα]
    apply mem_normalizer_iff_map_conj_eq.mpr
    change ((P i).map ι).map (MulAut.conj t).toMonoidHom = (P i).map ι
    rw [Subgroup.map_map]
    have he : (MulAut.conj t).toMonoidHom.comp ι = ι.comp β.toMonoidHom := by
      ext x
      exact congrArg Subtype.val (f.apply_symm_apply (α (f x))).symm
    rw [he, ← Subgroup.map_map, hinv i β hβ]
  let H : Fin 2 → Subgroup G := fun i => K i ⊔ (T : Subgroup G)
  have hlocal0 : HasRankTwoLocalQuotient (H 0) :=
    LocalCover.hasRankTwoLocalQuotient_join_max4 hmodels (hK 0) T.isPGroup'
      ((Subgroup.equivMapOfInjective (P 0) ι hι).symm.trans
        _root_.Rudvalis.SylowInvariantPair.firstEquiv)
  have hlocal1 : HasRankTwoLocalQuotient (H 1) :=
    LocalCover.hasRankTwoLocalQuotient_join_max6 hmodels (hK 1) T.isPGroup'
      ((Subgroup.equivMapOfInjective (P 1) ι hι).symm.trans
        _root_.Rudvalis.SylowInvariantPair.secondEquiv)
  have hKgen : K 0 ⊔ K 1 = L := by
    change (P 0).map ι ⊔ (P 1).map ι = L
    rw [← Subgroup.map_sup, hgen]
    change (⊤ : Subgroup _root_.Rudvalis.Model).map (L.subtype.comp f.toMonoidHom) = L
    rw [← Subgroup.map_map, Subgroup.map_top_of_surjective _ f.surjective,
      ← MonoidHom.range_eq_map, range_subtype]
  refine ⟨{H 0, H 1}, ?_, ?_⟩
  · rw [sSup_pair]
    change (K 0 ⊔ (T : Subgroup G)) ⊔ (K 1 ⊔ (T : Subgroup G)) = ⊤
    rw [sup_sup_sup_comm, sup_idem, hKgen, hLT]
  · intro Q hQ
    rcases Set.mem_insert_iff.mp hQ with rfl | hQ
    · exact ⟨le_sup_right, hlocal0⟩
    · have he : Q = H 1 := Set.mem_singleton_iff.mp hQ
      subst Q
      exact ⟨le_sup_right, hlocal1⟩


/-- Application with exactly the ambient group and Sylow of E.1.14(5).
 The two fixed-model geometric premises remain to be constructed. -/
theorem exists_local_cover_of_model_geometry {K : GroupClass}
    (_hG : IsSQTK K G) [IsSimpleGroup (generalizedFitting G)]
    (hmodels : LocalQuotientModels) (T : Sylow 2 G)
    (hLT : generalizedFitting G ⊔ (T : Subgroup G) = ⊤)
    (e : generalizedFitting G ≃* _root_.Rudvalis.Model)
    (hgen : P 0 ⊔ P 1 = ⊤)
    (hinv : ∀ i (β : MulAut _root_.Rudvalis.Model),
      (S : Subgroup _root_.Rudvalis.Model).map β.toMonoidHom = S →
      (P i).map β.toMonoidHom = P i) :
    ∃ Δ : Set (Subgroup G), sSup Δ = ⊤ ∧
      ∀ H ∈ Δ, (T : Subgroup G) ≤ H ∧ HasRankTwoLocalQuotient H :=
  exists_local_cover_of_invariant_pair hmodels (generalizedFitting G) T e hLT hgen hinv

/-- Every simple normal Rudvalis copy with a Sylow supplement has a generating
 cover with the required local quotient structure. Only the intrinsic quotient
 models are additional input; both concrete geometric premises are discharged. -/
theorem exists_local_cover_of_simple_normal
    (hmodels : LocalQuotientModels) (L : Subgroup G) [L.Normal] [IsSimpleGroup L]
    (T : Sylow 2 G) (e : L ≃* _root_.Rudvalis.Model)
    (hLT : L ⊔ (T : Subgroup G) = ⊤) :
    ∃ Δ : Set (Subgroup G), sSup Δ = ⊤ ∧
      ∀ H ∈ Δ, (T : Subgroup G) ≤ H ∧ HasRankTwoLocalQuotient H := by
  let : IsSimpleGroup _root_.Rudvalis.Model := e.symm.isSimpleGroup
  exact exists_local_cover_of_invariant_pair hmodels L T e hLT
    LocalCover.locals_sup_eq_top _root_.Rudvalis.SylowInvariantPair.locals_invariant

/-- The generating cover used in E.1.14(5) for the original ambient SQTK group
 and Sylow subgroup. Apart from its source hypotheses, only the independent
 intrinsic local quotient calculations remain explicit. -/
theorem exists_local_cover {K : GroupClass}
    (_hG : IsSQTK K G) [IsSimpleGroup (generalizedFitting G)]
    (hmodels : LocalQuotientModels) (T : Sylow 2 G)
    (hLT : generalizedFitting G ⊔ (T : Subgroup G) = ⊤)
    (e : generalizedFitting G ≃* _root_.Rudvalis.Model) :
    ∃ Δ : Set (Subgroup G), sSup Δ = ⊤ ∧
      ∀ H ∈ Δ, (T : Subgroup G) ≤ H ∧ HasRankTwoLocalQuotient H :=
  exists_local_cover_of_simple_normal hmodels (generalizedFitting G) T e hLT

end CFSG.Quasithin.ChapterE.Rudvalis
