module
public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.Orthogonal.AmbientActors.LayerGeometry
public import Theory.ElementaryAbelian.AbelianNormalClosure
public import Theory.Representation.BinaryOffender.PermutationConjugacy

/-!
# Placement of actual outer elementary actors

First conjugate an outer involution to the marked pure field involution by
an element of L. Its elementary actor's inner intersection lies in the literal
centralizer C_L(t), identified with SL₂(K). Sylow conjugacy in this centralizer
places that intersection in a conjugate of R_t while preserving t. Composing
the two actual layer elements places the entire actor in a conjugate of X.
No representation identity or unproved normalizer classification is assumed.

Source: Aschbacher–Smith, K.3.1.2, printed p.454 in `refs/quasithin.pdf`,
combined manuscript of 1 March 2004.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterK.RankOne
open Representation Representation.BinaryOffender Subgroup
open Representation.OrthogonalFourMinus.FiniteModel
open Representation.OrthogonalFourMinus.RankOne
open Matrix.SpecialLinearGroup
open scoped ENNReal
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  {s : ℕ} [NeZero s] {ρ : Representation (ZMod 2) G V} {L : Subgroup G}
namespace OrthogonalModel
variable (M : OrthogonalModel s ρ L) [L.Normal]

omit [Finite G] in
private theorem centralizer_root_image {t : G}
    (ht : M.ambientAut t = Theory.PSL2.fieldAut (conjugation s)) :
    (upperUnipotent (fixedField s)).map
      (((centralizer ({t} : Set G) ⊓ L : Subgroup G).subtype).comp
        (M.fixedFieldEquivLayerCentralizer ht).toMonoidHom) =
      M.modelImage (fixedRootGroup s) := by
  have he (u : fixedField s) :
      ((centralizer ({t} : Set G) ⊓ L : Subgroup G).subtype.comp
        (M.fixedFieldEquivLayerCentralizer ht).toMonoidHom) (transvection zero_ne_one u) =
        M.modelEmbedding (upper s u.val) := by
    change M.modelEmbedding (fixedFieldEmbedding s (transvection zero_ne_one u)) = _
    apply congrArg M.modelEmbedding
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [fixedFieldEmbedding, upper, transvection_coe, Matrix.SpecialLinearGroup.map_apply_coe]
  ext g
  constructor
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨u, rfl⟩ := (mem_upperUnipotent _ _).mp ha
    refine ⟨upper s u.val, (mem_fixedRootGroup_iff s _).mpr ⟨u, rfl⟩, ?_⟩
    exact (he u).symm
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨u, rfl⟩ := (mem_fixedRootGroup_iff s _).mp ha
    exact ⟨transvection zero_ne_one u, (mem_upperUnipotent _ _).mpr ⟨u, rfl⟩, he u⟩

omit [Finite G] in
/-- An elementary subgroup in the literal layer centralizer lies in a
centralizer-conjugate of the marked fixed-field root group. -/
theorem centralizer_elementary_placement {t : G}
    (ht : M.ambientAut t = Theory.PSL2.fieldAut (conjugation s))
    (B : Subgroup G) [IsElementaryAbelian 2 B]
    (hBC : B ≤ centralizer ({t} : Set G) ⊓ L) :
    ∃ c : G, c ∈ centralizer ({t} : Set G) ⊓ L ∧
      B ≤ (M.modelImage (fixedRootGroup s)).map (MulAut.conj c).toMonoidHom := by
  let C : Subgroup G := centralizer ({t} : Set G) ⊓ L
  let e := M.fixedFieldEquivLayerCentralizer ht
  let f : Matrix.SpecialLinearGroup (Fin 2) (fixedField s) →* G := C.subtype.comp e.toMonoidHom
  let P := (B.subgroupOf C).map e.symm.toMonoidHom
  let : IsElementaryAbelian 2 (B.subgroupOf C) := IsElementaryAbelian.subgroupOf hBC
  let : IsElementaryAbelian 2 P := IsElementaryAbelian.map e.symm.toMonoidHom
  obtain ⟨Q, hQ⟩ := (IsElementaryAbelian.isPGroup 2 P).exists_le_sylow
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq
    (Matrix.SpecialLinearGroup (Fin 2) (fixedField s))
    (upperUnipotentSylow (fixedField s) 2) Q
  have hQa : (Q : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (fixedField s))) =
      (upperUnipotent (fixedField s)).map (MulAut.conj a).toMonoidHom := by
    rw [← ha]; rfl
  have hPf : P.map f = B := by
    change ((B.subgroupOf C).map e.symm.toMonoidHom).map f = B
    rw [Subgroup.map_map]
    have he : f.comp e.symm.toMonoidHom = C.subtype := by
      ext x
      exact congrArg Subtype.val (e.apply_symm_apply x)
    rw [he, Subgroup.map_subgroupOf_eq_of_le hBC]
  refine ⟨f a, (e a).property, ?_⟩
  have hm := Subgroup.map_mono (f := f) hQ
  rw [hQa, hPf, Subgroup.map_map] at hm
  have hc : f.comp (MulAut.conj a).toMonoidHom =
      (MulAut.conj (f a)).toMonoidHom.comp f := by
    ext x
    simp [MulAut.conj_apply]
  rw [hc, ← Subgroup.map_map, M.centralizer_root_image ht] at hm
  exact hm

/-- Placement when the actual canonical involution already belongs to the actor. -/
theorem elementary_containing_pure_placement (h : SourceHypotheses ρ L)
    {t : G} (htL : t ∉ L)
    (ht : M.ambientAut t = Theory.PSL2.fieldAut (conjugation s))
    (A : Subgroup G) [IsElementaryAbelian 2 A] (htA : t ∈ A) :
    ∃ c : G, c ∈ centralizer ({t} : Set G) ⊓ L ∧
      A ≤ (M.outerActor t).map (MulAut.conj c).toMonoidHom := by
  let : IsElementaryAbelian 2 (A ⊓ L : Subgroup G) :=
    IsElementaryAbelian.of_le (show A ⊓ L ≤ A from inf_le_left)
  have hAC : A ⊓ L ≤ centralizer ({t} : Set G) ⊓ L := by
    intro a ha
    refine ⟨mem_centralizer_singleton_iff.mpr ?_, ha.2⟩
    exact congrArg Subtype.val
      ((IsMulCommutative.is_comm (M := A)).comm ⟨a, ha.1⟩ ⟨t, htA⟩)
  obtain ⟨c, hc, hB⟩ := M.centralizer_elementary_placement ht (A ⊓ L) hAC
  refine ⟨c, hc, ?_⟩
  have hct : c * t * c⁻¹ = t := by
    rw [(mem_centralizer_singleton_iff.mp hc.1), mul_inv_cancel_right]
  rw [M.outer_elementary_decomposition h A htA htL, outerActor,
    Subgroup.map_sup, MonoidHom.map_zpowers]
  change (A ⊓ L) ⊔ zpowers t ≤ _ ⊔ zpowers (c * t * c⁻¹)
  rw [hct]
  exact sup_le_sup hB le_rfl

omit [Finite G] in
/-- Conjugation preserves membership of the entire actor in the normal layer. -/
theorem conjugate_le_layer_iff (A : Subgroup G) (c : G) :
    A.map (MulAut.conj c).toMonoidHom ≤ L ↔ A ≤ L := by
  constructor
  · intro h a ha
    have hc := (inferInstance : L.Normal).conj_mem _
      (h (mem_map_of_mem (MulAut.conj c).toMonoidHom ha)) c⁻¹
    simpa [MulAut.conj_apply, mul_assoc] using hc
  · rintro h _ ⟨a, ha, rfl⟩
    exact (inferInstance : L.Normal).conj_mem a (h ha) c

/-- Every outer elementary actor is genuinely layer-conjugate to a subgroup
of the literal X. The conjugating element belongs to the original layer. -/
theorem outer_elementary_transport (h : SourceHypotheses ρ L)
    {t : G} (htL : t ∉ L)
    (ht : M.ambientAut t = Theory.PSL2.fieldAut (conjugation s))
    (A : Subgroup G) (hA : IsElementaryTwo A) (hout : ¬ A ≤ L) :
    ∃ (c : L) (B : Subgroup G), B ≤ M.outerActor t ∧ ¬ B ≤ L ∧
      IsElementaryTwo B ∧ A = B.map (MulAut.conj (c : G)).toMonoidHom := by
  let : IsElementaryAbelian 2 A := hA.2
  obtain ⟨u, hu, huL⟩ := Set.not_subset.mp hout
  have hu2 : u ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian u hu
  obtain ⟨c₀, hc₀⟩ := M.outer_involution_conjugate h hu2 huL ht
  let A₀ := A.map (MulAut.conj (c₀ : G)⁻¹).toMonoidHom
  let : IsElementaryAbelian 2 A₀ := IsElementaryAbelian.map _
  have htA₀ : t ∈ A₀ := by
    refine ⟨u, hu, ?_⟩
    simp [← hc₀, mul_assoc]
  obtain ⟨c₁, hc₁, hA₀⟩ := M.elementary_containing_pure_placement h htL ht A₀ htA₀
  let c : L := ⟨(c₀ : G) * c₁, L.mul_mem c₀.property hc₁.2⟩
  have hcancel : A₀.map (MulAut.conj (c₀ : G)).toMonoidHom = A := by
    ext x
    simp [A₀, MulAut.conj_apply, mul_assoc]
  have hAc : A ≤ (M.outerActor t).map (MulAut.conj (c : G)).toMonoidHom := by
    have he := Subgroup.map_mono (f := (MulAut.conj (c₀ : G)).toMonoidHom) hA₀
    rw [hcancel, Subgroup.map_map] at he
    have hf : (MulAut.conj (c₀ : G)).toMonoidHom.comp (MulAut.conj c₁).toMonoidHom =
        (MulAut.conj (c : G)).toMonoidHom := by
      ext x
      simp [c, MulAut.conj_apply, mul_assoc]
    rwa [hf] at he
  let B := A.map (MulAut.conj (c : G)⁻¹).toMonoidHom
  have hBX : B ≤ M.outerActor t := by
    have he := Subgroup.map_mono (f := (MulAut.conj (c : G)⁻¹).toMonoidHom) hAc
    have hf : ((M.outerActor t).map (MulAut.conj (c : G)).toMonoidHom).map
        (MulAut.conj (c : G)⁻¹).toMonoidHom = M.outerActor t := by
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    rwa [hf] at he
  refine ⟨c, B, hBX, ?_, hA.map_conj _, ?_⟩
  · exact fun hb => hout ((conjugate_le_layer_iff A (c : G)⁻¹).mp hb)
  · ext x
    simp [B, MulAut.conj_apply, mul_assoc]

end OrthogonalModel
end CFSG.Quasithin.ChapterK.RankOne
