module
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AutomorphismAction.AlternatingSix
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.CoreAction
public import Theory.GroupTheory.PGroup.NormalSupplementKernel

/-!
# The literal six-letter quotient of an alternating-six local join

For an A₆ block L normalized by a Sylow two-subgroup T, conjugation gives
an action of LT on the marked U(L)/C_U(L). The induced six-letter map
restricts to the original quotient L/O₂(L), with image A₆ there.
Its kernel is exactly O₂(LT): the restriction has two-group kernel,
LT/L is a two-group, and conversely the local core centralizes U(L).
All normality in the kernel argument is relative to LT.

The pointwise module equation is retained for the subsequent local-residual
and moved-module calculations. No faithful action or kernel equality is
assumed, and no chosen Chapter 12 module is substituted for U(L).
Source: Aschbacher–Smith C.1.11–13 and 3.3.31, printed pp.124–125 and 602.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC
namespace AlternatingSixBlockAction
variable {G : Type*} [Group G] {T : Sylow 2 G} {L : Subgroup G}
  (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
  {ρ : Actor →* MulAut (Multiplicative Vector)} (m : BlockModuleModel L ρ)
  (hρ : ∀ g v, (ρ g v).toAdd =
    BinaryPermutation.naturalRepresentation (Fin 6) g v.toAdd)

/-- Conjugation by the literal local join, acting on the block. -/
def joinAutomorphisms : ↥(L ⊔ (T : Subgroup G)) →* MulAut L :=
  L.normalizerMonoidHom.comp (inclusion (sup_le L.le_normalizer hTL))

/-- On the characteristic block layer this is literal ambient conjugation. -/
theorem joinAutomorphisms_blockU_coe (g : ↥(L ⊔ (T : Subgroup G))) (u : blockU L) :
    ((MulAut.characteristic (blockU L) (joinAutomorphisms hTL g) u : L) : G) =
      (g : G) * (u.val : G) * (g : G)⁻¹ := by rfl

/-- The six-letter action of the local join comes from its actual natural block module. -/
def joinPermutation : ↥(L ⊔ (T : Subgroup G)) →* Equiv.Perm (Fin 6) :=
  (permutationAction m hρ).comp (joinAutomorphisms hTL)

/-- The quotient retains conjugation on the actual U(L)/C_U(L), with the same marking. -/
theorem joinPermutation_module (g : ↥(L ⊔ (T : Subgroup G))) (u : blockU L) :
    BinaryPermutation.naturalRepresentation (Fin 6) (joinPermutation hTL m hρ g)
      (m.moduleIso (QuotientGroup.mk' (blockFixed L) u)).toAdd =
    (m.moduleIso (QuotientGroup.mk' (blockFixed L)
      (MulAut.characteristic (blockU L) (joinAutomorphisms hTL g) u))).toAdd := by
  change BinaryPermutation.naturalRepresentation (Fin 6)
    (permutationAction m hρ (joinAutomorphisms hTL g)) _ = _
  rw [permutationAction_apply, m.moduleAction_mk]

/-- The component restriction is exactly the marked quotient by O₂(L). -/
theorem joinPermutation_component (l : L) :
    joinPermutation hTL m hρ (inclusion le_sup_left l) =
      (m.quotientIso (QuotientGroup.mk' (pCore 2 L) l) : Equiv.Perm (Fin 6)) := by
  have he : joinAutomorphisms hTL (inclusion le_sup_left l) = MulAut.conj l := by
    ext x
    rfl
  change permutationAction m hρ (joinAutomorphisms hTL (inclusion le_sup_left l)) = _
  rw [he, permutationAction_inner]

/-- In particular the image contains the specified natural alternating group. -/
theorem joinPermutation_component_image :
    (L.subgroupOf (L ⊔ (T : Subgroup G))).map (joinPermutation hTL m hρ) =
      alternatingGroup (Fin 6) := by
  apply le_antisymm
  · rintro x ⟨l, hl, rfl⟩
    have he : l = inclusion le_sup_left (⟨l, hl⟩ : L) := rfl
    rw [he, joinPermutation_component]
    exact Subtype.property _
  · intro x hx
    obtain ⟨l, hl⟩ := m.quotientIso.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 L))
      ⟨x, hx⟩
    refine ⟨inclusion le_sup_left l, l.property, ?_⟩
    rw [joinPermutation_component]
    exact congrArg Subtype.val hl

private theorem joinPermutation_kernel_twoGroup : IsPGroup 2 (joinPermutation hTL m hρ).ker := by
  let H := L ⊔ (T : Subgroup G)
  let L₀ := L.subgroupOf H
  let P := (T : Subgroup G).subgroupOf H
  let q := joinPermutation hTL m hρ
  let : L₀.Normal := normal_subgroupOf_of_le_normalizer (sup_le L.le_normalizer hTL)
  apply q.kernel_isPGroup_of_normal_supplement L₀ P T.isPGroup'.comap_subtype
    (by rw [← subgroupOf_sup le_sup_left le_sup_right, subgroupOf_self])
  let e : L₀ ≃* L := subgroupOfEquivOfLe le_sup_left
  let f := q.comp L₀.subtype
  have hf (x : f.ker) : e x.val ∈ pCore 2 L := by
    have he : q x.val.val =
        (m.quotientIso (QuotientGroup.mk' (pCore 2 L) (e x.val)) : Equiv.Perm (Fin 6)) :=
      joinPermutation_component hTL m hρ (e x.val)
    have hz : m.quotientIso (QuotientGroup.mk' (pCore 2 L) (e x.val)) = 1 :=
      Subtype.ext (he.symm.trans x.property)
    exact (QuotientGroup.eq_one_iff (N := pCore 2 L) (e x.val)).mp
      (m.quotientIso.injective (hz.trans m.quotientIso.map_one.symm))
  let r : f.ker →* pCore 2 L := (e.toMonoidHom.comp f.ker.subtype).codRestrict _ hf
  apply (pCore_isPGroup (p := 2) (G := L)).of_injective r
  intro x y hxy
  apply Subtype.ext
  exact e.injective (congrArg Subtype.val hxy)

variable [Finite G]

/-- The permutation action kills precisely the actual local two-core. -/
theorem joinPermutation_kernel (hb : IsShort L) :
    (joinPermutation hTL m hρ).ker =
      ((L ⊔ (T : Subgroup G)).pCoreIn 2).subgroupOf (L ⊔ (T : Subgroup G)) := by
  let H := L ⊔ (T : Subgroup G)
  let Q := H.pCoreIn 2
  let q := joinPermutation hTL m hρ
  have hQT : Q ≤ (T : Subgroup G) := by
    have he := map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ H from le_sup_right)
    simpa only [Sylow.coe_subtype, he] using
      pCoreIn_le_sylow H (T.subtype le_sup_right)
  have hHQ : H ≤ normalizer (Q : Set G) := H.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hQU : Q ≤ centralizer ((blockU L).map L.subtype : Set G) :=
    hb.normalizing_twoGroup_centralizes_blockU (isPGroup_pCoreIn 2 H)
      (le_sup_left.trans hHQ) (hQT.trans hTL)
  have hker : q.ker ≤ pCore 2 H := le_sSup
    ⟨inferInstance, joinPermutation_kernel_twoGroup hTL m hρ⟩
  apply le_antisymm
  · intro x hx
    exact mem_map_of_mem H.subtype (hker hx)
  · intro x hx
    change permutationAction m hρ (joinAutomorphisms hTL x) = 1
    rw [permutationAction_eq_one_iff]
    apply MulEquiv.ext
    intro v
    obtain ⟨u, rfl⟩ := m.moduleIso.surjective.comp (QuotientGroup.mk'_surjective (blockFixed L)) v
    dsimp only [Function.comp_apply]
    rw [m.moduleAction_mk]
    have hu : MulAut.characteristic (blockU L) (joinAutomorphisms hTL x) u = u := by
      apply Subtype.ext
      apply Subtype.ext
      change (x : G) * (u.val : G) * (x : G)⁻¹ = (u.val : G)
      exact mul_inv_eq_iff_eq_mul.mpr
        (hQU hx _ (mem_map_of_mem L.subtype u.property)).symm
    rw [hu]
    rfl

end AlternatingSixBlockAction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- Every actual A₆ block normalized by T supplies a six-letter quotient with the literal core kernel. -/
theorem IsAlternatingBlock.exists_six_letter_quotient (hb : IsAlternatingBlock L 6)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G)) :
    ∃ q : ↥(L ⊔ (T : Subgroup G)) →* Equiv.Perm (Fin 6),
      q.ker = ((L ⊔ (T : Subgroup G)).pCoreIn 2).subgroupOf (L ⊔ (T : Subgroup G)) ∧
      (L.subgroupOf (L ⊔ (T : Subgroup G))).map q = alternatingGroup (Fin 6) := by
  obtain ⟨ρ, ⟨m⟩, hρ⟩ := hb.2.2
  exact ⟨AlternatingSixBlockAction.joinPermutation hTL m hρ,
    AlternatingSixBlockAction.joinPermutation_kernel hTL m hρ hb.2.1,
    AlternatingSixBlockAction.joinPermutation_component_image hTL m hρ⟩

end CFSG.Quasithin.ChapterC
