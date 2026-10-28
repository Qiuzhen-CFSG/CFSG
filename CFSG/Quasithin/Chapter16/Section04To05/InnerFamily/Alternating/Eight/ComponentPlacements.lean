module

public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.Alternating.Eight.Products

/-!
# Conjugate component placements for the marked A₈ model

For each marked involution, the source chooses a conjugate of the actual
component `L ⟨z⟩` inside its index-two overgroup.  The Sylow conjugacy is
performed in the marked involution centralizer, so the chosen conjugator still
maps `z` to that mark. The index-two assertion is read from the product
coordinates, without assuming any product-fusion exclusions or emptiness of Δ₀.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
16.4.9(2), printed p.1192.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter16.Intersections

namespace CFSG.Quasithin.Chapter16.Intersections.AlternatingEight

variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {z r : G} {L : Subgroup G}

-- `Products` already imports `InnerFamily.Transport.SylowIn.map`, which shares
-- its public name with the declaration in `IntersectionStructure.SylowTransport`.
-- Those modules cannot be imported together, so use Sylow conjugacy directly here.
private theorem sylowIn_exists_conjugate_le {R H Q : Subgroup G}
    (h : SylowIn R H) (hp : IsPGroup 2 Q) (hle : Q ≤ H) :
    ∃ a ∈ H, Q.conjBy a ≤ R := by
  obtain ⟨S, rfl⟩ := h
  obtain ⟨U, hU⟩ := (hp.of_equiv (subgroupOfEquivOfLe hle).symm).exists_le_sylow
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq H U S
  refine ⟨a, a.property, ?_⟩
  intro x hx
  obtain ⟨y, hy, rfl⟩ := hx
  refine ⟨a * ⟨y, hle hy⟩ * a⁻¹, ?_, rfl⟩
  rw [← ha]
  exact mem_map_of_mem (MulAut.conj a).toMonoidHom (hU hy)

omit [Finite G] in
private theorem component_relIndex_two
    (M : AlternatingProductModel L z r 8) :
    (L ⊔ zpowers z).relIndex (AlternatingOvergroup L z r) = 2 := by
  let Q := (alternatingGroup (Fin 8)).comap M.permutationAction
  have himage : Q.map (AlternatingOvergroup L z r).subtype = L ⊔ zpowers z := by
    apply le_antisymm
    · rintro a ⟨b, hb, rfl⟩
      change (M.equiv b).1 ∈ alternatingGroup (Fin 8) at hb
      let l := M.equiv.symm ((M.equiv b).1, 1)
      have hl : (l : G) ∈ L := by
        rw [M.component_iff]
        constructor
        · simpa only [l, M.equiv.apply_symm_apply] using hb
        · simp only [l, M.equiv.apply_symm_apply]
      have hker : b * l⁻¹ ∈ M.permutationAction.ker := by
        change M.permutationAction (b * l⁻¹) = 1
        rw [map_mul, map_inv]
        change (M.equiv b).1 * (M.equiv l).1⁻¹ = 1
        simp only [l, M.equiv.apply_symm_apply, mul_inv_cancel]
      have hzp : ((b * l⁻¹ : AlternatingOvergroup L z r) : G) ∈ zpowers z := by
        rw [← M.permutationAction_kernel_image]
        exact mem_map_of_mem _ hker
      have hm := (L ⊔ zpowers z).mul_mem (mem_sup_right hzp) (mem_sup_left hl)
      simpa using hm
    · apply sup_le
      · intro a ha
        refine ⟨⟨a, mem_sup_left (mem_sup_left ha)⟩, ?_, rfl⟩
        exact ((M.component_iff _).mp ha).1
      · apply zpowers_le.mpr
        refine ⟨⟨z, mem_sup_right (mem_zpowers z)⟩, ?_, rfl⟩
        change (M.equiv ⟨z, mem_sup_right (mem_zpowers z)⟩).1 ∈ alternatingGroup (Fin 8)
        rw [M.central_image]
        exact one_mem _
  have hQ : (L ⊔ zpowers z).subgroupOf (AlternatingOvergroup L z r) = Q := by
    apply map_injective (AlternatingOvergroup L z r).subtype_injective
    rw [map_subgroupOf_eq_of_le (show L ⊔ zpowers z ≤ AlternatingOvergroup L z r
      from sup_le (le_sup_left.trans le_sup_left) le_sup_right)]
    exact himage.symm
  change ((L ⊔ zpowers z).subgroupOf (AlternatingOvergroup L z r)).index = 2
  rw [hQ]
  exact (index_comap_of_surjective _ M.permutationAction_surjective).trans
    alternatingGroup.index_eq_two

/-- Each marked involution admits a compatible Sylow conjugate containing A;
its conjugate of LE supplies the actual index-two placement. -/
theorem nonempty_placements
    (h : StandardSetup T z L)
    (M : AlternatingProductModel L z r 8)
    (hTLE : (T : Subgroup G) ≤ AlternatingOvergroup L z r)
    (F : MarkedEmbedding L z r) (hr : IsConj z r) :
    Nonempty (Placements F) := by
  classical
  let : IsElementaryAbelian 2 F.subgroup := F.elementary
  have hA : IsPGroup 2 F.subgroup := IsElementaryAbelian.isPGroup 2 F.subgroup
  have hTcz : SylowIn (T : Subgroup G) (involutionCentralizer z) := by
    refine ⟨T.subtype h.sylow_centralizes, ?_⟩
    exact map_subgroupOf_eq_of_le h.sylow_centralizes
  have hmark_mem (i : Fin 5) : F.mark i ∈ F.subgroup := by
    exact ⟨word {i}, rfl⟩
  have hcentral (i : Fin 5) : F.subgroup ≤ involutionCentralizer (F.mark i) := by
    intro a ha
    change a ∈ centralizer ({F.mark i} : Set G)
    rw [mem_centralizer_singleton_iff]
    have hc : Commute (⟨a, ha⟩ : F.subgroup)
        (⟨F.mark i, hmark_mem i⟩ : F.subgroup) :=
      (isMulCommutative_iff.mp
        (inferInstance : IsMulCommutative F.subgroup)) _ _
    exact congrArg Subtype.val hc.eq
  have hplacements (i : Fin 5) :
      ∃ x : G, MulAut.conj x z = F.mark i ∧
        F.subgroup ≤ (T : Subgroup G).conjBy x := by
    obtain ⟨x₀, hx₀⟩ := (isConj_iff.mp (F.mark_isConj hr i))
    have hS := hTcz.map (MulAut.conj x₀)
    change SylowIn ((T : Subgroup G).conjBy x₀)
      ((involutionCentralizer z).conjBy x₀) at hS
    have hcx : (involutionCentralizer z).conjBy x₀ =
        involutionCentralizer (F.mark i) := by
      change (centralizer ({z} : Set G)).map (MulAut.conj x₀).toMonoidHom = _
      rw [map_centralizer_equiv, Set.image_singleton]
      change involutionCentralizer (MulAut.conj x₀ z) = _
      rw [show MulAut.conj x₀ z = F.mark i from hx₀]
    rw [hcx] at hS
    obtain ⟨a, ha, hA⟩ := sylowIn_exists_conjugate_le hS hA (hcentral i)
    refine ⟨a⁻¹ * x₀, ?_, ?_⟩
    · simpa [MulAut.conj_apply, hx₀, mul_assoc] using
        (show MulAut.conj a⁻¹ (F.mark i) = F.mark i from by
          rw [MulAut.conj_apply, inv_inv]
          calc
            a⁻¹ * F.mark i * a = a⁻¹ * (F.mark i * a) := by rw [mul_assoc]
            _ = a⁻¹ * (a * F.mark i) := by
              rw [← (mem_centralizer_singleton_iff.mp ha)]
            _ = F.mark i := by simp)
    · have hh := map_mono (f := (MulAut.conj a⁻¹).toMonoidHom) hA
      change (F.subgroup.conjBy a).conjBy a⁻¹ ≤
        ((T : Subgroup G).conjBy x₀).conjBy a⁻¹ at hh
      simpa only [conjBy_conjBy, inv_mul_cancel, one_mul, conjBy_one] using hh
  choose x hxcenter hxA using hplacements
  let P : Placements F :=
    { conjugator := x
      center := hxcenter
      overgroup := fun i => (AlternatingOvergroup L z r).conjBy (x i)
      contains := by
        intro i
        exact hxA i |>.trans (map_mono (f := (MulAut.conj (x i)).toMonoidHom) hTLE)
      component_le := by
        intro i
        exact map_mono (f := (MulAut.conj (x i)).toMonoidHom) (by
          exact sup_le (le_sup_left.trans le_sup_left) le_sup_right)
      index := by
        intro i
        simpa only [conjBy] using
          (Subgroup.relIndex_map_map_of_injective
            (L ⊔ zpowers z) (AlternatingOvergroup L z r)
            (f := (MulAut.conj (x i)).toMonoidHom)
            (MulAut.conj (x i)).injective).trans
            (component_relIndex_two M) }
  exact ⟨P⟩

end CFSG.Quasithin.Chapter16.Intersections.AlternatingEight
