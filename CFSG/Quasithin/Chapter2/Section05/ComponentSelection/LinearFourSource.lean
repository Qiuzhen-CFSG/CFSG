module
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SurvivingIntersections.Local
public import Theory.SpecificGroups.BinaryLinear.InvariantNodeActions.MiddleFour
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.InvariantLocalSource
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Binary

/-! Exclude the actual L4(2) component in the empty-Γ-even configuration.
Every automorphism preserving its Sylow fixes the middle two-space parabolic.
That characteristic-two subgroup is therefore forced into M by the relative
component orbit argument. The proved 2.3.9 intersection is a transvection
centralizer, contained in an image-line parabolic. A two-space parabolic
cannot lie in a line parabolic. No component normality or additional flag
geometry is assumed.
Source: Aschbacher--Smith 2.5.2, printed p.551, and 2.3.9(7)(g). -/
public section
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open Subgroup Theory.GroupTheory ComponentRefinement
open LieType.Binary
variable {G : Type*} [Group G] [Finite G] {M H L : Subgroup G} {S : Sylow 2 H} {z : G}

theorem linear_four_two_false
    (hH : H ∈ gammaZero (Chapter1.He G) M)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (h : LocalSetup H L M S z) (e : L ≃* PSL 4)
    (hinner : ∃u:L, IsConjugationProjection L z u) : False := by
  obtain ⟨_,t,ht,ht2,hI⟩ := four_refinement h e hinner
  obtain ⟨c⟩ := projection_transvectionCoordinates h (Or.inl rfl) e ht ht2
  obtain ⟨P,hP⟩ := h.component_sylow
  let f := linearModel e
  let R := P.mapSurjective (f := f.toMonoidHom) f.surjective
  obtain ⟨W,hW,hRK,hKinvariant⟩ := BinaryLinear.InvariantNodeActions.exists_sylow_invariant_middle R
  let K0 := BinaryLinear.parabolic W
  let K := K0.map f.symm.toMonoidHom
  let A := K.map L.subtype
  have hmap : K.map f.toMonoidHom = K0 := by
    dsimp [K]
    rw [map_map]
    simp
  have hW0 : W ≠ ⊥ := by intro he; rw [he,finrank_bot] at hW; omega
  have hW1 : W ≠ ⊤ := by
    intro he
    rw [he,finrank_top,Module.finrank_fin_fun] at hW
    omega
  have hAc : A ∈ Chapter1.He G := by
    apply Chapter1.mem_He_iff.mpr
    let q := (K0.equivMapOfInjective f.symm.toMonoidHom f.symm.injective).trans
      (K.equivMapOfInjective L.subtype L.subtype_injective)
    exact (Theory.Quasithin.centralizer_pCore_le_iff 2 q).mp
      (BinaryLinear.centralizer_parabolic_twoCore_le hW0 hW1)
  have hinv : (S : Subgroup H).map H.subtype ⊓ normalizer (L : Set G) ≤ normalizer (A : Set G) := by
    intro s hs
    let α := L.normalizerMonoidHom ⟨s,hs.2⟩
    have hα : (P : Subgroup L).map α.toMonoidHom = P := by
      rw [hP]
      exact LieType.Binary.component_intersection_fixed_by_normalizer _ hs.1 hs.2
    let β := MulAut.congr f α
    have he : β.toMonoidHom.comp f.toMonoidHom = f.toMonoidHom.comp α.toMonoidHom := by
      apply MonoidHom.ext
      intro x
      change f (α (f.symm (f x))) = f (α x)
      rw [f.symm_apply_apply]
    have hR : (R : Subgroup (BinaryLinear.OuterCyclic.LinearGroup 4)).map β.toMonoidHom = R := by
      change ((P : Subgroup L).map f.toMonoidHom).map β.toMonoidHom =
        (P : Subgroup L).map f.toMonoidHom
      rw [map_map,he,← map_map,hα]
    have hK0 := hKinvariant β hR
    have hK : K.map α.toMonoidHom = K := by
      apply map_injective (f := f.toMonoidHom) f.injective
      rw [map_map,← he,← map_map,hmap,hK0]
    apply mem_normalizer_iff_map_conj_eq.mpr
    have he' : (MulAut.conj s).toMonoidHom.comp L.subtype = L.subtype.comp α.toMonoidHom := by
      ext x;rfl
    change (K.map L.subtype).map (MulAut.conj s).toMonoidHom = K.map L.subtype
    rw [map_map,he',← map_map,hK]
  have hAM := component_invariant_local_le hH hempty S h.sylow_le h.component
    h.component_le (map_subtype_le K) hAc hinv
  have hKC : K ≤ centralizer ({t} : Set L) := by
    intro x hx
    have hm : (x : G) ∈ L ⊓ M := ⟨x.property,hAM (mem_map_of_mem L.subtype hx)⟩
    rw [hI] at hm
    apply mem_centralizer_singleton_iff.mpr
    exact Subtype.ext (mem_centralizer_singleton_iff.mp hm.2)
  have hK : K = subspaceStabilizer e W := by
    ext x
    rw [mem_map_equiv]
    rfl
  rw [hK,c.centralizer_eq] at hKC
  have hc0 : c.line ≠ ⊥ := by
    intro he
    have hd := c.line_finrank
    rw [he,finrank_bot] at hd
    omega
  have hc1 : c.line ≠ ⊤ := by
    intro he
    have hd := c.line_finrank
    rw [he,finrank_top,Module.finrank_fin_fun] at hd
    omega
  have he := subspaceStabilizer_eq_of_le e hc0 hc1 (hKC.trans inf_le_left)
  rw [he,c.line_finrank] at hW
  omega

/-- The literal inner automorphism supplied by 1.1.5(3)(a) gives the
same original-source exclusion without a chosen implementing involution. -/
theorem linear_four_two_action_false
    (hH : H ∈ gammaZero (Chapter1.He G) M)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (h : LocalSetup H L M S z) (e : L ≃* PSL 4)
    (α : MulAut L) (hα : ∀ x : L, (α x : G) = z * (x : G) * z⁻¹)
    (hinner : α ∈ (MulAut.conj (G := L)).range) : False := by
  obtain ⟨u,hu⟩ := hinner
  apply linear_four_two_false hH hempty h e
  refine ⟨u,fun x => ?_⟩
  rw [← hα,← hu]
  rfl

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
