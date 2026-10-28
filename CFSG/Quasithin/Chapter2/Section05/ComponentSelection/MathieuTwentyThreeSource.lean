module
public import CFSG.Quasithin.Chapter2.Section01To03.LocalStructure.StructuralSource
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SurvivingIntersections.MathieuCovers.Source
public import Theory.Mathieu.M23.QuasithinGeometry.SylowEscape
public import CFSG.Quasithin.MainConverse.MathieuLocal.M23Even
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.InvariantLocalSource
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SurvivingIntersections.MathieuTwentyThree
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Binary.ParabolicPairs.InvariantGeometry

/-! The M23 component cannot survive the original empty-Γ-even hypothesis.
Its Sylow-invariant triple stabilizer is characteristic two by the proved
model centralizer theorem. The relative component orbit argument places it
in M. But the actual component intersection is a heptad stabilizer, which
this triple stabilizer escapes. The original Sylow and conjugation action
are retained, and no component normality is assumed.
Source: Aschbacher--Smith 2.3.9(7)(f) and 2.5.2, pp.525--526 and 551. -/
public section
open scoped Pointwise
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open Subgroup Theory.GroupTheory ComponentRefinement
open Sporadic.Mathieu
variable {G : Type*} [Group G] [Finite G] {M H L : Subgroup G} {S : Sylow 2 H} {z : G}

theorem mathieu_twentyThree_intersection_false
    (hH : H ∈ gammaZero (Chapter1.He G) M)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (h : LocalSetup H L M S z) (e : L ≃* M23)
    (B : Finset (Fin 23)) (hB : B.card = 7)
    (hI : (M.subgroupOf L).map e.toMonoidHom = MulAction.stabilizer M23 B) : False := by
  obtain ⟨P,hP⟩ := h.component_sylow
  let R := P.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨K0,hRK,hlocal,hKinvariant,hescape⟩ := M23Geometry.SylowEscape.exists_invariant_local R
  let K := K0.map e.symm.toMonoidHom
  let A := K.map L.subtype
  have hmap : K.map e.toMonoidHom = K0 := by
    dsimp [K]
    rw [map_map]
    simp
  have hAc : A ∈ Chapter1.He G := by
    apply Chapter1.mem_He_iff.mpr
    let f := (K0.equivMapOfInjective e.symm.toMonoidHom e.symm.injective).trans
      (K.equivMapOfInjective L.subtype L.subtype_injective)
    exact (Theory.Quasithin.centralizer_pCore_le_iff 2 f).mp
      (MainConverse.m23_twoLocal_characteristicTwo R K0 hlocal hRK)
  have hinv : (S : Subgroup H).map H.subtype ⊓ normalizer (L : Set G) ≤ normalizer (A : Set G) := by
    intro s hs
    let α := L.normalizerMonoidHom ⟨s,hs.2⟩
    have hα : (P : Subgroup L).map α.toMonoidHom = P := by
      rw [hP]
      exact LieType.Binary.component_intersection_fixed_by_normalizer _ hs.1 hs.2
    let β := MulAut.congr e α
    have he : β.toMonoidHom.comp e.toMonoidHom = e.toMonoidHom.comp α.toMonoidHom := by
      apply MonoidHom.ext
      intro x
      change e (α (e.symm (e x))) = e (α x)
      rw [e.symm_apply_apply]
    have hR : (R : Subgroup M23).map β.toMonoidHom = R := by
      change ((P : Subgroup L).map e.toMonoidHom).map β.toMonoidHom =
        (P : Subgroup L).map e.toMonoidHom
      rw [map_map,he,← map_map,hα]
    have hK0 := hKinvariant β hR
    have hK : K.map α.toMonoidHom = K := by
      apply map_injective (f := e.toMonoidHom) e.injective
      rw [map_map,← he,← map_map,hmap,hK0]
    apply mem_normalizer_iff_map_conj_eq.mpr
    have he' : (MulAut.conj s).toMonoidHom.comp L.subtype = L.subtype.comp α.toMonoidHom := by
      ext x;rfl
    change (K.map L.subtype).map (MulAut.conj s).toMonoidHom = K.map L.subtype
    rw [map_map,he',← map_map,hK]
  have hAM := component_invariant_local_le hH hempty S h.sylow_le h.component
    h.component_le (map_subtype_le K) hAc hinv
  apply hescape B hB
  rw [← hmap,← hI]
  apply map_mono
  intro k hk
  exact hAM (mem_map_of_mem L.subtype hk)

theorem mathieu_twentyThree_action_false
    (hH : H ∈ gammaZero (Chapter1.He G) M)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (h : LocalSetup H L M S z) (e : L ≃* M23)
    (α : MulAut L) (hα : ∀ x : L, (α x : G) = z * (x : G) * z⁻¹)
    (hinner : α ∈ (MulAut.conj (G := L)).range) : False := by
  obtain ⟨B,hB,hI⟩ := mathieuTwentyThree_intersection h e α hα hinner
  exact mathieu_twentyThree_intersection_false hH hempty h e B
    (m23Blocks_card B hB) hI

/-- The original selected configuration and literal M23 quotient action.
The structural 1.1.5 premise and the possible two-kernel are discharged;
only the separate earlier C.1.29 block theorem remains explicit. -/
theorem mathieu_twentyThree_quotient_false {C : GroupClass}
    (c : MathieuSourceSetup H L M S z) (hG : IsSimpleQTKE C G)
    (sourceC : LocalC129Input C G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (d : SporadicQuotientInput L z .m23) : False := by
  obtain ⟨_,e,_,⟨B,hB,hI⟩,_⟩ :=
    c.mathieuTwentyThree_intersection hG structural115Input sourceC d
  exact mathieu_twentyThree_intersection_false c.gamma hempty
    (c.localSetup hG structural115Input sourceC) e B (m23Blocks_card B hB) hI

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
