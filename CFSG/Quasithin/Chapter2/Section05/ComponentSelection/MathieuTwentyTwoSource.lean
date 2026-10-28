module
public import CFSG.Quasithin.Chapter2.Section01To03.LocalStructure.StructuralSource
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SurvivingIntersections.MathieuCovers.Source
public import Theory.Mathieu.M22.Properties.SylowEscape
public import CFSG.Quasithin.MainConverse.MathieuLocal.M22Even
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.InvariantLocalSource
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SurvivingIntersections.MathieuTwentyTwo
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Binary.ParabolicPairs.InvariantGeometry

/-! The M22 component cannot survive the original empty-Γ-even hypothesis.
Its Sylow-invariant pair-core normalizer is characteristic two by the proved
model centralizer theorem. The relative component orbit argument places it
in M. But the actual component intersection is a hexad stabilizer, which
this pair-core normalizer escapes. The original Sylow and conjugation action
are retained, and no component normality is assumed.
Source: Aschbacher--Smith 2.3.9(7)(f) and 2.5.2, pp.525--526 and 551. -/
public section
open scoped Pointwise
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open Subgroup Theory.GroupTheory ComponentRefinement
open Sporadic.Mathieu
variable {G : Type*} [Group G] [Finite G] {M H L : Subgroup G} {S : Sylow 2 H} {z : G}

theorem mathieu_twentyTwo_intersection_false
    (hH : H ∈ gammaZero (Chapter1.He G) M)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (h : LocalSetup H L M S z) (e : L ≃* M22)
    (B : Finset (Fin 22)) (hB : B.card = 6)
    (hI : (M.subgroupOf L).map e.toMonoidHom = MulAction.stabilizer M22 B) : False := by
  obtain ⟨P,hP⟩ := h.component_sylow
  let R := P.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨K0,hRK,hlocal,hKinvariant,hescape⟩ := M22SylowEscape.exists_invariant_local R
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
      (MainConverse.m22_twoLocal_characteristicTwo R K0 hlocal hRK)
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
    have hR : (R : Subgroup M22).map β.toMonoidHom = R := by
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

theorem mathieu_twentyTwo_action_false
    (hH : H ∈ gammaZero (Chapter1.He G) M)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (h : LocalSetup H L M S z) (e : L ≃* M22)
    (α : MulAut L) (hα : ∀ x : L, (α x : G) = z * (x : G) * z⁻¹)
    (hinner : α ∈ (MulAut.conj (G := L)).range) : False := by
  obtain ⟨B,hB,hI⟩ := mathieuTwentyTwo_intersection h e α hα hinner
  exact mathieu_twentyTwo_intersection_false hH hempty h e B
    (m22Block_card B hB) hI

/-- The simple M22 branch of the original selected configuration. The
structural 1.1.5 input is discharged; the separate earlier C.1.29 theorem
and the triviality of the covering two-kernel remain explicit. -/
theorem mathieu_twentyTwo_quotient_false_of_core_eq_bot {C : GroupClass}
    (c : MathieuSourceSetup H L M S z) (hG : IsSimpleQTKE C G)
    (sourceC : LocalC129Input C G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (d : SporadicQuotientInput L z .m22) (hk : pCore 2 L = ⊥) : False := by
  exact mathieu_twentyTwo_action_false c.gamma hempty
    (c.localSetup hG structural115Input sourceC)
    (twoCoreQuotientEquiv d.quotientIso hk) d.action d.conjugation d.inner

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
