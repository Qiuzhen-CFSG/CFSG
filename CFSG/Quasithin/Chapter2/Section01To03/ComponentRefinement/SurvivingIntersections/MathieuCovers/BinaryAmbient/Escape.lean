module
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SurvivingIntersections.NativeSource.BinaryHexad
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.InvariantLocalSource
public import CFSG.Quasithin.MainConverse.MathieuLocal.M22Even
public import Theory.Mathieu.M22.Properties.SylowEscape
public import Theory.GroupTheory.PCorePreimageCentralizer
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Binary.ParabolicPairs.InvariantGeometry

/-!
# Excluding the binary M₂₂ cover under the original empty-Γ-even hypothesis

The Sylow-invariant pair-core normalizer in the actual M₂₂ quotient escapes
every hexad stabilizer. Pull it back through the original central two-kernel:
its two-core remains self-centralizing and every relevant Sylow actor
preserves the pullback. The component-orbit form of 2.5.1 therefore puts this
local subgroup in M. Its image cannot lie in the already identified hexad
image of M intersect L, a contradiction.

The source theorem below constructs that hexad intersection from the actual
binary cover. No centrality in the larger T, normalization of L by a
kernel-moving element, or intrinsic Sylow-fixer assertion is used.

Source: Aschbacher–Smith 2.3.9(7)(f) and 2.5.1–2, pp.525–526,551.
-/

public section
open scoped Pointwise
namespace CFSG.Quasithin.Chapter2.ComponentRefinement.BinaryAmbient
open Subgroup Theory.GroupTheory Sporadic.Mathieu
open ChapterI.Section02.ExceptionalCovers M22Local
open Sporadic.Mathieu.M22CentralCover
variable {G : Type*} [Group G] [Finite G]
variable {H L M : Subgroup G} {S : Sylow 2 H} {z : G}

/-- The marked hexad intersection is incompatible with empty Γ-even even
when its original component is a nontrivial central two-cover. -/
theorem hexad_intersection_false
    (hH : H ∈ gammaZero (Chapter1.He G) M)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (h : LocalSetup H L M S z) (e : (L ⧸ center L) ≃* M22)
    (hZ : IsPGroup 2 (center L))
    (B : Finset (Fin 22)) (hB : B.card = 6)
    (hI : M.subgroupOf L = hexadPreimage e B) : False := by
  let π := projection e
  have hπ : Function.Surjective π := projection_surjective e
  have hk : IsPGroup 2 π.ker := by
    change IsPGroup 2 (projection e).ker
    rwa [projection_ker]
  obtain ⟨P,hP⟩ := h.component_sylow
  let R := P.mapSurjective (f := π) hπ
  obtain ⟨K0,hRK,hlocal,hKinvariant,hescape⟩ := M22SylowEscape.exists_invariant_local R
  let K := K0.comap π
  let A := K.map L.subtype
  have hmap : K.map π = K0 := map_comap_eq_self_of_surjective hπ K0
  have hAc : A ∈ Chapter1.He G := by
    apply Chapter1.mem_He_iff.mpr
    let ei := K.equivMapOfInjective L.subtype L.subtype_injective
    apply (Theory.Quasithin.centralizer_pCore_le_iff 2 ei).mp
    apply π.centralizer_pCore_subgroup_of_image hk K
    rw [hmap]
    exact MainConverse.m22_twoLocal_characteristicTwo R K0 hlocal hRK
  have hinv : (S : Subgroup H).map H.subtype ⊓ normalizer (L : Set G) ≤
      normalizer (A : Set G) := by
    intro s hs
    let α := L.normalizerMonoidHom ⟨s,hs.2⟩
    have hα : (P : Subgroup L).map α.toMonoidHom = P := by
      rw [hP]
      exact LieType.Binary.component_intersection_fixed_by_normalizer _ hs.1 hs.2
    let β := MulAut.centralQuotientAction e α
    have he : β.toMonoidHom.comp π = π.comp α.toMonoidHom := by
      apply MonoidHom.ext
      intro x
      exact MulAut.centralQuotientAction_apply e α x
    have hR : (R : Subgroup M22).map β.toMonoidHom = R := by
      change ((P : Subgroup L).map π).map β.toMonoidHom = (P : Subgroup L).map π
      rw [map_map,he,← map_map,hα]
    have hK0 := hKinvariant β hR
    have hK : K.map α.toMonoidHom = K := by
      apply le_antisymm
      · rintro _ ⟨x,hx,rfl⟩
        change π (α x) ∈ K0
        have hex : β (π x) = π (α x) := DFunLike.congr_fun he x
        rw [← hex,← hK0]
        exact mem_map_of_mem β.toMonoidHom hx
      · intro x hx
        refine ⟨α.symm x,?_,α.apply_symm_apply x⟩
        have hb : β.symm (π x) ∈ K0 := by
          rw [← mem_map_equiv,hK0]
          exact hx
        have hxπ : π (α.symm x) = β.symm (π x) := by
          apply β.injective
          rw [β.apply_symm_apply]
          change (β.toMonoidHom.comp π) (α.symm x) = _
          rw [he,MonoidHom.comp_apply]
          change π (α (α.symm x)) = π x
          rw [α.apply_symm_apply]
        change π (α.symm x) ∈ K0
        rw [hxπ]
        exact hb
    apply mem_normalizer_iff_map_conj_eq.mpr
    have he' : (MulAut.conj s).toMonoidHom.comp L.subtype =
        L.subtype.comp α.toMonoidHom := rfl
    change (K.map L.subtype).map (MulAut.conj s).toMonoidHom = K.map L.subtype
    rw [map_map,he',← map_map,hK]
  have hAM := Section05.ComponentSelection.component_invariant_local_le hH hempty S
    h.sylow_le h.component h.component_le (map_subtype_le K) hAc hinv
  apply hescape B hB
  intro x hx
  obtain ⟨l,rfl⟩ := hπ x
  have hl : l ∈ M.subgroupOf L := hAM (mem_map_of_mem L.subtype hx)
  rw [hI] at hl
  exact hl

/-- Original Γ₀/Sylow/local-C source application: the binary M₂₂ kernel
cannot occur when Γ-even-zero is empty. Every model and local premise above
is supplied by the actual quotient and its proved binary hexad recognition. -/
theorem source_false {C : GroupClass}
    (c : MathieuSourceSetup H L M S z) (hG : IsSimpleQTKE C G)
    (sourceC : LocalC129Input C G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (d : SporadicQuotientInput L z .m22) (hc : Nat.card (pCore 2 L) = 2) : False := by
  let h := c.localSetup hG structural115Input sourceC
  let e := h.mathieuTwentyTwo_centerQuotient d.quotientIso
  obtain ⟨B,hB,hI,_⟩ := c.mathieuTwentyTwo_binary_intersection hG sourceC d hc
  apply hexad_intersection_false c.gamma hempty h e ?_ B (m22Block_card B hB) hI
  rw [h.mathieuTwentyTwo_center_eq d.quotientIso]
  exact pCore_isPGroup

end CFSG.Quasithin.Chapter2.ComponentRefinement.BinaryAmbient
