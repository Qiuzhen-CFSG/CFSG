module
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicComponent.RankFiveNaturalSixSpans
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicComponent.RankFiveNaturalSixTerminal

/-!
# The image of the source conjugate core

The two actual point-centralizer spans generate the full core. Their conjugates
centralize the original spans, so their six-letter images lie in the two
complementary transposition groups. Normality in the original Sylow intersection
removes the crossing transposition, leaving the complementary duad action.

Source: Aschbacher–Smith, 14.6.10(5), printed p.1030.
-/

public section
open Subgroup BinaryPermutation Module Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06.RankFiveNaturalSix
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open NaturalGeometry
variable {G : Type*} [Group G]

private theorem image_centralizer_fixes (K P D : Subgroup G)
    (E : sourceModule K ≃* Multiplicative (core (Fin 6)))
    (f : normalizer (K : Set G) →* S)
    (he : ∀ (n : normalizer (K : Set G)) (v : sourceModule K)
      (hv : n.val*v.val*n.val⁻¹ ∈ sourceModule K),
      (E ⟨n.val*v.val*n.val⁻¹,hv⟩).toAdd = coreRepresentation (Fin 6) (f n) (E v).toAdd)
    (U : Submodule (ZMod 2) (core (Fin 6)))
    (hP : sourceImage (sourceModule K) E P = U)
    (hDC : D ≤ centralizer (P : Set G)) :
    ∀ g ∈ (D.subgroupOf (normalizer (K : Set G))).map f, ∀ v ∈ U,
      coreRepresentation (Fin 6) g v = v := by
  rintro _ ⟨n,hn,rfl⟩ v hv
  obtain ⟨p,hp,hpv⟩ := hP.symm ▸ hv
  have hnp : n.val*p.val*n.val⁻¹ = p.val := by
    have hh : p.val*n.val = n.val*p.val := hDC hn p hp
    rw [←hh,mul_inv_cancel_right]
  have hh := he n p (hnp.symm ▸ p.property)
  have hnpeq : (⟨n.val*p.val*n.val⁻¹,hnp.symm ▸ p.property⟩ : sourceModule K) = p := Subtype.ext hnp
  rw [hnpeq] at hh
  have hpv' : (E p).toAdd = v := congrArg Multiplicative.toAdd hpv
  rw [hpv'] at hh
  exact hh.symm

/-- Normality of the literal conjugate core in the source Sylow subgroup,
and centralization of its two original point spans, force its image into the
complementary transposition subgroup. -/
theorem source_crossing_image_le (K S0 Bplane : Subgroup G)
    (E : sourceModule K ≃* Multiplicative (core (Fin 6)))
    (f : normalizer (K : Set G) →* S)
    (he : ∀ (n : normalizer (K : Set G)) (v : sourceModule K)
      (hv : n.val*v.val*n.val⁻¹ ∈ sourceModule K),
      (E ⟨n.val*v.val*n.val⁻¹,hv⟩).toAdd = coreRepresentation (Fin 6) (f n) (E v).toAdd)
    (hA : (K.subgroupOf (normalizer (K : Set G))).map f = alternatingGroup (Fin 6))
    (hVW : Bplane ≤ sourceModule K) (hV : sourceImage (sourceModule K) E Bplane = CoreCrossing.plane)
    (hWS : sourceModule K ≤ S0) (hSN : S0 ≤ normalizer (K : Set G))
    (halign : T0 ≤ (S0.subgroupOf (normalizer (K : Set G))).map f)
    (z w : sourceModule K) (hz : (E z).toAdd = CoreCrossing.z) (hw : (E w).toAdd = CoreCrossing.w)
    (t : G) (htS : t ∈ normalizer (S0 : Set G))
    (hc : ∀ p ∈ Bplane, p ≠ 1 →
      let P := conjugateSpanBy Bplane (K ⊓ centralizer ({p} : Set G))
      P.map (MulAut.conj t).toMonoidHom ≤ centralizer (P : Set G)) :
    (((sourceModule K).map (MulAut.conj t).toMonoidHom).subgroupOf
      (normalizer (K : Set G))).map f ≤ zpowers swap45 := by
  let W := sourceModule K
  let P := conjugateSpanBy Bplane (K ⊓ centralizer ({z.val} : Set G))
  let Q := conjugateSpanBy Bplane (K ⊓ centralizer ({w.val} : Set G))
  let φ := (MulAut.conj t).toMonoidHom
  have hgen : P ⊔ Q = W := source_two_point_spans_generate K Bplane E f he hA hVW hV z w hz hw
  have hPS : P ≤ S0 := (le_sup_left.trans hgen.le).trans hWS
  have hQS : Q ≤ S0 := (le_sup_right.trans hgen.le).trans hWS
  have ht (D : Subgroup G) (hD : D ≤ S0) : D.map φ ≤ S0 := by
    exact (map_mono hD).trans (mem_normalizer_iff_map_conj_eq.mp htS).le
  have hPN := (ht P hPS).trans hSN
  have hQN := (ht Q hQS).trans hSN
  have hzV : z.val ∈ Bplane := by
    apply (mem_sourceImage W E Bplane z).mp
    rw [hV,hz]
    exact Submodule.subset_span (by simp)
  have hwV : w.val ∈ Bplane := by
    apply (mem_sourceImage W E Bplane w).mp
    rw [hV,hw]
    exact Submodule.subset_span (by simp)
  have hzne : z.val ≠ 1 := by
    intro hh
    have hez : z = 1 := Subtype.ext hh
    rw [hez,map_one,toAdd_one] at hz
    exact (by decide : (0 : core (Fin 6)) ≠ CoreCrossing.z) hz
  have hwne : w.val ≠ 1 := by
    intro hh
    have hew : w = 1 := Subtype.ext hh
    rw [hew,map_one,toAdd_one] at hw
    exact (by decide : (0 : core (Fin 6)) ≠ CoreCrossing.w) hw
  have hPc := image_centralizer_fixes K P (P.map φ) E f he _
    (source_z_span K E f he hA Bplane hVW hV z hz) (hc z hzV hzne)
  have hQc := image_centralizer_fixes K Q (Q.map φ) E f he _
    (source_w_span K E f he hA Bplane hVW hV w hw) (hc w hwV hwne)
  let D := W.map φ
  have hSW : S0 ≤ normalizer (W : Set G) := hSN.trans
    (normalizer_le_normalizer_characteristic_image K (ChapterC.blockU K))
  have hSD : S0 ≤ normalizer (D : Set G) := by
    have hh := (map_mono (f := φ) hSW).trans (W.le_normalizer_map φ)
    rw [show S0.map φ = S0 from mem_normalizer_iff_map_conj_eq.mp htS] at hh
    exact hh
  have hSD' : S0.subgroupOf (normalizer (K : Set G)) ≤
      normalizer (D.subgroupOf (normalizer (K : Set G)) : Set (normalizer (K : Set G))) :=
    (comap_mono hSD).trans (D.le_normalizer_comap _)
  have hn := halign.trans ((map_mono hSD').trans ((D.subgroupOf _).le_normalizer_map f))
  apply CoreCrossing.normal_crossing_le _ ?_ hn
  have hmap : (D.subgroupOf (normalizer (K : Set G))).map f =
      ((P.map φ).subgroupOf (normalizer (K : Set G))).map f ⊔
      ((Q.map φ).subgroupOf (normalizer (K : Set G))).map f := by
    dsimp only [D]
    rw [←hgen,Subgroup.map_sup,subgroupOf_sup hPN hQN,Subgroup.map_sup]
  rw [hmap]
  apply sup_le
  · intro g hg
    exact mem_sup_right ((CoreCrossing.fixes_orbitSpan_iff g).mp
      (CoreCrossing.orbitSpan_eq_hyperplane ▸ hPc g hg))
  · intro g hg
    exact mem_sup_left ((CoreCrossing.fixes_crossingHyperplane_iff g).mp (hQc g hg))
end CFSG.Quasithin.Chapter14.Section06.RankFiveNaturalSix
