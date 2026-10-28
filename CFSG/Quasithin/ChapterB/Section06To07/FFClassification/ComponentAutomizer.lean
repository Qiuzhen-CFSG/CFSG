module

public import CFSG.Quasithin.ChapterB.Section06To07.Structure
public import Theory.GroupTheory.GeneralizedFitting.ComponentOrbitAutomizer

/-!
# Minimal parabolicity of the literal component automizer

Every proper nontrivial subgroup of a simple component invariant under
its Sylow stabilizer lies in the original unique maximal overgroup M.
The component intersection with M is nontrivial and proper. Its normality
under N_M(L) makes the image of N_M(L) in N_H(L)/C_H(L) proper. Every
proper overgroup of the actual Sylow image lies in this image, proving
uniqueness and hence minimal parabolicity of the automizer.

Source: Aschbacher–Smith, B.6.8(3) and its use in B.6.9, printed pp.114–116
(1 March 2004). The full normalizer need not be minimal parabolic; the
quotient by its actual centralizer is essential.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.ChapterB
variable {G : Type*} [Group G] [Finite G]

/-- Every proper nontrivial stabilizer-invariant seed lies in the original maximal overgroup. -/
theorem component_seed_le_minimalParabolicMax
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    {L A : Subgroup G} (hL : IsComponent G L) [IsSimpleGroup L]
    (hAL : A ≤ L) (ha : A ≠ ⊥) (haL : A ≠ L)
    (hinv : (T : Subgroup G) ⊓ normalizer (L : Set G) ≤ normalizer (A : Set G)) :
    A ≤ minimalParabolicMax T hP := by
  have hm := minimalParabolicMax_spec T hP
  exact le_sup_left.trans (hP.1.le_maximal ⟨hm.2,hm.1.covBy_top⟩ le_sup_right
    (lt_top_iff_ne_top.mpr (component_seed_sup_sylow_ne_top T hL hAL ha haL hinv)))

/-- A residual-generating component is outside the unique maximal overgroup. -/
theorem component_not_le_minimalParabolicMax
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤) {L : Subgroup G}
    (ho : componentOrbit L (T : Subgroup G) = pResidual 2 G) :
    ¬ L ≤ minimalParabolicMax T hP := by
  intro hl
  have ht := (minimalParabolicMax_spec T hP).2
  have hr : pResidual 2 G ≤ minimalParabolicMax T hP := by
    rw [← ho]
    exact (componentOrbit_le_sup L (T : Subgroup G)).trans (sup_le hl ht)
  have hh := sup_le hr ht
  rw [pResidual_sup_sylow_eq_top T] at hh
  exact (minimalParabolicMax_spec T hP).1.ne_top (top_unique hh)

/-- The component intersection with the original maximal overgroup is nontrivial and proper. -/
theorem component_maximal_intersection
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤) {L : Subgroup G}
    (hL : IsComponent G L) (heven : 2 ∣ Nat.card L)
    (ho : componentOrbit L (T : Subgroup G) = pResidual 2 G) :
    L ⊓ minimalParabolicMax T hP ≠ ⊥ ∧ L ⊓ minimalParabolicMax T hP ≠ L := by
  refine ⟨?_, ?_⟩
  · intro hb
    apply component_sylow_intersection_ne_bot T hL heven
    apply le_bot_iff.mp
    intro l hl
    have hh : (l : G) ∈ L ⊓ minimalParabolicMax T hP :=
      ⟨l.property, (minimalParabolicMax_spec T hP).2 hl⟩
    rw [hb, mem_bot] at hh
    exact mem_bot.mpr (Subtype.ext hh)
  · intro he
    apply component_not_le_minimalParabolicMax T hP ho
    rw [← he]
    exact inf_le_right

/-- The actual maximal-overgroup image in the automizer is proper. -/
theorem component_automizer_maximal_image_ne_top
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤) {L : Subgroup G}
    (hL : IsComponent G L) [IsSimpleGroup L] (heven : 2 ∣ Nat.card L)
    (ho : componentOrbit L (T : Subgroup G) = pResidual 2 G) :
    ((minimalParabolicMax T hP).subgroupOf (normalizer (L : Set G))).map
      (NormalizerAction.quotient L) ≠ ⊤ := by
  intro he
  let M := minimalParabolicMax T hP
  let A := L ⊓ M
  let N := normalizer (L : Set G)
  let q := NormalizerAction.quotient L
  obtain ⟨hAb,hAL⟩ := component_maximal_intersection T hP hL heven ho
  have hn : L ≤ normalizer (A : Set G) := by
    apply le_normalizer_iff.mpr
    intro l hl a ha
    have hq : q ⟨l,L.le_normalizer hl⟩ ∈ (M.subgroupOf N).map q := by
      rw [he]
      trivial
    obtain ⟨m,hm,hmq⟩ := hq
    have hc := congrArg (fun z => (NormalizerAction.action L z) (⟨a,ha.1⟩ : L)) hmq
    have hv := congrArg Subtype.val hc
    change (m : G) * a * (m : G)⁻¹ = l * a * l⁻¹ at hv
    refine ⟨L.mul_mem (L.mul_mem hl ha.1) (L.inv_mem hl), ?_⟩
    rw [← hv]
    exact M.mul_mem (M.mul_mem hm ha.2) (M.inv_mem hm)
  let : (A.subgroupOf L).Normal := (normal_subgroupOf_iff_le_normalizer inf_le_left).mpr hn
  obtain hb | ht := IsSimpleGroup.eq_bot_or_eq_top_of_normal (A.subgroupOf L) inferInstance
  · apply hAb
    have hh := congrArg (map L.subtype) hb
    simpa only [map_subgroupOf_eq_of_le (show A ≤ L from inf_le_left), Subgroup.map_bot] using hh
  · apply hAL
    have hh := congrArg (map L.subtype) ht
    simpa only [map_subgroupOf_eq_of_le (show A ≤ L from inf_le_left),
      ← MonoidHom.range_eq_map, range_subtype] using hh

/-- Every proper automizer overgroup of the actual Sylow image lies in the original maximal image. -/
theorem component_automizer_overgroup_le
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤) {L : Subgroup G}
    (hL : IsComponent G L) [IsSimpleGroup L] (heven : 2 ∣ Nat.card L)
    (ho : componentOrbit L (T : Subgroup G) = pResidual 2 G)
    (B : Subgroup (NormalizerAction.Star L)) (hB : B ≠ ⊤)
    (hSB : ((T : Subgroup G).subgroupOf (normalizer (L : Set G))).map
      (NormalizerAction.quotient L) ≤ B) :
    B ≤ ((minimalParabolicMax T hP).subgroupOf (normalizer (L : Set G))).map
      (NormalizerAction.quotient L) := by
  let N := normalizer (L : Set G)
  let q := NormalizerAction.quotient L
  let c := NormalizerAction.componentMap L
  let A := (B.comap c).map L.subtype
  have hAL : A ≤ L := map_subtype_le _
  have hB0 : A ≠ ⊥ := by
    intro hb
    apply component_sylow_intersection_ne_bot T hL heven
    apply le_bot_iff.mp
    intro l hl
    have hcl : c l ∈ B := hSB (mem_map_of_mem q hl)
    have hm : (l : G) ∈ A := mem_map_of_mem L.subtype hcl
    rw [hb, mem_bot] at hm
    exact mem_bot.mpr (Subtype.ext hm)
  have hBL : A ≠ L := by
    intro he
    have hcB : NormalizerAction.componentImage L ≤ B := by
      rw [← NormalizerAction.componentMap_range]
      rintro z ⟨l,rfl⟩
      have hm : (l : G) ∈ A := he.symm ▸ l.property
      obtain ⟨a,ha,hal⟩ := hm
      have he' : a = l := Subtype.ext hal
      exact he' ▸ ha
    apply hB
    apply top_unique
    rw [← component_automizer_sylow_supplement T hL ho]
    exact sup_le hcB hSB
  have hinv : (T : Subgroup G) ⊓ N ≤ normalizer (A : Set G) := by
    apply le_normalizer_iff.mpr
    intro t ht x hx
    obtain ⟨l,hl,rfl⟩ := hx
    let n : N := ⟨t,ht.2⟩
    let l' := L.normalizerMonoidHom n l
    have hcl : c l' = q n * c l * (q n)⁻¹ := by
      change q (inclusion L.le_normalizer l') =
        q n * q (inclusion L.le_normalizer l) * (q n)⁻¹
      rw [← map_inv, ← map_mul, ← map_mul]
      congr 1
    refine ⟨l', ?_, rfl⟩
    change c l' ∈ B
    rw [hcl]
    have htB : q n ∈ B := hSB (mem_map_of_mem q ht.1)
    exact B.mul_mem (B.mul_mem htB hl) (B.inv_mem htB)
  have hAM := component_seed_le_minimalParabolicMax T hP hL hAL hB0 hBL hinv
  let S := ((T : Subgroup G).subgroupOf N).map q
  let D := NormalizerAction.componentImage L
  let B₀ := ((minimalParabolicMax T hP).subgroupOf N).map q
  have hSB₀ : S ≤ B₀ := map_mono (subgroupOf_mono _ (minimalParabolicMax_spec T hP).2)
  let : D.Normal := (inferInstance : (L.subgroupOf N).Normal).map q
    (QuotientGroup.mk'_surjective (NormalizerAction.C L))
  intro b hb
  have hm : b ∈ D ⊔ S := by
    rw [component_automizer_sylow_supplement T hL ho]
    trivial
  obtain ⟨d,hd,s,hs,hds⟩ := mem_sup_of_normal_left.mp hm
  have hdB : d ∈ B := by
    have hh := B.mul_mem hb (B.inv_mem (hSB hs))
    simpa only [← hds, mul_inv_cancel_right] using hh
  change d ∈ NormalizerAction.componentImage L at hd
  rw [← NormalizerAction.componentMap_range] at hd
  obtain ⟨l,rfl⟩ := hd
  have hlA : (l : G) ∈ A := mem_map_of_mem L.subtype hdB
  have hdB₀ : c l ∈ B₀ := mem_map_of_mem q (hAM hlA)
  exact hds ▸ B₀.mul_mem hdB₀ (hSB₀ hs)

/-- The literal component automizer is a minimal parabolic over the original normalizer-Sylow image. -/
theorem component_automizer_minimalParabolic
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤) {L : Subgroup G}
    (hL : IsComponent G L) [IsSimpleGroup L] (heven : 2 ∣ Nat.card L)
    (ho : componentOrbit L (T : Subgroup G) = pResidual 2 G) :
    ∃ S : Sylow 2 (NormalizerAction.Star L),
      (S : Subgroup (NormalizerAction.Star L)) = ((T : Subgroup G).subgroupOf (normalizer (L : Set G))).map
        (NormalizerAction.quotient L) ∧ IsMinimalParabolicOver S ⊤ := by
  obtain ⟨S₀,hS₀⟩ := component_normalizer_sylow T hL ho
  let S := S₀.mapSurjective (f := NormalizerAction.quotient L)
    (QuotientGroup.mk'_surjective (NormalizerAction.C L))
  have hS : (S : Subgroup (NormalizerAction.Star L)) = ((T : Subgroup G).subgroupOf (normalizer (L : Set G))).map
      (NormalizerAction.quotient L) := by
    change (S₀ : Subgroup (normalizer (L : Set G))).map _ = _
    rw [hS₀]
  refine ⟨S,hS, (isMinimalParabolicOver_top_iff S).mpr ⟨?_, ?_⟩⟩
  · let B := ((minimalParabolicMax T hP).subgroupOf (normalizer (L : Set G))).map
      (NormalizerAction.quotient L)
    have hb : B ≠ ⊤ := component_automizer_maximal_image_ne_top T hP hL heven ho
    have hsB : (S : Subgroup (NormalizerAction.Star L)) ≤ B := by
      rw [hS]
      exact map_mono (subgroupOf_mono _ (minimalParabolicMax_spec T hP).2)
    have hmax : IsCoatom B := by
      refine ⟨hb, ?_⟩
      intro D hBD
      by_contra hD
      have hd := component_automizer_overgroup_le T hP hL heven ho D hD
        (hS ▸ hsB.trans hBD.le)
      exact hBD.not_ge hd
    refine ⟨B, ⟨hmax,hsB⟩, ?_⟩
    intro D hD
    have hd := component_automizer_overgroup_le T hP hL heven ho D hD.1.ne_top
      (hS ▸ hD.2)
    exact ((hD.1.le_iff_eq hb).mp hd).symm
  · exact component_automizer_sylow_not_normal T hL heven S hS

end CFSG.Quasithin.ChapterB
