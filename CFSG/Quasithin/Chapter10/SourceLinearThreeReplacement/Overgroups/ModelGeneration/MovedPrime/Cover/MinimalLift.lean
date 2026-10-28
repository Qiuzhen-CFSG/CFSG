module
public import CFSG.Quasithin.ChapterB.Section06To07.Structure
public import Theory.GroupTheory.GeneralizedFitting.ComponentOrbitAutomizer

/-!
# Lifting minimal parabolicity from the literal component automizer

Pull the automizer's unique maximal Sylow overgroup back to a seed in the
simple component. Its Sylow orbit has proper normalizer: if that orbit were
normal in the ambient group, the simple-component dichotomy would force the
component to normalize the proper nontrivial seed.

Every proper Sylow overgroup has proper image in the automizer. When the
component normalizer is normal, decomposing this overgroup over the full
Sylow shows that it normalizes the seed orbit. Its normalizer is therefore
the unique maximal Sylow overgroup. All normality assertions retain their
actual carriers, and the quotient is the literal N(K)/C(K).

Source: Aschbacher--Smith B.6.8(3), E.2.2 and its reuse in 10.3.3,
printed pp.114--115, 215--216 and 756--757.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.ModelGeneration.Cover
variable {H : Type*} [Group H] [Finite H]

omit [Finite H] in
private theorem simple_seed_not_normalized {K A : Subgroup H}
    [IsSimpleGroup K] (hAK : A ≤ K) (ha : A ≠ ⊥) (haK : A ≠ K) :
    ¬ K ≤ normalizer (A : Set H) := by
  intro hn
  let : (A.subgroupOf K).Normal := (normal_subgroupOf_iff_le_normalizer hAK).mpr hn
  obtain hb | ht := IsSimpleGroup.eq_bot_or_eq_top_of_normal (A.subgroupOf K) inferInstance
  · apply ha
    have hh := congrArg (map K.subtype) hb
    simpa only [map_subgroupOf_eq_of_le hAK, Subgroup.map_bot] using hh
  · apply haK
    have hh := congrArg (map K.subtype) ht
    simpa only [map_subgroupOf_eq_of_le hAK, ← MonoidHom.range_eq_map, range_subtype] using hh

omit [Finite H] in
private theorem seed_orbit_normalizer_ne_top (S : Sylow 2 H)
    {K A : Subgroup H} (hK : IsComponent H K) [IsSimpleGroup K]
    (hAK : A ≤ K) (ha : A ≠ ⊥) (haK : A ≠ K)
    (hinv : (S : Subgroup H) ⊓ normalizer (K : Set H) ≤ normalizer (A : Set H)) :
    normalizer (componentOrbit A (S : Subgroup H) : Set H) ≠ ⊤ := by
  intro ht
  let X := componentOrbit A (S : Subgroup H)
  let : X.Normal := normalizer_eq_top_iff.mp ht
  let := hK.2
  have hXA : X ≤ normalizer (A : Set H) :=
    (componentOrbit_le_seed_sup_centralizer hK hAK hinv).trans
      (sup_le A.le_normalizer ((centralizer_le hAK).trans (centralizer_le_normalizer _)))
  apply simple_seed_not_normalized hAK ha haK
  rcases simple_subnormal_normal_dichotomy K X hK.1 with h | h
  · exact h.trans hXA
  · exact ((commutator_eq_bot_iff_le_centralizer.mp h).trans
      (centralizer_le (le_componentOrbit A (S : Subgroup H)))).trans
        (centralizer_le_normalizer _)

omit [Finite H] in
private theorem overgroup_normalizes_seed_orbit (S : Sylow 2 H)
    {N A P : Subgroup H} [N.Normal]
    (hcover : (S : Subgroup H) ⊔ N = ⊤) (hSP : (S : Subgroup H) ≤ P)
    (hinv : P ⊓ N ≤ normalizer (A : Set H)) :
    P ≤ normalizer (componentOrbit A (S : Subgroup H) : Set H) := by
  have he : componentOrbit A P = componentOrbit A (S : Subgroup H) := by
    apply le_antisymm
    · apply iSup_le
      intro x
      have hx : (x : H) ∈ (S : Subgroup H) ⊔ N := by rw [hcover]; trivial
      obtain ⟨s, hs, n, hn, hsn⟩ := mem_sup_of_normal_right.mp hx
      have hnP : n ∈ P := by
        have hh := P.mul_mem (P.inv_mem (hSP hs)) x.property
        simpa only [← hsn, inv_mul_cancel_left] using hh
      have hAn : A.map (MulAut.conj n).toMonoidHom = A :=
        mem_normalizer_iff_map_conj_eq.mp (hinv ⟨hnP,hn⟩)
      have hmap : (MulAut.conj (s * n)).toMonoidHom =
          (MulAut.conj s).toMonoidHom.comp (MulAut.conj n).toMonoidHom := by
        ext a
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      rw [← hsn, hmap, ← map_map, hAn]
      exact le_iSup (fun s : S => A.map (MulAut.conj (s : H)).toMonoidHom) ⟨s,hs⟩
    · apply iSup_le
      intro s
      exact le_iSup (fun p : P => A.map (MulAut.conj (p : H)).toMonoidHom) ⟨s,hSP s.property⟩
  rw [← he]
  exact le_normalizer_componentOrbit A P

private theorem proper_overgroup_automizer_image (S : Sylow 2 H)
    {K P : Subgroup H} (hK : IsComponent H K) [IsSimpleGroup K]
    (heven : 2 ∣ Nat.card K) (hgen : K ⊔ (S : Subgroup H) = ⊤)
    (hSP : (S : Subgroup H) ≤ P) (hP : P ≠ ⊤) :
    (P.subgroupOf (normalizer (K : Set H))).map (NormalizerAction.quotient K) ≠ ⊤ := by
  intro he
  let A := K ⊓ P
  have hAb : A ≠ ⊥ := by
    intro hb
    apply component_sylow_intersection_ne_bot S hK heven
    apply le_bot_iff.mp
    intro k hk
    have hh : (k : H) ∈ A := ⟨k.property, hSP hk⟩
    rw [hb, mem_bot] at hh
    exact mem_bot.mpr (Subtype.ext hh)
  have hAK : A ≠ K := by
    intro he
    apply hP
    apply top_unique
    rw [← hgen]
    exact sup_le (he ▸ (show A ≤ P from inf_le_right)) hSP
  apply simple_seed_not_normalized (show A ≤ K from inf_le_left) hAb hAK
  apply le_normalizer_iff.mpr
  intro k hk a ha
  have hq : NormalizerAction.quotient K ⟨k,K.le_normalizer hk⟩ ∈
      (P.subgroupOf (normalizer (K : Set H))).map (NormalizerAction.quotient K) := by
    rw [he]
    trivial
  obtain ⟨m,hm,hmq⟩ := hq
  have hc := congrArg (fun z => (NormalizerAction.action K z) (⟨a,ha.1⟩ : K)) hmq
  have hv := congrArg Subtype.val hc
  change (m : H) * a * (m : H)⁻¹ = k * a * k⁻¹ at hv
  refine ⟨K.mul_mem (K.mul_mem hk ha.1) (K.inv_mem hk), ?_⟩
  rw [← hv]
  exact P.mul_mem (P.mul_mem hm ha.2) (P.inv_mem hm)

/-- Minimality of the faithful component automizer lifts to the original group. -/
theorem minimalParabolic_of_component_automizer
    (S : Sylow 2 H)
    {K : Subgroup H} (hK : IsComponent H K) [IsSimpleGroup K]
    (heven : 2 ∣ Nat.card K)
    (hN : (normalizer (K : Set H)).Normal)
    (hgen : K ⊔ (S : Subgroup H) = ⊤)
    (R : Sylow 2 (NormalizerAction.Star K))
    (hR : (R : Subgroup (NormalizerAction.Star K)) = NormalizerAction.sylowImage K S)
    (hsup : NormalizerAction.componentImage K ⊔ (R : Subgroup _) = ⊤)
    (hmin : ChapterB.IsMinimalParabolicOver R ⊤) :
    ChapterB.IsMinimalParabolicOver S ⊤ := by
  let N := normalizer (K : Set H)
  let q := NormalizerAction.quotient K
  let B := ChapterB.minimalParabolicMax R hmin
  let A := (B.comap (NormalizerAction.componentMap K)).map K.subtype
  have hAK : A ≤ K := map_subtype_le _
  have hSB : NormalizerAction.sylowImage K S ≤ B :=
    hR ▸ (ChapterB.minimalParabolicMax_spec R hmin).2
  have hAb : A ≠ ⊥ := by
    intro hb
    apply component_sylow_intersection_ne_bot S hK heven
    apply le_bot_iff.mp
    intro k hk
    have hkB : NormalizerAction.componentMap K k ∈ B := hSB (mem_map_of_mem q hk)
    have ha : (k : H) ∈ A := mem_map_of_mem K.subtype hkB
    rw [hb,mem_bot] at ha
    exact mem_bot.mpr (Subtype.ext ha)
  have hAKne : A ≠ K := by
    intro he
    have hKB : NormalizerAction.componentImage K ≤ B := by
      rw [← NormalizerAction.componentMap_range]
      rintro z ⟨k,rfl⟩
      have hkA : (k : H) ∈ A := he.symm ▸ k.property
      obtain ⟨a,ha,hak⟩ := hkA
      have hh : a = k := Subtype.ext hak
      exact hh ▸ ha
    apply (ChapterB.minimalParabolicMax_spec R hmin).1.ne_top
    apply top_unique
    rw [← hsup]
    exact sup_le hKB (hR ▸ hSB)
  have hseed (P : Subgroup H)
      (hPB : (P.subgroupOf N).map q ≤ B) : P ⊓ N ≤ normalizer (A : Set H) := by
    apply le_normalizer_iff.mpr
    intro n hn a ha
    obtain ⟨k,hk,rfl⟩ := ha
    let nN : N := ⟨n,hn.2⟩
    have hnB : q nN ∈ B := hPB (mem_map_of_mem q hn.1)
    let k' := K.normalizerMonoidHom nN k
    have he : NormalizerAction.componentMap K k' = q nN *
        NormalizerAction.componentMap K k * (q nN)⁻¹ := by
      change q (inclusion K.le_normalizer k') = q nN *
        q (inclusion K.le_normalizer k) * (q nN)⁻¹
      rw [← map_inv, ← map_mul, ← map_mul]
      congr 1
    refine ⟨k', ?_, rfl⟩
    change NormalizerAction.componentMap K k' ∈ B
    rw [he]
    exact B.mul_mem (B.mul_mem hnB hk) (B.inv_mem hnB)
  have hAS : (S : Subgroup H) ⊓ N ≤ normalizer (A : Set H) := hseed _ hSB
  let X := componentOrbit A (S : Subgroup H)
  let M := normalizer (X : Set H)
  have hM : M ≠ ⊤ := seed_orbit_normalizer_ne_top S hK hAK hAb hAKne hAS
  have hSM : (S : Subgroup H) ≤ M := le_normalizer_componentOrbit A (S : Subgroup H)
  let := hN
  have hcover : (S : Subgroup H) ⊔ N = ⊤ := by
    apply top_unique
    rw [← hgen]
    exact sup_le (K.le_normalizer.trans le_sup_right) le_sup_left
  have hbound (P : Subgroup H) (hSP : (S : Subgroup H) ≤ P) (hP : P ≠ ⊤) : P ≤ M := by
    let U := (P.subgroupOf N).map q
    have hU : U ≠ ⊤ := proper_overgroup_automizer_image S hK heven hgen hSP hP
    have hRU : (R : Subgroup (NormalizerAction.Star K)) ≤ U := by
      rw [hR]
      exact map_mono (subgroupOf_mono N hSP)
    have hUB : U ≤ B := hmin.1.le_maximal
      ⟨(ChapterB.minimalParabolicMax_spec R hmin).2,
        (ChapterB.minimalParabolicMax_spec R hmin).1.covBy_top⟩
      hRU (lt_top_iff_ne_top.mpr hU)
    exact overgroup_normalizes_seed_orbit S hcover hSP (hseed P hUB)
  apply (ChapterB.isMinimalParabolicOver_top_iff S).mpr
  constructor
  · have hmax : IsCoatom M := by
      refine ⟨hM, ?_⟩
      intro P hMP
      by_contra hP
      exact hMP.not_ge (hbound P (hSM.trans hMP.le) hP)
    refine ⟨M, ⟨hmax,hSM⟩, ?_⟩
    intro P hP
    exact ((hP.1.le_iff_eq hM).mp (hbound P hP.2 hP.1.ne_top)).symm
  · intro hSn
    let := hSn
    have hRn : (R : Subgroup (NormalizerAction.Star K)).Normal := by
      rw [hR]
      exact (inferInstance : ((S : Subgroup H).subgroupOf N).Normal).map q
        (QuotientGroup.mk'_surjective (NormalizerAction.C K))
    exact (ChapterB.isMinimalParabolicOver_top_iff R).mp hmin |>.2 hRn

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.ModelGeneration.Cover
