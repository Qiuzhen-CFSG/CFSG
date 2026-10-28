module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedConjugateFieldGeometryClosure
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedConjugateFieldGeometryArrangement
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedConjugateFieldGeometrySylow
public import Theory.GroupTheory.SylowNormalizedResidual

/-!
# Field-plane centralizer cores in the natural four-dimensional case

The normalizer of an involutory field fixed space acts on that plane as
SL₂ over the fixed field. Its action is irreducible even when that field
has two elements. Displacement identifies the quotient of the original
layer by the plane with the plane, equivariantly for its full normalizer.

The normalizer is covered by its two-residual and the arranged Sylow
subgroup. Thus their joint action supplies the irreducibility needed in
G.2.1, including n=2, without asserting that O²(S₃) is S₃. G.2.2 then puts
the layer in the actual core of the plane centralizer and bounds its
commutator with that core by the plane. All normality is relative.

The companion LocalNoncyclic module applies these facts to both members
of the original conjugate pair. This is an earlier-source argument and
uses no LocalAnalysis record or M₂₂ identification.

Source: Aschbacher--Smith, 6.2.4(1--4), printed p.680, using 6.1.14 and
G.2.1--2, printed pp.670--671 and 332.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open Representation.SL2NaturalOffenders.FixedField ConjugateFixedSpaces
variable {G : Type*} [Group G] [Finite G]
  {κ : GroupClass} {L M B U : Subgroup G} {n : ℕ}

omit [Finite G] in
private theorem field_normalizer_invariant
    (hnatural : IsNaturalModule L B n)
    (hfield : IsInvolutoryFieldFixedSpace L M B U n) (hUne : U ≠ ⊥)
    (A : Subgroup G) (hAU : A ≤ U)
    (hNA : L ⊓ normalizer (U : Set G) ≤ normalizer (A : Set G)) : A = ⊥ ∨ A = U := by
  obtain ⟨F, _, _, _, _, e, f, hf⟩ := hnatural
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  obtain ⟨t, _, htB, hU, K, _, _, _, _, d, σ, hσ, hσsq, hσact⟩ := hfield
  obtain ⟨hasq, haout⟩ := field_quotientActor e d t σ hσ hσsq hσact
  let E := vectorActor f ⟨t, htB⟩
  have hi : Function.Involutive E := by
    apply intertwiner_involutive_of_fixed (quotientActor e t) E
      (vectorActor_intertwines e f hf t htB) hasq
    obtain ⟨u, hune⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hUne
    let v : B := ⟨u, (hU.le u.property).1⟩
    refine ⟨(f v).toAdd, ?_, ?_⟩
    · intro hz
      have hv : v = 1 := f.injective (by simpa using congrArg Multiplicative.ofAdd hz)
      exact hune (Subtype.ext (congrArg (fun b : B => (b : G)) hv))
    · apply (vectorActor_fixed_iff f ⟨t, htB⟩ _).mpr
      simpa [v] using (hU.le u.property).2
  obtain ⟨τ, _, _, p, hp, _, fU, hfU⟩ := fixedNormalizer_marking e f hf t htB hU hi hasq haout
  by_cases hA : A = ⊥
  · exact Or.inl hA
  right
  apply le_antisymm hAU
  obtain ⟨x, hxA, hx⟩ := SetLike.not_le_iff_exists.mp (mt le_bot_iff.mp hA)
  simp only [Subgroup.mem_bot] at hx
  let v : U := ⟨x, hAU hxA⟩
  have hv : (fU v).toAdd ≠ 0 := by
    intro hv
    have he : v = 1 := fU.injective (hv.trans fU.map_one.symm)
    exact hx (congrArg Subtype.val he)
  intro y hy
  by_cases hy1 : y = 1
  · subst y; exact A.one_mem
  let w : U := ⟨y, hy⟩
  have hw : (fU w).toAdd ≠ 0 := by
    intro hw
    have he : w = 1 := fU.injective (hw.trans fU.map_one.symm)
    exact hy1 (congrArg Subtype.val he)
  obtain ⟨s, hs⟩ := Theory.SpecificGroups.SymplecticFour.natural_transitive hv hw
  obtain ⟨l, hl⟩ := hp s
  have hc := hfU l v
  rw [hl, hs] at hc
  change (fU.symm (fU w) : G) = _ at hc
  rw [fU.symm_apply_apply] at hc
  change (w : G) ∈ A
  rw [hc]
  exact (mem_normalizer_iff.mp (hNA l.property) x).mp hxA

omit [Finite G] in
private theorem field_normalizer_interval
    (hnatural : IsNaturalModule L B n)
    (hfield : IsInvolutoryFieldFixedSpace L M B U n) (hUne : U ≠ ⊥) :
    U ≠ B ∧ ∀ A : Subgroup G, U ≤ A → A ≤ B →
      L ⊓ normalizer (U : Set G) ≤ normalizer (A : Set G) → A = U ∨ A = B := by
  obtain ⟨d, hd, hk, he⟩ := field_fixedSpace_displacement hnatural hfield hUne
  have hLB : L ≤ normalizer (B : Set G) := by
    obtain ⟨_, _, _, _, _, hm⟩ := hnatural
    exact hm.normalizes
  constructor
  · intro hUB
    obtain ⟨u, hune⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hUne
    obtain ⟨b, hb⟩ := hd u
    have hbker : b ∈ d.ker := by
      rw [hk]
      change (b : G) ∈ U
      rw [hUB]
      exact b.property
    exact hune (hb.symm.trans hbker)
  · intro A hUA hAB hNA
    let J := ((A.subgroupOf B).map d).map U.subtype
    have hJU : J ≤ U := map_subtype_le _
    have hNJ : L ⊓ normalizer (U : Set G) ≤ normalizer (J : Set G) := by
      apply le_normalizer_iff.mpr
      intro l hl x hx
      obtain ⟨u, ⟨b, hb, rfl⟩, rfl⟩ := hx
      let b' := B.normalizerMonoidHom ⟨l, hLB hl.1⟩ b
      have hb' : b' ∈ A.subgroupOf B := (mem_normalizer_iff.mp (hNA hl) b).mp hb
      exact ⟨d b', ⟨b', hb', rfl⟩, he ⟨l, hl⟩ b b' rfl⟩
    rcases field_normalizer_invariant hnatural hfield hUne J hJU hNJ with hzero | hfull
    · left
      apply le_antisymm _ hUA
      intro x hx
      let b : B := ⟨x, hAB hx⟩
      have hh : (d b : G) ∈ J := ⟨d b, ⟨b, hx, rfl⟩, rfl⟩
      rw [hzero, mem_bot] at hh
      have hbker : b ∈ d.ker := Subtype.ext hh
      rw [hk] at hbker
      exact hbker
    · right
      have hmap : (A.subgroupOf B).map d = ⊤ := by
        apply map_injective U.subtype_injective
        simpa only [← MonoidHom.range_eq_map, U.range_subtype] using hfull
      have hker : d.ker ≤ A.subgroupOf B := by rw [hk]; exact comap_mono hUA
      have hh := comap_map_eq_self hker
      rw [hmap, comap_top] at hh
      exact le_antisymm hAB (subgroupOf_eq_top.mp hh.symm)

private theorem normalized_le_residual_sup_of_sylow
    {N H S : Subgroup G} (hNH : N ≤ H)
    (hSN : S ≤ normalizer (N : Set G))
    (R : Sylow 2 H) (hR : (R : Subgroup H).map H.subtype = S) :
    N ≤ (pResidual 2 N).map N.subtype ⊔ S := by
  have hn : (R : Subgroup H) ≤ normalizer (N.subgroupOf H : Set H) := by
    rw [← subgroupOf_normalizer_eq hNH]
    intro r hr
    exact hSN (hR ▸ mem_map_of_mem H.subtype hr)
  have hh := map_mono (f := H.subtype)
    (le_embedded_pResidual_sup_sylow_of_normalizes R (N.subgroupOf H) hn)
  rwa [Subgroup.map_sup, map_embedded_pResidual, map_subgroupOf_eq_of_le hNH, hR] at hh

/-- The full fixed-plane normalizer supplies G.2.1 also over the binary
fixed field. Its Sylow supplement avoids identifying O²(S₃) with S₃. -/
theorem local_field_normalizer_hypothesis
    (S : Subgroup G) (hnatural : IsNaturalModule L B n)
    (hfield : IsInvolutoryFieldFixedSpace L M B U n)
    (hbase : (fieldNormalizerSetup L B U S).BaseHypothesis)
    (hSL : S ≤ normalizer (L : Set G)) :
    (fieldNormalizerSetup L B U S).Hypothesis := by
  obtain ⟨hproper, hirr⟩ := field_normalizer_interval hnatural hfield hbase.point_ne_bot
  have hLB : L ≤ normalizer (B : Set G) := by
    obtain ⟨_, _, _, _, _, hm⟩ := hnatural
    exact hm.normalizes
  have hSN : S ≤ normalizer (L ⊓ normalizer (U : Set G) : Set G) :=
    (le_inf hSL (hbase.T_normalizes_point.trans (normalizer (U : Set G)).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  obtain ⟨R, hR⟩ := hbase.sylow_H
  have hcover := normalized_le_residual_sup_of_sylow
    (show L ⊓ normalizer (U : Set G) ≤ normalizer (U : Set G) from inf_le_right) hSN R hR
  refine { hbase with
    local_normalizes_V := ?_
    quotient_nonzero := hproper
    irreducible := ?_ }
  · rw [fieldNormalizerSetup_local_actor]
    exact sup_le ((map_subtype_le _).trans (inf_le_left.trans hLB)) hbase.T_normalizes_V
  · intro A hUA hAB hNA
    apply hirr A hUA hAB
    rw [fieldNormalizerSetup_local_actor] at hNA
    exact hcover.trans hNA

/-- The field-plane closure lies in the actual centralizer core and is
central modulo the plane under that core, including the n=2 source case. -/
theorem local_field_plane_core
    {T : Sylow 2 G}
    (h : Hypothesis611 κ T L M B n)
    (hnatural : IsNaturalModule L (layer L B) n)
    (hE : ChapterE.Section06.HypothesisE61 κ T M (layer L B))
    (hfield : IsInvolutoryFieldFixedSpace L M (layer L B) U n) (hUne : U ≠ ⊥) :
    layer L B ≤ (centralizer (U : Set G)).pCoreIn 2 ∧
      ⁅layer L B, (centralizer (U : Set G)).pCoreIn 2⁆ ≤ U := by
  let := h.layer_elementary
  have hML := (normal_subgroupOf_iff_le_normalizer h.L_le).mp h.L_normal
  obtain ⟨P, _, hBP, hPL, hPB, hfieldP, hSyl⟩ := field_fixedSpace_sylow_arrangement
    T L M (layer L B) U n h.sylow_normalizes_layer hE.normalizer_le hML hE.ti
      hnatural hfield hUne
  obtain ⟨_, _, hNSyl, _⟩ := field_fixedSpace_sylow_control hE (by have := h.n_gt_one; omega)
    hnatural hML hfield hUne P hBP hPB hSyl
  obtain ⟨_, _, hchar⟩ := field_fixedSpace_even_local P (h.simpleQTKE.evenCharacteristic P)
    hBP hPB hfieldP hUne
  let S := (P : Subgroup G) ⊓ normalizer (U : Set G)
  have hUB : U ≤ layer L B := hfield.choose_spec.2.2.1.le.trans inf_le_left
  have hBS : layer L B ≤ S := le_inf hBP
    (((layer L B).le_centralizer.trans (centralizer_le hUB)).trans (Subgroup.centralizer_le_normalizer _))
  have hb := fieldNormalizerSetup_base S hUB hUne hBS inf_le_right
    (inf_le_left.trans hPB) (inf_le_left.trans hPL) hNSyl hchar
  have hs := local_field_normalizer_hypothesis S hnatural hfield hb (inf_le_left.trans hPL)
  have hBC : layer L B ≤ (fieldNormalizerSetup L (layer L B) U S).U :=
    le_conjugateSpanBy _ _
  have hcore : (fieldNormalizerSetup L (layer L B) U S).U ≤
      (centralizer (U : Set G)).pCoreIn 2 :=
    le_pCoreIn_of_normalizes hs.U_isPGroup hs.U_le_centralizer_point
      ((Subgroup.centralizer_le_normalizer _).trans (le_normalizer_conjugateSpanBy _ _))
  have hQ : (centralizer (U : Set G)).pCoreIn 2 ≤
      (normalizer (U : Set G)).pCoreIn 2 :=
    pCoreIn_mono_of_normalizes (Subgroup.centralizer_le_normalizer _)
      (normalizer_le_normalizer_centralizer U)
  exact ⟨hBC.trans hcore,
    (commutator_mono hBC hQ).trans hs.commutator_U_core_le_point⟩

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
