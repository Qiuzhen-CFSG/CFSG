module
public import Theory.Representation.BinaryConjugationSection.LineConjugacy
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.RadicalOrientation.Basic
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.Cosets
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.Constructions
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Component.ModelExtension.SourceSetup
public import CFSG.Quasithin.Chapter13.Section07.ConjugateIntersections

/-!
# Aligning the actual critical pair in the linear-four branch

The natural H/O₂(H) action on U_H/V₁ is transitive on nonzero vectors.
The nontrivial seed commutator with O₂(H), and its containment in the
central line, lift this to conjugacy of actual order-two subgroups of U_H.
When A₁ ≤ U_H, choose the conjugator taking A₁ to the specified V₁^g.
The equality H = N_G(V₁) then transports Uγ and Vγ by that very same
conjugator. The tensor-span containment U₀ ≤ V_H puts Uγ inside the
abelian V_H and proves [U_H,Uγ] = 1.

The final theorem applies this to the original LocalSetup and CriticalPair,
discharging the flag, central commutator and abelianness premises from the
earlier source data. The natural marking and H = G₁ are the earlier
13.8.27(b) inputs, supplied by qt-d-138-six-g2-source. Construction of the
13.8.29 tensor-span containment, the subsequent parabolic-image argument
and the contradiction from 13.8.31(3) remain with qt-d-138-linear-four-source;
qt-d-1381-source owns final assembly. This does not yet establish 13.8.31(1).

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
combined manuscript (1 March 2004), 13.8.31(1), printed pp.964–965.
Subgroup.conjBy is left conjugation; the specified source right conjugator
is retained as g⁻¹ throughout the statements.
-/

public section
open Subgroup Representation
namespace CFSG.Quasithin.Chapter13.Section08.LinearFour
open CriticalGeometry BinaryLinear.OuterCyclic
variable {G : Type*} [Group G] [Finite G]

/-- Align the critical line with the original g-conjugate of V1; the same
conjugator aligns both of the actual critical-pair groups. -/
theorem source_critical_line_alignment
    (L T H V V1 V2 V3 : Subgroup G) (c : CriticalPair L T H V)
    (ρ : Representation (ZMod 2) H (Fin 4 → ZMod 2))
    (d : BinaryConjugationSection H (Source.UH H V3) V1 ρ)
    (e : (H ⧸ pCore 2 H) ≃* LinearGroup 4)
    (hact : ∀ h w, ρ h w = e (QuotientGroup.mk' (pCore 2 H) h) w)
    (hH : H = normalizer (V1 : Set G)) (hV1 : Nat.card V1 = 2)
    (hcomm : ⁅Source.UH H V3,H.pCoreIn 2⁆ ≤ V1)
    (hseed : ⁅V3,H.pCoreIn 2⁆ ≠ ⊥)
    (hA : c.Aone V1 ≤ Source.UH H V3) (hdisj : V1 ⊓ c.Aone V1 = ⊥)
    (h12 : V1 ≤ V2) (h2U : V2 ≤ Source.UH H V3)
    (g : G2 V2) (hg : (g:G) ∉ H) :
    ∃ k : H,
      (c.Aone V1).conjBy (k:G) = V1.conjBy ((g:G)⁻¹) ∧
      (c.Ugamma V3).conjBy (k:G) = (Source.UH H V3).conjBy ((g:G)⁻¹) ∧
      c.Vgamma.conjBy (k:G) = (Source.VH H V).conjBy ((g:G)⁻¹) := by
  have htrans : ∀ u v : Fin 4 → ZMod 2, u ≠ 0 → v ≠ 0 → ∃ h : H, ρ h u = v := by
    intro u v hu hv
    obtain ⟨a,ha⟩ := exists_linearEquiv_apply_eq hu hv
    obtain ⟨h,hh⟩ := QuotientGroup.mk'_surjective (pCore 2 H) (e.symm a)
    exact ⟨h,by rw [hact,hh,e.apply_symm_apply]; exact ha⟩
  have hHQ : H ≤ normalizer (H.pCoreIn 2 : Set G) := by
    apply (normal_subgroupOf_iff_le_normalizer (pCoreIn_le 2 H)).mp
    have he : (H.pCoreIn 2).subgroupOf H = pCore 2 H :=
      comap_map_eq_self_of_injective H.subtype_injective _
    rw [he]
    infer_instance
  have hHZ : H ≤ centralizer (V1 : Set G) := by
    rw [hH]
    exact normalizer_le_centralizer_of_card_two V1 hV1
  have hZQ : V1 ≤ centralizer (H.pCoreIn 2 : Set G) :=
    le_centralizer_iff.mp ((pCoreIn_le 2 H).trans hHZ)
  have hmove : ⁅Source.UH H V3,H.pCoreIn 2⁆ ≠ ⊥ := by
    intro he
    apply hseed
    exact bot_unique ((commutator_mono (le_conjugateSpanBy V3 H) le_rfl).trans_eq he)
  have hcA : Nat.card (c.Aone V1) = 2 := by
    rw [CriticalPair.Aone,card_map_of_injective (MulAut.conj _).injective,hV1]
  have hAZ : ¬ c.Aone V1 ≤ V1 := by
    intro hh
    have hb : c.Aone V1 = ⊥ := by rw [←hdisj,inf_eq_right.mpr hh]
    rw [hb,Nat.card_eq_fintype_card] at hcA
    simp at hcA
  have hcB : Nat.card (V1.conjBy ((g:G)⁻¹)) = 2 := by
    change Nat.card (V1.map _) = 2
    rw [card_map_of_injective (MulAut.conj _).injective,hV1]
  have hBU : V1.conjBy ((g:G)⁻¹) ≤ Source.UH H V3 := by
    rintro _ ⟨x,hx,rfl⟩
    exact h2U ((mem_normalizer_iff.mp g⁻¹.property x).mp (h12 hx))
  have hBZ : ¬ V1.conjBy ((g:G)⁻¹) ≤ V1 := by
    intro hh
    have he : V1.conjBy ((g:G)⁻¹) = V1 := eq_of_le_of_card_ge hh (by rw [hcB,hV1])
    have hn : (g:G)⁻¹ ∈ H := hH ▸ mem_normalizer_iff_map_conj_eq.mpr he
    exact hg (H.inv_mem_iff.mp hn)
  obtain ⟨k,hk⟩ := d.exists_line_conjugator_of_transitive_binary_kernel
    (H.pCoreIn 2) (pCoreIn_le 2 H) hHQ hZQ hV1 hcomm hmove htrans
    (c.Aone V1) (V1.conjBy ((g:G)⁻¹)) hcA hcB hA hBU hAZ hBZ
  refine ⟨k,hk,?_,?_⟩
  · change ((Source.UH H V3).conjBy (c.gb:G)).conjBy (k:G) = _
    rw [conjBy_conjBy]
    apply conjugates_eq_of_line_conjugates_eq V1 _
      (hH ▸ le_normalizer_conjugateSpanBy V3 H)
    exact (conjBy_conjBy V1 _ _).symm.trans hk
  · change ((Source.VH H V).conjBy (c.gb:G)).conjBy (k:G) = _
    rw [conjBy_conjBy]
    apply conjugates_eq_of_line_conjugates_eq V1 _
      (hH ▸ le_normalizer_conjugateSpanBy V H)
    exact (conjBy_conjBy V1 _ _).symm.trans hk


/-- In the contrary line-containment case, the original tensor span puts the
actual endpoint Uγ in VH and forces [UH,Uγ] = 1. -/
theorem source_critical_line_forces_centralization
    (L T H V V1 V2 V3 : Subgroup G) (c : CriticalPair L T H V)
    [IsMulCommutative (Source.VH H V)]
    (ρ : Representation (ZMod 2) H (Fin 4 → ZMod 2))
    (d : BinaryConjugationSection H (Source.UH H V3) V1 ρ)
    (e : (H ⧸ pCore 2 H) ≃* LinearGroup 4)
    (hact : ∀ h w, ρ h w = e (QuotientGroup.mk' (pCore 2 H) h) w)
    (hH : H = normalizer (V1 : Set G)) (hV1 : Nat.card V1 = 2)
    (hcomm : ⁅Source.UH H V3,H.pCoreIn 2⁆ ≤ V1)
    (hseed : ⁅V3,H.pCoreIn 2⁆ ≠ ⊥)
    (hA : c.Aone V1 ≤ Source.UH H V3) (hdisj : V1 ⊓ c.Aone V1 = ⊥)
    (h12 : V1 ≤ V2) (h2U : V2 ≤ Source.UH H V3)
    (hUV : U0 (Source.UH H V3) V2 ≤ Source.VH H V)
    (g : G2 V2) (hg : (g:G) ∉ H) :
    c.Ugamma V3 ≤ Source.VH H V ∧ ⁅Source.UH H V3,c.Ugamma V3⁆ = ⊥ := by
  obtain ⟨k,_,hk,_⟩ := source_critical_line_alignment L T H V V1 V2 V3 c
    ρ d e hact hH hV1 hcomm hseed hA hdisj h12 h2U g hg
  have hgU : (Source.UH H V3).conjBy ((g:G)⁻¹) ≤ Source.VH H V := by
    apply le_trans ?_ hUV
    rintro _ ⟨x,hx,rfl⟩
    exact subset_closure ⟨(g:G)⁻¹,g⁻¹.property,x,hx,rfl⟩
  have hγV : c.Ugamma V3 ≤ Source.VH H V := by
    have hm := map_mono (f := (MulAut.conj ((k:G)⁻¹)).toMonoidHom) (hk.le.trans hgU)
    change ((c.Ugamma V3).conjBy (k:G)).conjBy ((k:G)⁻¹) ≤
      (Source.VH H V).conjBy ((k:G)⁻¹) at hm
    rw [conjBy_inv] at hm
    have hn : (Source.VH H V).conjBy ((k:G)⁻¹) = Source.VH H V :=
      mem_normalizer_iff_map_conj_eq.mp
        (le_normalizer_conjugateSpanBy V H (H.inv_mem k.property))
    rwa [hn] at hm
  refine ⟨hγV,bot_unique ?_⟩
  exact (commutator_mono ((UH_le_U0 _ _).trans hUV) hγV).trans_eq
    (commutator_self_eq_bot_iff.mpr inferInstance)


/-- Original standing-source application of the contrary-case alignment.
The natural quotient and H = G1 are precisely the earlier 13.8.27(b) inputs;
the span containment is the still separate tensor geometry of 13.8.29. -/
theorem source_critical_pair_centralization
    {T : Sylow 2 G} {L V V1 V2 V3 M G1 H : Subgroup G}
    (s : TransvectionRecognition.Component.ModelExtension.LocalSetup T L V V1 V2 V3 M G1)
    (hF9 : (Section07.ConjugateIntersections.sourceSetup T L V V3 V1 H).Hypothesis)
    (c : CriticalPair L (T:Subgroup G) H V)
    (ρ : Representation (ZMod 2) H (Fin 4 → ZMod 2))
    (d : BinaryConjugationSection H (Source.UH H V3) V1 ρ)
    (e : (H ⧸ pCore 2 H) ≃* LinearGroup 4)
    (hact : ∀ h w, ρ h w = e (QuotientGroup.mk' (pCore 2 H) h) w)
    (hH : H = G1) (hseed : ⁅V3,G1.pCoreIn 2⁆ ≠ ⊥)
    (hA : c.Aone V1 ≤ Source.UH H V3) (hdisj : V1 ⊓ c.Aone V1 = ⊥)
    (hUV : U0 (Source.UH H V3) V2 ≤ Source.VH H V)
    (g : G2 V2) (hg : (g:G) ∉ H) :
    c.Ugamma V3 ≤ Source.VH H V ∧ ⁅Source.UH H V3,c.Ugamma V3⁆ = ⊥ := by
  let : IsMulCommutative (Source.VH H V) := by
    change IsMulCommutative (conjugateSpanBy V H)
    rw [hH]
    exact s.abelian_span
  apply source_critical_line_forces_centralization L T H V V1 V2 V3 c ρ d e hact
    (hH.trans s.first_normalizer) s.line_card
    hF9.commutator_UH_QH_le_point (hH ▸ hseed) hA hdisj s.line_le_plane
    (s.plane_le_seed.trans (le_conjugateSpanBy V3 H)) hUV g hg

end CFSG.Quasithin.Chapter13.Section08.LinearFour
