module

public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio
public import CFSG.Quasithin.ChapterF.Section09.Basic

/-!
# Discharging F.9.2(3) in the terminal A₅ argument

The literal F.9.1 record in Chapter 13 supplies the original F.9 setup,
including reducedness, relative normality, the seed kernel bound and the
commutator lifting condition. Its proved F.9.2 kernel theorem therefore
identifies the actual commutator preimage with O₂(H). This removes the
separate universal kernel premise from the terminal ratio contradiction.

The earlier 13.5.7, F.9.16(3), component-recognition and B.4 classification
inputs remain explicit with their source owners. No elementary-abelian
hypothesis on U_H is needed for the kernel identity itself.

Source: Aschbacher–Smith F.9.1–2 and the last paragraph of13.6, printedpp318,935.
-/

public section
open Subgroup
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio
open Section08
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₃ V₁ H : Subgroup G} [IsElementaryAbelian 2 V]

/-- The Chapter13 source record is the original F.9.1 setup on the same groups. -/
theorem SourceF91.f9Hypothesis (h : SourceF91 T L V V₃ V₁ H) :
    (⟨T, L, V, V₃, V₁, H⟩ : ChapterF.Section09.Setup G).Hypothesis := by
  obtain ⟨hn, hr⟩ := h.v_reduced
  have hVLT : V ≤ L ⊔ (T : Subgroup G) := h.v_le_sylow.trans le_sup_right
  exact {
    elementary := inferInstance
    residual := h.residual
    normalizes_L := h.normalizes_L
    characteristic_L := h.characteristic_L
    V_le_LT := hVLT
    reduced := ⟨hn, IsElementaryAbelian.subgroupOf hVLT, hr⟩
    sylow_centralizer := h.sylow_centralizer
    point_card := h.z_card
    normalizes_point := h.normalizes_V₁
    point_lt := h.z_lt
    plus_le := h.v₃_le
    H_centralizes := h.a_centralizes
    local_le := h.a_contains
    characteristic_H := h.a_characteristic
    kernel_core := h.a_kernel
    local_normalizes := h.b_normalizes
    irreducible := h.b_irreducible
    normalizer_control := h.c_normalizer
    generated_core := h.d_core
    commutator_lifting := h.e_commutators }

/-- F.9.2(3) identifies the original ambient commutator preimage with Q_H. -/
theorem SourceF91.commutatorPreimage_eq_QH (h : SourceF91 T L V V₃ V₁ H) :
    commutatorPreimage H (Source.UH H V₃) V₁ = Source.QH H := by
  let D : ChapterF.Section09.Setup G := ⟨T, L, V, V₃, V₁, H⟩
  have hD : D.Hypothesis := h.f9Hypothesis
  have hn : H ≤ normalizer (V₁ : Set G) :=
    h.a_centralizes.trans (Subgroup.centralizer_le_normalizer _)
  change commutatorPreimage H D.UH V₁ = D.QH
  apply le_antisymm
  · intro x hx
    have hk : x ∈ hD.kernel D.UH := by
      apply (hD.mem_kernel_iff hD.UH_le_H).mpr
      refine ⟨commutatorPreimage_le _ _ _ hx, ?_⟩
      intro u hu
      have hc := commutator_le.mp
        (commutator_commutatorPreimage_le H D.UH V₁ hn) x hx u hu
      simpa only [commutatorElement_inv] using V₁.inv_mem hc
    exact hD.kernel_UH_eq_QH ▸ hk
  · apply le_commutatorPreimage (pCoreIn_le 2 H)
    apply commutator_le.mpr
    intro x hx u hu
    have hk : x ∈ hD.kernel D.UH := hD.kernel_UH_eq_QH.symm ▸ hx
    have hc := (hD.mem_kernel_iff hD.UH_le_H).mp hk |>.2 u hu
    simpa only [commutatorElement_inv] using V₁.inv_mem hc

/-- The precise earlier kernel implication used by the terminal consumer is proved. -/
theorem earlierF923_of_source (T : Sylow 2 G) (L V V₃ V₁ : Subgroup G)
    [IsElementaryAbelian 2 V] : EarlierF923 T L V V₃ V₁ := by
  intro H h
  exact h.commutatorPreimage_eq_QH

universe u

/-- The actual terminal ratio contradiction with its F.9.2(3) premise discharged. -/
theorem terminal_contradiction_of_source_kernel
    {G : Type u} [Group G] [Finite G] {𝒦 : GroupClass.{u}}
    (hG : IsSimpleQTKE 𝒦 G)
    {T : Sylow 2 G} {L V V₃ M : Subgroup G} [IsElementaryAbelian 2 V]
    (d : FiveCoordinates V) (v z : V)
    (hv : BinaryPermutation.FiveGeometry.form (d.equiv v).toAdd ≠ 0)
    (hz : z ≠ 1) (hz2 : orderOf z.val = 2)
    (hqz : BinaryPermutation.FiveGeometry.form (d.equiv z).toAdd = 0)
    (hAlt : alternatingGroup (Fin 5) ≤ d.actor.range)
    (hfusion : ∀ x : V, x ≠ 1 → ∀ a : G, MulAut.conj a x.val ∈ V →
      ∃ n ∈ normalizer (V : Set G), MulAut.conj n x.val = MulAut.conj a x.val)
    [IsMulCommutative (centralizerConjugateClosure V z.val)]
    (hCv : centralizer ({v.val} : Set G) ≤ normalizer (V : Set G))
    (hmark : ∀ x : V, x.val ∈ V₃ ↔ (d.equiv x).toAdd.val 4 = 0)
    (hN : normalizer (V₃ : Set G) ≤ normalizer (V : Set G))
    (hcontains : residualCentralizer L (zpowers z.val) ⊔ (T : Subgroup G) ≤
      centralizer ({z.val} : Set G))
    (houtside : ¬ centralizer ({z.val} : Set G) ≤ M)
    (hcomponents : Components.Conclusion
      ((T : Subgroup G).subgroupOf (centralizer ({z.val} : Set G))))
    (h1357 : Earlier1357 T L V V₃ (zpowers z.val) (centralizer ({z.val} : Set G)) M)
    (hF9163 : EarlierF9163 T L V V₃ (zpowers z.val))
    (hB42 : SourceClassifications.FullB42.{u,u} 𝒦)
    (hB45 : Section08.Components.Suzuki.NaturalSections.RatioRecognition.SmallRatioSource.FullB45.{u,u} 𝒦) :
    False := by
  exact terminal_contradiction hG d v z hv hz hz2 hqz hAlt hfusion hCv hmark hN
    hcontains houtside hcomponents h1357 (earlierF923_of_source T L V V₃ (zpowers z.val))
    hF9163 hB42 hB45

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio
