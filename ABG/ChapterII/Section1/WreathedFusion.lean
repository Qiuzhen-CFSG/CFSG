module
public import ABG.ChapterII.Section1.WreathedFocalCases
public import ABG.ChapterII.Section1.WreathedInvolutionFusion
public import ABG.ChapterII.Section1.WreathedUAutomizerIndex
public import ABG.ChapterII.Section1.WreathedVAutomizerIndex
public import ABG.ChapterII.Section1.WreathedWeakCenter
public import ABG.ChapterII.Section1.WreathedQuaternionQuotient
public import ABG.ChapterII.Section1.CyclicFocalKernel
public import ABG.ChapterII.Section1.CyclicFocalComplement
public import ABG.ChapterII.Section1.FocalIndexTwo
public import ABG.ChapterII.Section1.FocalFull

/-!
# ABG Chapter II, Section 1, Proposition 2

A finite group with a wreathed Sylow two-subgroup has one of the four exact
fusion patterns. The theorem keeps the arbitrary chosen base U and quaternion
central product V in its fusion frame. It includes the normal subgroup of
index 2^n with generalized quaternion Sylow subgroup in the Q case, the
actual Sylow image U in the D case, weak closure of every center subgroup,
all involution class counts, and the two specified automizer indices.

Choose a presentation of the Sylow subgroup. Frame transport identifies U
with its canonical base and V with a Sylow conjugate of its canonical central
product, preserving both indices. Each index is two or six. The four focal
calculations give respectively the cyclic derived subgroup, the quaternion
subgroup Y, the base U, or the full Sylow subgroup. Cyclic focal subgroup gives
a normal two-complement. The cyclic quotient by Y realizes the Q kernel of
index 2^n, while the index-two focal kernel realizes the D case with its
actual Sylow image. Both kernels have no further normal subgroup of index
two. Full focal subgroup excludes an ambient normal subgroup of index two.
The proved weak-closure and involution-fusion theorems finish the four cases.

This is the full Proposition 2 on article pp.11--13 of
`refs/latex/alperin-brauer-gorenstein-pages/page-012.tex` through
`page-014.tex`, using the paper's Alperin/focal approach. No simplicity or
conditional fusion-control hypothesis is added to the source frame.
-/

namespace ABG.Wreathed

/-- All four complete wreathed fusion alternatives of ABG II.1 Proposition 2. -/
public theorem proposition_two
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (n : ℕ) (U V : Subgroup G)
    (hf : WreathedFusionFrame S n U V) :
    WreathedQDPattern U V ∨ WreathedQPattern S n U V ∨
      WreathedDPattern U V ∨ WreathedNormalComplementPattern U V := by
  obtain ⟨P⟩ := nonempty_presentation hf.1
  obtain ⟨hU, s, hs⟩ := hf.presentation_representatives P
  have hV : outerAutomizerIndex V =
      outerAutomizerIndex (P.V.map (S : Subgroup G).subtype) := by
    rw [← hs]
    exact outerAutomizerIndex_map _ (MulAut.conj (s : G))
  have hF := focal_subgroup_cases S P
  have hI := involution_fusion S n U V hf
  rcases u_automizer_index S n U V hf with hU2 | hU6 <;>
    rcases v_outer_automizer_index S n U V hf with hV2 | hV6
  · apply Or.inr (Or.inr (Or.inr ?_))
    have hF' := hF.1 (hU ▸ hU2) (hV.symm.trans hV2)
    have hcomp : HasNormalPComplement 2 G :=
      hasNormalTwoComplement_of_cyclic_focalSubgroupOf S (by
        rw [hF']
        exact P.derived_structure.2.1)
    exact ⟨hcomp, hI.2.2.2 hU2 hV2, hU2, hV2⟩
  · apply Or.inr (Or.inl ?_)
    have hF' := hF.2.1 (hU ▸ hU2) (hV.symm.trans hV6)
    let : P.Y.Normal := P.quaternion_subgroup.2.2
    let : IsCyclic (S ⧸ (S : Subgroup G).focalSubgroupOf) := by
      let : IsCyclic (S ⧸ P.Y) := P.quaternion_quotient.1
      let e := QuotientGroup.quotientMulEquivOfEq hF'
      exact isCyclic_of_injective e.toMonoidHom e.injective
    obtain ⟨K, hK, hKi, hKno, _, R, _, ⟨eR⟩⟩ :=
      exists_normal_sylow_of_cyclic_focal_quotient S
    have hKi' : K.index = 2 ^ n := by
      rw [hKi, hF']
      exact P.quaternion_quotient.2
    obtain ⟨m, hm, ⟨eY⟩⟩ := P.quaternion_subgroup.1
    have hSylow : HasGeneralizedQuaternionSylowTwo K :=
      ⟨R, m, hm, ⟨eR.trans ((MulEquiv.subgroupCongr hF').trans eY)⟩⟩
    exact ⟨⟨K, hK, hKi', hSylow, hKno⟩,
      weaklyClosed_center_subgroups_of_u_index_two S n U V hf hU2,
      hI.2.1 hU2 hV6, hU2, hV6⟩
  · apply Or.inr (Or.inr (Or.inl ?_))
    have hF' := hF.2.2.1 (hU ▸ hU6) (hV.symm.trans hV2)
    obtain ⟨K, hK, _, hKno, R, hR, _⟩ :=
      exists_normal_index_two_sylow_of_focalSubgroupOf S P.U P.index_U hF'
    exact ⟨⟨K, hK, hKno, R, hR.trans hU.symm⟩, hI.2.2.1 hU6 hV2, hU6, hV2⟩
  · exact Or.inl ⟨no_normal_index_two_of_focal_top S
      (hF.2.2.2 (hU ▸ hU6) (hV.symm.trans hV6)), hI.1 hU6 hV6, hU6, hV6⟩

end ABG.Wreathed
