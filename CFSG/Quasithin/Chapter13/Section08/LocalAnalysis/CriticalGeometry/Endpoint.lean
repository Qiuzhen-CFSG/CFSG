module
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.Cosets
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.RankBounds
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.ComponentCommutator
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.LocalConsequences

/-!
# Generation and rank at the genuine critical endpoint

The terminal edge is the conjugate of L₁T by the chosen endpoint element,
and its vertex two-core is the conjugate Qγ. Conjugate-span transport
identifies Vγ and transports its noncentrality. Thus the relative normal-
generation argument applies to the actual endpoint and terminal edge.

`generation_all` proves 13.8.18(1) for every F≤U_H outside D_H by the
proved component commutator theorem. `generation_hypotheses` proves (2),
and `rank_gt_one_of_component_generation` proves (3), in the stronger
form excluding the common-axis action. `rank_gt_one_of_generation_no_axis`
is 13.8.11(2): it derives D_H<U_H from generation across the proper edge,
then applies the corrected rank-one argument.

Earlier inputs remain explicit: the flag containments and elementary
abelianness (13.5/13.7), noncentrality (13.7.7), the fixed edge quotient
(13.8.4(5)), kernel identities and normalization (F.9.2/13), and the
chosen rank comparison (F.9.16). For component generation, normality,
two-perfectness, quasisimplicity of the actual endpoint star image and
H=K(L₁T) are the allowed earlier component conclusions.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 13.8.9(1),
13.8.11(2), and 13.8.18(1)–(3), printed pp.949–950 and 953.
-/

@[expose] public section
open Subgroup Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.CriticalGeometry
variable {G : Type*} [Group G]

theorem map_conjugateSpan (W J : Subgroup G) {G' : Type*} [Group G'] (f : G →* G') :
    (conjugateSpanBy W J).map f = conjugateSpanBy (W.map f) (J.map f) := by
  unfold conjugateSpanBy
  rw [MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨j, hj, w, hw, rfl⟩, rfl⟩
    exact ⟨f j, mem_map_of_mem f hj, f w, mem_map_of_mem f hw, by simp⟩
  · rintro ⟨_, ⟨j, hj, rfl⟩, _, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨j * w * j⁻¹, ⟨j, hj, w, hw, rfl⟩, by simp⟩

namespace CriticalPair
variable {L T H V : Subgroup G} (c : CriticalPair L T H V)

theorem edgeGroup_eq (L₁ : Subgroup G) (he : (L ⊔ T) ⊓ H = L₁ ⊔ T) :
    edgeGroup L T H c.gamma c.previous =
      (L₁ ⊔ T).map (MulAut.conj (c.gb : G)).toMonoidHom := by
  have hp : vertexGroup L T H c.previous =
      (L ⊔ T).map (MulAut.conj (c.gb : G)).toMonoidHom := by
    change vertexGroup L T H (c.path.getVert (c.path.length - 1)) = _
    rw [← c.gb_zero, vertexGroup_smul, vertexGroup_base]
    rfl
  change vertexGroup L T H c.gamma ⊓ vertexGroup L T H c.previous = _
  rw [c.vertexGroup_gamma, hp, ← map_inf _ _ _ (MulAut.conj (c.gb : G)).injective,
    inf_comm H, he]

theorem Qgamma_eq [Finite G] : c.Qgamma = (vertexGroup L T H c.gamma).pCoreIn 2 := by
  rw [c.vertexGroup_gamma]
  exact map_pCoreIn_of_ker_isPGroup _
    (IsPGroup.ker_isPGroup_of_injective (MulAut.conj (c.gb : G)).injective) H

theorem normalizes_Qgamma [Finite G] :
    vertexGroup L T H c.gamma ≤ normalizer (c.Qgamma : Set G) := by
  rw [c.Qgamma_eq]
  exact (vertexGroup L T H c.gamma).le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image _ (pCore 2 (vertexGroup L T H c.gamma)))

theorem Vgamma_span : c.Vgamma = conjugateSpanBy
    (V.map (MulAut.conj (c.gb : G)).toMonoidHom) (vertexGroup L T H c.gamma) := by
  rw [c.vertexGroup_gamma]
  exact map_conjugateSpan V H _

theorem normalizes_Ugamma (V₃ : Subgroup G) :
    vertexGroup L T H c.gamma ≤ normalizer (c.Ugamma V₃ : Set G) := by
  apply le_normalizer_iff_commutator_le_left.mpr
  rw [c.vertexGroup_gamma, CriticalPair.Ugamma, ← map_commutator]
  exact map_mono (le_normalizer_iff_commutator_le_left.mp (le_normalizer_conjugateSpanBy V₃ H))

theorem noncentral_of_generation
    (V₃ F : Subgroup G) (hVH : V ≤ H) (hFJ : F ≤ vertexGroup L T H c.gamma)
    (hgen : vertexGroup L T H c.gamma = conjugateSpanBy F (vertexGroup L T H c.gamma) ⊔
      edgeGroup L T H c.gamma c.previous)
    (hedge : ⁅edgeGroup L T H c.gamma c.previous,
      V.map (MulAut.conj (c.gb : G)).toMonoidHom⁆ ≤ c.Ugamma V₃)
    (hnoncentral : ¬ ⁅Source.VH H V, H⁆ ≤ Source.UH H V₃) :
    ¬ ⁅F, c.Vgamma⁆ ≤ c.Ugamma V₃ := by
  apply noncentral_of_relative_generation (vertexGroup L T H c.gamma) F
    (edgeGroup L T H c.gamma c.previous) (V.map (MulAut.conj (c.gb : G)).toMonoidHom)
    c.Vgamma (c.Ugamma V₃) hFJ
  · rw [c.vertexGroup_gamma]
    exact map_mono hVH
  · exact c.normalizes_Ugamma V₃
  · exact c.Vgamma_span
  · exact hgen
  · exact hedge
  · intro hc
    rw [c.vertexGroup_gamma, CriticalPair.Vgamma, CriticalPair.Ugamma, ← map_commutator] at hc
    have hh := (map_le_map_iff_of_injective (MulAut.conj (c.gb : G)).injective).mp hc
    exact hnoncentral (by rwa [commutator_comm])

theorem generation_all [Finite G]
    (L₁ K V₃ V₁ : Subgroup G)
    (hH : H = K ⊔ (L₁ ⊔ T)) (he : (L ⊔ T) ⊓ H = L₁ ⊔ T)
    (hK : ((K.map (MulAut.conj (c.gb : G)).toMonoidHom).subgroupOf
      (vertexGroup L T H c.gamma)).Normal)
    (hres : pResidual 2 ((K.map (MulAut.conj (c.gb : G)).toMonoidHom).subgroupOf
      (vertexGroup L T H c.gamma)) = ⊤)
    (hqs : IsQuasisimple (Source.starImage (vertexGroup L T H c.gamma)
      (K.map (MulAut.conj (c.gb : G)).toMonoidHom)))
    (hU : Source.UH H V₃ ≤ (edgeGroup L T H c.gamma c.previous).pCoreIn 2)
    (hD : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) =
      Source.UH H V₃ ⊓ c.Qgamma) :
    ∀ F : Subgroup G, F ≤ Source.UH H V₃ →
      ¬ F ≤ Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) →
      vertexGroup L T H c.gamma = conjugateSpanBy F (vertexGroup L T H c.gamma) ⊔
        edgeGroup L T H c.gamma c.previous := by
  have hJ : vertexGroup L T H c.gamma =
      K.map (MulAut.conj (c.gb : G)).toMonoidHom ⊔ edgeGroup L T H c.gamma c.previous := by
    rw [c.vertexGroup_gamma, c.edgeGroup_eq L₁ he]
    simpa only [Subgroup.map_sup] using congrArg (Subgroup.map (MulAut.conj (c.gb : G)).toMonoidHom) hH
  exact generation_of_edge_two_core _ _ _ _ _ _ hJ hK hres hqs hU
    (by simpa only [c.Qgamma_eq] using hD)

theorem rank_gt_one_of_generation_no_axis [Finite G]
    (V₃ V₁ : Subgroup G) [IsElementaryAbelian 2 (Source.UH H V₃)]
    [IsElementaryAbelian 2 (Source.VH H V)]
    (hV₃V : V₃ ≤ V) (hVH : V ≤ H) (hV₁H : V₁ ≤ H)
    (hHN : H ≤ normalizer (V₁ : Set G))
    (hVγH : c.Vgamma ≤ H) (hUHJ : Source.UH H V₃ ≤ vertexGroup L T H c.gamma)
    (hQ : ⁅Source.UH H V₃, Source.QH H⁆ ≤ V₁)
    (hnoncentral : ¬ ⁅Source.VH H V, H⁆ ≤ Source.UH H V₃)
    (hgen : vertexGroup L T H c.gamma =
      conjugateSpanBy (Source.UH H V₃) (vertexGroup L T H c.gamma) ⊔
        edgeGroup L T H c.gamma c.previous)
    (hedge : ⁅edgeGroup L T H c.gamma c.previous,
      V.map (MulAut.conj (c.gb : G)).toMonoidHom⁆ ≤ c.Ugamma V₃)
    (hstar : Source.starImage H (c.Ugamma V₃) ≠ ⊥)
    (hDγ : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ =
      c.Ugamma V₃ ⊓ Source.QH H)
    (hDH : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) =
      Source.UH H V₃ ⊓ c.Qgamma)
    (hQE : c.Qgamma ≤ edgeGroup L T H c.gamma c.previous)
    (hEJ : edgeGroup L T H c.gamma c.previous < vertexGroup L T H c.gamma)
    (hcomparison : (Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁)).relIndex
        (Source.UH H V₃) ≤
      (Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁).relIndex (c.Ugamma V₃))
    (hline : Nat.card V₁ = 2)
    (hno : let _ : IsElementaryAbelian 2 (c.Ugamma V₃) := IsElementaryAbelian.map _
      ¬ HasTransvectionAxis (Source.UH H V₃) (c.Ugamma V₃)
        (Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁)
        (hUHJ.trans (c.normalizes_Ugamma V₃))) :
    1 < rank (Source.starImage H c.Vgamma) := by
  let _ : IsElementaryAbelian 2 (c.Ugamma V₃) := IsElementaryAbelian.map _
  let _ : IsElementaryAbelian 2 c.Vgamma := IsElementaryAbelian.map _
  have hproper := DH_lt_of_generation (vertexGroup L T H c.gamma)
    (edgeGroup L T H c.gamma c.previous) c.Qgamma (Source.UH H V₃)
    (c.Ugamma V₃) (c.Aone V₁) c.normalizes_Qgamma hQE hEJ hgen hDH
  exact rank_gt_one_of_no_axis H (Source.UH H V₃) (c.Ugamma V₃) c.Vgamma (c.Aone V₁) V₁
    (conjugateSpanBy_le_self (hV₃V.trans hVH)) hVγH hV₁H hHN
    (map_mono (conjugateSpanBy_mono hV₃V le_rfl))
    (hVγH.trans (le_normalizer_conjugateSpanBy V₃ H)) (hUHJ.trans (c.normalizes_Ugamma V₃))
    hQ (c.noncentral_of_generation V₃ (Source.UH H V₃) hVH hUHJ hgen hedge hnoncentral)
    hstar hDγ hproper hcomparison hline hno

/-- The two hypotheses of 13.8.11 in case (2) of 13.8.8, as asserted by
13.8.18(2). The strict denominators refer to the chosen genuine critical pair. -/
theorem generation_hypotheses [Finite G]
    (L₁ K V₃ V₁ : Subgroup G)
    (hH : H = K ⊔ (L₁ ⊔ T)) (he : (L ⊔ T) ⊓ H = L₁ ⊔ T)
    (hK : ((K.map (MulAut.conj (c.gb : G)).toMonoidHom).subgroupOf
      (vertexGroup L T H c.gamma)).Normal)
    (hres : pResidual 2 ((K.map (MulAut.conj (c.gb : G)).toMonoidHom).subgroupOf
      (vertexGroup L T H c.gamma)) = ⊤)
    (hqs : IsQuasisimple (Source.starImage (vertexGroup L T H c.gamma)
      (K.map (MulAut.conj (c.gb : G)).toMonoidHom)))
    (hU : Source.UH H V₃ ≤ (edgeGroup L T H c.gamma c.previous).pCoreIn 2)
    (hD : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) =
      Source.UH H V₃ ⊓ c.Qgamma)
    (hV₃V : V₃ ≤ V) (hVγH : c.Vgamma ≤ H)
    (hDγ : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ =
      c.Ugamma V₃ ⊓ Source.QH H)
    (hDHlt : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) < Source.UH H V₃)
    (hDγlt : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ < c.Ugamma V₃) :
    Source.starImage H (c.Ugamma V₃) ≠ ⊥ ∧
      vertexGroup L T H c.gamma =
        conjugateSpanBy (Source.UH H V₃) (vertexGroup L T H c.gamma) ⊔
          edgeGroup L T H c.gamma c.previous := by
  refine ⟨starImage_ne_bot_of_Dgamma_lt H (Source.UH H V₃) (c.Ugamma V₃) V₁
    ((map_mono (conjugateSpanBy_mono hV₃V le_rfl)).trans hVγH) hDγ hDγlt, ?_⟩
  exact c.generation_all L₁ K V₃ V₁ hH he hK hres hqs hU hD
    (Source.UH H V₃) le_rfl hDHlt.not_ge

/-- The rank conclusion of 13.8.18(3), in the stronger form excluding only
the transvection group with axis Dγ. Component generation is discharged here. -/
theorem rank_gt_one_of_component_generation [Finite G]
    (L₁ K V₃ V₁ : Subgroup G)
    (hH : H = K ⊔ (L₁ ⊔ T)) (he : (L ⊔ T) ⊓ H = L₁ ⊔ T)
    (hK : ((K.map (MulAut.conj (c.gb : G)).toMonoidHom).subgroupOf
      (vertexGroup L T H c.gamma)).Normal)
    (hres : pResidual 2 ((K.map (MulAut.conj (c.gb : G)).toMonoidHom).subgroupOf
      (vertexGroup L T H c.gamma)) = ⊤)
    (hqs : IsQuasisimple (Source.starImage (vertexGroup L T H c.gamma)
      (K.map (MulAut.conj (c.gb : G)).toMonoidHom)))
    (hU : Source.UH H V₃ ≤ (edgeGroup L T H c.gamma c.previous).pCoreIn 2)
    (hD : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) =
      Source.UH H V₃ ⊓ c.Qgamma)
    [IsElementaryAbelian 2 (Source.UH H V₃)] [IsElementaryAbelian 2 (Source.VH H V)]
    (hV₃V : V₃ ≤ V) (hVH : V ≤ H) (hV₁H : V₁ ≤ H)
    (hHN : H ≤ normalizer (V₁ : Set G)) (hVγH : c.Vgamma ≤ H)
    (hQ : ⁅Source.UH H V₃, Source.QH H⁆ ≤ V₁)
    (hnoncentral : ¬ ⁅Source.VH H V, H⁆ ≤ Source.UH H V₃)
    (hedge : ⁅edgeGroup L T H c.gamma c.previous,
      V.map (MulAut.conj (c.gb : G)).toMonoidHom⁆ ≤ c.Ugamma V₃)
    (hDγ : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ =
      c.Ugamma V₃ ⊓ Source.QH H)
    (hDHlt : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) < Source.UH H V₃)
    (hDγlt : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ < c.Ugamma V₃)
    (hQE : c.Qgamma ≤ edgeGroup L T H c.gamma c.previous)
    (hEJ : edgeGroup L T H c.gamma c.previous < vertexGroup L T H c.gamma)
    (hcomparison : (Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁)).relIndex
        (Source.UH H V₃) ≤
      (Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁).relIndex (c.Ugamma V₃))
    (hline : Nat.card V₁ = 2)
    (hno : let _ : IsElementaryAbelian 2 (c.Ugamma V₃) := IsElementaryAbelian.map _
      ¬ HasTransvectionAxis (Source.UH H V₃) (c.Ugamma V₃)
        (Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁)
        ((hU.trans ((pCoreIn_le 2 _).trans inf_le_left)).trans (c.normalizes_Ugamma V₃))) :
    1 < rank (Source.starImage H c.Vgamma) := by
  obtain ⟨hstar, hgen⟩ := c.generation_hypotheses L₁ K V₃ V₁ hH he hK hres hqs hU hD
    hV₃V hVγH hDγ hDHlt hDγlt
  exact c.rank_gt_one_of_generation_no_axis V₃ V₁ hV₃V hVH hV₁H hHN hVγH
    (hU.trans ((pCoreIn_le 2 _).trans inf_le_left)) hQ hnoncentral hgen hedge
    hstar hDγ hD hQE hEJ hcomparison hline hno

end CriticalPair
end CFSG.Quasithin.Chapter13.Section08.CriticalGeometry
end
