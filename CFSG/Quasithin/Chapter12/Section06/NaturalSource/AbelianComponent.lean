module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.AbelianResidual
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.AbelianQuadratic
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.IndexTwoSource

/-!
# The escaping abelian-branch component and the reduced source actor

Generation of H∞ by C-components selects K outside M. The two-conjugate
orbit theorem makes K₀=⟨Kᵀ⟩ normal in the original H, and two-perfectness
makes L₁ normalize K. The actual subgroup J=K₀L₁T still contains the central
point and escapes M, hence belongs to the same Hz family. Restriction keeps
K a C-component of J. Applying F.9.16 at this J gives the faithful action
on its own U_J/V₁ and the same edge-core quadratic witness.

No equality between K₀ and O²(J) is asserted: L₁ may contribute to O²(J).
Quasisimplicity of K/O₂(K), the F.9.18 model analysis and the exhaustive
12.6.31 alternatives remain subsequent obligations.
Source: Aschbacher--Smith, paragraph following12.6.29 and12.6.30, printed p.835.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
open BinaryPermutation BinaryPermutation.TerminalOrthogonal
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)

/-- An escaping C-component in the abelian branch, with its original actor
and normal Sylow orbit. This is independent of the contrary-nonabelian
SelectedComponent interface. -/
theorem SourceHypothesis.original_abelian_component_exists
    (hz : z ≠ 1) (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    (hTI : CentralLine.HasTIConjugatesIn V (M L))
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz) :
    ∃ K : Subgroup G, K ≤ H ∧ (K.subgroupOf H).IsCComponent ∧ ¬ K ≤ M L ∧
      (D.fullSetup hZ T z).L₁ ≤ normalizer (K : Set G) ∧
      ((conjugateSpanBy K (T : Subgroup G)).subgroupOf H).Normal := by
  let E := D.fullSetup hZ T z
  have hQ := S.original_star_sqtk D hZ z hz hH
  have hgen : cComponentLayer H = solvableResidual H :=
    Chapter1.Section02.proposition_1_2_1_one_of_A_3_9
      (fun X _ _ hX hO => ChapterA.Section03.SourceComponents.generation
        (fun Y _ _ => ChapterA.Section02.theoremA_knownSimple (G := Y))
        (ChapterA.Section03.SourceComponents.source_model_inputs_of_theoremC
          (fun Y _ _ => ChapterA.Section02.theoremC_knownSimple (G := Y))) hX hO) hQ
  have hex : ∃ A : Subgroup H, A.IsCComponent ∧ ¬ A.map H.subtype ≤ M L := by
    by_contra! hn
    apply S.original_abelian_residual_escapes D hZ z hz hTV hTz hbound hTI hns hH
    rw [←hgen]
    apply map_le_iff_le_comap.mpr
    apply sSup_le
    intro A hA
    exact map_le_iff_le_comap.mp (hn A hA)
  obtain ⟨A,hA,hout⟩ := hex
  let K := A.map H.subtype
  have hKH : K ≤ H := map_subtype_le _
  have hk : K.subgroupOf H = A := comap_map_eq_self_of_injective H.subtype_injective _
  have hTH : (T : Subgroup G) ≤ H := fun x hx => hH.1.2 (Or.inr hx)
  have hAH : E.L₁ ≤ H := fun x hx => hH.1.2 (Or.inl hx)
  have hp : IsPPerfect 2 (E.L₁.subgroupOf H) :=
    (isPPerfect_embedded_pResidual 2 (L ⊓ E.Gz)).of_surjective
      (subgroupOfEquivOfLe hAH).symm.toMonoidHom (subgroupOfEquivOfLe hAH).symm.surjective
  have hn := Chapter1.Section02.twoPerfect_normalizes_cComponent_source hQ (hk.symm ▸ hA) hp
  rw [←subgroupOf_normalizer_eq hKH] at hn
  have hL : E.L₁ ≤ normalizer (K : Set G) := fun x hx =>
    hn (show (⟨x,hAH hx⟩ : H) ∈ E.L₁.subgroupOf H from hx)
  let Ti := T.subtype hTH
  have ho : (conjugateSpanBy A (Ti : Subgroup H)).Normal :=
    conjugateSpanBy_sylow_normal A Ti
      (Chapter1.Section02.proposition_1_2_1_three_orbit_source hQ hA)
  have he : (conjugateSpanBy A (Ti : Subgroup H)).map H.subtype =
      conjugateSpanBy K (T : Subgroup G) := by
    rw [map_conjugateSpanBy]
    congr 1
    exact map_subgroupOf_eq_of_le hTH
  have hc : ((conjugateSpanBy K (T : Subgroup G)).subgroupOf H).Normal := by
    rw [←he]
    change (((conjugateSpanBy A (Ti : Subgroup H)).map H.subtype).comap H.subtype).Normal
    rw [comap_map_eq_self_of_injective H.subtype_injective]
    exact ho
  exact ⟨K,hKH,hk.symm ▸ hA,hout,hL,hc⟩

/-- Perform the source's change of actor H₁ to K₀L₁T. The same escaping
component remains a C-component, and the reduced actor is again in Hz. -/
theorem SourceHypothesis.original_abelian_reduced_actor_exists
    (hz : z ≠ 1) (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    (hTI : CentralLine.HasTIConjugatesIn V (M L))
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz) :
    ∃ K : Subgroup G, K ≤ H ∧ (K.subgroupOf H).IsCComponent ∧ ¬ K ≤ M L ∧
      (D.fullSetup hZ T z).L₁ ≤ normalizer (K : Set G) ∧
      let K₀ := conjugateSpanBy K (T : Subgroup G)
      let J := K₀ ⊔ (D.fullSetup hZ T z).L₁ ⊔ (T : Subgroup G)
      (K₀.subgroupOf H).Normal ∧ J ≤ H ∧ J ∈ (D.fullSetup hZ T z).Hz ∧
        (K.subgroupOf J).IsCComponent := by
  let E := D.fullSetup hZ T z
  obtain ⟨K,hKH,hK,hout,hL,hK₀⟩ := S.original_abelian_component_exists
    D hZ z hz hTV hTz hbound hTI hns hH
  let K₀ := conjugateSpanBy K (T : Subgroup G)
  let J := K₀ ⊔ E.L₁ ⊔ (T : Subgroup G)
  have hTH : (T : Subgroup G) ≤ H := fun x hx => hH.1.2 (Or.inr hx)
  have hLH : E.L₁ ≤ H := fun x hx => hH.1.2 (Or.inl hx)
  have hK₀H : K₀ ≤ H := conjugateSpanBy_le hKH (hTH.trans H.le_normalizer)
  have hJH : J ≤ H := sup_le (sup_le hK₀H hLH) hTH
  have hKJ : K ≤ J := (le_conjugateSpanBy K T).trans (le_sup_left.trans le_sup_left)
  have hTJ : (T : Subgroup G) ≤ J := le_sup_right
  have hLJ : E.L₁ ≤ J := le_sup_right.trans le_sup_left
  have hzT : E.V₁ ≤ (T : Subgroup G) :=
    E.V₁_le_V₅.trans (E.V₅_le.trans S.chosen.le_sylow)
  have hline : E.V₁ ≤ J.pCoreIn 2 := le_pCoreIn_of_normalizes
    ((IsElementaryAbelian.isPGroup 2 V).to_le (E.V₁_le_V₅.trans E.V₅_le))
    (hzT.trans hTJ)
    ((hJH.trans hH.2.1).trans (Subgroup.centralizer_le_normalizer _))
  have hJ : J ∈ E.Hz := by
    refine ⟨⟨?_,fun x hx => ?_⟩,hJH.trans hH.2.1,fun hm => hout (hKJ.trans hm)⟩
    · intro he
      have hh := bot_unique (hline.trans_eq he)
      exact hz (Subtype.ext (mem_bot.mp (hh ▸ mem_zpowers z.val)))
    · rcases hx with hx | hx
      · exact hLJ hx
      · exact hTJ hx
  exact ⟨K,hKH,hK,hout,hL,hK₀,hJH,hJ,hK.subgroupOf_of_le hKJ hJH⟩

/-- The escaping component construction feeds F.9.16 on the reduced
source actor K₀L₁T, preserving its literal U_J/V₁ and edge-core witness. -/
theorem SourceHypothesis.original_abelian_reduced_actor_quadratic
    (hz : z ≠ 1) (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    (hTI : CentralLine.HasTIConjugatesIn V (M L))
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz) :
    ∃ K : Subgroup G, K ≤ H ∧ (K.subgroupOf H).IsCComponent ∧ ¬ K ≤ M L ∧
      (D.fullSetup hZ T z).L₁ ≤ normalizer (K : Set G) ∧
      let K₀ := conjugateSpanBy K (T : Subgroup G)
      let J := K₀ ⊔ (D.fullSetup hZ T z).L₁ ⊔ (T : Subgroup G)
      (K₀.subgroupOf H).Normal ∧ J ≤ H ∧ J ∈ (D.fullSetup hZ T z).Hz ∧
        (K.subgroupOf J).IsCComponent ∧
        ∃ hU : IsElementaryAbelian 2 ((D.fullSetup hZ T z).UH J),
          let _ := hU
          ∃ a : Chapter15.Section03.AbelianAmalgam.LocalQuotientAction
              J ((D.fullSetup hZ T z).UH J) (D.fullSetup hZ T z).V₁,
            Representation.BinaryOffender.quadraticRatio a.representation ≤ 2 ∧
            ∃ B : Subgroup J,
              B ≤ (((L ⊔ (T : Subgroup G)) ⊓ J).pCoreIn 2).subgroupOf J ∧
              Representation.BinaryOffender.IsElementaryTwo
                (B.map (QuotientGroup.mk' (pCore 2 J))) ∧
              Representation.BinaryOffender.IsQuadratic a.representation
                (B.map (QuotientGroup.mk' (pCore 2 J))) ∧
              Representation.BinaryOffender.fixedCodim a.representation
                (B.map (QuotientGroup.mk' (pCore 2 J))) ≤
                  2 * Representation.BinaryOffender.rank (B.map (QuotientGroup.mk' (pCore 2 J))) ∧
              B.map (QuotientGroup.mk' (pCore 2 J)) ⊓ centralizer
                (Chapter15.Section03.AbelianAmalgam.GenerationOne.actorImage J
                  (Chapter15.Section03.AbelianAmalgam.GenerationOne.residual J) :
                    Set (J ⧸ pCore 2 J)) = ⊥ := by
  obtain ⟨K,hKH,hK,hout,hL,hK₀,hJH,hJ,hKJ⟩ := S.original_abelian_reduced_actor_exists
    D hZ z hz hTV hTz hbound hTI hns hH
  exact ⟨K,hKH,hK,hout,hL,hK₀,hJH,hJ,hKJ,
    S.original_abelian_quadratic_actor D hZ z hz hTV hTz hbound hTI hns hJ⟩

end CFSG.Quasithin.Chapter12.Section06
