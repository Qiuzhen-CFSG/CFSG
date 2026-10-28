module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.AbelianSuzukiSections
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Suzuki.NaturalSections.MovedSpace
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Suzuki.Action
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Suzuki.BorelSource.Action

/-!
# The centralizing part of the original point residual in the Suzuki row

Set C = L₁-star intersect C_H-star(K₀-star). The original E₉ quotient
makes C a {2,3}-group. Its action on the recognized natural central
section is scalar and therefore trivial, since the defining exponent is
odd. Perfectness of the actual component orbit lifts this fixation to
all W = [U_H/V₁,K₀-star], without splitting the fixed-space extension.

Moreover C is normal in H-star: K₀-star centralizes C, and L₁T normalizes
both factors of its intersection. Generation by these actual subgroups
supplies normality in the reduced actor. Establishing nontrivial seed
movement by the centralizing part remains part of the Suzuki exclusion.

Source: Aschbacher--Smith 12.6.31, printed p.836, Suzuki paragraph.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open Chapter13.Section08.Components Chapter13.Section08.Components.SourceModels
open Chapter13.Section08.Components.Suzuki
open Chapter13.Section08.Components.Suzuki.NaturalSections
open Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
open Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Exchanged
open Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)
  (hz : z ≠ 1) (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
  (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
  (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
    Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
  (hTI : CentralLine.HasTIConjugatesIn V (M L))
  (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
  {H K : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
  (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
  (hgen : conjugateSpanBy K (T : Subgroup G) ⊔ (D.fullSetup hZ T z).L₁ ⊔
    (T : Subgroup G) = H)
  [IsElementaryAbelian 2 ((D.fullSetup hZ T z).UH H)]
  (a : LocalQuotientAction H ((D.fullSetup hZ T z).UH H) (D.fullSetup hZ T z).V₁)

include hz hTV hTz hbound hTI hns hH hKH hK hgen in
/-- The actual centralizer of K₀-star inside L₁-star fixes the entire
moved section. Its {2,3}-order is derived from the original E₉ quotient. -/
theorem SourceHypothesis.original_abelian_suzuki_centralizer_fixes_moved
    {m : ℕ} (hm : 0 < m)
    (eK : (K ⧸ pCore 2 K) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) :
    let K₀ := actorImage H (conjugateSpanBy K (T : Subgroup G))
    subspaceCommutator a.representation ⊤ K₀ ≤
      fixedSpace a.representation (actorImage H (D.fullSetup hZ T z).L₁ ⊓
        centralizer (K₀ : Set (H ⧸ pCore 2 H))) := by
  let K₀ := actorImage H (conjugateSpanBy K (T : Subgroup G))
  let A := actorImage H (D.fullSetup hZ T z).L₁
  let C := A ⊓ centralizer (K₀ : Set (H ⧸ pCore 2 H))
  let W := subspaceCommutator a.representation ⊤ K₀
  change W ≤ fixedSpace a.representation C
  have hc : C ≤ centralizer (K₀ : Set (H ⧸ pCore 2 H)) := inf_le_right
  have hWK : K₀ ≤ subspaceStabilizer a.representation W :=
    subspaceCommutator_invariant a.representation ⊤ K₀
  have hWC : C ≤ subspaceStabilizer a.representation W :=
    subspaceCommutator_invariant_normalizer a.representation
      (le_subspaceStabilizer a.representation ⊤ (by simp))
      (hc.trans (Subgroup.centralizer_le_normalizer _))
  have hq := S.original_abelian_component_quasisimple D hZ z hz hTV hTz hbound hTI hns hH hKH hK
  let : IsQuasisimple (actorImage H K) :=
    hq.of_mulEquiv (componentStarEquiv H K hKH hK)
  have hTH : (T : Subgroup G) ≤ H := fun x hx => hH.1.2 (Or.inr hx)
  let : Group.IsPerfect K₀ := by
    change Group.IsPerfect (actorImage H (conjugateSpanBy K (T : Subgroup G)))
    have ho : actorImage H (conjugateSpanBy K (T : Subgroup G)) =
        conjugateSpanBy (actorImage H K) (actorImage H T) :=
      star_conjugateSpan H K T hKH hTH
    rw [ho]
    exact conjugateSpan_perfect _ _
  have hwgen : subspaceCommutator a.representation W K₀ = W :=
    perfect_movedSpace_generated a.representation K₀
  have hcard : ∃ r s : ℕ, Nat.card C = 2 ^ r * 3 ^ s := by
    obtain ⟨r,s,hrs⟩ := BorelSource.card_two_three
      (S.original_point_residual_star_twoThree D hZ z hz hTz hH)
    have hd : Nat.card C ∣ 2 ^ r * 3 ^ s :=
      (card_dvd_of_le (show C ≤ A from inf_le_left)).trans (dvd_of_eq hrs)
    obtain ⟨d,e,hd,he,hde⟩ := exists_dvd_and_dvd_of_dvd_mul hd
    obtain ⟨r',_,hr⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
    obtain ⟨s',_,hs⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp he
    exact ⟨r',s',by simpa only [hr,hs] using hde⟩
  obtain ⟨r,s,hrs⟩ := hcard
  rcases S.original_abelian_suzuki_sections D hZ z hz hTV hTz hbound hTI hns
      hH hKH hK hgen a hm eK with ⟨_,⟨b⟩⟩ | ⟨_,_,⟨b⟩⟩
  · exact central_extension_fixed_of_natural a.representation K₀ C W hWK hWC hc hwgen
      m r s hrs b.groupEquiv.toMonoidHom b.groupEquiv.surjective b.linearEquiv b.intertwines
  · exact central_extension_fixed_of_naturalPair a.representation K₀ C W hWK hWC hc hwgen
      m r s hrs b.groupEquiv.toMonoidHom b.groupEquiv.surjective b.linearEquiv b.intertwines

omit [IsElementaryAbelian 2 ((D.fullSetup hZ T z).UH H)] in
include hz hTV hH hKH hK hgen in
/-- The centralizer inside the original point residual is normal in H-star.
Normality is relative to the actual reduced actor, not to the ambient G. -/
theorem SourceHypothesis.original_abelian_residual_centralizer_normal :
    (actorImage H (D.fullSetup hZ T z).L₁ ⊓
      centralizer (actorImage H (conjugateSpanBy K (T : Subgroup G)) :
        Set (H ⧸ pCore 2 H))).Normal := by
  let E := D.fullSetup hZ T z
  let K₀ := conjugateSpanBy K (T : Subgroup G)
  let J := E.L₁ ⊔ (T : Subgroup G)
  let q := QuotientGroup.mk' (pCore 2 H)
  have hTH : (T : Subgroup G) ≤ H := fun x hx => hH.1.2 (Or.inr hx)
  have hLH : E.L₁ ≤ H := fun x hx => hH.1.2 (Or.inl hx)
  have hJH : J ≤ H := sup_le hLH hTH
  have hK₀H : K₀ ≤ H := conjugateSpanBy_le hKH (hTH.trans H.le_normalizer)
  have ho : K₀.subgroupOf H = conjugateSpanBy (K.subgroupOf H) (T.subgroupOf H) :=
    subgroupOf_conjugateSpan H K T hKH hTH
  have hn : (K₀.subgroupOf H).Normal := by
    rw [ho]
    exact conjugateSpanBy_sylow_normal (K.subgroupOf H) (T.subtype hTH)
      (Chapter1.Section02.proposition_1_2_1_three_orbit_source
        (S.original_star_sqtk D hZ z hz hH) hK)
  let : (actorImage H K₀).Normal := hn.map q (QuotientGroup.mk'_surjective _)
  have hJL : J ≤ normalizer (E.L₁ : Set G) := sup_le E.L₁.le_normalizer
    ((le_inf hTH hTV).trans
      (S.original_module_normalizer_normalizes_residual D hZ z hTV hH))
  have hstarJL : actorImage H J ≤ normalizer (actorImage H E.L₁ : Set (H ⧸ pCore 2 H)) := by
    rintro _ ⟨x,hx,rfl⟩
    apply (E.L₁.subgroupOf H).le_normalizer_map q
    apply mem_map_of_mem
    rw [←subgroupOf_normalizer_eq hLH]
    exact hJL hx
  have hstar : actorImage H K₀ ⊔ actorImage H J = ⊤ := by
    unfold actorImage
    rw [←Subgroup.map_sup,←subgroupOf_sup hK₀H hJH]
    have hg : K₀ ⊔ J = H := by simpa only [K₀,J,sup_assoc] using hgen
    rw [hg,subgroupOf_self,map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  let C := actorImage H E.L₁ ⊓ centralizer (actorImage H K₀ : Set (H ⧸ pCore 2 H))
  change C.Normal
  apply normalizer_eq_top_iff.mp
  apply top_unique
  rw [←hstar]
  apply sup_le
  · exact (le_centralizer_iff.mp (show C ≤ centralizer (actorImage H K₀ : Set _) from
      inf_le_right)).trans (Subgroup.centralizer_le_normalizer _)
  · exact (le_inf hstarJL
      ((le_normalizer_of_normal : actorImage H J ≤ normalizer (actorImage H K₀ : Set _)).trans
        (normalizer_le_normalizer_centralizer _))).trans inf_normalizer_le_normalizer_inf

end CFSG.Quasithin.Chapter12.Section06
