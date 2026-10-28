module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuShadowRows.M22CodeFullCenter
public import Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.CodeHeldCubic

/-!
# Excluding the original cubic cover in the remaining Held component

The original odd-normalizer control puts the centralizer of the actual
covering cubic inside N_G(L). Within the containing component it therefore
normalizes the original point residual. Restrict the original Sylow to
that component and use its literal quotient map to Held. The native
controlled-cubic obstruction excludes the center of order three, retaining
every two-core and the actual original residual.

Consequently the remaining inside-core case has centerless L/O₂(L) and
full point-residual quotient A₆. This does not exclude that remaining Held
case, remove hcore, or complete the original M22-code exclusion and M24
cocode selection.

Source: Aschbacher--Smith 8.2.2(1), printed p.715, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Chapter7.NormalizedSource Sporadic.Mathieu MathieuCode
open ChapterB.ComponentRecognition.KnownFFTypes.Sporadic
open Chapter8.Section02.Centralizer Chapter1
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)

/-- The full original covering center cannot have order three in the Held component. -/
theorem sourceOrbit_m22_code_not_held_cubic_cover
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent
      m22OuterCodeRepresentation)
    (z : D.sourceOrbit) (hz : (z : G) ∈ centralizer (T : Set G)) (hne : z ≠ 1)
    {K : Subgroup G} (hKC : K ≤ centralizer ({(z : G)} : Set G))
    (hRK : localResidual L z ≤ K)
    (hnK : centralizer ({(z : G)} : Set G) ≤ normalizer (K : Set G))
    (eK : (K ⧸ pCore 2 K) ≃* Held.He)
    (hc : Nat.card (center (L ⧸ pCore 2 L)) = 3) : False := by
  let C := centralizer ({(z : G)} : Set G)
  let R := localResidual L z
  let A := R.subgroupOf K
  have hTC : (T : Subgroup G) ≤ C := fun t ht =>
    mem_centralizer_singleton_iff.mpr (hz t ht)
  obtain ⟨S,hS⟩ := (T.subtype hTC).exists_map_subtype_eq_inf_of_normalizes hKC hnK
  have hST : (S : Subgroup K).map K.subtype ≤ (T : Subgroup G) := by
    rw [hS,Sylow.coe_subtype,map_subgroupOf_eq_of_le hTC]
    exact inf_le_left
  have hTN : (T : Subgroup G) ≤ normalizer (R : Set G) :=
    (le_inf D.sylow_normalizes_component hTC).trans (MathieuSextet.residual_normalized L z)
  have hSA : (S : Subgroup K) ≤ normalizer (A : Set K) := by
    intro s hs
    apply mem_normalizer_iff.mpr
    intro r
    change ((r : G) ∈ R ↔ (s : G)*(r : G)*(s : G)⁻¹ ∈ R)
    exact mem_normalizer_iff.mp (hTN (hST (mem_map_of_mem K.subtype hs))) r
  let a : A ≃* R := subgroupOfEquivOfLe hRK
  let aq := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  obtain ⟨ez⟩ := D.sourceOrbit_m22_code_residual_center_equiv h.toHypothesis1221 d z hz hne
  have hRz : Nat.card (center (R ⧸ pCore 2 R)) = 3 := (Nat.card_congr ez.toEquiv).trans hc
  have hAz : Nat.card (center (A ⧸ pCore 2 A)) = 3 :=
    (Nat.card_congr (centerCongr aq).toEquiv).trans hRz
  obtain ⟨_,⟨eR⟩⟩ := D.sourceOrbit_m22_code_centralizer_projective h.toHypothesis1221 d z hz hne
  have h5R : 5 ∣ Nat.card (R ⧸ pCore 2 R) := by
    have hh := card_quotient_dvd_card (center (R ⧸ pCore 2 R))
    rw [Nat.card_congr eR.toEquiv,nat_card_alternatingGroup,Nat.card_fin] at hh
    exact (by decide : 5 ∣ Nat.factorial 6 / 2).trans hh
  have h5A : 5 ∣ Nat.card (A ⧸ pCore 2 A) := by
    rwa [Nat.card_congr aq.toEquiv]
  obtain ⟨x,hx,hxR,_,hNx⟩ := D.sourceOrbit_m22_code_residual_cubic_normalizer
    h hmany hV hnon d z hz hne hRz
  let xK : K := ⟨x,hRK hxR⟩
  have hxK : orderOf xK = 3 := (orderOf_coe xK).symm.trans hx
  have hCA : centralizer ({xK} : Set K) ≤ normalizer (A : Set K) := by
    intro g hg
    have hgx : (g : G) ∈ centralizer ({x} : Set G) :=
      mem_centralizer_singleton_iff.mpr
        (congrArg (fun y : K => (y : G)) (mem_centralizer_singleton_iff.mp hg))
    have hgN : (g : G) ∈ normalizer (L : Set G) := by
      apply hNx
      apply centralizer_le_normalizer (zpowers x : Set G)
      simpa only [zpowers_eq_closure,centralizer_closure] using hgx
    have hgR := MathieuSextet.residual_normalized L z ⟨hgN,hKC g.property⟩
    apply mem_normalizer_iff.mpr
    intro r
    exact mem_normalizer_iff.mp hgR (r : G)
  let q := eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hq : Function.Surjective q := eK.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : IsPGroup 2 q.ker := by
    have he : q.ker = pCore 2 K := by
      ext g
      change eK (QuotientGroup.mk' (pCore 2 K) g) = 1 ↔ g ∈ pCore 2 K
      rw [eK.map_eq_one_iff]
      exact QuotientGroup.eq_one_iff g
    rw [he]
    exact pCore_isPGroup
  exact NormalizedShadowRows.controlled_cubic_cover_not_held q hq hk S A hSA h5A hAz xK hxK hCA

/-- The same inside-core configuration now retains only the full A₆ residual section. -/
theorem sourceOrbit_m22_code_inside_core_held_simple_section
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent
      m22OuterCodeRepresentation)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hcore : D.sourceOrbit ≤ H.pCoreIn 2) :
    let X := (pResidual 2 H).map H.subtype
    ∃ z : D.sourceOrbit, z ≠ 1 ∧ orderOf (z : G) = 2 ∧
      H ≤ centralizer ({(z : G)} : Set G) ∧
      ∃ P K : Subgroup G,
        Chapter1.XiEmbedding.LocalInput 3 (T : Subgroup G) X P (centralizer ({(z : G)} : Set G)) ∧
        K ∈ cComponentsIn (centralizer ({(z : G)} : Set G)) ∧
        localResidual L z ≤ K ∧
        centralizer ({(z : G)} : Set G) ≤ normalizer (K : Set G) ∧
        IsQuasisimple (K ⧸ pCore 2 K) ∧ center (K ⧸ pCore 2 K) = ⊥ ∧
        X ≤ K ∧ Nonempty (P ≃* Chapter1.XiEmbedding.Plane 3) ∧
        Nonempty ((K ⧸ pCore 2 K) ≃* Held.He) ∧
        center (L ⧸ pCore 2 L) = ⊥ ∧
        Nonempty ((localResidual L z ⧸ pCore 2 (localResidual L z)) ≃*
          alternatingGroup (Fin 6)) := by
  obtain ⟨z,hne,ho,hHC,P,K,hin,hK,hRK,hnK,hq,hzK,hXK,hP,eK,hcover⟩ :=
    D.sourceOrbit_m22_code_inside_core_held_cover_alternatives h hmany hV hnon d hH hcore
  have hz : (z : G) ∈ centralizer (T : Set G) := by
    intro t ht
    exact mem_centralizer_singleton_iff.mp (hHC (hH.1.1.2 ht))
  rcases hcover with hc | ⟨hc,_⟩
  · exact ⟨z,hne,ho,hHC,P,K,hin,hK,hRK,hnK,hq,hzK,hXK,hP,⟨eK⟩,hc⟩
  · exact (D.sourceOrbit_m22_code_not_held_cubic_cover h hmany hV hnon d
      z hz hne hK.1 hRK hnK eK hc).elim

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
