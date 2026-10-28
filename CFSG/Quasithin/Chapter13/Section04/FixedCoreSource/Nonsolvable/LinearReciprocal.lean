module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.OriginalProductModule
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.LinearWholeModule
public import Theory.Representation.PSL3Two.FanoNonFF
public import Theory.Representation.BinaryConjugationCoordinates.ReciprocalNonFF

/-!
# Reciprocal conjugates of the original linear omega module

The linear alternative of the original H₂,L₂T pair has one of the three
actual six-dimensional modules: natural plus dual, point core or line core.
Each model is non-FF. The component fills the quotient by O₂(H₀), and its
module-action kernel is precisely its two-core. It therefore supplements
the full module centralizer with the same quotient kernel, transferring
the non-FF property to the actual H₀ action on V₀=⟨Ω₁Z(T)^H₀⟩.

If V₀ᵍ≤H₀ and V₀≤H₀ᵍ, reciprocal noncentral action would give strict
centralizer-index inequalities in both directions. Hence [V₀,V₀ᵍ]=1.
The final theorem constructs the original pair for both the recognized
linear-three and ordinary A₆ centralizers, and applies this result under
the literal reciprocal containments in R₂=O₂(L₂T). Thus the linear case
of 13.4.16 is complete, including all three module alternatives.

The product case retains its established weight-four and fixed-line
commutator conclusions. Its reciprocal exclusion, the weight and socle
clauses of 13.4.14, both-weight uniqueness, 13.4.15 and the final graph
argument remain separate. Earlier Chapter12/13.3, the original plane
amalgam and the independent LargeDistanceInput remain explicit inputs.
Source: Aschbacher–Smith 13.4.7 and 13.4.16, printed pp.900–901,912–913.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Section03.Noncentrality.SupercriticalSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V A B : Subgroup G}

/-- The actual linear omega module has a non-FF full action image. Its
reciprocal conjugates commute, using the original component supplement
and quotient kernel rather than an assumed full-actor module marking. -/
theorem original_linear_pair_module_nonFF
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hout : ¬ A ⊔ B ≤ normalizer (L : Set G))
    (hindexL : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexA : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (A : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexB : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hres : let X := A ⊔ B
      let Z := omegaOneCenterAmbient (T : Subgroup G)
      let K₁ := (pResidual 2 A).map A.subtype
      let K₂ := (pResidual 2 B).map B.subtype
      let C₁ := X ⊓ centralizer ((Z ⊓ centralizer (K₁ : Set G) : Subgroup G) : Set G)
      let C₂ := X ⊓ centralizer ((Z ⊓ centralizer (K₂ : Set G) : Subgroup G) : Set G)
      (primeToResidual 3 C₁).map C₁.subtype = K₁ ∨
        (primeToResidual 3 C₂).map C₂.subtype = K₂)
    (h1332 : Source1332OneTwo T)
    (hlin : Solvable.LinearAmalgamConclusion T (A ⊔ B)) :
    let X := A ⊔ B
    let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) X
    ∃ he : IsElementaryAbelian 2 U, let := he
      ¬ IsFFModule (imageRepresentation (elementaryRepresentation (p := 2)
        (U.normalizerMonoidHom.comp (inclusion (le_normalizer_conjugateSpanBy
          (omegaOneCenterAmbient (T : Subgroup G)) X))))) ∧
      Nat.card U = 64 ∧ ∀ g : G,
        U.conjBy g ≤ X → U ≤ X.conjBy g → ⁅U,U.conjBy g⁆ = ⊥ := by
  let X := A ⊔ B
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let U := conjugateSpanBy Z X
  obtain ⟨C,hC,_,_,_,_,⟨eC⟩⟩ := hlin.1
  let K := C.subgroupOf X
  have hmap : K.map X.subtype = C := map_subgroupOf_eq_of_le hC.1
  have eK : ((K.map X.subtype) ⧸ pCore 2 (K.map X.subtype)) ≃* Matrix.PSL3Two.PSL :=
    hmap.symm ▸ eC
  obtain ⟨heU,e,hA,hB,hS,hm,hcard⟩ := Amalgam.original_pair_linear_whole_module
    h₀ h structural D m hTA hTB eA eB hne hout hindexL hindexA hindexB hres
      h1332 K hC.2 eK
  let := heU
  let C' := K.map X.subtype
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 C'))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hCU : C' ≤ normalizer (U : Set G) :=
    (map_subtype_le K).trans (le_normalizer_conjugateSpanBy Z X)
  have hker : f.ker = (centralizer (U : Set G)).subgroupOf C' := by
    change (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 C'))).ker = _
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
    apply map_injective C'.subtype_injective
    rw [subgroupOf_map_subtype,inf_comm]
    exact (Amalgam.original_pair_component_action_kernel h₀ D m h1332 hTA hTB eA eB
      hne hindexA hindexB hres K hC.2).symm
  have hgen : C' ⊔ (X ⊓ centralizer (U : Set G)) = X := by
    apply le_antisymm (sup_le (map_subtype_le K) inf_le_left)
    have hg := (Amalgam.original_pair_linear_core_supplement h₀ D m h1332
      hTA hTB eA eB hne hindexA hindexB K hC.2 eK).2
    apply hg.symm.le.trans
    apply sup_le_sup_left
    exact le_inf (pCoreIn_le 2 X)
      ((Amalgam.original_pair_action_kernel h₀ D m hTA hTB eA eB hne
        hindexA hindexB).2.1.symm.le.trans inf_le_right)
  let ρ := elementaryRepresentation (p := 2)
    (U.normalizerMonoidHom.comp (inclusion (le_normalizer_conjugateSpanBy Z X)))
  have hn : ¬ IsFFModule (imageRepresentation ρ) := by
    have step {M : Type} [AddCommGroup M] [Module (ZMod 2) M]
        (σ : Representation (ZMod 2) BinaryLinearThree.Group M)
        (E : Representation.Equiv (σ.comp f) (elementaryRepresentation (p := 2)
          (U.normalizerMonoidHom.comp (inclusion hCU))))
        (hs : ¬ IsFFModule σ) : ¬ IsFFModule (imageRepresentation ρ) :=
      BinaryConjugationCoordinates.nonFF_of_supplement_model X U C'
        (le_normalizer_conjugateSpanBy Z X) (map_subtype_le K) hgen f hf hker σ E hs
    rcases hm with hm | hm | hm
    · obtain ⟨em⟩ := hm
      exact step _ em BinaryLinearThree.FanoNonFF.sum_not_ff
    · obtain ⟨em⟩ := hm
      exact step _ em BinaryLinearThree.FanoNonFF.point_not_ff
    · obtain ⟨em⟩ := hm
      exact step _ em BinaryLinearThree.FanoNonFF.line_not_ff
  refine ⟨heU,hn,hcard,fun g h₁ h₂ => ?_⟩
  exact BinaryConjugationCoordinates.reciprocal_conjugate_of_nonFF_image X U
    (le_normalizer_conjugateSpanBy Z X) hn g h₁ h₂

open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open AlternatingSixReconstruction.Natural.Exhaustion
/-- Construct the original pair in either recognized component row and
apply the reciprocal commutator exclusion to the literal R₂=O₂(L₂T) in
the linear alternative. The product alternative retains both the original
weight and fixed-line commutator placement. -/
theorem small_component_original_reciprocal_amalgam
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hM : normalizer (L : Set G) = L ⊔ (T : Subgroup G))
    (h1347 : Solvable.PlaneAmalgamSource1347 D m)
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (centralizer ({z.val} : Set G)))
    (hHN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hfK : K ∈ MainForward.faithfulLocalComponents T)
    (model : Nonempty ((K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) ∨
      Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6))) :
    ∃ W : Submodule (ZMod 2) (BinaryPermutation.natural (Fin 6)),
      Module.finrank (ZMod 2) W = 2 ∧
      (T : Subgroup G) ≤ normalizer (m.naturalPreimage W : Set G) ∧
      ∃ P : Subgroup G,
        P ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
        P ⋖ centralizer ({z.val} : Set G) ∧
        Nonempty ((P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3)) ∧
        let B := (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G)
        let X := P ⊔ B
        let K₂ := (pResidual 2 P).map P.subtype
        let L₂ := (pResidual 2 B).map B.subtype
        X ∈ Chapter1.HOver G (T : Set G) ∧
        ((⁅K₂,L₂⁆ ≤ K₂.pCoreIn 2 ∧ m.weight z = 4 ∧
          V ⊓ centralizer (L : Set G) ≤
            ⁅omegaOneCenterAmbient (T : Subgroup G),K₂⁆ ∧
          ⁅omegaOneCenterAmbient (T : Subgroup G),K₂⁆ ≤
            ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆) ∨
          (Solvable.LinearAmalgamConclusion T X ∧
            X = normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) ∧
            IsMaximalTwoLocal X ∧
            Nonempty ((X ⧸ pCore 2 X) ≃* Matrix.PSL3Two.SL) ∧
            (∀ Q ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
              Q ≤ X → Q = P) ∧
            Nat.card (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) X) = 64 ∧
            (∀ g : G,
              (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) X).conjBy g ≤
                B.pCoreIn 2 →
              conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) X ≤
                (B.pCoreIn 2).conjBy g →
              ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) X,
                (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) X).conjBy g⁆ = ⊥))) := by
  obtain ⟨W,hW,hT,P,hP,hPH,⟨eP⟩,⟨eB⟩,_,hlocal,_,hchief,hiP,hiB,hfixed,hcentral⟩ :=
    small_component_original_pair hl h₀ h structural modules D m h1332 fixed hindex hM
      z hzT hzL hK hHN hKM hfK model
  let B := (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G)
  have hTB : (T : Subgroup G) ≤ B := le_inf le_sup_right hT
  have hBM : B ≤ normalizer (L : Set G) := by rw [hM]; exact inf_le_left
  have hne : P ≠ B := fun he => hP.1.2 (he ▸ hBM)
  have hB : B ∈ Chapter1.HOver G (T : Set G) := by
    have hVB : V ≤ B.pCoreIn 2 := by
      let := D.elementary
      exact le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 V)
        (D.le_sylow.trans hTB) (hBM.trans (normalizer_component_le_module h structural D m))
    refine ⟨?_,hTB⟩
    intro he
    have hv : V = ⊥ := bot_unique (he ▸ hVB)
    have hc := m.card_module
    rw [hv,card_bot] at hc
    omega
  have hcentral' :
      let Z := omegaOneCenterAmbient (T : Subgroup G)
      let K₁ := (pResidual 2 P).map P.subtype
      let K₂ := (pResidual 2 B).map B.subtype
      let X := P ⊔ B
      let C₁ := X ⊓ centralizer ((Z ⊓ centralizer (K₁ : Set G) : Subgroup G) : Set G)
      let C₂ := X ⊓ centralizer ((Z ⊓ centralizer (K₂ : Set G) : Subgroup G) : Set G)
      X ∈ Chapter1.HOver G (T : Set G) →
        (K₁.subgroupOf C₁).Normal ∧ (K₂.subgroupOf C₂).Normal ∧
        ((primeToResidual 3 C₁).map C₁.subtype = K₁ ∨
          (primeToResidual 3 C₂).map C₂.subtype = K₂) := by
    dsimp only
    intro hx
    obtain ⟨_,_,_,_,h₁,h₂,hr⟩ := hcentral (P ⊔ B) hx.1 le_sup_left le_sup_right
    exact ⟨h₁,h₂,Or.inl hr⟩
  have hc := h1347 W hW hT P hP.1.1 hB ⟨eP⟩ ⟨eB⟩ hne
    (Solvable.original_second_flag_residual_eq_inner D m W hT)
    (Or.inr (fun s hs ht => le_trans (by decide : 2 ≤ 3) (hchief s hs ht))) hiP hiB
    hcentral'
  refine ⟨W,hW,hT,P,hP,hPH,⟨eP⟩,hlocal,?_⟩
  rcases hc.2 with hc | hc
  · have hH : centralizer ({z.val} : Set G) = K ⊔ (T : Subgroup G) := by
      rcases model with he | he <;> obtain ⟨eK⟩ := he
      · exact (linear_full_centralizer hl h₀ h structural modules D m h1332 fixed hindex
          hM z hzT hzL hK.1 hHN hKM hfK eK).1
      · exact (ordinary_six_full_centralizer h₀ h structural modules D m h1332 fixed hindex
          hM z hzT hzL hK hHN hKM hfK eK).1
    have hfixedB : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G) =
        V ⊓ centralizer (L : Set G) := by
      rw [←Amalgam.omega_fixed_twoResidual B hTB]
      exact hfixed
    exact Or.inl ⟨hc,original_product_weight_four h structural D m W hW hT P hP
      z hzL hPH.le hc,original_product_fixed_commutator h₀ h structural D m P B K
        hP hTB hBM eP eB hiP hiB hfixedB hcentral' hc
        ((Solvable.original_sylow_le_centralizer hzT).trans hHN) (hPH.le.trans_eq hH)⟩
  · obtain ⟨hX,hmax,hquot,hunique⟩ := original_linear_pair_maximal h structural D m
      z.val hzT P B hP hTB hBM eP eB hlocal
      (fun Y hY hPY hBY => ⟨(hcentral Y hY hPY hBY).1,(hcentral Y hY hPY hBY).2.1⟩) hc
    obtain ⟨_,_,hcard,hrecip⟩ := original_linear_pair_module_nonFF h₀ h structural D m
      hP.1.1.2 hTB eP eB hne (fun hx => hP.1.2 (le_sup_left.trans hx))
      hindex hiP hiB (hcentral' hlocal).2.2 h1332 hc
    refine Or.inr ⟨hc,hX,hmax,hquot,hunique,hcard,?_⟩
    intro g h₁ h₂
    have hR : B.pCoreIn 2 ≤ P ⊔ B := (pCoreIn_le 2 B).trans le_sup_right
    exact hrecip g (h₁.trans hR) (h₂.trans (map_mono hR))



end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
