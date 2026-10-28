module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalOddNormalizer.TerminalRudvalis.Marking
public import CFSG.Quasithin.Chapter12.Section02.Preliminaries.NormalizerSourceAt
public import CFSG.Quasithin.Chapter12.Section02.SourceApplications.At
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalOddNormalizer.TerminalComponent
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalOddNormalizer.TerminalRudvalis.Residual

/-!
# Original unitary source argument at the same ambient group and Sylow subgroup

This is the ambient-local specialization of `OriginalOddNormalizer.TerminalRudvalis.Marking`.
Its proof retains the original subgroups, actions, relative Sylow placement,
and quotient maps. Only the earlier 12.2.2 and 12.2.13 inputs are restricted
to the fixed G,T. The universal public API remains in the imported module.
The source argument and reference are recorded there; no additional local
classification or normalizer premise is introduced by this specialization.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At
open CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open Subgroup Theory.GroupTheory Chapter4 Chapter4.Section04 ChapterE
open CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers
open OriginalPlaneCentralizers Chapter12.Section02
open scoped Pointwise IsMulCommutative
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- The full native module normalizer is exactly the original intersection
with N_G(L); both directions use the actual residual and ambient inclusion. -/
theorem unitary_original_terminal_rudvalis_normalizer (s : _root_.CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers.Context T L V)
    (A : Subgroup G) (K : Subgroup (normalizer (A : Set G)))
    (d : K ≃* Rudvalis.Model)
    (hV : V ≤ K.map (normalizer (A : Set G)).subtype)
    (hRV : (oddActorResidual L A).pCoreIn 2 = V) :
    let J := K.map (normalizer (A : Set G)).subtype
    let j := (K.equivMapOfInjective (normalizer (A : Set G)).subtype
      (normalizer (A : Set G)).subtype_injective).symm.trans d
    normalizer ((V.subgroupOf J).map j.toMonoidHom : Set Rudvalis.Model) =
      ((normalizer (L : Set G)).subgroupOf J).map j.toMonoidHom := by
  let N := normalizer (A : Set G)
  let J := K.map N.subtype
  let j : J ≃* Rudvalis.Model :=
    (K.equivMapOfInjective N.subtype N.subtype_injective).symm.trans d
  have hNV := (unitary_original_module_normalizers s.hypothesis s.maximal
    s.quotient s.chosen s.structural).2
  have he : normalizer (V.subgroupOf J : Set J) = (normalizer (L : Set G)).subgroupOf J := by
    rw [←subgroupOf_normalizer_eq hV]
    apply le_antisymm
    · intro x hx
      exact hNV hx
    · intro x hx
      have hxA : (x : G) ∈ normalizer (A : Set G) := (map_subtype_le K) x.property
      have hxR := normalizes_oddActorResidual L A ⟨hx,hxA⟩
      have hxV := normalizer_le_normalizer_characteristic_image
        (oddActorResidual L A) (pCore 2 (oddActorResidual L A)) hxR
      change (x : G) ∈ normalizer (V : Set G)
      rwa [show (pCore 2 (oddActorResidual L A)).map (oddActorResidual L A).subtype = V
        from hRV] at hxV
  change normalizer ((V.subgroupOf J).map j.toMonoidHom : Set Rudvalis.Model) = _
  rw [←map_normalizer_eq_of_bijective _ j.bijective,he]

/-- The original component quotient becomes a faithful Rudvalis marking of
the whole module, fixed residual and original three-space centralizer. -/
theorem unitary_original_terminal_rudvalis_marking (s : _root_.CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers.Context T L V)
    (U : Subgroup G) (hUV : U ≤ V) (hU : Nat.card U = 8)
    (hC : centralizer (U : Set G) ≤ normalizer (L : Set G))
    (A : Subgroup G) (hAN : A ≤ normalizer (L : Set G))
    (hcomm : ⁅A,L⁆ ≤ L.pCoreIn 2) (hodd : Odd (Nat.card A))
    (hAV : A ≤ centralizer (V : Set G))
    (K : Subgroup (normalizer (A : Set G)))
    (hK : IsComponent (normalizer (A : Set G)) K) (hcore : pCore 2 K = ⊥)
    (e : K ⧸ center K ≃* Rudvalis.Model)
    (hV : V ≤ K.map (normalizer (A : Set G)).subtype)
    (hR : oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype) :
    center K = ⊥ ∧ ∃ d : K ≃* Rudvalis.Model,
      (∀ k, d k = e (QuotientGroup.mk' (center K) k)) ∧
      (oddActorResidual L A).pCoreIn 2 = V ∧ Nat.card (oddActorResidual L A) = 64 * 6048 ∧
      let J := K.map (normalizer (A : Set G)).subtype
      let j := (K.equivMapOfInjective (normalizer (A : Set G)).subtype
        (normalizer (A : Set G)).subtype_injective).symm.trans d
      let E := (V.subgroupOf J).map j.toMonoidHom
      let Rbar := ((oddActorResidual L A).subgroupOf J).map j.toMonoidHom
      let Ubar := (U.subgroupOf J).map j.toMonoidHom
      let C := ((normalizer (L : Set G)).subgroupOf J).map j.toMonoidHom
      Rbar.pCoreIn 2 = E ∧ Nat.card Rbar = 64 * 6048 ∧
      IsElementaryAbelian 2 E ∧ Nat.card E = 64 ∧ normalizer (E : Set Rudvalis.Model) = C ∧
      Ubar ≤ E ∧ Nat.card Ubar = 8 ∧ centralizer (Ubar : Set Rudvalis.Model) ≤ C ∧
      ∀ z : E, z ≠ 1 →
        IsConj (z : Rudvalis.Model) (Rudvalis.b ^ 2) ∧
        Nat.card (centralizer ({(z : Rudvalis.Model)} : Set Rudvalis.Model)) = 245760 := by
  let := hK.2
  obtain ⟨hz,d,hd⟩ := Rudvalis.Multiplier.center_eq_bot_and_exists_equiv e hcore
  let N := normalizer (A : Set G)
  let J := K.map N.subtype
  let j : J ≃* Rudvalis.Model := (K.equivMapOfInjective N.subtype N.subtype_injective).symm.trans d
  let R := oddActorResidual L A
  let i : R →* Rudvalis.Model := j.toMonoidHom.comp (inclusion hR)
  have hi : Function.Injective i := j.injective.comp (inclusion_injective hR)
  have h12 := (unitary_original_hypothesis1223 s.hypothesis s.maximal s.quotient).toHypothesis1221
  have hVR : V ≤ R := ((chosen_oddActorResidual_cover h12 s.chosen A hAN hcomm hodd hAV).2.2.1).trans
    (pCoreIn_le 2 R)
  have hsub : (V.subgroupOf R).map (inclusion hR) = V.subgroupOf J := by
    apply map_injective J.subtype_injective
    rw [map_map,map_subgroupOf_eq_of_le hV]
    change (V.subgroupOf R).map R.subtype = V
    exact map_subgroupOf_eq_of_le hVR
  have hE : (V.subgroupOf R).map i = (V.subgroupOf J).map j.toMonoidHom := by
    rw [show i = j.toMonoidHom.comp (inclusion hR) from rfl,←map_map,hsub]
  obtain ⟨hRV,hcardR,hel,hcardE,hPE,hB,hpoints⟩ :=
    unitary_original_terminal_rudvalis_residual s A hAN hcomm hodd hAV i hi
  have hBmap : i.range = (R.subgroupOf J).map j.toMonoidHom := by
    ext x
    constructor
    · rintro ⟨r,rfl⟩
      exact ⟨inclusion hR r,r.property,rfl⟩
    · rintro ⟨r,hr,rfl⟩
      exact ⟨⟨r,hr⟩,rfl⟩
  rw [hE] at hel hcardE hPE hpoints
  rw [hBmap] at hPE hB
  refine ⟨hz,d,hd,hRV,hcardR,hPE,hB,hel,hcardE,
    unitary_original_terminal_rudvalis_normalizer s A K d hV hRV,
    map_mono (subgroupOf_mono J hUV),?_,?_,hpoints⟩
  · rw [card_map_of_injective j.injective,
      Nat.card_congr (subgroupOfEquivOfLe (hUV.trans hV)).toEquiv,hU]
  · intro x hx
    refine ⟨j.symm x,?_,j.apply_symm_apply x⟩
    apply hC
    intro u hu
    let uJ : J := ⟨u,(hUV.trans hV) hu⟩
    have he := hx (j uJ) (mem_map_of_mem j.toMonoidHom hu)
    have hh : uJ * j.symm x = j.symm x * uJ := by
      apply j.injective
      simpa only [map_mul,j.apply_symm_apply] using he
    exact congrArg J.subtype hh

/-- Apply the native marking to the actual terminal actor. Every original
flag hypothesis, witness and equation is retained, including residual uniqueness
and the proved centralizer bound for the original order-eight subgroup. -/
theorem unitary_original_terminal_component_rudvalis_marked
    (D : ChapterF.Section09.Setup G) [IsElementaryAbelian 2 D.V]
    (s : _root_.CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers.Context D.T D.L D.V)
    (earlier : Theorem12213At KnownSimple.IsKnownSimple D.T)
    (hUV : D.Vplus ≤ D.V) (hZV : D.V₁ ≤ D.V)
    (hTZ : (D.T : Subgroup G) ≤ normalizer (D.V₁ : Set G))
    (hTU : (D.T : Subgroup G) ≤ normalizer (D.Vplus : Set G))
    (hZ : Nat.card D.V₁ = 2) (hU : Nat.card D.Vplus = 8)
    (B : Subgroup G) (hBV : B ≤ D.V)
    (hTB : (D.T : Subgroup G) ≤ normalizer (B : Set G)) (hB : Nat.card B = 4)
    (hHfull : D.H = normalizer (D.V₁ : Set G))
    (h1332 : Noncentrality.SupercriticalSource.Source1332OneTwo D.T)
    (fixed : OriginalFixedModule1332At D.T D.L)
    (five : OriginalAlternatingFiveModules1332At D.T D.L) :
    centralizer (D.Vplus : Set G) ≤ normalizer (D.L : Set G) ∧
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ 3 < p ∧ Nat.card A = p ∧
      A ≤ normalizer (D.L : Set G) ∧ A ≤ centralizer (D.V : Set G) ∧
      ⁅A,D.L⁆ ≤ D.L.pCoreIn 2 ∧
      ¬ normalizer (A : Set G) ≤ normalizer (D.L : Set G) ∧
      UniqueMaximalOvergroup (oddActorResidual D.L A) (normalizer (D.L : Set G)) ∧
      ∃ K : Subgroup (normalizer (A : Set G)),
        IsComponent (normalizer (A : Set G)) K ∧ K.Normal ∧
        ⁅K,D.V.subgroupOf (normalizer (A : Set G))⁆ = K ∧
        ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (D.L : Set G) ∧
        pCore 2 K = ⊥ ∧
        (Nonempty (K ⧸ center K ≃* Janko4.Model) ∨
          Nonempty (K ⧸ center K ≃* Rudvalis.Model)) ∧
        D.V ≤ K.map (normalizer (A : Set G)).subtype ∧
        oddActorResidual D.L A ≤ K.map (normalizer (A : Set G)).subtype ∧
        centralizer (K : Set (normalizer (A : Set G))) =
          pPrimeCore 2 (normalizer (A : Set G)) ∧
        ∀ e : K ⧸ center K ≃* Rudvalis.Model,
          center K = ⊥ ∧ ∃ d : K ≃* Rudvalis.Model,
            (∀ k, d k = e (QuotientGroup.mk' (center K) k)) ∧
            (oddActorResidual D.L A).pCoreIn 2 = D.V ∧
            Nat.card (oddActorResidual D.L A) = 64 * 6048 ∧
            let J := K.map (normalizer (A : Set G)).subtype
            let j := (K.equivMapOfInjective (normalizer (A : Set G)).subtype
              (normalizer (A : Set G)).subtype_injective).symm.trans d
            let E := (D.V.subgroupOf J).map j.toMonoidHom
            let Rbar := ((oddActorResidual D.L A).subgroupOf J).map j.toMonoidHom
            let Ubar := (D.Vplus.subgroupOf J).map j.toMonoidHom
            let C := ((normalizer (D.L : Set G)).subgroupOf J).map j.toMonoidHom
            Rbar.pCoreIn 2 = E ∧ Nat.card Rbar = 64 * 6048 ∧
            IsElementaryAbelian 2 E ∧ Nat.card E = 64 ∧
            normalizer (E : Set Rudvalis.Model) = C ∧
            Ubar ≤ E ∧ Nat.card Ubar = 8 ∧ centralizer (Ubar : Set Rudvalis.Model) ≤ C ∧
            ∀ z : E, z ≠ 1 →
              IsConj (z : Rudvalis.Model) (Rudvalis.b ^ 2) ∧
              Nat.card (centralizer ({(z : Rudvalis.Model)} : Set Rudvalis.Model)) = 245760 := by
  obtain ⟨hC,p,A,hp,hp3,hcard,hAN,hAV,hcomm,hout,hu,
    K,hK,hN,hm,houtK,hcore,hmodel,hV,hR,hcent⟩ :=
    unitary_original_terminal_component D s earlier hUV hZV hTZ hTU hZ hU
      B hBV hTB hB hHfull h1332 fixed five
  refine ⟨hC,p,A,hp,hp3,hcard,hAN,hAV,hcomm,hout,hu,
    K,hK,hN,hm,houtK,hcore,hmodel,hV,hR,hcent,?_⟩
  intro e
  have hodd : Odd (Nat.card A) := by
    rw [hcard]
    exact hp.odd_of_ne_two (by omega)
  exact unitary_original_terminal_rudvalis_marking s D.Vplus hUV hU hC A hAN
    hcomm hodd hAV K hK hcore e hV hR

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At
