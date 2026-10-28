module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.LinearSocleCases
public import Theory.Representation.PSL3Two.CubicSixSpace
public import Theory.GroupTheory.NoncentralChiefRefinement.CubicComparison.NormalizedModule
public import Theory.GroupTheory.PResidual.SylowIndexThree
public import Theory.GroupTheory.CoprimeQuotientSubgroups

/-!
# Chief factors for the escaping weight-two parabolic

Each cubic in either parabolic acts with length at least two on the
recognized six-dimensional linear module. Lift an actual cubic through
the marked component quotient, and use the mutually normalized module
intersection to bound every complete chief series of the literal O²(P).
The normalizer and two-core quotient maps are retained throughout.

The source application constructs the original pair in either component
row. Weight two excludes the product alternative; thus the new bound
supplies premise 13.4.7(a) for P₂ in the P₂/P₄ comparison. Its other
applicability clauses and the comparison are assembled separately.
Earlier Chapter12/13.3, the plane amalgam, M=LT and LargeDistanceInput
remain explicit with their original producers.
Source: Aschbacher–Smith 13.4.12, printed pp.910–911.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Section03.Noncentrality.SupercriticalSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}

private theorem model_parabolic_chief_count
    (P C U : Subgroup G) [IsElementaryAbelian 2 U]
    (hTP : (T : Subgroup G) ≤ P) (hUT : U ≤ (T : Subgroup G))
    (hPU : P ≤ normalizer (U : Set G)) (hCU : C ≤ normalizer (U : Set G))
    (eP : (P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3))
    (f : C →* BinaryLinearThree.Group) (hk : IsPGroup 2 f.ker)
    (hthree : 3 ∣ Nat.card ((P.subgroupOf C).map f))
    {M : Type} [AddCommGroup M] [Module (ZMod 2) M]
    (σ : Representation (ZMod 2) BinaryLinearThree.Group M)
    (E : Representation.Equiv (σ.comp f) (elementaryRepresentation (p := 2)
      (U.normalizerMonoidHom.comp (inclusion hCU))))
    (hcodim : ∀ J : Subgroup BinaryLinearThree.Group, Nat.card J = 3 → 4 ≤ fixedCodim σ J)
    (s : NoncentralChiefRefinement.ChiefSeries ((pResidual 2 P).map P.subtype))
    (h0 : s.head = ⊥) (h1 : s.last = ⊤) : 2 ≤ s.noncentralTwoCount := by
  let R := (pResidual 2 P).map P.subtype
  have hd : 3 ∣ Nat.card (P.subgroupOf C) := hthree.trans
    (card_dvd_of_surjective (f.subgroupMap _) (f.subgroupMap_surjective _))
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' (G := P.subgroupOf C) 3 hd
  let A := zpowers a.val.val
  have hao : orderOf a.val.val = 3 := by
    rw [C.orderOf_coe,(P.subgroupOf C).orderOf_coe,ha]
  have hA : Nat.card A = 3 := by rw [Nat.card_zpowers,hao]
  have hAC : A ≤ C := zpowers_le.mpr a.val.property
  have hAP : A ≤ P := zpowers_le.mpr a.property
  have hAR : A ≤ R := by
    apply zpowers_le.mpr
    have hx : (⟨a.val.val,a.property⟩ : P) ∈ pResidual 2 P := by
      apply mem_pResidual_of_orderOf_coprime
      rw [←P.orderOf_coe,hao]
      decide
    exact mem_map_of_mem P.subtype hx
  let g : A →* BinaryLinearThree.Group := f.comp (inclusion hAC)
  have hg : Function.Injective g := by
    obtain ⟨n,hn⟩ := hk.exists_card_eq
    have hp : IsPGroup 3 (A.subgroupOf C) :=
      (IsPGroup.of_card (p := 3) (n := 1) (by simpa using hA)).comap_subtype
    have hh := injective_comp_subtype_of_coprime_ker f
      (show Nat.Coprime 3 (Nat.card f.ker) by rw [hn]; exact (by decide : Nat.Coprime 3 2).pow_right n)
      (A.subgroupOf C) hp
    intro x y hxy
    have he : (⟨⟨x.val,hAC x.property⟩,x.property⟩ : A.subgroupOf C) =
        ⟨⟨y.val,hAC y.property⟩,y.property⟩ := hh hxy
    exact Subtype.ext (congrArg (fun v : A.subgroupOf C => v.val.val) he)
  let eu : U ≃* Multiplicative M := {
    toFun v := Multiplicative.ofAdd (E.symm (Additive.ofMul v))
    invFun v := (E v.toAdd).toMul
    left_inv v := congrArg Additive.toMul (E.apply_symm_apply (Additive.ofMul v))
    right_inv v := congrArg Multiplicative.ofAdd (E.symm_apply_apply v.toAdd)
    map_mul' v w := congrArg Multiplicative.ofAdd (E.symm.toLinearEquiv.map_add _ _) }
  have hAU := hAC.trans hCU
  have he (a : A) (v : U) :
      (eu (U.normalizerMonoidHom ⟨a.val,hAU a.property⟩ v)).toAdd =
        σ (g a) (eu v).toAdd := by
    exact LinearMap.congr_fun (E.symm.isIntertwining' (inclusion hAC a)) (Additive.ofMul v)
  have hlen := BinaryLinearThree.CubicSixSpace.length_ge_two σ hcodim A U hA hAU g hg eu he
  let er := (pResidual 2 P).equivMapOfInjective P.subtype P.subtype_injective
  have hR : Nat.card (R ⧸ pCore 2 R) = 3 := by
    rw [Nat.card_congr (QuotientGroup.congr _ _ er.symm (pCore_map_iso 2 er.symm)).toEquiv]
    exact residual_core_quotient_card_of_sylow_index_three (T.subtype hTP)
      (SymmetricThreeTwoCore.sylow_index_three eP _)
  exact NoncentralChiefRefinement.CubicComparison.count_ge_of_normalized_module R U A hR
    (IsElementaryAbelian.isPGroup 2 U) hA hAR
    ((hUT.trans hTP).trans (le_normalizer_embedded_pResidual 2 P))
    ((map_subtype_le _).trans hPU) hlen s h0 h1

variable {L V A B : Subgroup G}

/-- Each actual parabolic residual in a recognized linear amalgam has at
least two noncentral binary chief factors, in every complete chief series. -/
theorem original_linear_pair_residual_chief_count
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
    (∀ s : NoncentralChiefRefinement.ChiefSeries ((pResidual 2 A).map A.subtype),
      s.head = ⊥ → s.last = ⊤ → 2 ≤ s.noncentralTwoCount) ∧
    (∀ s : NoncentralChiefRefinement.ChiefSeries ((pResidual 2 B).map B.subtype),
      s.head = ⊥ → s.last = ⊤ → 2 ≤ s.noncentralTwoCount) := by
  let X := A ⊔ B
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let U := conjugateSpanBy Z X
  obtain ⟨C,hC,_,_,_,_,⟨eC⟩⟩ := hlin.1
  let K := C.subgroupOf X
  have hmap : K.map X.subtype = C := map_subgroupOf_eq_of_le hC.1
  have eK : ((K.map X.subtype) ⧸ pCore 2 (K.map X.subtype)) ≃* Matrix.PSL3Two.PSL :=
    hmap.symm ▸ eC
  obtain ⟨heU,e,hA,hB,_,hm,_⟩ := Amalgam.original_pair_linear_whole_module
    h₀ h structural D m hTA hTB eA eB hne hout hindexL hindexA hindexB hres
      h1332 K hC.2 eK
  let := heU
  let C' := K.map X.subtype
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 C'))
  have hk : IsPGroup 2 f.ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
    exact pCore_isPGroup
  have hUX : U ≤ X := conjugateSpanBy_le (fun z hz =>
    (hTA.trans le_sup_left) ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1) X.le_normalizer
  have haction := Amalgam.original_pair_action_kernel h₀ D m
    hTA hTB eA eB hne hindexA hindexB
  have hUT : U ≤ (T : Subgroup G) := by
    apply (show U ≤ X.pCoreIn 2 from ?_).trans (haction.2.2.2.symm.le.trans inf_le_left)
    intro u hu
    exact mem_map_of_mem X.subtype (haction.1.le_pCore
      (show (⟨u,hUX hu⟩ : X) ∈ U.subgroupOf X from hu))
  have hCU : C' ≤ normalizer (U : Set G) :=
    (map_subtype_le K).trans (le_normalizer_conjugateSpanBy Z X)
  have step (P : Subgroup G) (hTP : (T : Subgroup G) ≤ P) (hPX : P ≤ X)
      (eP : (P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3))
      (hthree : 3 ∣ Nat.card ((P.subgroupOf C').map f))
      (s : NoncentralChiefRefinement.ChiefSeries ((pResidual 2 P).map P.subtype))
      (h0 : s.head = ⊥) (h1 : s.last = ⊤) : 2 ≤ s.noncentralTwoCount := by
    have hPU := hPX.trans (le_normalizer_conjugateSpanBy Z X)
    rcases hm with hm | hm | hm
    · exact model_parabolic_chief_count P C' U hTP hUT hPU hCU eP f hk hthree
        _ hm.some BinaryLinearThree.CubicSixSpace.sum_codim s h0 h1
    · exact model_parabolic_chief_count P C' U hTP hUT hPU hCU eP f hk hthree
        _ hm.some BinaryLinearThree.CubicSixSpace.point_codim s h0 h1
    · exact model_parabolic_chief_count P C' U hTP hUT hPU hCU eP f hk hthree
        _ hm.some BinaryLinearThree.CubicSixSpace.line_codim s h0 h1
  exact ⟨step A hTA le_sup_left eA (by rw [hA,Matrix.PSL3Two.card_pointParabolicSL]; decide),
    step B hTB le_sup_right eB (by rw [hB,Matrix.PSL3Two.card_lineParabolicSL]; decide)⟩

open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open AlternatingSixReconstruction.Natural.Exhaustion
/-- The original weight-two centralizer supplies the chief-factor premise
of the later P₂/P₄ amalgam, for either recognized component row. -/
theorem small_component_weight_two_chief_amalgam
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
      Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6))) (hweight : m.weight z = 2) :
    ∃ W : Submodule (ZMod 2) (BinaryPermutation.natural (Fin 6)),
      Module.finrank (ZMod 2) W = 2 ∧
      (T : Subgroup G) ≤ normalizer (m.naturalPreimage W : Set G) ∧
      ∃ P : Subgroup G,
        P ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
        P ⋖ centralizer ({z.val} : Set G) ∧
        Nonempty ((P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3)) ∧
        let B := (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G)
        Solvable.LinearAmalgamConclusion T (P ⊔ B) ∧
        (∀ s : NoncentralChiefRefinement.ChiefSeries ((pResidual 2 P).map P.subtype),
          s.head = ⊥ → s.last = ⊤ → 2 ≤ s.noncentralTwoCount) := by
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
  have hlin : Solvable.LinearAmalgamConclusion T (P ⊔ B) := by
    rcases hc.2 with hp | hl
    · have hw := original_product_weight_four h structural D m W hW hT P hP
        z hzL hPH.le hp
      omega
    · exact hl
  exact ⟨W,hW,hT,P,hP,hPH,⟨eP⟩,hlin,
    (original_linear_pair_residual_chief_count h₀ h structural D m hP.1.1.2 hTB eP eB
      hne (fun hx => hP.1.2 (le_sup_left.trans hx)) hindex hiP hiB
      (hcentral' hlocal).2.2 h1332 hlin).1⟩

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
