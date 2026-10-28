module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.FixedLinesAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.NonsolvableAt.Nonsolvable.FixedLineKernel
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.NonsolvableAt.Nonsolvable.OffenderIntersection
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.NormalizerAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ProductMixed
public import Theory.Representation.BinaryConjugationCoordinates.IndexThreeDisplacement
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.OriginalProductModule
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.FixedLineKernel
public import Theory.GroupTheory.Commutator.NormalizedIndexTwo
public import Theory.GroupTheory.CommutatorPreimage

/-!
# Product mixed reciprocity and the first reciprocal reduction: structure at the original group

The commuting residuals make each fixed-line orbit normal in the original
join. Sylow splitting and the absence of common fixed points identify each
orbit with its residual commutator. The index-three displacement calculation
therefore gives two planes. The literal O₂(L₂T) centralizes one plane; it
normalizes the other and its fixed line, so it moves the whole omega module
into C_V(L).

Under mixed reciprocal containment, the commutator is both in V and in a
conjugate of this fixed line. Original normalizer fusion puts it in C_V(L),
and the proved augmentation fixed-line kernel makes it trivial. This proves
the product case of 13.4.15 without a new transvection or model premise.

Specialize the original proof to `Structural1222At` at the same G,T.
All action maps, full quotient kernels and source hypotheses are retained;
no universal Chapter12 record is inferred. Intrinsic model and group lemmas
are reused from the preserved source module. This family feeds guarded
nonsolvable-centralizer exclusion on the actual five-dimensional module.

Source: Aschbacher--Smith 13.4.10--17, printed pp.907--915;
see the original `Nonsolvable/ProductMixed` proof for the local step.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The actual product radical moves the omega module only along its fixed line. -/
theorem original_product_radical_movement_at
    (h₀ : Hypothesis1331 T L) (D : ChosenModule T L V) (m : CoreMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hindexL : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (P B : Subgroup G) (hTP : (T : Subgroup G) ≤ P) (hTB : (T : Subgroup G) ≤ B)
    (hout : ¬ P ⊔ B ≤ normalizer (L : Set G))
    (eP : (P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : P ≠ B)
    (hiP : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (P : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hiB : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hcentral : let X := P ⊔ B
      let Z := omegaOneCenterAmbient (T : Subgroup G)
      let K₁ := (pResidual 2 P).map P.subtype
      let K₂ := (pResidual 2 B).map B.subtype
      let C₁ := X ⊓ centralizer ((Z ⊓ centralizer (K₁ : Set G) : Subgroup G) : Set G)
      let C₂ := X ⊓ centralizer ((Z ⊓ centralizer (K₂ : Set G) : Subgroup G) : Set G)
      X ∈ Chapter1.HOver G (T : Set G) →
        (K₁.subgroupOf C₁).Normal ∧ (K₂.subgroupOf C₂).Normal ∧
        ((primeToResidual 3 C₁).map C₁.subtype = K₁ ∨
          (primeToResidual 3 C₂).map C₂.subtype = K₂))
    (hcomm : ⁅(pResidual 2 P).map P.subtype,(pResidual 2 B).map B.subtype⁆ ≤
      ((pResidual 2 P).map P.subtype).pCoreIn 2)
    :
    ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) (P ⊔ B),B.pCoreIn 2⁆ ≤
      omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G) := by
  let X := P ⊔ B
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let R := (pResidual 2 P).map P.subtype
  let S := (pResidual 2 B).map B.subtype
  let U := conjugateSpanBy Z X
  let F₁ := Z ⊓ centralizer (P : Set G)
  let F₂ := Z ⊓ centralizer (B : Set G)
  let U₁ := conjugateSpanBy F₂ P
  let U₂ := conjugateSpanBy F₁ B
  have hlocal := Amalgam.original_pair_local D m hTP hTB eP eB hne hiP hiB
  have hres := (hcentral hlocal).2.2
  have hdistinct := Amalgam.pair_fixed_subgroups_ne hTP hTB eP eB hne hres
  obtain ⟨_,hc₁,hc₂,hdis,hsplit,_⟩ := Amalgam.original_pair_fixed_lines_at
    h structural D m hout hindexL hiP hiB hdistinct
  have hZT : Z ≤ (T : Subgroup G) := fun z hz =>
    ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1
  have hZX : Z ≤ X := hZT.trans (hTP.trans le_sup_left)
  have hUX : U ≤ X := conjugateSpanBy_le hZX X.le_normalizer
  obtain ⟨hred,hker,_,_⟩ := Amalgam.original_pair_action_kernel h₀ D m hTP hTB
    eP eB hne hiP hiB
  let : IsElementaryAbelian 2 (U.subgroupOf X) := hred.elementary
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.of_injective
    (subgroupOfEquivOfLe hUX).symm.toMonoidHom
    (subgroupOfEquivOfLe hUX).symm.injective
  have hRN : X ≤ normalizer (R : Set G) := by
    refine sup_le (le_normalizer_embedded_pResidual 2 P) ?_
    have hs : S ⊔ (T : Subgroup G) = B := embedded_pResidual_sup_of_common_sylow B T
      (T.subtype hTB) (by rw [T.coe_subtype,map_subgroupOf_eq_of_le hTB])
    rw [←hs]
    exact sup_le (le_normalizer_iff_commutator_le_left.mpr (hcomm.trans (pCoreIn_le 2 R)))
      (hTP.trans (le_normalizer_embedded_pResidual 2 P))
  have hcore : R.pCoreIn 2 ≤ X.pCoreIn 2 := pCoreIn_mono_of_normalizes
    ((map_subtype_le _).trans le_sup_left) hRN
  have hc : ⁅R,S⁆ ≤ centralizer (U : Set G) :=
    hcomm.trans (hcore.trans (hker.symm.le.trans inf_le_right))
  obtain ⟨_,_,_,hboth,_⟩ := Amalgam.original_pair_commuting_action h₀ D m
    hTP hTB eP eB hne hiP hiB hcentral hc
  have hcentralSwap :
      let X := B ⊔ P
      let Z := omegaOneCenterAmbient (T : Subgroup G)
      let K₁ := (pResidual 2 B).map B.subtype
      let K₂ := (pResidual 2 P).map P.subtype
      let C₁ := X ⊓ centralizer ((Z ⊓ centralizer (K₁ : Set G) : Subgroup G) : Set G)
      let C₂ := X ⊓ centralizer ((Z ⊓ centralizer (K₂ : Set G) : Subgroup G) : Set G)
      X ∈ Chapter1.HOver G (T : Set G) →
        (K₁.subgroupOf C₁).Normal ∧ (K₂.subgroupOf C₂).Normal ∧
        ((primeToResidual 3 C₁).map C₁.subtype = K₁ ∨
          (primeToResidual 3 C₂).map C₂.subtype = K₂) := by
    dsimp only
    rw [sup_comm B P]
    intro hx
    obtain ⟨h₁,h₂,hr⟩ := hcentral hx
    exact ⟨h₂,h₁,hr.symm⟩
  obtain ⟨_,_,hn₁,hcard₁⟩ := product_line_orbit h₀ D m P B hTP hTB eP eB hne
    hiP hiB hcentral hcomm hc₂ (by
      simpa only [inf_assoc,inf_left_comm,inf_comm,inf_idem,inf_left_idem] using hdis)
  obtain ⟨_,_,hn₂,_⟩ := product_line_orbit h₀ D m B P hTB hTP eB eP hne.symm
    hiB hiP hcentralSwap (by rw [commutator_comm]; exact hboth.trans inf_le_right)
    hc₁ (by simpa only [inf_assoc,inf_left_comm,inf_comm,inf_idem,inf_left_idem] using hdis)
  have hn₂' : X ≤ normalizer (U₂ : Set G) := by simpa only [sup_comm B P] using hn₂
  have hU₁U : U₁ ≤ U := conjugateSpanBy_mono inf_le_left le_sup_left
  have hU₂U : U₂ ≤ U := conjugateSpanBy_mono inf_le_left le_sup_right
  change F₁ ⊔ F₂ = Z at hsplit
  have hwhole : U = U₁ ⊔ U₂ := by
    apply le_antisymm
    · apply conjugateSpanBy_le
      · rw [←hsplit]
        exact sup_le ((le_conjugateSpanBy F₁ B).trans le_sup_right)
          ((le_conjugateSpanBy F₂ P).trans le_sup_left)
      · intro x hx
        rw [mem_normalizer_iff_map_conj_eq,Subgroup.map_sup,
          mem_normalizer_iff_map_conj_eq.mp (hn₁ hx),
          mem_normalizer_iff_map_conj_eq.mp (hn₂' hx)]
    · exact sup_le hU₁U hU₂U
  let Q := B.pCoreIn 2
  have hQT : Q ≤ (T : Subgroup G) := by
    rintro q ⟨q,hq,rfl⟩
    exact pCore_isPGroup.le_sylow_of_normal (T.subtype hTB) hq
  have hQB : Q ≤ B := pCoreIn_le 2 B
  have hQX : Q ≤ X := hQB.trans le_sup_right
  have hF₂U₁ : F₂ ≤ U₁ := le_conjugateSpanBy F₂ P
  have hF₂Q : F₂ ≤ centralizer (Q : Set G) := fun z hz =>
    centralizer_le hQT (((mem_omegaOneCenterAmbient_iff _ _).mp hz.1).2.2)
  have hindex : F₂.relIndex U₁ = 2 := by
    have hh : Nat.card F₂ * F₂.relIndex U₁ = Nat.card U₁ := by
      simpa only [relIndex_bot_left] using
        relIndex_mul_relIndex (⊥ : Subgroup G) F₂ U₁ bot_le hF₂U₁
    rw [hc₂,hcard₁] at hh
    omega
  have hc₁Q : ⁅U₁,Q⁆ ≤ F₂ := commutator_le_of_normalized_index_two U₁ F₂ Q hF₂U₁
    hindex (hQX.trans hn₁)
    ((le_centralizer_iff.mp hF₂Q).trans (Subgroup.centralizer_le_normalizer _))
  have hQBnorm : B ≤ normalizer (Q : Set G) := B.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image B (pCore 2 B))
  have hc₂Q : U₂ ≤ centralizer (Q : Set G) := conjugateSpanBy_le
    (fun z hz => centralizer_le hQT (((mem_omegaOneCenterAmbient_iff _ _).mp hz.1).2.2))
    (hQBnorm.trans (normalizer_le_normalizer_centralizer Q))
  have hFU : F₂ ≤ U := hF₂U₁.trans hU₁U
  let H := normalizer (F₂ : Set G)
  have hUH : U ≤ H := ((le_centralizer_iff.mp (hFU.trans U.le_centralizer))).trans
    (Subgroup.centralizer_le_normalizer _)
  have hQH : Q ≤ H := (le_centralizer_iff.mp hF₂Q).trans (Subgroup.centralizer_le_normalizer _)
  have hgen : U ≤ commutatorPreimage H Q F₂ := by
    rw [hwhole]
    exact sup_le (le_commutatorPreimage (hU₁U.trans hUH) hc₁Q)
      (le_commutatorPreimage (hU₂U.trans hUH)
        ((commutator_eq_bot_iff_le_centralizer.mpr hc₂Q).le.trans bot_le))
  exact (commutator_mono hgen le_rfl).trans
    (commutator_commutatorPreimage_le H Q F₂ le_rfl)

/-- Product case of 13.4.15 with the original conjugator and radical containments. -/
theorem original_product_pair_mixed_commute_at
    (h₀ : Hypothesis1331 T L) (D : ChosenModule T L V) (m : CoreMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hindexL : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (P B : Subgroup G) (hTP : (T : Subgroup G) ≤ P) (hTB : (T : Subgroup G) ≤ B)
    (hout : ¬ P ⊔ B ≤ normalizer (L : Set G))
    (eP : (P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : P ≠ B)
    (hiP : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (P : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hiB : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hcentral : let X := P ⊔ B
      let Z := omegaOneCenterAmbient (T : Subgroup G)
      let K₁ := (pResidual 2 P).map P.subtype
      let K₂ := (pResidual 2 B).map B.subtype
      let C₁ := X ⊓ centralizer ((Z ⊓ centralizer (K₁ : Set G) : Subgroup G) : Set G)
      let C₂ := X ⊓ centralizer ((Z ⊓ centralizer (K₂ : Set G) : Subgroup G) : Set G)
      X ∈ Chapter1.HOver G (T : Set G) →
        (K₁.subgroupOf C₁).Normal ∧ (K₂.subgroupOf C₂).Normal ∧
        ((primeToResidual 3 C₁).map C₁.subtype = K₁ ∨
          (primeToResidual 3 C₂).map C₂.subtype = K₂))
    (hcomm : ⁅(pResidual 2 P).map P.subtype,(pResidual 2 B).map B.subtype⁆ ≤
      ((pResidual 2 P).map P.subtype).pCoreIn 2)
    (hBM : B ≤ normalizer (L : Set G))
    (hfixed : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G) =
      V ⊓ centralizer (L : Set G))
    (hfusion : ∀ v : V, v ≠ 1 → ∀ w ∈ V, IsConj v.val w →
      ∃ n ∈ normalizer (V : Set G), MulAut.conj n v.val = w) :
    let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) (P ⊔ B)
    ∀ g : G, U.conjBy g ≤ B.pCoreIn 2 → V ≤ (B.pCoreIn 2).conjBy g →
      ⁅V,U.conjBy g⁆ = ⊥ := by
  dsimp only
  intro g h₁ h₂
  let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) (P ⊔ B)
  let F := V ⊓ centralizer (L : Set G)
  have hUgN : U.conjBy g ≤ normalizer (V : Set G) :=
    h₁.trans ((pCoreIn_le 2 B).trans
      (hBM.trans (normalizer_component_le_module_at h structural D m)))
  have hmove : ⁅U,B.pCoreIn 2⁆ ≤ F := by
    change ⁅U,B.pCoreIn 2⁆ ≤ V ⊓ centralizer (L : Set G)
    rw [←hfixed]
    exact original_product_radical_movement_at h₀ D m h structural hindexL P B hTP hTB
      hout eP eB hne hiP hiB hcentral hcomm
  have hcF : ⁅V,U.conjBy g⁆ ≤ F.conjBy g := by
    have hm := map_mono (f := (MulAut.conj g).toMonoidHom) hmove
    rw [map_commutator] at hm
    rw [commutator_comm]
    exact (commutator_mono le_rfl h₂).trans hm
  have hpoints : ∀ w ∈ F.conjBy g, w ≠ 1 → IsConj m.constant.val w := by
    rintro w ⟨x,hx,rfl⟩ hw
    have hx1 : (⟨x,hx.1⟩ : V) ≠ 1 := by
      intro hx1
      apply hw
      have he : x = 1 := congrArg Subtype.val hx1
      simp [he]
    have hxconst : (⟨x,hx.1⟩ : V) = m.constant :=
      ((m.fixed_iff ⟨x,hx.1⟩).mp hx.2).resolve_left hx1
    have he : x = m.constant.val := congrArg Subtype.val hxconst
    rw [he]
    exact isConj_iff.mpr ⟨g,rfl⟩
  have hinter : F.conjBy g ⊓ V ≤ F := by
    simpa only [conjBy_one] using
      m.intersection_le_conjugate_fixed_at h structural hfusion (F.conjBy g) hpoints 1
  exact original_fixed_line_kernel_at h structural D m (U.conjBy g) hUgN
    ((le_inf hcF (le_normalizer_iff_commutator_le_left.mp hUgN)).trans hinter)

/-- First paragraph of 13.4.16: a counterexample returns to M and centralizes V. -/
theorem original_product_pair_reciprocal_reduction_at
    (h₀ : Hypothesis1331 T L) (D : ChosenModule T L V) (m : CoreMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hindexL : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (P B : Subgroup G) (hTP : (T : Subgroup G) ≤ P) (hTB : (T : Subgroup G) ≤ B)
    (hout : ¬ P ⊔ B ≤ normalizer (L : Set G))
    (eP : (P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : P ≠ B)
    (hiP : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (P : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hiB : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hcentral : let X := P ⊔ B
      let Z := omegaOneCenterAmbient (T : Subgroup G)
      let K₁ := (pResidual 2 P).map P.subtype
      let K₂ := (pResidual 2 B).map B.subtype
      let C₁ := X ⊓ centralizer ((Z ⊓ centralizer (K₁ : Set G) : Subgroup G) : Set G)
      let C₂ := X ⊓ centralizer ((Z ⊓ centralizer (K₂ : Set G) : Subgroup G) : Set G)
      X ∈ Chapter1.HOver G (T : Set G) →
        (K₁.subgroupOf C₁).Normal ∧ (K₂.subgroupOf C₂).Normal ∧
        ((primeToResidual 3 C₁).map C₁.subtype = K₁ ∨
          (primeToResidual 3 C₂).map C₂.subtype = K₂))
    (hcomm : ⁅(pResidual 2 P).map P.subtype,(pResidual 2 B).map B.subtype⁆ ≤
      ((pResidual 2 P).map P.subtype).pCoreIn 2)
    (hBM : B ≤ normalizer (L : Set G))
    (hfixed : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G) =
      V ⊓ centralizer (L : Set G))
    (hfusion : ∀ v : V, v ≠ 1 → ∀ w ∈ V, IsConj v.val w →
      ∃ n ∈ normalizer (V : Set G), MulAut.conj n v.val = w) :
    let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) (P ⊔ B)
    ∀ g : G, U.conjBy g ≤ B.pCoreIn 2 → U ≤ (B.pCoreIn 2).conjBy g →
      ⁅U,U.conjBy g⁆ ≠ ⊥ →
      g ∈ normalizer (L : Set G) ∧ ⁅V,U⁆ = ⊥ ∧
        ⁅U,U.conjBy g⁆ = V ⊓ centralizer (L : Set G) := by
  dsimp only
  intro g h₁ h₂ hnecomm
  let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) (P ⊔ B)
  let F := V ⊓ centralizer (L : Set G)
  let E := ⁅U,U.conjBy g⁆
  have hmove : ⁅U,B.pCoreIn 2⁆ ≤ F := by
    change ⁅U,B.pCoreIn 2⁆ ≤ V ⊓ centralizer (L : Set G)
    rw [←hfixed]
    exact original_product_radical_movement_at h₀ D m h structural hindexL P B hTP hTB
      hout eP eB hne hiP hiB hcentral hcomm
  have hEF : E ≤ F := (commutator_mono le_rfl h₁).trans hmove
  have hEFg : E ≤ F.conjBy g := by
    have hh := map_mono (f := (MulAut.conj g).toMonoidHom) hmove
    rw [map_commutator] at hh
    change ⁅U,U.conjBy g⁆ ≤ F.conjBy g
    rw [commutator_comm]
    exact (commutator_mono le_rfl h₂).trans hh
  have htwo : 2 ≤ Nat.card E := by
    have hp := Nat.card_pos (α := E)
    have hn : Nat.card E ≠ 1 := fun hc => hnecomm (E.eq_bot_of_card_eq hc)
    omega
  have hEq : E = F := eq_of_le_of_card_ge hEF (by
    change Nat.card (V ⊓ centralizer (L : Set G) : Subgroup G) ≤ Nat.card E
    rw [m.card_fixed]
    exact htwo)
  have hEqg : E = F.conjBy g := eq_of_le_of_card_ge hEFg (by
    change Nat.card (F.map (MulAut.conj g).toMonoidHom) ≤ Nat.card E
    rw [card_map_of_injective (MulAut.conj g).injective]
    change Nat.card (V ⊓ centralizer (L : Set G) : Subgroup G) ≤ Nat.card E
    rw [m.card_fixed]
    exact htwo)
  have hgF : g ∈ normalizer (F : Set G) :=
    mem_normalizer_iff_map_conj_eq.mpr (hEqg.symm.trans hEq)
  have hgM : g ∈ normalizer (L : Set G) := by
    have hgc := normalizer_le_centralizer_of_card_two F m.card_fixed hgF
    rw [←fixed_generator_centralizer_at h structural D m
      ⟨m.constant.property,m.constant_fixed⟩
      (fun he => m.constant_ne_one (Subtype.ext he))]
    exact mem_centralizer_singleton_iff.mpr
      (hgc m.constant.val ⟨m.constant.property,m.constant_fixed⟩).symm
  have hVg : V.conjBy g = V := mem_normalizer_iff_map_conj_eq.mp
    (normalizer_component_le_module_at h structural D m hgM)
  have hVQ : V ≤ B.pCoreIn 2 := by
    let := D.elementary
    exact le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 V)
      (D.le_sylow.trans hTB) (hBM.trans (normalizer_component_le_module_at h structural D m))
  have hVQg : V ≤ (B.pCoreIn 2).conjBy g := by
    rw [←hVg]
    exact map_mono hVQ
  have hcg := original_product_pair_mixed_commute_at h₀ D m h structural hindexL P B
    hTP hTB hout eP eB hne hiP hiB hcentral hcomm hBM hfixed hfusion g h₁ hVQg
  refine ⟨hgM,?_,hEq⟩
  apply map_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective
  rw [map_commutator,Subgroup.map_bot]
  change ⁅V.conjBy g,U.conjBy g⁆ = ⊥
  rw [hVg]
  exact hcg

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
