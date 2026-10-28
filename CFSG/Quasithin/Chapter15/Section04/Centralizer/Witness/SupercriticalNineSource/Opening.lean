module

public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Witness.ActionKernel
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Family.SourceConstruction.ModuleStructure
public import Theory.GroupTheory.CoprimeCentralizerDirectProduct
public import Theory.GroupTheory.Commutator.CentralizingComplement
public import Theory.GroupAction.IrreducibleTwoCoreKernel

/-!
# Nontriviality of the original two-core image in 15.4.10

If O₂(X) lies in O₂(M), it fixes the actual M-normal closure V(M) of
Ω₁(Z(T)). A Sylow three-subgroup supplements O₂(X), so coprime action
makes its displacement, which is [V(M),X], disjoint from its fixed points.
This displacement is T-invariant and elementary. A nonidentity T-fixed
point therefore lies in Ω₁(Z(T)), which X centralizes, a contradiction.

The conclusion concerns the literal image of the original O₂(X) in
M/O₂(M); no later centralizer identity or nontrivial-action premise is used.
Source: Aschbacher--Smith 15.4.10, first paragraph, printed p.1159.
-/

public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section04.CentralizerWitness.SupercriticalNineSource
open FamilySource FamilySource.ModuleStructure
variable {G : Type*} [Group G] [Finite G]

private theorem fixed_in_omega (T : Sylow 2 G) (D : Subgroup G)
    [IsElementaryAbelian 2 D] (hDT : D ≤ (T : Subgroup G))
    (hn : (T : Subgroup G) ≤ normalizer (D : Set G)) (hne : D ≠ ⊥) :
    ∃ d : G, d ∈ D ∧ d ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ∧ d ≠ 1 := by
  let : Normalizes (T : Subgroup G) D := ⟨hn⟩
  let : Nontrivial D := (Subgroup.nontrivial_iff_ne_bot D).mpr hne
  obtain ⟨d, hd⟩ := ne_bot_iff_exists_ne_one.mp
    (irreducible_fixed_nontrivial (W := D) (⊤ : Subgroup T) (T.isPGroup'.to_subgroup ⊤))
  refine ⟨d.val.val, d.val.property, ?_, ?_⟩
  · apply (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mpr
    refine ⟨hDT d.val.property, elemPow_eq_one_of_isElementaryAbelian _ d.val.property, ?_⟩
    intro t ht
    have he := congrArg Subtype.val (d.property ⟨⟨t, ht⟩, mem_top _⟩)
    change t * d.val.val * t⁻¹ = d.val.val at he
    exact mul_inv_eq_iff_eq_mul.mp he
  · intro he
    exact hd (Subtype.ext (Subtype.ext he))

/-- The counterexample in the first paragraph forces the original two-core
of X to survive in M/O₂(M). -/
theorem twoCore_not_le (T : Sylow 2 G) (M X : Subgroup G)
    (hTM : (T : Subgroup G) ≤ M) (hXM : X ≤ M) (hM : HasCharacteristicTwo M)
    (hX : X ∈ NormalCentralizerXi (T : Subgroup G)
      (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)))
    (hX3 : Nat.card (X ⧸ pCore 2 X) = 3)
    (hcounter : ¬ X ≤ centralizer (localV (T : Subgroup G) M : Set G)) :
    ¬ X.pCoreIn 2 ≤ M.pCoreIn 2 := by
  intro hcore
  let V := localV (T : Subgroup G) M
  let Z := Stellmacher.omegaOneCenterAmbient (T : Subgroup G)
  let : IsElementaryAbelian 2 V := localV_elementary T M hTM hM
  have hVT : V ≤ (T : Subgroup G) := localV_le_sylow T M hTM hM
  have hMV : M ≤ normalizer (V : Set G) := localV_normalized _ _
  have hTC : (T : Subgroup G) ≤ centralizer (Z : Set G) := by
    intro t ht z hz
    exact ((Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2 t ht |>.symm
  have hQV : X.pCoreIn 2 ≤ centralizer (V : Set G) := hcore.trans
    (ActionKernel.twoCore_centralizes_closure T M M Z hTM le_rfl hTC)
  let S : Sylow 3 X := Classical.choice inferInstance
  let A : Subgroup G := (S : Subgroup X).map X.subtype
  have hAX : A ≤ X := map_subtype_le _
  have hAV : A ≤ normalizer (V : Set G) := hAX.trans (hXM.trans hMV)
  have hq3 : IsPGroup 3 (X ⧸ pCore 2 X) := IsPGroup.of_card (n := 1) (by simpa using hX3)
  have hgen : X.pCoreIn 2 ⊔ A = X := by
    let q := QuotientGroup.mk' (pCore 2 X)
    have htop : (S : Subgroup X).map q = ⊤ :=
      top_unique ((hq3.to_subgroup ⊤).le_sylow_of_normal
        (S.mapSurjective (QuotientGroup.mk'_surjective _)))
    have hs : pCore 2 X ⊔ (S : Subgroup X) = ⊤ := by
      have hh := congrArg (fun D : Subgroup (X ⧸ pCore 2 X) => D.comap q) htop
      simpa only [comap_map_eq, q, QuotientGroup.ker_mk', comap_top, sup_comm] using hh
    have hh := congrArg (fun D : Subgroup X => D.map X.subtype) hs
    simpa only [pCoreIn, A, Subgroup.map_sup, ← MonoidHom.range_eq_map, range_subtype] using hh
  have hcomm : ⁅V, A⁆ = ⁅V, X⁆ := commutator_eq_of_centralizing_sup hgen hQV hAV
  have hcop : Nat.Coprime (Nat.card A) (Nat.card V) :=
    IsPGroup.coprime_card_of_ne 3 2 (by decide) A V (S.isPGroup'.map X.subtype)
      (IsElementaryAbelian.isPGroup 2 V)
  have hdis := commutator_disjoint_centralizer_of_coprime V A hAV hcop
  rw [hcomm] at hdis
  let D := ⁅V, X⁆
  have hDV : D ≤ V := le_normalizer_iff_commutator_le_left.mp (hXM.trans hMV)
  have hn : (T : Subgroup G) ≤ normalizer (D : Set G) := by
    intro t ht
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [map_commutator, mem_normalizer_iff_map_conj_eq.mp (hMV (hTM ht)),
      mem_normalizer_iff_map_conj_eq.mp (hX.1.1 ht)]
  have hne : D ≠ ⊥ := by
    intro he
    exact hcounter (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp he))
  let : IsElementaryAbelian 2 D := {
    toIsMulCommutative := ⟨⟨fun x y => Subtype.ext (by
      exact congrArg (fun v : V => (v : G)) (mul_comm (⟨x.val, hDV x.property⟩ : V)
        (⟨y.val, hDV y.property⟩ : V)))⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun d =>
      Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (p := 2) _ (hDV d.property))) }
  obtain ⟨d, hdD, hdZ, hd1⟩ := fixed_in_omega T D (hDV.trans hVT) hn hne
  exact hd1 (Subgroup.disjoint_def.mp hdis hdD ⟨hDV hdD,
    (le_centralizer_iff.mp (hAX.trans hX.2.1)) hdZ⟩)

/-- The literal image of O₂(X), rather than an abstract action kernel, is nontrivial. -/
theorem twoCore_image_ne_bot (T : Sylow 2 G) (M X : Subgroup G)
    (hTM : (T : Subgroup G) ≤ M) (hXM : X ≤ M) (hM : HasCharacteristicTwo M)
    (hX : X ∈ NormalCentralizerXi (T : Subgroup G)
      (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)))
    (hX3 : Nat.card (X ⧸ pCore 2 X) = 3)
    (hcounter : ¬ X ≤ centralizer (localV (T : Subgroup G) M : Set G)) :
    image M (X.pCoreIn 2) ≠ ⊥ := by
  intro he
  have hk := (map_eq_bot_iff ((X.pCoreIn 2).subgroupOf M)).mp he
  rw [quotientMap, QuotientGroup.ker_mk'] at hk
  apply twoCore_not_le T M X hTM hXM hM hX hX3 hcounter
  intro x hx
  exact ⟨⟨x, hXM (pCoreIn_le 2 X hx)⟩, hk hx, rfl⟩

end CFSG.Quasithin.Chapter15.Section04.CentralizerWitness.SupercriticalNineSource
