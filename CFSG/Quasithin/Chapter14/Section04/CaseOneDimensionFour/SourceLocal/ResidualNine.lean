module

public import CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.SourceLocal.TwoCoreAction
public import Theory.GroupTheory.QuaternionCentralProductOrthogonalAction.ResidualNine
public import Theory.GroupTheory.PCoreRestriction

/-!
# The order-nine residual in the original order-32 source branch

The quaternion action puts O₂(H) inside N_G(L). Its intersection with L is
U, so the image of L∩H in H/O₂(H) has order six. The original flag escape
forces that image to be proper. The faithful orthogonal action then gives
an elementary order-nine two-residual and quotient order 18 or 36.

A single generator modulo the residual excludes order 36, since the literal
quotient embeds in S₃ × S₃, whose exponent divides six. The configuration
consumer thus no longer assumes the quotient order. Its remaining core
identity and generating inverter belong to qt-d-14414-g2-source; independent
I.4.5 recognition belongs to qt-i45-g2-recognition and final source assembly
to qt-d-14414-source. EarlierSetupResults retains its earlier source inputs.

Source: Aschbacher–Smith, 14.4.4(1),(3) and 14.4.5, printed pp.1007–1008.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

theorem source_twoCore_le_normalizer (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (previous : EarlierSetupResults KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32) :
    F.H.pCoreIn 2 ≤ normalizer (L : Set G) := by
  let := chosen.elementary
  let H := higherRankHypothesis d earlier hq chosen
  obtain ⟨q⟩ := source_quaternion d earlier hq chosen previous.structural
    previous.alternatives F hne hZ hcard
  have hUL := (source_block_core d earlier hq chosen previous.structural
    previous.alternatives F hne hZ hcard).2
  have hCN : centralizer (F.U : Set G) ≤ normalizer (L : Set G) :=
    (centralizer_le (le_conjugateSpanBy V F.H)).trans
      (H.seed_centralizer_le previous.structural previous.uniqueness)
  rintro x ⟨y, hy, rfl⟩
  have hk : y ∈ F.uhatAction.ker := (source_uhat_kernel d earlier hq chosen previous F hZ).symm ▸ hy
  let α := F.U.normalizerMonoidHom ⟨(y : G), le_normalizer_conjugateSpanBy V F.H y.property⟩
  have hα : quotientAut (center F.U) α = 1 := hk
  obtain ⟨u, hu⟩ := (q.quotientAut_eq_one_iff_inner α).mp hα
  have hc : (u : G)⁻¹ * y ∈ centralizer (F.U : Set G) := by
    intro v hv
    have he := congrArg Subtype.val (DFunLike.congr_fun hu (⟨v,hv⟩ : F.U))
    change (u : G) * v * (u : G)⁻¹ = (y : G) * v * (y : G)⁻¹ at he
    calc
      v * ((u : G)⁻¹ * y) = (u : G)⁻¹ * ((u : G) * v * (u : G)⁻¹) * y := by group
      _ = (u : G)⁻¹ * ((y : G) * v * (y : G)⁻¹) * y := by rw [he]
      _ = ((u : G)⁻¹ * y) * v := by group
  have hm := (normalizer (L : Set G)).mul_mem (L.le_normalizer (hUL u.property)) (hCN hc)
  change (y : G) ∈ normalizer (L : Set G)
  simpa only [mul_inv_cancel_left] using hm

theorem source_twoCore_inf_block (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32) :
    L ⊓ F.H.pCoreIn 2 = F.U := by
  obtain ⟨hU, _, _, _⟩ := source_point_core d earlier hq chosen structural alternatives F hne hZ hcard
  apply le_antisymm
  · intro x hx
    rw [hU]
    exact inf_pCoreIn_le_of_le 2 (show L ⊓ F.H ≤ F.H from inf_le_right)
      ⟨⟨hx.1, F.H.pCoreIn_le 2 hx.2⟩, hx.2⟩
  · exact le_inf ((source_block_core d earlier hq chosen structural alternatives F hne hZ hcard).2)
      (source_closure_le_twoCore d earlier hq chosen structural alternatives F hne)

theorem source_point_quotient_card (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32) :
    Nat.card (((L ⊓ F.H).subgroupOf F.H).map (QuotientGroup.mk' (pCore 2 F.H))) = 6 := by
  let A := L ⊓ F.H
  let π := QuotientGroup.mk' (pCore 2 F.H)
  let f : A →* (F.H ⧸ pCore 2 F.H) := π.comp (inclusion inf_le_right)
  have hU := (source_point_core d earlier hq chosen structural alternatives F hne hZ hcard).1
  have hUA : F.U ≤ A := hU.le.trans (A.pCoreIn_le 2)
  have hk : f.ker = F.U.subgroupOf A := by
    ext x
    change π ⟨(x : G), x.property.2⟩ = 1 ↔ (x : G) ∈ F.U
    dsimp only [π]
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    have hc : (⟨(x : G), x.property.2⟩ : F.H) ∈ pCore 2 F.H ↔ (x : G) ∈ F.H.pCoreIn 2 := by
      exact ⟨fun hx => mem_map_of_mem F.H.subtype hx,
        fun ⟨y,hy,he⟩ => (Subtype.ext he : y = ⟨(x : G), x.property.2⟩) ▸ hy⟩
    rw [hc, ← source_twoCore_inf_block d earlier hq chosen structural alternatives F hne hZ hcard]
    exact ⟨fun hx => ⟨x.property.1,hx⟩, fun hx => hx.2⟩
  have hr : f.range = (A.subgroupOf F.H).map π := by
    rw [MonoidHom.range_comp]
    congr 1
    ext x
    constructor
    · rintro ⟨y, rfl⟩; exact y.property
    · intro hx; exact ⟨⟨x,hx⟩, rfl⟩
  have hh := f.ker.card_mul_index
  rw [index_ker, hr, hk, Nat.card_congr (subgroupOfEquivOfLe hUA).toEquiv, hcard,
    (source_point_core d earlier hq chosen structural alternatives F hne hZ hcard).2.2.1] at hh
  dsimp only [A, π] at hh
  omega

theorem source_quotient_gt_six (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (previous : EarlierSetupResults KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32) :
    6 < Nat.card (F.H ⧸ pCore 2 F.H) := by
  let := chosen.elementary
  let H := higherRankHypothesis d earlier hq chosen
  have hQM := source_twoCore_le_normalizer d earlier hq chosen previous F hne hZ hcard
  have hc := source_point_quotient_card d earlier hq chosen previous.structural
    previous.alternatives F hne hZ hcard
  by_contra hn
  have he : ((L ⊓ F.H).subgroupOf F.H).map (QuotientGroup.mk' (pCore 2 F.H)) = ⊤ :=
    eq_of_le_of_card_ge le_top (by rw [card_top, hc]; omega)
  apply H.flag_escape F previous.alternatives
  intro x hx
  let π := QuotientGroup.mk' (pCore 2 F.H)
  obtain ⟨a, ha, hae⟩ := (he.symm ▸ (mem_top (π ⟨x,hx⟩)))
  have hker : a⁻¹ * (⟨x,hx⟩ : F.H) ∈ pCore 2 F.H := by
    apply (QuotientGroup.eq_one_iff _).mp
    change π (a⁻¹ * ⟨x,hx⟩) = 1
    rw [map_mul,map_inv,hae,inv_mul_cancel]
  have hm := (normalizer (L : Set G)).mul_mem (L.le_normalizer ha.1)
    (hQM (mem_map_of_mem F.H.subtype hker))
  change (a : G) * ((a : G)⁻¹ * x) ∈ normalizer (L : Set G) at hm
  simpa only [mul_inv_cancel_left] using hm

theorem source_quotient_square_embedding (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (previous : EarlierSetupResults KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32) :
    ∃ f : (F.H ⧸ pCore 2 F.H) →* BinaryFourPlus.factorSign.ker,
      Function.Injective f := by
  let := chosen.elementary
  let H := higherRankHypothesis d earlier hq chosen
  obtain ⟨q⟩ := source_quaternion d earlier hq chosen previous.structural
    previous.alternatives F hne hZ hcard
  have hVU : V ≤ F.U := le_conjugateSpanBy V F.H
  let E := V.subgroupOf F.U
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.subgroupOf hVU
  have hc : Nat.card E = 8 := (Nat.card_congr (subgroupOfEquivOfLe hVU).toEquiv).trans
    (by simpa [F.last] using F.card 3 (by decide))
  have hk : ((quotientAut (center F.U)).comp F.uAction).ker = pCore 2 F.H :=
    source_uhat_kernel d earlier hq chosen previous F hZ
  obtain ⟨f, hf, _⟩ := q.square_quotient_embedding F.uAction (pCore 2 F.H) hk
    (T.subtype (F.invariant 1)) E hc (by
      intro t ht v hv
      change (t : G) * (v : G) * (t : G)⁻¹ ∈ V
      exact (mem_normalizer_iff.mp
        (H.sylow_normalizes_seed previous.structural ht) v).mp hv)
  exact ⟨f, hf⟩

theorem source_residual_nine (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (previous : EarlierSetupResults KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32) :
    IsElementaryAbelian 3 ((pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))) ∧
      Nat.card ((pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))) = 9 := by
  obtain ⟨f, hf⟩ := source_quotient_square_embedding d earlier hq chosen previous F hne hZ hcard
  rw [map_pResidual_of_surjective 2 _ (QuotientGroup.mk'_surjective _)]
  exact BinaryFourPlus.residual_nine_of_embedding
    (BinaryFourPlus.factorSign.ker.subtype.comp f) (Subtype.val_injective.comp hf)
    (pCore_quotient_pCore_eq_bot 2)
    (source_quotient_gt_six d earlier hq chosen previous F hne hZ hcard)

theorem source_quotient_card_cases (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (previous : EarlierSetupResults KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32) :
    Nat.card (HStar F.H) = 18 ∨ Nat.card (HStar F.H) = 36 := by
  obtain ⟨f, hf⟩ := source_quotient_square_embedding d earlier hq chosen previous F hne hZ hcard
  have hdiv : Nat.card (HStar F.H) ∣ 36 := by
    have hc : Nat.card BinaryFourPlus.factorSign.ker = 36 := by
      rw [Nat.card_congr BinaryFourPlus.factorSignEquiv.toEquiv, Nat.card_prod, Nat.card_perm]
      norm_num
    have hd := f.range.card_subgroup_dvd_card
    rw [Nat.card_congr (MonoidHom.ofInjective hf).toEquiv.symm, hc] at hd
    exact hd
  have h9 : 9 ∣ Nat.card (HStar F.H) := by
    rw [← (source_residual_nine d earlier hq chosen previous F hne hZ hcard).2]
    exact (Subgroup.card_subgroup_dvd_card _)
  have h6 : 6 ∣ Nat.card (HStar F.H) := by
    rw [← source_point_quotient_card d earlier hq chosen previous.structural
      previous.alternatives F hne hZ hcard]
    exact (Subgroup.card_subgroup_dvd_card _)
  have hc : Nat.card (HStar F.H) ∈ (36 : ℕ).divisors := Nat.mem_divisors.mpr ⟨hdiv, by decide⟩
  rw [show (36 : ℕ).divisors = {1, 2, 3, 4, 6, 9, 12, 18, 36} by decide] at hc
  simp only [Finset.mem_insert, Finset.mem_singleton] at hc
  rcases hc with hc | hc | hc | hc | hc | hc | hc | hc | hc <;> omega


theorem source_quotient_card_of_generator (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (previous : EarlierSetupResults KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32)
    (s : F.H) (hgen : pResidual 2 F.H ⊔ zpowers s = ⊤) :
    Nat.card (HStar F.H) = 18 := by
  let D := F.H ⧸ pCore 2 F.H
  let π := QuotientGroup.mk' (pCore 2 F.H)
  let R := pResidual 2 D
  let ψ := QuotientGroup.mk' R
  obtain ⟨f,hf⟩ := source_quotient_square_embedding d earlier hq chosen previous F hne hZ hcard
  have hp : (π s) ^ 6 = 1 := BinaryFourPlus.sixth_pow_eq_one_of_square_embedding f hf _
  have hd : orderOf (ψ (π s)) ∣ 6 := orderOf_dvd_of_pow_eq_one (by rw [← map_pow,hp,map_one])
  have hR : Nat.card R = 9 := by
    have hh := (source_residual_nine d earlier hq chosen previous F hne hZ hcard).2
    rwa [map_pResidual_of_surjective 2 _ (QuotientGroup.mk'_surjective _)] at hh
  have hg : R ⊔ zpowers (π s) = ⊤ := by
    have hh := congrArg (Subgroup.map π) hgen
    rwa [Subgroup.map_sup, map_pResidual_of_surjective 2 _ (QuotientGroup.mk'_surjective _),
      MonoidHom.map_zpowers, map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at hh
  have hcyclic : zpowers (ψ (π s)) = ⊤ := by
    have hh := congrArg (Subgroup.map ψ) hg
    rw [Subgroup.map_sup, MonoidHom.map_zpowers,
      map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at hh
    have hb : R.map ψ = ⊥ := by
      apply bot_unique
      rintro y ⟨x,hx,rfl⟩
      exact (QuotientGroup.eq_one_iff x).mpr hx
    rwa [hb, bot_sup_eq] at hh
  have hi : R.index = orderOf (ψ (π s)) := by
    rw [index_eq_card, ← card_top (G := D ⧸ R), ← hcyclic, Nat.card_zpowers]
  have hmul := R.card_mul_index
  rw [hR, hi] at hmul
  rcases source_quotient_card_cases d earlier hq chosen previous F hne hZ hcard with he | he
  · exact he
  · have he' : Nat.card D = 36 := he
    rw [he'] at hmul
    have ho : orderOf (ψ (π s)) = 4 := by omega
    rw [ho] at hd
    norm_num at hd

theorem configuration_of_source_inverter (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (previous : EarlierSetupResults KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32)
    (hcore : F.U = F.H.pCoreIn 2) (s : F.H)
    (hgen : pResidual 2 F.H ⊔ zpowers s = ⊤)
    (hinv : ∀ k : pResidual 2 F.H,
      QuotientGroup.mk' (pCore 2 F.H) (s * k * s⁻¹) =
        (QuotientGroup.mk' (pCore 2 F.H) k)⁻¹) :
    Nonempty (DimensionFour.G2ThreeConfiguration G) :=
  configuration_of_source_closure d earlier hq chosen previous.structural previous.alternatives
    F hne hZ hcard hcore
    (source_quotient_card_of_generator d earlier hq chosen previous F hne hZ hcard s hgen)
    s hgen hinv

end CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour
