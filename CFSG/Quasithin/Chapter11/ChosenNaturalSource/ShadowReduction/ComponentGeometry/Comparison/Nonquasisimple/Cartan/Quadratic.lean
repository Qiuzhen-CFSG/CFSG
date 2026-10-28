module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Nonquasisimple.Cartan.Overcomponent
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingFiveRankOne
public import Theory.SpecificGroups.SL2.CardFourEquiv

/-!
# The quadratic-field overcomponent contradicts the original flag

The original L₁ lies in N_Kz(R₁)^∞. Its two-core is killed by the actual
projection N_G(R₁) → N_G(R₁)/O₂(N_G(R₁)), and its PSL₂(4) quotient
becomes an actual A₅ subgroup. The original full Sylow preserves this
seed, retaining the local-component condition after the same projection.

If a containing component has quotient PSL₂(p²), the checked quadratic
local-embedding theorem forces p = 5. The source exceptional congruence
p ≡ ±1 mod 5 excludes this. Thus the printed T-action contradiction uses
the actual original seed and its full Sylow, without an abstract action
marking or an assumed embedding shortlist.

Cartan.lean applies this exclusion to the component constructed from the
Frattini residual. Final assembly remains with
qt-d-1222-comparison-nonquasisimple.
Source: Aschbacher--Smith, 11.4.2, printed p.777; A.3.12(8), pp.47--48.
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Cartan
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {E : Closure.Geometry D}

private def coreImageEquiv {A : Type*} [Group A] [Finite A] (B : Subgroup A)
    (hc : B.pCoreIn 2 ≤ pCore 2 A) :
    (B ⧸ pCore 2 B) ≃* B.map (QuotientGroup.mk' (pCore 2 A)) := by
  let q := QuotientGroup.mk' (pCore 2 A)
  let b := q.subgroupMap B
  have hk : b.ker = pCore 2 B := by
    rw [ker_subgroupMap, QuotientGroup.ker_mk']
    apply le_antisymm (show (pCore 2 A).comap B.subtype ≤ pCore 2 B from
      le_sSup ⟨inferInstance,pCore_isPGroup.comap_subtype⟩)
    intro x hx
    exact hc (mem_map_of_mem _ hx)
  exact QuotientGroup.liftEquiv _ (q.subgroupMap_surjective B) hk.symm

/-- The original field-four flag seed has its actual A₅ image in N_G(R₁)/O₂(N_G(R₁)). -/
theorem seed_image_model (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (hseed : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hfour : S.field.degree = 2) :
    let N := normalizer ((ofFlag S f X z H).R₁ : Set G)
    let q := QuotientGroup.mk' (pCore 2 N)
    Nonempty (((ofFlag S f X z H).L₁.subgroupOf N).map q ≃* alternatingGroup (Fin 5)) := by
  intro N q
  let E := ofFlag S f X z H
  have hAN : E.L₁ ≤ N := le_sup_left.trans seedJoin_normalizes_radical
  let A := E.L₁.subgroupOf N
  let a : A ≃* E.L₁ := subgroupOfEquivOfLe hAN
  have hc : E.L₁.pCoreIn 2 ≤ N.pCoreIn 2 := by
    rw [radical_normalizer_core]
    exact pCoreIn_mono_of_normalizes le_sup_left
      (sup_le E.L₁.le_normalizer (f.sylow_normalizes_Li 0))
  have hcA : A.pCoreIn 2 ≤ pCore 2 N := by
    rintro x ⟨b,hb,rfl⟩
    have hb' : a b ∈ pCore 2 E.L₁ :=
      (pCore_map_iso 2 a) ▸ mem_map_of_mem a.toMonoidHom hb
    obtain ⟨n,hn,he⟩ := hc (mem_map_of_mem E.L₁.subtype hb')
    exact (show n = A.subtype b from Subtype.ext he) ▸ hn
  let e := (coreImageEquiv A hcA).symm.trans
    (QuotientGroup.congr _ _ a (pCore_map_iso 2 a))
  obtain ⟨F, _, _, hF, ⟨b⟩⟩ := hseed
  have hF4 : Nat.card F = 4 := by norm_num [hF,hfour]
  obtain ⟨d⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF4
  exact ⟨e.trans (b.trans d)⟩

private theorem quadratic_not_card_sixty {A : Type*} [Group A] [Finite A]
    {p : ℕ} (hp : Source.ExceptionalPrime p)
    (hm : ClassicalGroup.IsPSL A 2 (p ^ 2)) (hc : Nat.card A = 60) : False := by
  have hp3 : 3 < p := by have := hp.1.two_le; have := hp.2.1; omega
  have ho : Odd (p ^ 2) := (hp.1.odd_of_ne_two (by omega)).pow
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  have horder := Matrix.ProjectiveSpecialLinearGroup.psl2_card_twice (hF.symm ▸ ho)
  rw [hF, ← Nat.card_congr e.toEquiv,hc] at horder
  have hsq : 16 ≤ p ^ 2 := by nlinarith
  have hpow : 256 ≤ (p ^ 2) ^ 2 := by
    simpa only [pow_two] using Nat.mul_self_le_mul_self hsq
  have hfour : 255 ≤ (p ^ 2) ^ 2 - 1 := by omega
  nlinarith

/-- The quadratic-field overcomponent contradicts the ORIGINAL full-Sylow
invariance of the flag seed. The local A₅ embedding theorem forces p = 5,
which is incompatible with the source's exceptional-prime congruence. -/
theorem ofFlag_overcomponent_not_quadratic (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (hseed : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hfour : S.field.degree = 2) {p : ℕ} (hp : Source.ExceptionalPrime p)
    {K₀ : Subgroup G}
    (hK : Source.ComponentIn (normalizer ((ofFlag S f X z H).R₁ : Set G)) K₀)
    (hBK : normalizerResidual (ofFlag S f X z H) ≤ K₀)
    (hm : ClassicalGroup.IsPSL (K₀ ⧸ pCore 2 K₀) 2 (p ^ 2)) : False := by
  let E := ofFlag S f X z H
  let N := normalizer (E.R₁ : Set G)
  let q := QuotientGroup.mk' (pCore 2 N)
  have hTN : (T : Subgroup G) ≤ N := le_sup_right.trans seedJoin_normalizes_radical
  have hAN : E.L₁ ≤ N := le_sup_left.trans seedJoin_normalizes_radical
  let A := E.L₁.subgroupOf N
  let Abar := A.map q
  let Kbar := (K₀.subgroupOf N).map q
  let Tn := T.subtype hTN
  let Tbar := Tn.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 N))
  have ha : A ∈ Chapter1.L N (Tn : Subgroup N) :=
    (Chapter1.mem_LIn_iff_subgroupOf hTN hAN).mp
      ⟨hAN, LocalGeometry.Components.flag_mem_local_of_model D S f 0 hseed⟩
  have hab : Abar ∈ ChapterA.Section03.localCComponents Tbar :=
    Chapter1.Section02.mem_L_map_twoCore_mem_localCComponents ha
  let : Group.IsNilpotent (pCore 2 N) := pCore_isNilpotent
  have hKb : Kbar.IsCComponent := hK.2.map_quotient (pCore 2 N)
  have hAK : Abar ≤ Kbar := map_mono (comap_mono
    ((ofFlag_seed_le_residual S f X z H).trans hBK))
  obtain ⟨eA⟩ := seed_image_model S f X z H hseed hfour
  have hcard : Nat.card Abar = 60 := by
    rw [Nat.card_congr eA.toEquiv, nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  let eK := QuotientGroup.congr _ _ (subgroupOfEquivOfLe hK.1)
    (pCore_map_iso 2 (subgroupOfEquivOfLe hK.1))
  have hmodel : ClassicalGroup.IsPSL Kbar 2 (p ^ 2) :=
    hm.of_mulEquiv ((cComponentTwoCoreQuotientEquiv hK.2).symm.trans eK)
  have hne : Abar ≠ Kbar := by
    intro he
    exact quadratic_not_card_sixty hp hmodel (he ▸ hcard)
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup Abar := eA.isSimpleGroup
  have hcore : pCore 2 Abar = ⊥ := by
    apply (inferInstance : (pCore 2 Abar).Normal).eq_bot_or_eq_top.resolve_right
    intro he
    have ht : IsPGroup 2 (⊤ : Subgroup Abar) := he ▸ pCore_isPGroup
    have hA2 : IsPGroup 2 Abar := ht.of_equiv topEquiv
    obtain ⟨n,hn⟩ := (IsPGroup.iff_card).mp hA2
    rw [hcard] at hn
    have hd : 5 ∣ 2 ^ n := hn ▸ (by decide : 5 ∣ 60)
    have := (Nat.Prime.dvd_of_dvd_pow (by decide : Nat.Prime 5) hd)
    norm_num at this
  have hsection : Nonempty ((Abar ⧸ pCore 2 Abar) ≃* alternatingGroup (Fin 5)) :=
    ⟨((QuotientGroup.quotientMulEquivOfEq hcore).trans QuotientGroup.quotientBot).trans eA⟩
  have hp5 := (ChapterA.Section03.SourceEmbeddings.proper_quadraticPSL2_five_models
    Tbar hab hKb hAK hne hp.1 (hp.1.odd_of_ne_two (by
      intro he; have := hp.2.1; norm_num [he] at this)) hmodel hsection).1
  have := hp.2.1
  norm_num [hp5] at this

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Cartan
