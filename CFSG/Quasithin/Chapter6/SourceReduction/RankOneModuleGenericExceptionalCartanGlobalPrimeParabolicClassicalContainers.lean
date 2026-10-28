module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeParabolicCubicFields
public import Theory.SpecificGroups.G2Even.TwoRank
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.G2
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeParabolicCubicFields

/-!
# Classical common-component rigidity and the exceptional rank-two sieve

Restrict the original full Sylow to its common component. Every proper
local component of binary PSL₃, SL₃, Sp₄ or G₂ has an SL₂ quotient with
an elementary Sylow two-subgroup. The original diagram residual instead
has a nonabelian Sylow two-subgroup, so it equals the common component.
This argument retains the intrinsic two-core and the cubic scalar kernel.

For G₂, equality is impossible: the two-rank and Sylow-order formulas
would simultaneously identify (2f,3f) or (3f,4f) with (3g,6g).
The small binary linear and derived endpoints are excluded by the exact
orders of the original residual quotients. Thus the same source pair
retains only classical equality, triality, Ree and Held in the simple
common-container rows, and the previously proved cubic SL₃ field row.

The internal import reuses the nonabelian-Sylow obstruction from the
preceding cubic-field implementation without widening its public API.
The strict changed-Sylow orbit is preserved. Its remaining contradictions,
zero-core recognition, higher-field generation and final normalization
are not asserted here.

Source: Aschbacher–Smith A.3.12, 5.1.10 and 5.2.2, printed
pp.47–48,634,648–649, refs/quasithin.pdf. The matrix-group calculations
reuse the native and attributed ATLAS-port models in the imported modules.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
open Chapter1.Section02 LocalModels ChapterA.Section03.SourceEmbeddings

private theorem projective_three_local_quotient
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {g : ℕ} (hg : 1 < g) (hF : Nat.card F = 2^g)
    (S : Sylow 2 PSL(3,F)) (V : Subgroup PSL(3,F))
    (hl : V ∈ ChapterA.Section03.localCComponents S) (hne : V ≠ ⊤) :
    Nonempty ((V ⧸ pCore 2 V) ≃* SL(2,F)) := by
  obtain ⟨x,hx⟩ := FiveLocalFF.linear_three_local_placement hF hg S V hl hne
  let a := (MulAut.conj x).subgroupMap V
  let aq := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  rcases hx with hx | hx
  · let b := MulEquiv.subgroupCongr hx
    exact ⟨aq.trans ((QuotientGroup.congr _ _ b (pCore_map_iso 2 b)).trans
      (Matrix.PSL3.LinearThree.pointLocalCoreQuotientEquiv F))⟩
  · let b := MulEquiv.subgroupCongr hx
    exact ⟨aq.trans ((QuotientGroup.congr _ _ b (pCore_map_iso 2 b)).trans
      (Matrix.PSL3.LinearThree.lineLocalCoreQuotientEquiv F))⟩

private theorem symplectic_four_local_quotient
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {g : ℕ} (hg : 1 < g) (hF : Nat.card F = 2^g)
    (S : Sylow 2 (Theory.SpecificGroups.SymplecticFour.Sp F))
    (V : Subgroup (Theory.SpecificGroups.SymplecticFour.Sp F))
    (hl : V ∈ ChapterA.Section03.localCComponents S) (hne : V ≠ ⊤) :
    Nonempty ((V ⧸ pCore 2 V) ≃* SL(2,F)) := by
  obtain ⟨x,hx⟩ := FiveLocalFF.symplectic_local_placement hF hg S V hl hne
  let a := (MulAut.conj x).subgroupMap V
  let aq := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  rcases hx with hx | hx
  · let b := MulEquiv.subgroupCongr hx
    exact ⟨aq.trans ((QuotientGroup.congr _ _ b (pCore_map_iso 2 b)).trans
      (Theory.SpecificGroups.SymplecticFour.pointLocalCoreQuotientEquiv hF hg))⟩
  · let b := MulEquiv.subgroupCongr hx
    exact ⟨aq.trans ((QuotientGroup.congr _ _ b (pCore_map_iso 2 b)).trans
      (Theory.SpecificGroups.SymplecticFour.planeLocalCoreQuotientEquiv hF hg))⟩

private theorem eq_of_diagram_local_quotients
    {Y Q M F : Type*} [Group Y] [Finite Y] [Group Q] [Finite Q]
    [Group M] [Finite M] [Field F] [Finite F] [CharP F 2]
    (S : Sylow 2 Y) {V C : Subgroup Y}
    (hl : V ∈ ChapterA.Section03.localCComponents S)
    (hC : C.IsCComponent) (hVC : V ≤ C)
    (a : (V ⧸ pCore 2 V) ≃* Q) {f : ℕ} (hf : 1 < f)
    (hm : ClassicalGroup.IsPSL Q 3 (2^f) ∨ IsSL Q 3 (2^f) ∨
      ClassicalGroup.IsPSp Q 2 (2^f)) (e : (C ⧸ pCore 2 C) ≃* M)
    (hlocal : ∀ (P : Sylow 2 M) (B : Subgroup M),
      B ∈ ChapterA.Section03.localCComponents P → B ≠ ⊤ →
      Nonempty ((B ⧸ pCore 2 B) ≃* SL(2,F))) : V = C := by
  by_contra hne
  obtain ⟨P,_,hV⟩ := exists_local_sylow_restriction S hl hVC hC.subnormal
  let B := V.subgroupOf C
  have ht : (⊤ : Subgroup C).IsCComponent := by
    simpa only [subgroupOf_self] using hC.subgroupOf le_rfl
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 C))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 C := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  let : Group.IsNilpotent q.ker := hk ▸ pCore_isNilpotent
  let : Group.IsSolvable q.ker := inferInstance
  have hproper : B.map q ≠ ⊤ := by
    intro he
    have hb : B = ⊤ := local_cComponent_eq_of_map_eq hV ht le_top q
      (hk ▸ pCore_isPGroup.le_sylow_of_normal P)
      (by simpa only [map_top_of_surjective q hq] using he)
    exact hne (le_antisymm hVC (subgroupOf_eq_top.mp hb))
  obtain ⟨b⟩ := hlocal (P.mapSurjective hq) (B.map q)
    (Chapter1.Section02.localCComponents_map_of_solvable_ker hV q) hproper
  let av := subgroupOfEquivOfLe hVC
  let aq := QuotientGroup.congr _ _ av (pCore_map_iso 2 av)
  have hkb : IsPGroup 2 (q.subgroupMap B).ker := by
    rw [ker_subgroupMap,hk]
    exact pCore_isPGroup.comap_subtype
  let bq := (q.subgroupMap B).quotientPCoreEquivOfSurjective (q.subgroupMap_surjective B) hkb
  exact diagram_not_binary_sl2 hf hm ((a.symm.trans aq.symm).trans (bq.trans b))

variable {G : Type*} [Group G] [Finite G]

/-- A binary classical common component containing the original diagram
residual is that whole residual, with all two-core and scalar kernels retained. -/
theorem SelectedSourceModels.parabolic_common_classical_eq
    {T : Sylow 2 G} {H R X I : Subgroup G} {g : ℕ}
    (hs : SelectedSourceModels H R) (hn : ¬ (R.subgroupOf H).IsCComponent)
    (hTH : (T : Subgroup G) ≤ H) (hHX : H ≤ X)
    (hIX : I ≤ X) (hI : (I.subgroupOf X).IsCComponent) (hKI : residual H ≤ I)
    (hg : 1 < g)
    (hm : let Ibar := (I.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))
      ClassicalGroup.IsPSL Ibar 3 (2^g) ∨ IsSL Ibar 3 (2^g) ∨
        ClassicalGroup.IsPSp Ibar 2 (2^g)) : residual H = I := by
  let K := residual H
  have hKH : K ≤ H := map_subtype_le _
  have hKX : K ≤ X := hKH.trans hHX
  have hKlocal : K ∈ ChapterA.Section03.localCComponents (T : Subgroup G) := by
    change (K.subgroupOf (K ⊔ (T : Subgroup G))).IsCComponent
    rw [show K ⊔ (T : Subgroup G) = H from residual_sup_sylow T H hTH]
    exact hs.residual_component_of_not_right hn
  let a : K.subgroupOf X ≃* pResidual 2 H :=
    (subgroupOfEquivOfLe hKX).trans
      ((pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective).symm
  let aq := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  obtain ⟨f,hf,_,hmodel⟩ := hs.resolve_left hn
  let : Group.IsNilpotent (pCore 2 X) := pCore_isNilpotent
  suffices he : K.subgroupOf X = I.subgroupOf X by
    simpa only [map_subgroupOf_eq_of_le hKX,map_subgroupOf_eq_of_le hIX] using
      congrArg (map X.subtype) he
  rcases hm with ⟨F,_,_,hF,⟨e⟩⟩ | hm | ⟨F,_,_,hF,⟨e⟩⟩
  · let : Fintype F := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow (f := g)
      (by simpa only [Nat.card_eq_fintype_card] using hF)
    exact eq_of_diagram_local_quotients (T.subtype (hTH.trans hHX))
      (local_restrict hKlocal hKX) hI (subgroupOf_mono X hKI) aq hf hmodel
      ((cComponentTwoCoreQuotientEquiv hI).trans e)
      (projective_three_local_quotient hg hF)
  · have he := hs.parabolic_common_binary_sl3_eq hn hTH hHX hIX hI hKI hg hm
    exact congrArg (fun J : Subgroup G => J.subgroupOf X) he
  · let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
    exact eq_of_diagram_local_quotients (T.subtype (hTH.trans hHX))
      (local_restrict hKlocal hKX) hI (subgroupOf_mono X hKI) aq hf hmodel
      (((cComponentTwoCoreQuotientEquiv hI).trans e).trans
        Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.symm)
      (symplectic_four_local_quotient hg hF)


private theorem g2_local_quotient
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hq : 2 < Nat.card F) (S : Sylow 2 (Atlas.G2.Model F))
    (V : Subgroup (Atlas.G2.Model F))
    (hl : V ∈ ChapterA.Section03.localCComponents S) (hne : V ≠ ⊤) :
    Nonempty ((V ⧸ pCore 2 V) ≃* SL(2,F)) := by
  obtain ⟨x,hx⟩ := FiveLocalFF.G2.local_placement hq S V hl hne
  let a := (MulAut.conj x).subgroupMap V
  let aq := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  rcases hx with hx | hx
  · let b := MulEquiv.subgroupCongr hx
    exact ⟨aq.trans ((QuotientGroup.congr _ _ b (pCore_map_iso 2 b)).trans
      (Atlas.G2.LieParabolicSetup.local₁CoreQuotientEquivPSL.trans
        Atlas.G2.LieParabolicSetup.longSLEquivPSL.symm))⟩
  · let b := MulEquiv.subgroupCongr hx
    exact ⟨aq.trans ((QuotientGroup.congr _ _ b (pCore_map_iso 2 b)).trans
      (Atlas.G2.LieParabolicSetup.local₂CoreQuotientEquivPSL.trans
        Atlas.G2.LieParabolicSetup.longSLEquivPSL.symm))⟩

private theorem sylow_card_equiv {Y Z : Type*} [Group Y] [Finite Y] [Group Z] [Finite Z]
    (e : Y ≃* Z) (S : Sylow 2 Y) (P : Sylow 2 Z) : Nat.card S = Nat.card P := by
  exact (Nat.card_congr (e.subgroupMap (S : Subgroup Y)).toEquiv).trans
    ((S.mapSurjective e.surjective).card_eq_multiplicity.trans P.card_eq_multiplicity.symm)

private theorem linear_three_not_g2
    {F E : Type*} [Field F] [Finite F] [Field E] [Finite E] [CharP E 2]
    {f g : ℕ} (hf : 1 < f) (_hg : 1 < g)
    (hF : Nat.card F = 2^f) (hE : Nat.card E = 2^g)
    (e : PSL(3,F) ≃* Atlas.G2.Model E) : False := by
  have hr := primeRank_equiv 2 e
  rw [Matrix.PSL3Even.two_rank F (by omega) hF,
    Atlas.G2.EvenTwoRank.two_rank E hE] at hr
  have hc := sylow_card_equiv e
    (Matrix.PSL3.LinearThree.unipotentSylow F (by omega) hF)
    (Atlas.G2.LieParabolicSetup.sylow (F := E))
  change Nat.card (Matrix.PSL3.LinearThree.unipotent F) =
    Nat.card (Atlas.G2.unipotent (K := E)) at hc
  rw [Matrix.PSL3.LinearThree.card_unipotent,Atlas.G2.card_unipotent,
    hF,hE,←pow_mul,←pow_mul] at hc
  have he := (Nat.pow_right_injective (by decide : 1 < 2)) hc
  omega

private theorem diagram_not_g2
    {Q E : Type*} [Group Q] [Finite Q] [Field E] [Finite E] [CharP E 2]
    {f g : ℕ} (hf : 1 < f) (hg : 1 < g) (hE : Nat.card E = 2^g)
    (hm : ClassicalGroup.IsPSL Q 3 (2^f) ∨ IsSL Q 3 (2^f) ∨
      ClassicalGroup.IsPSp Q 2 (2^f)) (e : Q ≃* Atlas.G2.Model E) : False := by
  have hlarge : 2 < Nat.card E := by
    rw [hE]
    exact lt_of_lt_of_le (by decide : 2 < 2^2)
      (Nat.pow_le_pow_right (by decide) (by omega))
  rcases hm with ⟨F,_,_,hF,⟨a⟩⟩ | ⟨F,_,_,hF,⟨a⟩⟩ | ⟨F,_,_,hF,⟨a⟩⟩
  · exact linear_three_not_g2 hf hg hF hE (a.symm.trans e)
  · let : IsSimpleGroup (Atlas.G2.Model E) := Atlas.G2.isSimple hlarge
    let : IsSimpleGroup SL(3,F) := (a.symm.trans e).isSimpleGroup
    let : Group.IsPerfect SL(3,F) := Atlas.sl_perfect 3 (by decide)
    have hz : center SL(3,F) = ⊥ :=
      (inferInstance : (center SL(3,F)).Normal).eq_bot_or_eq_top.resolve_right
        (fun ht => Group.IsPerfect.not_isMulCommutative SL(3,F) (center_eq_top_iff.mp ht))
    let b : PSL(3,F) ≃* SL(3,F) :=
      (QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot
    exact linear_three_not_g2 hf hg hF hE (b.trans (a.symm.trans e))
  · let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
    let b := Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.trans (a.symm.trans e)
    have hr := primeRank_equiv 2 b
    rw [Theory.SpecificGroups.SymplecticFour.EvenTwoRank.rank hF (by omega),
      Atlas.G2.EvenTwoRank.two_rank E hE] at hr
    have hc := sylow_card_equiv b
      (Theory.SpecificGroups.SymplecticFour.unipotentSylow hF (by omega))
      (Atlas.G2.LieParabolicSetup.sylow (F := E))
    change Nat.card (Theory.SpecificGroups.SymplecticFour.unipotent (F := F)) =
      Nat.card (Atlas.G2.unipotent (K := E)) at hc
    rw [Theory.SpecificGroups.SymplecticFour.card_unipotent,Atlas.G2.card_unipotent,
      hF,hE,←pow_mul,←pow_mul] at hc
    have he := (Nat.pow_right_injective (by decide : 1 < 2)) hc
    omega

/-- No characteristic-two G₂ common component contains the original diagram
residual. Proper placement forces an SL₂ quotient; equality contradicts the
simultaneous two-rank and Sylow-order formulas. -/
theorem SelectedSourceModels.parabolic_common_not_g2
    {T : Sylow 2 G} {H R X I : Subgroup G} {g : ℕ}
    (hs : SelectedSourceModels H R) (hn : ¬ (R.subgroupOf H).IsCComponent)
    (hTH : (T : Subgroup G) ≤ H) (hHX : H ≤ X)
    (_hIX : I ≤ X) (hI : (I.subgroupOf X).IsCComponent) (hKI : residual H ≤ I)
    (hg : 1 < g) :
    ¬ ClassificationModels.IsG2At
      ((I.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))) (2^g) := by
  rintro ⟨F,_,_,hF,⟨e⟩⟩
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (f := g)
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  have hlarge : 2 < Nat.card F := by
    rw [hF]
    exact lt_of_lt_of_le (by decide : 2 < 2^2)
      (Nat.pow_le_pow_right (by decide) (by omega))
  let K := residual H
  have hKH : K ≤ H := map_subtype_le _
  have hKX : K ≤ X := hKH.trans hHX
  have hKlocal : K ∈ ChapterA.Section03.localCComponents (T : Subgroup G) := by
    change (K.subgroupOf (K ⊔ (T : Subgroup G))).IsCComponent
    rw [show K ⊔ (T : Subgroup G) = H from residual_sup_sylow T H hTH]
    exact hs.residual_component_of_not_right hn
  let a : K.subgroupOf X ≃* pResidual 2 H :=
    (subgroupOfEquivOfLe hKX).trans
      ((pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective).symm
  let aq := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  obtain ⟨f,hf,_,hmodel⟩ := hs.resolve_left hn
  let : Group.IsNilpotent (pCore 2 X) := pCore_isNilpotent
  let b := (cComponentTwoCoreQuotientEquiv hI).trans e
  have he : K.subgroupOf X = I.subgroupOf X :=
    eq_of_diagram_local_quotients (T.subtype (hTH.trans hHX))
      (local_restrict hKlocal hKX) hI (subgroupOf_mono X hKI) aq hf hmodel b
      (g2_local_quotient hlarge)
  let ec := MulEquiv.subgroupCongr he
  let eqc := QuotientGroup.congr _ _ ec (pCore_map_iso 2 ec)
  exact diagram_not_g2 hf hg hF hmodel (aq.symm.trans (eqc.trans b))


private theorem small_order_arithmetic {f C : ℕ} (hf : 1 < f)
    (hC : C = 168 ∨ C = 360 ∨ C = 6048 ∨ C = 17971200)
    (hpart : 2^(3*f) ∣ C)
    (hd : ((2^f)^3*((2^f)^3-1)*((2^f)^2-1)) / Nat.gcd 3 (2^f-1) ∣ C ∨
      (2^f)^3*((2^f)^3-1)*((2^f)^2-1) ∣ C ∨
      (2^f)^4*((2^f)^2-1)*((2^f)^4-1) ∣ C) : False := by
  have hnot : ¬ 2^12 ∣ C := by
    rcases hC with rfl | rfl | rfl | rfl <;> norm_num
  have hf3 : f ≤ 3 := by
    by_contra! hgt
    exact hnot ((pow_dvd_pow 2 (by omega : 12 ≤ 3*f)).trans hpart)
  rcases hC with rfl | rfl | rfl | rfl <;> interval_cases f <;> norm_num at hd

private theorem diagram_not_small_order
    {Q : Type*} [Group Q] [Finite Q] {f C : ℕ} (hf : 1 < f)
    (hC : C = 168 ∨ C = 360 ∨ C = 6048 ∨ C = 17971200)
    (hd : Nat.card Q ∣ C)
    (hm : ClassicalGroup.IsPSL Q 3 (2^f) ∨ IsSL Q 3 (2^f) ∨
      ClassicalGroup.IsPSp Q 2 (2^f)) : False := by
  rcases hm with ⟨F,_,_,hF,⟨e⟩⟩ | ⟨F,_,_,hF,⟨e⟩⟩ | ⟨F,_,_,hF,⟨e⟩⟩
  · have hp := (Matrix.PSL3.LinearThree.unipotent F).card_subgroup_dvd_card
    rw [Matrix.PSL3.LinearThree.card_unipotent F,hF,←pow_mul,Nat.mul_comm f 3,
      ←Nat.card_congr e.toEquiv] at hp
    have hpart := hp.trans hd
    rw [Nat.card_congr e.toEquiv,Matrix.PSL3.LinearThree.card_projective,hF] at hd
    exact small_order_arithmetic hf hC hpart (.inl hd)
  · rw [Nat.card_congr e.toEquiv,Matrix.PSL3.LinearThree.DefiningSylow.card_specialLinear,hF] at hd
    have hp : 2^(3*f) ∣ C := by
      rw [Nat.mul_comm 3 f,pow_mul]
      exact (dvd_mul_of_dvd_left (dvd_mul_right _ _) _).trans hd
    exact small_order_arithmetic hf hC hp (.inr (.inl hd))
  · let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
    let a := e.trans Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.symm
    rw [Nat.card_congr a.toEquiv,Theory.SpecificGroups.SymplecticFour.card_sp,hF] at hd
    have hp : 2^(3*f) ∣ C := by
      apply (pow_dvd_pow 2 (by omega : 3*f ≤ 4*f)).trans
      rw [Nat.mul_comm 4 f,pow_mul]
      exact (dvd_mul_of_dvd_left (dvd_mul_right _ _) _).trans hd
    exact small_order_arithmetic hf hC hp (.inr (.inr hd))

/-- The smallest binary linear and derived endpoints cannot contain the
original diagram quotient, including its possible cubic scalar kernel. -/
theorem SelectedSourceModels.parabolic_common_not_small_order
    {H R X I : Subgroup G} (hs : SelectedSourceModels H R)
    (hn : ¬ (R.subgroupOf H).IsCComponent) (hIX : I ≤ X) (hKI : residual H ≤ I) :
    let Ibar := (I.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))
    ¬ (Nat.card Ibar = 168 ∨ Nat.card Ibar = 360 ∨
      Nat.card Ibar = 6048 ∨ Nat.card Ibar = 17971200) := by
  dsimp only
  intro hc
  obtain ⟨f,hf,_,hm⟩ := hs.resolve_left hn
  exact diagram_not_small_order hf hc (original_residual_card_dvd_common_image hIX hKI) hm

/-- The original pair excludes all G₂ and small derived common containers.
Its binary classical common component is the original residual; triality,
Ree and Held, and the strict changed orbit, remain explicit. -/
theorem source_prime_pair_parabolic_classical_containers
    {T : Sylow 2 G} {L W H A B D : Subgroup G} {n p : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D) :
    ∃ R : Subgroup G, LocalData T L H B D R ∧ SelectedSourceModels H R ∧
      (((generated L H D R).pCoreIn 2 = ⊥ ∧
        ChapterF.Source.HypothesisF11 ![D ⊔ Global.sourceS L H,R] (Global.sourceS L H)) ∨
       ((generated L H D R).pCoreIn 2 ≠ ⊥ ∧
        ¬ D ≤ normalizer (R : Set G) ∧
        (normalizingSylow T R).relIndex (T : Subgroup G) = 2 ∧
        (ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4 → p = 5 ∧ n ≠ 2) ∧
        ∃ P : Sylow 2 (extension T L H B D R),
          let T₁ := (P : Subgroup (extension T L H B D R)).map (extension T L H B D R).subtype
          normalizingSylow T R < T₁ ∧
          T₁ ≤ normalizer ((D ⊔ normalizingSylow T R : Subgroup G) : Set G) ∧
          ∃ U : Sylow 2 G, (U : Subgroup G) = T₁ ∧
            ¬ (R.subgroupOf H).IsCComponent ∧
            (∃ f : ℕ, 1 < f ∧ ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 (2 ^ f) ∧
              (ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 (2 ^ f) ∨
               LocalModels.IsSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 (2 ^ f) ∨
               ClassicalGroup.IsPSp ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 (2 ^ f))) ∧
            let X := normalizer (normalizingSylow T R : Set G) ⊔ H
            ∃ I : Subgroup G, residual H ≤ I ∧ I ≤ X ∧
              (I.subgroupOf X).IsCComponent ∧ (I.subgroupOf X).Normal ∧
              conjugateSpanBy R (U : Subgroup G) < I ∧
              let Ibar := (I.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))
              IsQuasisimple Ibar ∧
                ((IsSimpleGroup Ibar ∧
                  ((∃ g : ℕ, 1 < g ∧
                    (ClassicalGroup.IsPSL Ibar 3 (2^g) ∨ ClassicalGroup.IsPSp Ibar 2 (2^g)) ∧
                    residual H = I) ∨
                   (∃ g : ℕ, 1 ≤ g ∧ Triality.Standard.IsTrialityGroupAt (2^g) Ibar) ∨
                   (∃ m : ℕ, 1 ≤ m ∧ IsReeF4At Ibar m) ∨
                   Nonempty (Ibar ≃* Held.He))) ∨
                  (Nonempty (center Ibar ≃* Multiplicative (ZMod 3)) ∧
                    (∃ f : ℕ, 1 < f ∧ (2^f) % 3 = 1 ∧ IsSL Ibar 3 (2^f) ∧
                      residual H = I ∧
                      IsSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 (2^f) ∧
                      ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 (2^f) ∧
                      p = 5 ∧ ¬ n ∣ f))))) := by
  obtain ⟨R,d,hs,hcases⟩ := source_prime_pair_parabolic_cubic_fields h hH hgen hthree c hd
  refine ⟨R,d,hs,?_⟩
  rcases hcases with hz | ⟨hz,hD,hi,hA5,P,hlt,hDT,U,hU,hn,hfield,I,hKI,hIX,hI,hIn,horbit,hquasi,hm⟩
  · exact .inl hz
  refine .inr ⟨hz,hD,hi,hA5,P,hlt,hDT,U,hU,hn,hfield,I,hKI,hIX,hI,hIn,horbit,hquasi,?_⟩
  rcases hm with ⟨hsi,hm⟩ | hm
  · refine .inl ⟨hsi,?_⟩
    rcases hm with hm | hm
    · have hsmall := hs.parabolic_common_not_small_order hn hIX hKI
      cases hm with
      | linear g hg hm =>
        have hg' : 1 < g := by
          by_contra! hle
          have he : g = 1 := by omega
          obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
          apply hsmall (.inl ?_)
          rw [Nat.card_congr e.toEquiv,Matrix.PSL3.LinearThree.card_projective,hF,he]
          norm_num
        exact .inl ⟨g,hg',.inl hm,
          hs.parabolic_common_classical_eq hn hH.1.1.2 le_sup_right hIX hI hKI hg' (.inl hm)⟩
      | symplectic g hg hm =>
        exact .inl ⟨g,hg,.inr hm,
          hs.parabolic_common_classical_eq hn hH.1.1.2 le_sup_right hIX hI hKI hg
            (.inr (.inr hm))⟩
      | g2 g hg hm =>
        exact (hs.parabolic_common_not_g2 hn hH.1.1.2 le_sup_right hIX hI hKI hg hm).elim
      | triality g hg hm => exact .inr (.inl ⟨g,hg,hm⟩)
      | ree m hm hmodel => exact .inr (.inr (.inl ⟨m,hm,hmodel⟩))
      | symplectic_derived he =>
        apply (hsmall (.inr (.inl ?_))).elim
        rw [Nat.card_congr (he.some.trans
          Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix).toEquiv,
          nat_card_alternatingGroup]
        norm_num
      | g2_derived he =>
        apply (hsmall (.inr (.inr (.inl ?_)))).elim
        rw [Nat.card_congr he.some.toEquiv,
          Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp)]
      | tits he =>
        apply (hsmall (.inr (.inr (.inr ?_)))).elim
        exact (Nat.card_congr he.some.toEquiv).trans Tits.parrottGroup_card
    · exact .inr (.inr (.inr hm))
  · exact .inr hm

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
