module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.LocalSylow
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FixedGeometry
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.Baumann.Inheritance

/-!
# Common conclusions before the mixed-factor case division

This is the fourth paragraph of the proof of Aschbacher–Smith 15.4.18,
combined manuscript of 1 March 2004, printed p.1162. Put
`Z = Ω₁(Z(T))`, `E = Ω₁(Z(J(T)))`, `Gᵢ = YᵢTᵢ`, and `I = ⟨G₁,G₂⟩`.
The raw mixed construction supplies a nontrivial elementary `E₀ ≤ T`
centralized by `I`, and a Sylow subgroup of `C_G(E₀)` with image `Tᵢ ≤ T`.

The proved Sylow-transfer lemma constructs every hypothesis of 1.1.5.
Its first clause and the relative centralizer case of 1.1.3(2) give
`F*(C_I(z)) = O₂(C_I(z))`. Its second clause gives inversion on the
actual odd core. Inversion commutes with every automorphism, so
`[Z,Yᵢ] ≤ C_I(O(I))`. Together with `Z ∩ [Z,Y₁] ≠ 1`, this proves
`O(I) = 1`. This proves the commutator containment needed in the source
directly from 1.1.5(2), without invoking the more general A.1.26(1).
Consequently the residual identities for the factors are unnecessary here.

The final assembly also derives the nontrivial intersection: the source
factor identity `V₁ = [E,Y₁]`, elementary abelianness and `V₁ ≤ T` put
`[Z,Y₁]` in an elementary two-subgroup. Normalization by `T` and
noncentralization of `Y₁` then force a nonidentity central involution in it.
Finally, the universal 15.4.17(2) is specialized to `B = E₀`, `H = C_G(E₀)`.

The three earlier implications are explicit universal parameters, retaining
all their source hypotheses. This module proves a conditional helper, not
1.1.5, 1.1.3(2), 15.4.17(2), or the final assertion `s(Y) = 2`.
The source-assembly owner must supply those earlier theorems and the raw
factor and Sylow data. All Fitting expressions below are intrinsic `F*`.
-/

@[expose] public section

open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.Prebranch
variable {G : Type*} [Group G] [Finite G]

/-- Precisely the first two clauses of source 1.1.5, universally quantified
with all its hypotheses. `He` uses the equivalent self-centralizing-two-core
condition of 1.1.1; the component classification in clause (3) is not used. -/
def Lemma115OneTwo (K : GroupClass) (G : Type*) [Group G] [Finite G] : Prop :=
  ∀ (_ : IsSimpleQTKE K G) (H : Subgroup G) (S : Sylow 2 H) (M : Subgroup G) (z : G),
    Chapter1.Lemma115Hypotheses H S M z →
      (H ⊓ M) ∈ Chapter1.He G ∧
        ∀ r : H, r ∈ pPrimeCore 2 H → z * (r : G) * z⁻¹ = (r : G)⁻¹

/-- Universal source 1.1.3(2). Both the lower bound `XC_M(X)` and the
upper bound `N_M(X)` are relative to the same subgroup `M`. -/
def Lemma113Two (K : GroupClass) (G : Type*) [Group G] [Finite G] : Prop :=
  ∀ (_ : IsSimpleQTKE K G) (M X L : Subgroup G),
    M ∈ Chapter1.He G → IsPGroup 2 X → X ≤ M →
    X ⊔ (M ⊓ centralizer (X : Set G)) ≤ L →
    L ≤ M ⊓ normalizer (X : Set G) →
    L ∈ Chapter1.He G ∧ M ⊓ centralizer (X : Set G) ∈ Chapter1.He G

/-- Universal source 15.4.17(2), with the actual common Sylow subgroup,
relative normality of `B` in `H`, and central intersection hypothesis. -/
def Lemma15417Two (K : GroupClass) (G : Type*) [Group G] [Finite G] : Prop :=
  ∀ (_ : IsSimpleQTKE K G) (T : Sylow 2 G) (B H I : Subgroup G),
    B ≠ ⊥ → B ≤ (T : Subgroup G) → B ≤ H → centralizer (B : Set G) ≤ H →
    H ≤ normalizer (B : Set G) →
    ∀ S : Sylow 2 H, (S : Subgroup H).map H.subtype = (T : Subgroup G) ⊓ H →
    (T : Subgroup G) ⊓ H ≤ I → I ≤ H →
    Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ⊓ I.pCoreIn 2 ≠ ⊥ →
    Theory.GroupTheory.generalizedFitting I = pCore 2 I

omit [Finite G] in
private theorem commutator_centralizes_of_inversion (N A B : Subgroup G) [N.Normal]
    (hinv : ∀ a ∈ A, a ≠ 1 → ∀ n : N, MulAut.conjNormal a n = n⁻¹) :
    ⁅A, B⁆ ≤ centralizer (N : Set G) := by
  apply commutator_le.mpr
  intro a ha b _
  let φ : G →* MulAut N := MulAut.conjNormal
  have hc : φ a * φ b = φ b * φ a := by
    by_cases ha1 : a = 1
    · simp [ha1]
    · apply MulEquiv.ext
      intro n
      change φ a (φ b n) = φ b (φ a n)
      rw [hinv a ha ha1, hinv a ha ha1, map_inv]
  have he : φ ⁅a, b⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hc
  apply mem_centralizer_iff.mpr
  intro n hn
  have hh := congrArg (fun f : MulAut N => ((f ⟨n, hn⟩ : N) : G)) he
  change ⁅a, b⁆ * n * ⁅a, b⁆⁻¹ = n at hh
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm

omit [Finite G] in
/-- Every factor commutator centralizes the odd core once all nonidentity
elements of `Z` invert it. Normality is used inside `I` only. -/
theorem factor_commutator_centralizes_oddCore {I Z Y : Subgroup G}
    (hZI : Z ≤ I) (hYI : Y ≤ I)
    (hinv : ∀ z ∈ Z, z ≠ 1 → ∀ r : I, r ∈ pPrimeCore 2 I →
      z * (r : G) * z⁻¹ = (r : G)⁻¹) :
    ⁅Z, Y⁆ ≤ I ⊓ centralizer ((pPrimeCore 2 I).map I.subtype : Set G) := by
  refine le_inf ((Subgroup.commutator_le_sup Z Y).trans (sup_le hZI hYI)) ?_
  have hc := commutator_centralizes_of_inversion (pPrimeCore 2 I)
    (Z.subgroupOf I) (Y.subgroupOf I) (by
      intro z hz hz1 r
      apply Subtype.ext
      apply Subtype.ext
      exact hinv z hz (fun he => hz1 (Subtype.ext he)) r r.property)
  rw [← map_subgroupOf_eq_of_le hZI, ← map_subgroupOf_eq_of_le hYI, ← map_commutator]
  rintro _ ⟨x, hx, rfl⟩
  apply mem_centralizer_iff.mpr
  rintro _ ⟨r, hr, rfl⟩
  exact congrArg Subtype.val (mem_centralizer_iff.mp (hc hx) r hr)

/-- The nonidentity element in `Z ∩ [Z,Y]` both centralizes and inverts
`O(I)`. Its elements then have order dividing both two and an odd number. -/
theorem oddCore_eq_bot_of_central_commutator {I Z Y : Subgroup G}
    (hZI : Z ≤ I) (hYI : Y ≤ I)
    (hinv : ∀ z ∈ Z, z ≠ 1 → ∀ r : I, r ∈ pPrimeCore 2 I →
      z * (r : G) * z⁻¹ = (r : G)⁻¹)
    (hmeet : Z ⊓ ⁅Z, Y⁆ ≠ ⊥) : pPrimeCore 2 I = ⊥ := by
  obtain ⟨z, hz1⟩ := ne_bot_iff_exists_ne_one.mp hmeet
  have hzG : (z : G) ≠ 1 := fun he => hz1 (Subtype.ext he)
  have hc := (factor_commutator_centralizes_oddCore hZI hYI hinv z.property.2).2
  apply eq_bot_iff.mpr
  intro r hr
  apply mem_bot.mpr
  have he : (r : G) = (r : G)⁻¹ := by
    have hcomm := (mem_centralizer_iff.mp hc r (mem_map.mpr ⟨r, hr, rfl⟩)).symm
    simpa only [hcomm, mul_inv_cancel_right] using hinv z z.property.1 hzG r hr
  have hpow : r ^ 2 = 1 := Subtype.ext (by
    change (r : G) ^ 2 = 1
    rw [pow_two]
    exact (congrArg (fun x : G => x * (r : G)) he).trans (inv_mul_cancel _))
  apply orderOf_eq_one_iff.mp
  exact Nat.eq_one_of_dvd_coprimes (pPrimeCore_coprime_card (p := 2) (G := I))
    (orderOf_dvd_of_pow_eq_one hpow) ((pPrimeCore 2 I).orderOf_dvd_natCard hr)

/-- Apply 1.1.3(2) to `M' = I ∩ M`, `X = ⟨z⟩`, and `L = N_{M'}(X)`.
The bound `C_G(z) ≤ M` identifies the resulting centralizer with `C_I(z)`. -/
theorem characteristicTwo_centralizer_of_local115 {K : GroupClass}
    (hG : IsSimpleQTKE K G) (earlier115 : Lemma115OneTwo K G)
    (earlier1132 : Lemma113Two K G) {I M : Subgroup G} (P : Sylow 2 I) {z : G}
    (hlocal : Chapter1.Lemma115Hypotheses I P M z) :
    Theory.GroupTheory.generalizedFitting (I ⊓ centralizer ({z} : Set G) : Subgroup G) =
      pCore 2 (I ⊓ centralizer ({z} : Set G) : Subgroup G) := by
  have hzI : z ∈ I := map_subtype_le _ hlocal.mem_sylow
  have hzM : z ∈ M := hlocal.centralizer_le (mem_centralizer_singleton_iff.mpr rfl)
  have hX : IsPGroup 2 (zpowers z) := by
    have : IsElementaryAbelian 2 (zpowers z) :=
      IsElementaryAbelian.zpowers_of_pow_eq_one (hlocal.involution ▸ pow_orderOf_eq_one z)
    exact IsElementaryAbelian.isPGroup 2 _
  have hXM : zpowers z ≤ I ⊓ M := zpowers_le.mpr ⟨hzI, hzM⟩
  have hc := (earlier1132 hG (I ⊓ M) (zpowers z)
    ((I ⊓ M) ⊓ normalizer (zpowers z : Set G))
    (earlier115 hG I P M z hlocal).1 hX hXM
    (sup_le (le_inf hXM (zpowers z).le_normalizer)
      (inf_le_inf_left _ (Subgroup.centralizer_le_normalizer _))) le_rfl).2
  have he : (I ⊓ M) ⊓ centralizer (zpowers z : Set G) =
      I ⊓ centralizer ({z} : Set G) := by
    rw [zpowers_eq_closure, centralizer_closure]
    exact le_antisymm (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
      (le_inf (le_inf inf_le_left (inf_le_right.trans hlocal.centralizer_le)) inf_le_right)
  exact generalizedFitting_eq_twoCore_of_mem_He (he ▸ hc)

/-- Specialization of 15.4.17(2) to the constructed centralizer of `E₀`.
Elementary abelianness supplies `E₀ ≤ C_G(E₀)`; Sylow maximality identifies
`T ∩ C_G(E₀)` with the supplied image `Tᵢ`. -/
theorem generalizedFitting_implication_of_promoted_centralizer {K : GroupClass}
    (hG : IsSimpleQTKE K G) (earlier17 : Lemma15417Two K G) (T : Sylow 2 G)
    {E₀ Tᵢ I : Subgroup G} [IsElementaryAbelian 2 E₀]
    (hE₀ : E₀ ≠ ⊥) (hE₀T : E₀ ≤ (T : Subgroup G))
    (S : Sylow 2 (centralizer (E₀ : Set G)))
    (hS : (S : Subgroup (centralizer (E₀ : Set G))).map
      (centralizer (E₀ : Set G)).subtype = Tᵢ)
    (hTᵢT : Tᵢ ≤ (T : Subgroup G)) (hTᵢI : Tᵢ ≤ I)
    (hIC : I ≤ centralizer (E₀ : Set G))
    (hZ : Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ⊓ I.pCoreIn 2 ≠ ⊥) :
    Theory.GroupTheory.generalizedFitting I = pCore 2 I := by
  have hTC : (T : Subgroup G) ⊓ centralizer (E₀ : Set G) = Tᵢ :=
    (inf_eq_sylow_map S T.isPGroup' (hS ▸ hTᵢT)).trans hS
  have hE₀C : E₀ ≤ centralizer (E₀ : Set G) := by
    intro e he
    exact mem_centralizer_iff.mpr fun a ha => setLike_mul_comm ha he
  exact earlier17 hG T E₀ (centralizer (E₀ : Set G)) I hE₀ hE₀T hE₀C le_rfl
    (Subgroup.centralizer_le_normalizer _) S (hS.trans hTC.symm) (hTC ▸ hTᵢI) hIC hZ


/-- The source factor identity `V = [E,Y]` and center geometry force
`Z ∩ [Z,Y] ≠ 1`. Only the first factor is required to be normalized by `T`;
the mixed second factor must not be presumed `T`-invariant. -/
theorem centralOmega_meets_factor_commutator (T : Sylow 2 G) {Y V : Subgroup G}
    [IsElementaryAbelian 2 V]
    (hV : V = ⁅ChapterB.thompsonAlpha (T : Subgroup G), Y⁆)
    (hVT : V ≤ (T : Subgroup G))
    (hTY : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hnoncentral : ¬ Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ≤
      centralizer (Y : Set G)) :
    Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ⊓
      ⁅Stellmacher.omegaOneCenterAmbient (T : Subgroup G), Y⁆ ≠ ⊥ := by
  let Z := Stellmacher.omegaOneCenterAmbient (T : Subgroup G)
  let D := ⁅Z, Y⁆
  have hDV : D ≤ V := by
    rw [hV]
    exact commutator_mono (centralOmega_le_thompsonAlpha (T : Subgroup G)) le_rfl
  let : IsElementaryAbelian 2 D := {
    toIsMulCommutative := .of_setLike_mul_comm fun a ha b hb =>
      setLike_mul_comm (hDV ha) (hDV hb)
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun d =>
      Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (p := 2) (d : G) (hDV d.property)) }
  have hTZ : (T : Subgroup G) ≤ normalizer (Z : Set G) := by
    apply le_normalizer_iff.mpr
    intro t ht z hz
    have hc := ((Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2 t ht
    simpa only [hc, mul_inv_cancel_right] using hz
  have hTD : (T : Subgroup G) ≤ normalizer (D : Set G) := by
    intro t ht
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [map_commutator, mem_normalizer_iff_map_conj_eq.mp (hTZ ht),
      mem_normalizer_iff_map_conj_eq.mp (hTY ht)]
  intro hmeet
  exact hnoncentral (commutator_eq_bot_iff_le_centralizer.mp
    (eq_bot_of_normalized_of_disjoint_centralOmega T.isPGroup' (hDV.trans hVT) hTD hmeet))

/-- Construct the full 1.1.5 hypotheses for each permitted `z,M`, and
then prove both characteristic-two conclusions and odd-core inversion. -/
theorem local_conclusions_of_promoted_centralizer {K : GroupClass}
    (hG : IsSimpleQTKE K G) (earlier115 : Lemma115OneTwo K G)
    (earlier1132 : Lemma113Two K G) (T : Sylow 2 G)
    {E₀ Tᵢ I : Subgroup G} [IsElementaryAbelian 2 E₀]
    (hE₀ : E₀ ≠ ⊥) (hE₀T : E₀ ≤ (T : Subgroup G))
    (S : Sylow 2 (centralizer (E₀ : Set G)))
    (hS : (S : Subgroup (centralizer (E₀ : Set G))).map
      (centralizer (E₀ : Set G)).subtype = Tᵢ)
    (hTᵢT : Tᵢ ≤ (T : Subgroup G)) (hTᵢI : Tᵢ ≤ I)
    (hIC : I ≤ centralizer (E₀ : Set G))
    {z : G} (hz : z ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) (hz1 : z ≠ 1)
    {M : Subgroup G} (hM : IsMaximalTwoLocal M) (hCM : centralizer ({z} : Set G) ≤ M) :
    ∃ P : Sylow 2 I, (P : Subgroup I).map I.subtype = Tᵢ ∧
      Chapter1.Lemma115Hypotheses I P M z ∧
      Theory.GroupTheory.generalizedFitting (I ⊓ M : Subgroup G) =
        pCore 2 (I ⊓ M : Subgroup G) ∧
      Theory.GroupTheory.generalizedFitting (I ⊓ centralizer ({z} : Set G) : Subgroup G) =
        pCore 2 (I ⊓ centralizer ({z} : Set G) : Subgroup G) ∧
      ∀ r : I, r ∈ pPrimeCore 2 I → z * (r : G) * z⁻¹ = (r : G)⁻¹ := by
  obtain ⟨P, hP, hp⟩ := local115_from_promoted_centralizer hG.toIsQTKE T hE₀ hE₀T S hS
    hTᵢT hTᵢI hIC hz hz1 hM hCM
  exact ⟨P, hP, hp, generalizedFitting_eq_twoCore_of_mem_He (earlier115 hG I P M z hp).1,
    characteristicTwo_centralizer_of_local115 hG earlier115 earlier1132 P hp,
    (earlier115 hG I P M z hp).2⟩

/-- Choose maximal two-local overgroups of involution centralizers to
obtain inversion for every `z ∈ Z#`, then apply the commutator argument. -/
theorem oddCore_eq_bot_of_promoted_centralizer {K : GroupClass}
    (hG : IsSimpleQTKE K G) (earlier115 : Lemma115OneTwo K G) (T : Sylow 2 G)
    {E₀ Tᵢ I Y : Subgroup G} [IsElementaryAbelian 2 E₀]
    (hE₀ : E₀ ≠ ⊥) (hE₀T : E₀ ≤ (T : Subgroup G))
    (S : Sylow 2 (centralizer (E₀ : Set G)))
    (hS : (S : Subgroup (centralizer (E₀ : Set G))).map
      (centralizer (E₀ : Set G)).subtype = Tᵢ)
    (hTᵢT : Tᵢ ≤ (T : Subgroup G)) (hTᵢI : Tᵢ ≤ I)
    (hIC : I ≤ centralizer (E₀ : Set G)) (hYI : Y ≤ I)
    (hmeet : Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ⊓
      ⁅Stellmacher.omegaOneCenterAmbient (T : Subgroup G), Y⁆ ≠ ⊥) :
    pPrimeCore 2 I = ⊥ := by
  have hTC : (T : Subgroup G) ⊓ centralizer (E₀ : Set G) = Tᵢ :=
    (inf_eq_sylow_map S T.isPGroup' (hS ▸ hTᵢT)).trans hS
  have hZI : Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ≤ I := by
    intro z hz
    obtain ⟨hzT, _, hzc⟩ := (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hz
    have hzC : z ∈ centralizer (E₀ : Set G) :=
      mem_centralizer_iff.mpr fun e he => hzc e (hE₀T he)
    exact hTᵢI (hTC ▸ (show z ∈ (T : Subgroup G) ⊓ centralizer (E₀ : Set G) from ⟨hzT, hzC⟩))
  apply oddCore_eq_bot_of_central_commutator hZI hYI ?_ hmeet
  intro z hz hz1
  have hzorder : orderOf z = 2 := orderOf_eq_prime_iff.mpr
    ⟨((Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hz).2.1, hz1⟩
  obtain ⟨M, hCM, hM⟩ := Finite.exists_le_maximal
    (Theory.GroupTheory.isTwoLocal_involution_centralizer hzorder)
  obtain ⟨P, _, hp⟩ := local115_from_promoted_centralizer hG.toIsQTKE T hE₀ hE₀T S hS
    hTᵢT hTᵢI hIC hz hz1 hM hCM
  exact (earlier115 hG I P M z hp).2


/-- Assemble the common pre-branch conclusions for the actual generated
mixed group. The nontrivial commutator intersection is proved from the
first factor's source identity and normalization; it is not an input.
The joins defining `I` are the source products `Gᵢ = YᵢTᵢ` once the mixed
construction has supplied their normalization. -/
theorem mixed_prebranch {K : GroupClass}
    (hG : IsSimpleQTKE K G) (earlier115 : Lemma115OneTwo K G)
    (earlier1132 : Lemma113Two K G) (earlier17 : Lemma15417Two K G)
    (T : Sylow 2 G) {Y₁ Y₂ Tᵢ E₀ V₁ I : Subgroup G}
    [IsElementaryAbelian 2 E₀] [IsElementaryAbelian 2 V₁]
    (hI : I = (Y₁ ⊔ Tᵢ) ⊔ (Y₂ ⊔ Tᵢ))
    (hE₀ : E₀ ≠ ⊥) (hE₀T : E₀ ≤ (T : Subgroup G))
    (S : Sylow 2 (centralizer (E₀ : Set G)))
    (hS : (S : Subgroup (centralizer (E₀ : Set G))).map
      (centralizer (E₀ : Set G)).subtype = Tᵢ)
    (hTᵢT : Tᵢ ≤ (T : Subgroup G)) (hIC : I ≤ centralizer (E₀ : Set G))
    (hV₁ : V₁ = ⁅ChapterB.thompsonAlpha (T : Subgroup G), Y₁⁆)
    (hV₁T : V₁ ≤ (T : Subgroup G))
    (hTY₁ : (T : Subgroup G) ≤ normalizer (Y₁ : Set G))
    (hZnoncentral : ¬ Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ≤
      centralizer (Y₁ : Set G)) :
    (∀ z ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G), z ≠ 1 →
      ∀ M : Subgroup G, IsMaximalTwoLocal M → centralizer ({z} : Set G) ≤ M →
      ∃ P : Sylow 2 I, (P : Subgroup I).map I.subtype = Tᵢ ∧
        Chapter1.Lemma115Hypotheses I P M z ∧
        Theory.GroupTheory.generalizedFitting (I ⊓ M : Subgroup G) =
          pCore 2 (I ⊓ M : Subgroup G) ∧
        Theory.GroupTheory.generalizedFitting (I ⊓ centralizer ({z} : Set G) : Subgroup G) =
          pCore 2 (I ⊓ centralizer ({z} : Set G) : Subgroup G)) ∧
    pPrimeCore 2 I = ⊥ ∧
    (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ⊓ I.pCoreIn 2 ≠ ⊥ →
      Theory.GroupTheory.generalizedFitting I = pCore 2 I) := by
  have hTᵢI : Tᵢ ≤ I := hI ▸ (le_sup_right.trans le_sup_left)
  have hY₁I : Y₁ ≤ I := hI ▸ (le_sup_left.trans le_sup_left)
  refine ⟨?_, oddCore_eq_bot_of_promoted_centralizer hG earlier115 T hE₀ hE₀T S hS
    hTᵢT hTᵢI hIC hY₁I
    (centralOmega_meets_factor_commutator T hV₁ hV₁T hTY₁ hZnoncentral), ?_⟩
  · intro z hz hz1 M hM hCM
    obtain ⟨P, hP, hp, hfit, hcentral, _⟩ := local_conclusions_of_promoted_centralizer
      hG earlier115 earlier1132 T hE₀ hE₀T S hS hTᵢT hTᵢI hIC hz hz1 hM hCM
    exact ⟨P, hP, hp, hfit, hcentral⟩
  · exact generalizedFitting_implication_of_promoted_centralizer hG earlier17 T hE₀ hE₀T
      S hS hTᵢT hTᵢI hIC

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.Prebranch
