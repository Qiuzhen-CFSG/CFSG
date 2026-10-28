module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.QuadraticGeometry
public import Theory.GroupTheory.CommutatorPreimage

/-!
# Local algebra for the extraspecial branch of 15.3.49

Controlled fusion and abelianness of the centralizer-generated subgroup give
F.9.8(f). The conjugate-normalizer test in 15.3.47 then upgrades a commutator
containment to cross-centralization. We also isolate the normalizer argument
for `V_H > U_H V` and the last conjugate-generation step of (n).

All normality is relative: it is expressed by containment in an ambient
normalizer. In particular `H` need not be normal in `G`. These are conditional
local steps, not an exclusion of the extraspecial quotient. The coset geometry,
component reduction and model exclusions still have to be assembled.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
15.3.49(e), (f), (g), (m), (n), printed pp.1143–1144.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination

open Subgroup
open scoped IsMulCommutative commutatorElement

variable {G : Type*} [Group G]

/-- F.9.8(f) from the actual centralizer conjugate span and controlled fusion.
In the source `z` generates `Z` and `M_c = C_G(z)`. -/
theorem conjugate_commutes_of_abelian_localSpan
    (V M : Subgroup G) (z : G)
    (hM : M = normalizer (V : Set G))
    (hfusion : ∀ a : G, MulAut.conj a z ∈ V → ConjugateBy M z (MulAut.conj a z))
    [IsMulCommutative (localSpan V (centralizer ({z} : Set G)))]
    (g : G) (hg : z ∈ V.map (MulAut.conj g).toMonoidHom) :
    ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ = ⊥ := by
  obtain ⟨c, hc⟩ := exists_centralizer_conjugator_of_element_fusion
    (fun a ha => by simpa only [ConjugateBy, hM] using hfusion a ha) hg
  have hconj : V.map (MulAut.conj (c : G)).toMonoidHom ≤
      localSpan V (centralizer ({z} : Set G)) := by
    rintro x ⟨v, hv, rfl⟩
    exact subset_closure ⟨c, c.property, v, hv, rfl⟩
  rw [← hc]
  exact le_bot_iff.mp ((commutator_mono (le_conjugateSpanBy _ _) hconj).trans_eq
    (commutator_self_eq_bot_iff.mpr inferInstance))

/-- The pointwise argument in (f). Here `W` is a conjugate of `V`, and the
last input is precisely the normalizer test supplied by 15.3.47 for that
conjugate. A nonzero commutator lies in the abelian group `W`, making `W`
normalize it and triggering the test. -/
theorem centralizes_of_conjugate_normalizer_test
    (V E W : Subgroup G) [IsMulCommutative W]
    (hEW : E ≤ W) (hcomm : ⁅V, E⁆ ≤ W)
    (htest : ∀ x ∈ E, ⁅V, zpowers x⁆ ≠ ⊥ →
      W ≤ normalizer (⁅V, zpowers x⁆ : Subgroup G) → W ≤ centralizer (V : Set G)) :
    E ≤ centralizer (V : Set G) := by
  intro x hx
  by_cases hc : ⁅V, zpowers x⁆ = ⊥
  · have h := le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hc)
    exact h (mem_zpowers x)
  · have hz : zpowers x ≤ E := (zpowers_le).mpr hx
    have hCW : ⁅V, zpowers x⁆ ≤ W := (commutator_mono le_rfl hz).trans hcomm
    have hWW : W ≤ centralizer (W : Set G) :=
      le_centralizer_iff_isMulCommutative.mpr inferInstance
    have hn : W ≤ normalizer (⁅V, zpowers x⁆ : Subgroup G) :=
      (hWW.trans (centralizer_le hCW)).trans (Subgroup.centralizer_le_normalizer _)
    exact htest x hx hc hn (hEW hx)

/-- Applying the preceding pointwise argument at every `H`-conjugate of `V`
gives centralization of `V_H`, with `V_H` its actual conjugate span. -/
theorem centralizes_localSpan
    (V E H : Subgroup G)
    (hconj : ∀ h ∈ H, E ≤ centralizer (V.map (MulAut.conj h).toMonoidHom : Set G)) :
    E ≤ centralizer (localSpan V H : Set G) := by
  apply le_centralizer_iff.mpr
  apply (closure_le _).mpr
  rintro x ⟨h, hh, v, hv, rfl⟩
  exact le_centralizer_iff.mp (hconj h hh) (mem_map_of_mem _ hv)

/-- Once the quotient centralizer itself centralizes the whole group, the
quotient centralizer and the ordinary relative centralizer coincide. -/
theorem commutatorPreimage_eq_relativeCentralizer
    (X U Z : Subgroup G)
    (hcross : commutatorPreimage X U Z ≤ centralizer (U : Set G)) :
    commutatorPreimage X U Z = X ⊓ centralizer (U : Set G) := by
  apply le_antisymm (le_inf (commutatorPreimage_le _ _ _) hcross)
  apply le_commutatorPreimage inf_le_left
  exact (commutator_eq_bot_iff_le_centralizer.mpr
    (show X ⊓ centralizer (U : Set G) ≤ centralizer (U : Set G) from inf_le_right)).le
    |>.trans bot_le

/-- Step (g): a subgroup centralizing `V` is proper in an actor which does
not centralize `V`. The noncentrality is supplied by F.9.13(5). -/
theorem proper_of_crossCentralization
    (D U V : Subgroup G) (hDU : D ≤ U)
    (hDV : D ≤ centralizer (V : Set G)) (hUV : ⁅U, V⁆ ≠ ⊥) : D < U := by
  refine lt_of_le_of_ne hDU ?_
  intro heq
  exact hUV (commutator_eq_bot_iff_le_centralizer.mpr (heq ▸ hDV))

private theorem normalizes_commutator
    (H A B : Subgroup G)
    (hA : H ≤ normalizer (A : Set G)) (hB : H ≤ normalizer (B : Set G)) :
    H ≤ normalizer (⁅A, B⁆ : Subgroup G) := by
  intro h hh
  apply mem_normalizer_iff_map_conj_eq.mpr
  rw [map_commutator, mem_normalizer_iff_map_conj_eq.mp (hA hh),
    mem_normalizer_iff_map_conj_eq.mp (hB hh)]

/-- Step (m), with the two local commutator bounds and the nonsingular
fixed-plane containment made explicit. `Q_H` is only required to be normal
in `H`. The normalizer bound is the earlier 15.3.46(2) conclusion. -/
theorem localSpan_sup_lt
    (H M V ZS QH : Subgroup G) [IsElementaryAbelian 2 V]
    [IsMulCommutative (localSpan V H)]
    (q : QuadraticForm (ZMod 2) (Additive V))
    (hZS : ZS ≤ V) (hnonsingular : ¬ IsTotallySingular q ZS)
    (hQ : H ≤ normalizer (QH : Set G)) (houtside : ¬ H ≤ M)
    (hUQ : ⁅localSpan ZS H, QH⁆ ≤ V) (hVQ : ⁅V, QH⁆ ≤ V)
    (hfixed : ZS ≤ ⁅V, QH⁆)
    (hnormalizer : ∀ W : Subgroup G, W ≤ V →
      ¬ IsTotallySingular q W → normalizer (W : Set G) ≤ M) :
    localSpan ZS H ⊔ V < localSpan V H := by
  have hU : localSpan ZS H ≤ localSpan V H := conjugateSpanBy_mono hZS le_rfl
  have hV : V ≤ localSpan V H := le_conjugateSpanBy _ _
  refine lt_of_le_of_ne (sup_le hU hV) ?_
  intro heq
  let W : Subgroup G := ⁅localSpan V H, QH⁆
  have hnV : localSpan V H ≤ normalizer (V : Set G) :=
    ((le_centralizer_iff_isMulCommutative.mpr inferInstance).trans
      (centralizer_le hV)).trans (Subgroup.centralizer_le_normalizer _)
  have hpre : localSpan V H ≤ commutatorPreimage (localSpan V H) QH V := by
    rw [← heq]
    exact sup_le (le_commutatorPreimage (le_sup_left) hUQ)
      (le_commutatorPreimage (le_sup_right) hVQ)
  have hWV : W ≤ V := (commutator_mono hpre le_rfl).trans
    (commutator_commutatorPreimage_le _ _ _ hnV)
  have hZSW : ZS ≤ W := hfixed.trans (commutator_mono hV le_rfl)
  have hW : ¬ IsTotallySingular q W := by
    intro hs
    exact hnonsingular ⟨hZS, fun v hv => hs.2 v (hZSW hv)⟩
  exact houtside ((normalizes_commutator H _ QH
    (le_normalizer_conjugateSpanBy _ _) hQ).trans (hnormalizer W hWV hW))

/-- The final generation argument of (n). If `L` acts trivially on `V_H/U_H`
and the supplementary group normalizes `V`, its conjugate span is `U_H V`.
The proof derives the needed normalizer of the product. -/
theorem localSpan_eq_sup_of_trivial_section_action
    (H L R V ZS : Subgroup G)
    (hH : H = L ⊔ R) (hZS : ZS ≤ V)
    (hRV : R ≤ normalizer (V : Set G))
    (hcomm : ⁅localSpan V H, L⁆ ≤ localSpan ZS H) :
    localSpan V H = localSpan ZS H ⊔ V := by
  let U := localSpan ZS H
  have hU : U ≤ localSpan V H := conjugateSpanBy_mono hZS le_rfl
  have hV : V ≤ localSpan V H := le_conjugateSpanBy _ _
  have hRU : R ≤ normalizer (U : Set G) :=
    (hH ▸ le_sup_right).trans (le_normalizer_conjugateSpanBy _ _)
  have hLV : L ≤ normalizer (U ⊔ V : Subgroup G) :=
    le_normalizer_iff_commutator_le_left.mpr
      (((commutator_mono (sup_le hU hV) le_rfl).trans hcomm).trans le_sup_left)
  have hRV' : R ≤ normalizer (U ⊔ V : Subgroup G) :=
    (le_inf hRU hRV).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hHU : H ≤ normalizer (U ⊔ V : Subgroup G) := by
    rw [hH]
    exact sup_le hLV hRV'
  exact le_antisymm (conjugateSpanBy_le le_sup_right hHU) (sup_le hU hV)

/-- The symmetric centralizer cover in (n) makes `A` trivial on `X/U`.
The denominator is only normalized by `X` and `A`, not necessarily by `G`. -/
theorem commutator_le_of_centralizer_cover
    (X U A : Subgroup G) (hXU : X ≤ normalizer (U : Set G))
    (hAU : A ≤ normalizer (U : Set G))
    (hcover : X = U ⊔ (X ⊓ centralizer (A : Set G))) : ⁅X, A⁆ ≤ U := by
  have hUX : U ≤ X := hcover ▸ le_sup_left
  have hpre : X ≤ commutatorPreimage X A U := by
    conv_lhs => rw [hcover]
    apply sup_le
    · exact le_commutatorPreimage hUX (le_normalizer_iff_commutator_le_left.mp hAU)
    · exact le_commutatorPreimage inf_le_left
        ((commutator_eq_bot_iff_le_centralizer.mpr inf_le_right).le.trans bot_le)
  exact (commutator_mono hpre le_rfl).trans
    (commutator_commutatorPreimage_le X A U hXU)

/-- If `L = [L,A]`, triviality of `A` on an `H`-section forces triviality
of `L` there. This is the section-kernel step in (n). -/
theorem commutator_le_of_actor_generated
    (H X U L A : Subgroup G)
    (hHX : H ≤ normalizer (X : Set G)) (hHU : H ≤ normalizer (U : Set G))
    (hLH : L ≤ H) (hAH : A ≤ H) (hL : L = ⁅L, A⁆)
    (hXA : ⁅X, A⁆ ≤ U) : ⁅X, L⁆ ≤ U := by
  let K := commutatorPreimage H X U
  have hAK : A ≤ K := le_commutatorPreimage hAH (by rwa [commutator_comm])
  have hHK : H ≤ normalizer (K : Set G) :=
    commutatorPreimage_normalized H X U H hHU H.le_normalizer hHX hHU
  have hLK : L ≤ K := by
    rw [hL]
    exact (commutator_mono hLH hAK).trans (le_normalizer_iff_commutator_le_right.mp hHK)
  rw [commutator_comm]
  exact (commutator_mono hLK le_rfl).trans (commutator_commutatorPreimage_le H X U hHU)

/-- The group-theoretic conclusion of the symmetric-cover argument in (n).
It remains the geometry's responsibility to produce this cover when the
selected offender is not strong, and the component argument's responsibility
to supply `L = [L,A]`. -/
theorem localSpan_eq_sup_of_symmetric_cover
    (H L R V ZS A : Subgroup G)
    (hH : H = L ⊔ R) (hZS : ZS ≤ V)
    (hRV : R ≤ normalizer (V : Set G))
    (hVH : localSpan V H ≤ H) (hAH : A ≤ H)
    (hL : L = ⁅L, A⁆)
    (hcover : localSpan V H = localSpan ZS H ⊔
      (localSpan V H ⊓ centralizer (A : Set G))) :
    localSpan V H = localSpan ZS H ⊔ V := by
  have hHU := le_normalizer_conjugateSpanBy ZS H
  have hXA := commutator_le_of_centralizer_cover (localSpan V H) (localSpan ZS H) A
    (hVH.trans hHU) (hAH.trans hHU) hcover
  have hXL := commutator_le_of_actor_generated H (localSpan V H) (localSpan ZS H) L A
    (le_normalizer_conjugateSpanBy V H) hHU (hH ▸ le_sup_left) hAH hL hXA
  exact localSpan_eq_sup_of_trivial_section_action H L R V ZS hH hZS hRV hXL

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination
