module
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CPU
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.LinearCenters
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.BorelFour
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ActionConstruction.MixedLocal.PairAction
public import Theory.GroupTheory.PPerfectHom
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.ModelReduction

/-!
# The Borel action and the binary linear component obstruction

A group equal to its two-residual has trivial action on a two-element set.
Thus a Borel lying in the maximal local group fixes each of the two source
factors and normalizes its actual commutator module. When that two-module
lies in the Borel, relative normality puts it in the Borel's two-core.
This uses the residual identity `B=O²(B)` explicitly.

The component commutator conclusion from 1.1.5 supplies faithfulness.
For a relatively normal binary linear component, restrict the contrary
Sylow subgroup and construct the conjugation action of its central
four-group. An inner action fixing this Sylow subgroup has order at most
the computed center order, which is at most two. The contradiction uses
the actual PSL₄(2) or PSL₅(2) model. Its trivial center is proved by scalar
matrix calculation and a multiplicative equivalence through the genuine
projective quotient, including the arbitrary field witness of order two.

The source assembly must still obtain the model, inner action and
faithfulness from the full earlier 1.1.5 and embedding conclusions. It must
also place the Borel and commutator module in the root or block models for
the other case. No later 15.4.21–23 identification is an input here.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
Lemma 1.1.5(3) (pp.501–502) and the proof of 15.4.20 (p.1164).
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup
open Subgroup
open scoped MatrixGroups
variable {G : Type*} [Group G]

/-- A two-perfect subgroup fixes each of two factors permuted by its ambient
normalizer. This uses `B=O²(B)`, not a two-core identity. -/
theorem twoPerfect_normalizes_factors {B M : Subgroup G} {L : Bool → Subgroup G}
    (a : TwoFactors.MixedLocal.FactorPairAction M L)
    (hBM : B ≤ M) (hB : IsPPerfect 2 B) :
    ∀ i, B ≤ normalizer (L i : Set G) := by
  have hp : IsPGroup 2 (Equiv.Perm Bool) :=
    (IsPGroup.iff_card).mpr ⟨1, by rw [Nat.card_eq_fintype_card]; decide⟩
  have he := hB.hom_eq_one_of_isPGroup hp (a.permutation.comp (inclusion hBM))
  intro i b hb
  apply mem_normalizer_iff_map_conj_eq.mpr
  have hb' := a.conjugation ⟨b, hBM hb⟩ i
  have hperm : a.permutation (inclusion hBM ⟨b, hb⟩) = 1 := DFunLike.congr_fun he ⟨b, hb⟩
  have hperm' : a.permutation ⟨b, hBM hb⟩ = 1 := by
    convert hperm using 1
    congr 2
  change (L i).map (MulAut.conj b).toMonoidHom = L i
  simpa only [hperm', Equiv.Perm.one_apply] using hb'

/-- The two-residual Borel normalizes the actual commutator four-module,
because it fixes the factor and the ambient local group preserves `V(M)`. -/
theorem twoPerfect_normalizes_factor_modules {B M V : Subgroup G} {L : Bool → Subgroup G}
    (a : TwoFactors.MixedLocal.FactorPairAction M L)
    (hBM : B ≤ M) (hB : IsPPerfect 2 B)
    (hMV : M ≤ normalizer (V : Set G)) :
    ∀ i, B ≤ normalizer ((⁅V, L i⁆ : Subgroup G) : Set G) := by
  intro i b hb
  apply mem_normalizer_iff_map_conj_eq.mpr
  rw [map_commutator,
    mem_normalizer_iff_map_conj_eq.mp (hMV (hBM hb)),
    mem_normalizer_iff_map_conj_eq.mp (twoPerfect_normalizes_factors a hBM hB i hb)]

/-- An invariant two-subgroup in an actual Borel lies in its intrinsic
2-core. This is the placement step once the chosen Sylow group is in the Borel. -/
theorem factor_module_le_borel_core {B M V : Subgroup G} {L : Bool → Subgroup G}
    (a : TwoFactors.MixedLocal.FactorPairAction M L)
    (hBM : B ≤ M) (hB : IsPPerfect 2 B)
    (hMV : M ≤ normalizer (V : Set G)) (i : Bool)
    (hV : IsPGroup 2 (⁅V, L i⁆ : Subgroup G)) (hVB : ⁅V, L i⁆ ≤ B) :
    ⁅V, L i⁆ ≤ B.pCoreIn 2 :=
  le_pCoreIn_of_normalizes hV hVB (twoPerfect_normalizes_factor_modules a hBM hB hMV i)

/-- The component commutator conclusion of 1.1.5 makes the central group
faithful. The actual nontrivial component is essential. -/
theorem faithful_of_component_commutators {L Z : Subgroup G} (hL : L ≠ ⊥)
    (hcomm : ∀ z ∈ Z, z ≠ 1 → ⁅L, zpowers z⁆ = L) :
    Z ⊓ centralizer (L : Set G) = ⊥ := by
  apply eq_bot_iff.mpr
  intro z hz
  by_contra hzne
  have hc : ⁅zpowers z, L⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr (zpowers_le.mpr hz.2)
  rw [commutator_comm, hcomm z hz.1 hzne] at hc
  exact hL hc

variable [Finite G]

/-- The genuine binary projective linear models have trivial center.
The projective quotient is transported through its proved trivial kernel. -/
theorem binary_linear_center_eq_bot {A : Type*} [Group A]
    {n : ℕ} (hn : 0 < n) (hA : ClassicalGroup.IsPSL A n 2) : center A = ⊥ := by
  have hSL : center SL(n, ZMod 2) = ⊥ := by
    apply eq_bot_iff.mpr
    intro g hg
    change g = 1
    obtain ⟨a, ha, hga⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hg
    have ha0 : a ≠ 0 := by
      intro hzero
      simp [hzero, hn.ne'] at ha
    have ha1 : a = 1 := (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) a ha0
    apply Subtype.ext
    simpa [ha1] using hga.symm
  let eS : PSL(n, ZMod 2) ≃* SL(n, ZMod 2) :=
    (QuotientGroup.quotientMulEquivOfEq hSL).trans (QuotientGroup.quotientBot (G := SL(n, ZMod 2)))
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := hA
  let : Fintype F := Fintype.ofFinite F
  have hcard' : Fintype.card F = Fintype.card (ZMod 2) := by
    simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hcard
  let eF : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq hcard'
  let eA := (e.trans (Atlas.fieldEquivPSL n eF)).trans eS
  apply eq_bot_iff.mpr
  intro x hx
  have hxc : eA x ∈ center SL(n, ZMod 2) := by
    apply mem_center_iff.mpr
    intro y
    obtain ⟨z, rfl⟩ := eA.surjective y
    simpa only [map_mul] using congrArg eA (mem_center_iff.mp hx z)
  exact eA.injective ((mem_bot.mp (hSL ▸ hxc)).trans (map_one eA).symm)

/-- The central four-group cannot act faithfully by inner automorphisms on
an actual binary linear component. The action and its Sylow fixed points
are constructed from ambient conjugation and relative normality. -/
theorem no_binary_linear_component_central_four
    {H L U Z : Subgroup G} (hLH : L ≤ H) (hHL : H ≤ normalizer (L : Set G))
    (P : Sylow 2 H) (hP : (P : Subgroup H).map H.subtype = U)
    (hZU : Z ≤ U) (hZC : Z ≤ centralizer (U : Set G))
    (hcard : Nat.card Z = 4) (hfaith : Z ⊓ centralizer (L : Set G) = ⊥)
    (hinner : ∀ z : Z, ∃ l : L, ∀ x : L,
      (z : G) * (x : G) * (z : G)⁻¹ = (l : G) * (x : G) * (l : G)⁻¹)
    {n : ℕ} (hn : n = 4 ∨ n = 5) (hmodel : ClassicalGroup.IsPSL L n 2) : False := by
  have hcenter := binary_linear_center_eq_bot (by rcases hn with rfl | rfl <;> decide) hmodel
  have hUH : U ≤ H := hP ▸ map_subtype_le (P : Subgroup H)
  have hZL := hZU.trans (hUH.trans hHL)
  let α : Z →* MulAut L := L.normalizerMonoidHom.comp (inclusion hZL)
  have hinj : Function.Injective α := by
    apply (MonoidHom.ker_eq_bot_iff α).mp
    apply eq_bot_iff.mpr
    intro z hz
    have hfix : ∀ l : L, (z : G) * (l : G) * (z : G)⁻¹ = (l : G) := by
      intro l
      exact congrArg Subtype.val (DFunLike.congr_fun (MonoidHom.mem_ker.mp hz) l)
    have hcentral : (z : G) ∈ centralizer (L : Set G) := mem_centralizer_iff.mpr fun l hl =>
      (mul_inv_eq_iff_eq_mul.mp (hfix ⟨l, hl⟩)).symm
    exact Subtype.ext (mem_bot.mp (hfaith ▸ (show (z : G) ∈ Z ⊓ centralizer (L : Set G) from
      ⟨z.property, hcentral⟩)))
  have hαinner : ∀ z : Z, ∃ l : L, MulAut.conj l = α z := by
    intro z
    obtain ⟨l, hl⟩ := hinner z
    exact ⟨l, MulEquiv.ext fun x => Subtype.ext (hl x).symm⟩
  obtain ⟨Q, hQ⟩ := sylow_intersection_image_of_relative_normal hLH hHL P hP
  have hfixed : ∀ z : Z, ∀ q : Q, α z q = q := by
    intro z q
    apply Subtype.ext
    have hqU : ((q : L) : G) ∈ U :=
      (hQ ▸ (show ((q : L) : G) ∈ (Q : Subgroup L).map L.subtype from
        ⟨q, q.property, rfl⟩)).1
    exact mul_inv_eq_iff_eq_mul.mpr ((mem_centralizer_iff.mp (hZC z.property) _ hqU).symm)
  have hpZ : IsPGroup 2 Z := (P.isPGroup'.map H.subtype).to_le (hP ▸ hZU)
  have hbound := (faithful_inner_action_card_le_sylow_center Q hcenter α hinj hpZ hαinner hfixed).trans
    (binary_linear_sylow_center_card_le_two hn hmodel Q)
  omega

end CFSG.Quasithin.Chapter15.Section04.LocalSetup
