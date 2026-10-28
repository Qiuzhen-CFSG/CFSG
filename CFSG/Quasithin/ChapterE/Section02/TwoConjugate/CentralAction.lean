module

public import CFSG.Quasithin.ChapterE.Section02.TwoConjugate.Geometry
public import Theory.GroupTheory.CentralCommutatorQuotient
public import Theory.GroupTheory.OddActionCentralTwoKernel
public import GorensteinWalter.Section2.Bender1970_18
public import Theory.GroupTheory.GeneralizedFitting.Defs

/-!
# Central core action and nontrivial cubic action

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), E.2.10(4) and (9), printed pp. 222–224.

The two generators centralize `O₂(X)/P`. The local two-core hypothesis puts
`[J,V]` in `O₂(X)`, since `J` is two-closed. For each ambient element, its
commutator map from `J` to the central two-group `O₂(X)/P` kills a Sylow
2-subgroup of `J`. The image is therefore trivial by the Sylow index theorem,
proving that `X` centralizes `J/P`.

If `V` centralizes `A`, it centralizes `P`, and conjugate generation makes `P`
central in `X`. Every odd prime-order subgroup then fixes `O₂(X)` by the
central-kernel coprime-action lemma. Self-centralization of the generalized
Fitting subgroup forces these subgroups into `O₂(X)`, so `X` is a two-group,
contrary to the properness of `V`. The private bridge compares the actual
Fitting and component definitions used by the self-centralization theorem
with `Theory.GroupTheory.generalizedFitting`; no identification is assumed.
-/

@[expose] public section

open Subgroup
open scoped Pointwise commutatorElement
namespace CFSG.Quasithin.ChapterE.TwoConjugate
variable {X : Type*} [Group X] [Finite X]
variable {T : Sylow 2 X} {V M : Subgroup X} {g : X}
namespace Hypotheses

/-- The intrinsic generalized-Fitting hypothesis implies self-centralization
of the two-core. Containment of the alternate intrinsic definition suffices. -/
private theorem centralizer_twoCore_le_of_fstar
    (hf : Theory.GroupTheory.generalizedFitting X = pCore 2 X) :
    centralizer (pCore 2 X : Set X) ≤ pCore 2 X := by
  have hbridge : GorensteinWalter.generalizedFittingSubgroupOf (⊤ : Subgroup X) ≤
      Theory.GroupTheory.generalizedFitting X := by
    apply sup_le
    · apply le_trans _ (Theory.GroupTheory.fitting_le_generalizedFitting X)
      exact le_sSup ⟨fittingSubgroupOf_normal _ inferInstance,
        GorensteinWalter.fittingSubgroupOf_isNilpotent _⟩
    · apply sSup_le
      intro E hE
      have hsub : E.IsSubnormal := by
        have hh := hE.2.1.map (show Function.Surjective (⊤ : Subgroup X).subtype from
          fun x => ⟨⟨x, mem_top x⟩, rfl⟩)
        simpa only [map_subgroupOf_eq_of_le (show E ≤ ⊤ from le_top)] using hh
      exact Theory.GroupTheory.component_le_generalizedFitting X E
        ⟨hsub, (Theory.GroupTheory.isQuasisimple_def E).mpr hE.2.2.2⟩
  rw [hf] at hbridge
  exact (centralizer_le hbridge).trans
    (GorensteinWalter.fstar_self_centralizing.trans hbridge)


omit [Finite X] in
private theorem extend_commutator (h : Hypotheses T V M g)
    (N K : Subgroup X) [N.Normal] [K.Normal] (hc : ⁅N,V⁆ ≤ K) :
    ⁅N, (⊤ : Subgroup X)⁆ ≤ K := by
  let q := QuotientGroup.mk' K
  have hn : N.map (MulAut.conj g).toMonoidHom = N :=
    mem_normalizer_iff_map_conj_eq.mp (le_normalizer_of_normal (mem_top g))
  have hk : K.map (MulAut.conj g).toMonoidHom = K :=
    mem_normalizer_iff_map_conj_eq.mp (le_normalizer_of_normal (mem_top g))
  have hcW : ⁅N, W V g⁆ ≤ K := by
    have hh := map_mono (f := (MulAut.conj g).toMonoidHom) hc
    rwa [map_commutator, hn, hk] at hh
  have hV : V.map q ≤ centralizer (N.map q : Set (X ⧸ K)) := by
    apply le_centralizer_iff.mp
    apply commutator_eq_bot_iff_le_centralizer.mp
    rw [← map_commutator]
    exact (Subgroup.map_eq_bot_iff _).mpr (by simpa only [q, QuotientGroup.ker_mk'] using hc)
  have hW : (W V g).map q ≤ centralizer (N.map q : Set (X ⧸ K)) := by
    apply le_centralizer_iff.mp
    apply commutator_eq_bot_iff_le_centralizer.mp
    rw [← map_commutator]
    exact (Subgroup.map_eq_bot_iff _).mpr (by simpa only [q, QuotientGroup.ker_mk'] using hcW)
  have htop : (⊤ : Subgroup X).map q ≤ centralizer (N.map q : Set (X ⧸ K)) := by
    rw [← h.generate, Subgroup.map_sup]
    exact sup_le hV hW
  rw [← QuotientGroup.ker_mk' K]
  apply (Subgroup.map_eq_bot_iff (f := q) _).mp
  rw [map_commutator]
  exact commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp htop)

/-- Both conjugate generators centralize the two-core modulo `P`. -/
theorem commutator_twoCore_le_P (h : Hypotheses T V M g) :
    ⁅pCore 2 X, (⊤ : Subgroup X)⁆ ≤ P V M g := by
  let := h.core_geometry.1
  apply h.extend_commutator
  apply le_trans _ (show B V M ≤ P V M g from le_sup_left)
  rw [h.B_eq_twoCore_inf]
  exact le_inf (commutator_le_left _ _)
    (le_normalizer_iff_commutator_le_right.mp h.twoCore_normalizes_V)

/-- The local two-core hypothesis and two-closedness put `[J,V]` in `O₂(X)`. -/
theorem commutator_J_V_le_twoCore (h : Hypotheses T V M g) :
    ⁅J M, V⁆ ≤ pCore 2 X := by
  let D := (pCore 2 M).map M.subtype
  have hnorm : M ≤ normalizer (D : Set X) := by
    have hh := (pCore 2 M).le_normalizer_map M.subtype
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, M.range_subtype] using hh
  have hc : ⁅J M,V⁆ ≤ D :=
    (commutator_mono le_rfl h.le_local_core).trans
      (le_normalizer_iff_commutator_le_right.mp (M.normalCore_le.trans hnorm))
  exact h.le_twoCore_of_le_J _ ((pCore_isPGroup.map M.subtype).to_le hc)
    (commutator_le_left _ _)

/-- Conjugate generation extends the local core bound to all of `X`. -/
theorem commutator_J_le_twoCore (h : Hypotheses T V M g) :
    ⁅J M, (⊤ : Subgroup X)⁆ ≤ pCore 2 X :=
  h.extend_commutator _ _ h.commutator_J_V_le_twoCore

/-- E.2.10(4): `X` centralizes `J/P`. -/
theorem commutator_J_le_P (h : Hypotheses T V M g) :
    ⁅J M, (⊤ : Subgroup X)⁆ ≤ P V M g := by
  let := h.core_geometry.1
  let q := QuotientGroup.mk' (P V M g)
  let Q := (pCore 2 X).map q
  have hQc : Q ≤ center (X ⧸ P V M g) := by
    rintro _ ⟨a, ha, rfl⟩
    rw [mem_center_iff]
    intro b
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (P V M g) b
    apply Eq.symm
    apply commutatorElement_eq_one_iff_mul_comm.mp
    rw [← map_commutatorElement]
    exact (QuotientGroup.eq_one_iff _).mpr
      (h.commutator_twoCore_le_P (commutator_mem_commutator ha (mem_top x)))
  rw [commutator_comm]
  apply commutator_le.mpr
  intro x _ j hj
  have hr (a : X ⧸ P V M g) (ha : a ∈ (J M).map q) : ⁅q x, a⁆ ∈ Q := by
    obtain ⟨a, ha, rfl⟩ := ha
    rw [← map_commutatorElement]
    apply mem_map_of_mem
    apply h.commutator_J_le_twoCore
    rw [commutator_comm]
    exact commutator_mem_commutator (mem_top x) ha
  let f : J M →* Q := (centralCommutatorHom ((J M).map q) Q
    (hQc.trans (center_le_centralizer _)) (q x) hr).comp (q.subgroupMap (J M))
  obtain ⟨S, hS⟩ := h.core_two_closed
  have hSQ : (S : Subgroup (J M)) ≤ pCore 2 (J M) := le_sSup ⟨hS, S.isPGroup'⟩
  have hker : (S : Subgroup (J M)) ≤ f.ker := by
    intro s hs
    apply Subtype.ext
    change ⁅q x, q (s : X)⁆ = 1
    apply commutatorElement_eq_one_iff_mul_comm.mpr
    have hsQ : (s : X) ∈ pCore 2 X := by
      rw [← h.intrinsic_core_image]
      exact mem_map_of_mem _ (hSQ hs)
    exact mem_center_iff.mp (hQc (mem_map_of_mem q hsQ)) (q x)
  have hrange : IsPGroup 2 f.range := (pCore_isPGroup.map q).to_subgroup f.range
  obtain ⟨n, hn⟩ := hrange.exists_card_eq
  have hindex : f.ker.index = 2 ^ n := (index_ker f).trans hn
  have hnzero : n = 0 := by
    by_contra hnzero
    apply S.not_dvd_index
    apply dvd_trans _ (index_dvd_of_le hker)
    rw [hindex]
    exact dvd_pow_self 2 hnzero
  have hkertop : f.ker = ⊤ := index_eq_one.mp (by simpa [hnzero] using hindex)
  have hf : f ⟨j,hj⟩ = 1 := hkertop.ge (mem_top _)
  apply (QuotientGroup.eq_one_iff _).mp
  change q ⁅x,j⁆ = 1
  rw [map_commutatorElement]
  exact congrArg Subtype.val hf

/-- E.2.10(9): the cubic action is nontrivial in characteristic two. -/
theorem commutator_V_A_ne_bot (h : Hypotheses T V M g) (hproper : V ≠ ⊤)
    (hf : Theory.GroupTheory.generalizedFitting X = pCore 2 X) :
    ⁅V, A V M g⁆ ≠ ⊥ := by
  intro hzero
  let := h.elementary
  let := h.core_geometry.1
  have hPV : ⁅P V M g, V⁆ = ⊥ := by
    apply commutator_eq_bot_iff_le_centralizer.mpr
    apply sup_le
    · exact inf_le_right.trans V.le_centralizer
    · exact le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hzero)
  have hPX : ⁅P V M g, (⊤ : Subgroup X)⁆ = ⊥ :=
    bot_unique (h.extend_commutator _ _ hPV.le)
  have hPc : P V M g ≤ center X := by
    intro a ha
    rw [mem_center_iff]
    intro x
    have hh := commutator_mem_commutator ha (mem_top x)
    rw [hPX, mem_bot] at hh
    exact (commutatorElement_eq_one_iff_mul_comm.mp hh).symm
  have hself := centralizer_twoCore_le_of_fstar hf
  have hXp : IsPGroup 2 X := by
    apply (isPGroup_iff_primeFactors_card_subset (by decide : 2 ≠ 0)).mpr
    intro r hr
    obtain ⟨hrprime, hrdvd, _⟩ := Nat.mem_primeFactors.mp hr
    have hr2 : r = 2 := by
      by_contra hne
      let : Fact r.Prime := ⟨hrprime⟩
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := X) r hrdvd
      let R := zpowers x
      let Q := pCore 2 X
      let N := (P V M g).subgroupOf Q
      have hRodd : Odd (Nat.card R) := by
        rw [Nat.card_zpowers, hx]
        exact hrprime.odd_of_ne_two hne
      let _ : MulDistribMulAction R Q :=
        conjMulDistribMulActionOfLeNormalizer R Q le_normalizer_of_normal
      have hNc : N ≤ center Q := by
        intro a ha
        rw [mem_center_iff]
        intro b
        exact Subtype.ext (mem_center_iff.mp (hPc ha) b)
      have hNp : IsPGroup 2 N := (pCore_isPGroup.to_le h.P_le_twoCore).comap_subtype
      have hfix : ∀ a : R, ∀ z ∈ N, a • z = z := by
        intro a z hz
        apply Subtype.ext
        change (a : X) * (z : X) * (a : X)⁻¹ = z
        have hc : (a : X) * (z : X) = (z : X) * (a : X) :=
          mem_center_iff.mp (hPc (show (z : X) ∈ P V M g from hz)) (a : X)
        rw [hc, mul_inv_cancel_right]
      have hquot : ∀ a : R, ∀ z : Q, (a • z) * z⁻¹ ∈ N := by
        intro a z
        change ⁅(a : X), (z : X)⁆ ∈ P V M g
        apply h.commutator_twoCore_le_P
        rw [commutator_comm]
        exact commutator_mem_commutator (mem_top _) z.property
      have htrivial := MulDistribMulAction.trivial_of_odd_of_central_two_kernel
        hRodd N hNc hNp hfix hquot
      have hxQ : x ∈ Q := by
        apply hself
        rw [mem_centralizer_iff]
        intro z hz
        have hh := congrArg Subtype.val (htrivial ⟨x, mem_zpowers x⟩ ⟨z,hz⟩)
        change x * z * x⁻¹ = z at hh
        exact (mul_inv_eq_iff_eq_mul.mp hh).symm
      obtain ⟨n, hn⟩ := pCore_isPGroup.exists_orderOf_dvd_pow (⟨x,hxQ⟩ : pCore 2 X)
      have hdiv : r ∣ 2 ^ n := by simpa only [orderOf_mk, hx] using hn
      exact hne ((Nat.prime_dvd_prime_iff_eq hrprime Nat.prime_two).mp
        (hrprime.dvd_of_dvd_pow hdiv))
    subst r
    simp [Nat.prime_two]
  have htop : pCore 2 X = ⊤ := by
    apply top_unique
    exact le_sSup ⟨inferInstance, hXp.to_subgroup ⊤⟩
  exact h.V_not_le_twoCore hproper (by rw [htop]; exact le_top)

end Hypotheses
end CFSG.Quasithin.ChapterE.TwoConjugate
