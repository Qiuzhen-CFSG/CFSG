module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.DiagonalProduct.LinearCore.KernelAction.Setup
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.OuterActor
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.LocalCover.PreGeometry.Source

/-!
# The component-centralizer action modulo the centre

Put K = C_{Y₊}(L). The component and local three-rank bounds make C_I(L)
three-free. Since Y₊ lies in Y and Y/O₂(Y) is a three-group, K lies in
O₂(Y). The source normalizer equality and L = ⟨L^S⟩ show that Y₊S
normalizes K. Consequently K lies in the actual R = O₂(Y₊S), and in S.
With the additional earlier conclusion 15.3.36(2), R = C_T(V), K also
centralizes the actual natural module V.

The earlier pre-centre geometry now supplies C_S(L)=Z(L) in the original
quotient marking. Combining this with K≤S gives K≤Z(L). Since Y₊ normalizes
K, every [c,y] for c∈K lies in the mapped centre, proving the exact
`ActionModuloCenter` conclusion. The actual PSL₃ branch is impossible:
the constructed centre is a four-group, whereas PSL₃ has trivial centre.
The field-four branch retains the potentially nontrivial central two-cover.

The remaining explicit inputs are genuine earlier local conclusions:
the uniform Sylow, rank, normalizer, theta and characteristic-two facts in
`SourceBorel.Earlier`, the plane-normalizer consequence 15.3.11(3), the
complete 15.3.7 alternatives and natural residual image, 15.3.8, and
C_V(Y)=1 from that natural action. All Borel, root and central-cover
calculations are constructed by `PreGeometry.Source`. Its argument uses
the strategy on printed p.1136 from these earlier inputs; neither the
full product in 15.3.37 nor a theorem of 15.3.38--40 is a premise.
The centre need only be invariant under y, not fixed pointwise.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
15.3.2--12, 15.3.25, 15.3.33, 15.3.36(2), and the final paragraph of
15.3.37, printed pp.1121--1124 and 1135--1136 (PDF pp.1152--1153).
-/

public section

open Subgroup Theory.GroupTheory
open scoped commutatorElement MatrixGroups

namespace CFSG.Quasithin.Chapter15.Section03.Candidates.LinearCore.KernelAction.ModuloCenter

variable {G : Type*} [Group G] [Finite G]

/-- The ordinary centralizer kernel lies in the original two-core O₂(Y). -/
theorem kernel_le_twoCore {d : CharacteristicTwo.LocalData G} {I L : Subgroup G}
    (h : SourceSetup d I L) :
    d.Yplus ⊓ centralizer (L : Set G) ≤ d.Y.pCoreIn 2 := by
  have hYI : d.Yplus ≤ I := le_sup_left.trans h.outside.1.2
  have hYY : d.Yplus ≤ d.Y := by
    rcases d.choice with he | ⟨_, he⟩
    · exact he.le
    · rw [he]
      exact (map_subtype_le _).trans inf_le_left
  have hc := local_centralizer_three_coprime h.component_le h.component h.odd_core
    h.rank_component.ge h.rank_overgroup
  exact SuzukiExclusion.le_twoCore_of_three_free (inf_le_left.trans hYY) h.quotient_three
    (fun hd => Nat.prime_three.coprime_iff_not_dvd.mp hc
      (hd.trans (card_dvd_of_le (inf_le_inf_right _ hYI))))

/-- In particular the whole kernel, not just each commutator, is a two-group. -/
theorem kernel_isTwoGroup {d : CharacteristicTwo.LocalData G} {I L : Subgroup G}
    (h : SourceSetup d I L) : IsPGroup 2 (d.Yplus ⊓ centralizer (L : Set G) : Subgroup G) :=
  (d.Y.isPGroup_pCoreIn 2).to_le (kernel_le_twoCore h)

omit [Finite G] in
/-- Normality is relative to Y₊S; no ambient normality is assumed. -/
theorem localGroup_normalizes_kernel {d : CharacteristicTwo.LocalData G}
    {I L : Subgroup G} (h : SourceSetup d I L)
    (hn : d.Yplus ≤ normalizer (L : Set G)) :
    d.Yplus ⊔ d.S ≤ normalizer ((d.Yplus ⊓ centralizer (L : Set G) : Subgroup G) : Set G) := by
  have hSM : d.S ≤ d.M := inf_le_left.trans d.sylow_le
  have hSI : d.S ≤ I := le_sup_right.trans h.outside.1.2
  have hSY : d.S ≤ normalizer (d.Yplus : Set G) :=
    (le_inf hSM hSI).trans (h.normalizer_eq.symm.le.trans inf_le_right)
  have hSL : d.S ≤ normalizer (L : Set G) := by
    simpa only [← h.orbit_eq] using le_normalizer_conjugateSpanBy L d.S
  exact le_normalizer_inf (sup_le d.Yplus.le_normalizer hSY)
    ((sup_le hn hSL).trans (normalizer_le_normalizer_centralizer L))

/-- The invariant kernel lies in the local core R = O₂(Y₊S). -/
theorem kernel_le_localCore {d : CharacteristicTwo.LocalData G} {I L : Subgroup G}
    (h : SourceSetup d I L) (hn : d.Yplus ≤ normalizer (L : Set G)) :
    d.Yplus ⊓ centralizer (L : Set G) ≤ d.R :=
  le_pCoreIn_of_normalizes (kernel_isTwoGroup h) (inf_le_left.trans le_sup_left)
    (localGroup_normalizes_kernel h hn)

/-- The supplied Sylow marking places the kernel in the actual subgroup S. -/
theorem kernel_le_sylow {d : CharacteristicTwo.LocalData G} {I L : Subgroup G}
    (h : SourceSetup d I L) (hn : d.Yplus ≤ normalizer (L : Set G)) :
    d.Yplus ⊓ centralizer (L : Set G) ≤ d.S := by
  let K := d.Yplus ⊓ centralizer (L : Set G)
  have hKI : K ≤ I := inf_le_left.trans (le_sup_left.trans h.outside.1.2)
  have hSN : d.S ≤ normalizer (K : Set G) :=
    le_sup_right.trans (localGroup_normalizes_kernel h hn)
  obtain ⟨P, hP⟩ := h.sylow
  have hS : IsPGroup 2 d.S := hP ▸ P.isPGroup'.map I.subtype
  have hKS : IsPGroup 2 (K ⊔ d.S : Subgroup G) :=
    (kernel_isTwoGroup h).to_sup_of_normal_left' hS hSN
  have he : (K ⊔ d.S) ⊓ I = d.S := by
    rw [inf_eq_sylow_map P hKS (hP ▸ le_sup_right), hP]
  exact (le_inf le_sup_left hKI).trans he.le

omit [Finite G] in
/-- Conjugation by any element of Y₊ preserves the kernel. This bound does
not put the commutator in L. -/
theorem commutator_mem_kernel {d : CharacteristicTwo.LocalData G} {I L : Subgroup G}
    (h : SourceSetup d I L) (hn : d.Yplus ≤ normalizer (L : Set G))
    (y : d.Yplus) {c : G} (hc : c ∈ d.Yplus) (hcL : c ∈ centralizer (L : Set G)) :
    ⁅c, (y : G)⁆ ∈ d.Yplus ⊓ centralizer (L : Set G) :=
  (le_normalizer_iff_commutator_le_left.mp (localGroup_normalizes_kernel h hn))
    (commutator_mem_commutator ⟨hc, hcL⟩ (mem_sup_left y.property))

/-- The additional input is precisely 15.3.36(2), equivalently the equality
R = C_T(V) in 15.3.11(5i). It gives fixation of V, not fixation of K. -/
theorem kernel_centralizes_localModule {d : CharacteristicTwo.LocalData G}
    {I L : Subgroup G} (h : SourceSetup d I L)
    (hn : d.Yplus ≤ normalizer (L : Set G))
    (hR : d.R = (d.T : Subgroup G) ⊓ centralizer (d.V : Set G)) :
    d.Yplus ⊓ centralizer (L : Set G) ≤ centralizer (d.V : Set G) :=
  (kernel_le_localCore h hn).trans (hR.le.trans inf_le_right)

open DiagonalOuter.CoverReduction


omit [Finite G] in
private theorem precentreSetup {d : CharacteristicTwo.LocalData G} {I L : Subgroup G}
    (h : SourceSetup d I L) : MatrixImage.SourceSetup d I L :=
  { outside := h.outside
    sylow := h.sylow
    component_le := h.component_le
    component := h.component
    odd_core := h.odd_core
    component_outside := h.component_outside
    orbit_eq := h.orbit_eq
    rank_component := h.rank_component
    rank_yplus := h.rank_yplus
    rank_overgroup := h.rank_overgroup
    theta_eq := h.theta_eq
    normalizer_eq := h.normalizer_eq
    quotient_three := h.quotient_three
    yplus_quotient_three := h.yplus_quotient_three
    intersection_characteristic_two := h.intersection_characteristic_two
    residual_ne := h.residual_ne
    core_normalizes := h.core_normalizes
    component_cores_le := h.component_cores_le
    shadow := h.shadow
    characteristic_two_containment := h.characteristic_two_containment }

omit [Finite G] in
private theorem not_isPSL_of_precentre
    {d : CharacteristicTwo.LocalData G} {I L : Subgroup G} {n : ℕ}
    {c : ProjectiveMarking L (2 ^ n)} {y : d.Yplus}
    (g : LocalCover.PrecentreData d I L c y) {q : ℕ}
    (hL : ClassicalGroup.IsPSL L 3 q) : False := by
  obtain ⟨F, _, _, _, ⟨eL⟩⟩ := hL
  let _ := Atlas.sl_perfect (F := F) 3 (by decide)
  have hZ : center PSL(3,F) = ⊥ :=
    Group.IsPerfect.center_quotient_center_eq_bot SL(3,F)
  have hZL : center L = ⊥ := by
    apply (center L).eq_bot_iff_forall.mpr
    intro x hx
    apply eL.injective
    rw [map_one]
    have he : eL x ∈ center PSL(3,F) := (centerCongr eL ⟨x, hx⟩).property
    simpa only [hZ, mem_bot] using he
  have hcard : Nat.card (LocalCover.centerImage L) = 4 := by
    rw [g.center_plane, ← g.borel.second_interchange,
      card_map_of_injective (MulAut.conj g.borel.t).injective, g.borel.second_card]
  change Nat.card ((center L).map L.subtype) = 4 at hcard
  rw [hZL, Subgroup.map_bot, card_bot] at hcard
  norm_num at hcard

/-- The earlier pre-centre geometry puts the entire ordinary centralizer kernel
in the mapped centre. The field, quotient marking and actor are unchanged. -/
theorem kernel_le_center_of_marked_source
    {d : CharacteristicTwo.LocalData G} {I L : Subgroup G}
    (h : SourceSetup d I L) (earlier : LocalCover.SourceBorel.Earlier d)
    (hn : d.Yplus ≤ normalizer (L : Set G))
    {n : ℕ} (hnpos : 0 < n) (heven : Even n) (c : ProjectiveMarking L (2 ^ n))
    (y : d.Yplus) (hy : c.Diagonal (y : G))
    (hchoice : Chapter4.UniqueMaximalOvergroup (d.Y ⊔ d.S) d.M →
      d.Yplus = Stellmacher.twoResidualAmbient (d.Y ⊓ centralizer (d.V₁ : Set G)) →
      normalizer (d.V₁ : Set G) ≤ d.M ∧ normalizer (d.V₂ : Set G) ≤ d.M)
    (h7 : ThreeAlternatives.ElementaryAlternative d.M d.Mc d.V ∨
      ThreeAlternatives.ExtraspecialAlternative d.M d.Mc d.V d.action)
    (himage7 : d.action.image d.Y =
      Stellmacher.twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (hΩ : centralOmegaIn d.S ≤ d.V)
    (hVY : d.V ⊓ centralizer (d.Y : Set G) = ⊥) :
    d.Yplus ⊓ centralizer (L : Set G) ≤ (center L).map L.subtype := by
  obtain ⟨_, _, hCS, _⟩ := LocalCover.center_control_of_marked_source
    (precentreSetup h) earlier hnpos heven c y hy hchoice h7 himage7 hΩ hVY
  exact (le_inf (kernel_le_sylow h hn) inf_le_right).trans hCS.le

/-- The exact modulo-centre action conclusion in the given projective marking.
Kernel invariance puts the commutator back in K, and the constructed local
geometry puts K in Z(L). No fixation of Z(L) is assumed. -/
theorem actionModuloCenter_of_marked_source
    {d : CharacteristicTwo.LocalData G} {I L : Subgroup G}
    (h : SourceSetup d I L) (earlier : LocalCover.SourceBorel.Earlier d)
    (hn : d.Yplus ≤ normalizer (L : Set G))
    {n : ℕ} (hnpos : 0 < n) (heven : Even n) (c : ProjectiveMarking L (2 ^ n))
    (y : d.Yplus) (hy : c.Diagonal (y : G))
    (hchoice : Chapter4.UniqueMaximalOvergroup (d.Y ⊔ d.S) d.M →
      d.Yplus = Stellmacher.twoResidualAmbient (d.Y ⊓ centralizer (d.V₁ : Set G)) →
      normalizer (d.V₁ : Set G) ≤ d.M ∧ normalizer (d.V₂ : Set G) ≤ d.M)
    (h7 : ThreeAlternatives.ElementaryAlternative d.M d.Mc d.V ∨
      ThreeAlternatives.ExtraspecialAlternative d.M d.Mc d.V d.action)
    (himage7 : d.action.image d.Y =
      Stellmacher.twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (hΩ : centralOmegaIn d.S ≤ d.V)
    (hVY : d.V ⊓ centralizer (d.Y : Set G) = ⊥) :
    ActionModuloCenter d.Yplus L (y : G) := by
  have hK := kernel_le_center_of_marked_source h earlier hn hnpos heven c y hy
    hchoice h7 himage7 hΩ hVY
  intro z hz hzL
  exact hK (commutator_mem_kernel h hn y hz hzL)

/-- Both original linear branches, with the literal supplied field, equivalence,
conjugation and outer matrix. The simple PSL branch contradicts the constructed
nontrivial centre; the field-four branch retains its entire central two-cover.

The additional inputs are only the earlier uniform local conclusions in
`SourceBorel.Earlier`, 15.3.11(3), the full 15.3.7 alternatives and residual
image, 15.3.8, and C_V(Y)=1 from that natural residual action. The pre-centre
producer discharges all Borel, root, cover and image-generation calculations. -/
theorem actionModuloCenter_of_source
    {d : CharacteristicTwo.LocalData G} {I L : Subgroup G}
    (h : SourceSetup d I L) (earlier : LocalCover.SourceBorel.Earlier d)
    (hn : d.Yplus ≤ normalizer (L : Set G)) (y : d.Yplus) (hy : orderOf y = 3)
    {F : Type} [Field F] [Finite F]
    (hcase : (∃ n : ℕ, 0 < n ∧ Even n ∧ ClassicalGroup.IsPSL L 3 (2 ^ n) ∧
      Nat.card F = 2 ^ n) ∨ Nat.card F = 4)
    (e : (L ⧸ pCore 2 L) ≃* PSL(3,F))
    (α : MulAut L) (δ : Matrix.GeneralLinearGroup (Fin 3) F)
    (hconj : ConjugationOn L (y : G) α)
    (houter : Matrix.PSL3.OuterSolvable.linearConj F δ ∉ MulAut.innerSubgroup PSL(3,F))
    (hcompat : ∀ x : L, e (QuotientGroup.mk' (pCore 2 L) (α x)) =
      Matrix.PSL3.OuterSolvable.linearConj F δ (e (QuotientGroup.mk' (pCore 2 L) x)))
    (hchoice : Chapter4.UniqueMaximalOvergroup (d.Y ⊔ d.S) d.M →
      d.Yplus = Stellmacher.twoResidualAmbient (d.Y ⊓ centralizer (d.V₁ : Set G)) →
      normalizer (d.V₁ : Set G) ≤ d.M ∧ normalizer (d.V₂ : Set G) ≤ d.M)
    (h7 : ThreeAlternatives.ElementaryAlternative d.M d.Mc d.V ∨
      ThreeAlternatives.ExtraspecialAlternative d.M d.Mc d.V d.action)
    (himage7 : d.action.image d.Y =
      Stellmacher.twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (hΩ : centralOmegaIn d.S ≤ d.V)
    (hVY : d.V ⊓ centralizer (d.Y : Set G) = ⊥) :
    ActionModuloCenter d.Yplus L (y : G) := by
  have hyG : orderOf (y : G) = 3 := (Subgroup.orderOf_coe y).trans hy
  rcases hcase with ⟨n, hnpos, heven, hL, hF⟩ | hF
  · let c : ProjectiveMarking L (2 ^ n) := ⟨F, hF, e⟩
    have hd : c.Diagonal (y : G) := ⟨hyG, δ, houter, α, hconj, hcompat⟩
    obtain ⟨g⟩ := LocalCover.precentre_of_marked_source
      (precentreSetup h) earlier hnpos heven c y hd hchoice h7 himage7 hΩ hVY
    exact (not_isPSL_of_precentre g hL).elim
  · let c : ProjectiveMarking L (2 ^ 2) := ⟨F, hF, e⟩
    have hd : c.Diagonal (y : G) := ⟨hyG, δ, houter, α, hconj, hcompat⟩
    exact actionModuloCenter_of_marked_source h earlier hn (by decide) (by decide)
      c y hd hchoice h7 himage7 hΩ hVY


end CFSG.Quasithin.Chapter15.Section03.Candidates.LinearCore.KernelAction.ModuloCenter
