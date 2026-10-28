module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalJankoFourKernel
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalBinaryDegree
public import CFSG.Quasithin.Chapter6.SourceReduction.LocalCentralization.ModuleRecognition
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeZeroCoreDegree
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeRankOneSelection
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeSylowSevenFixed

/-!
# The original Hall and module structure in the binary-triality row

The original degree-two theorem makes the left Cartan equal to the
escaping cubic inside the same containing component. Its whole Borel
therefore centralizes omega. The full reduced-layer theorem identifies
all of the original [W,L] as one or two A₅ modules.

The original right Hall subgroup is identified with the field torus of
the literal residual quotient PSL₂(8). This uses the original right Borel
and Hall condition, without assuming trivial two-core of a generated pair.
Consequently this SAME subgroup has order seven. The seven-free left
quotient automorphism group and coprime fixed lifts show that it fixes the
entire original L-span of omega. That span is a noncentral reduced input
at degree two and has order at least sixteen. The seven-centralizer covers
L/O₂(L) by the actual inclusion map.

The concluding original-input sieve retains every earlier exclusion,
including J₄, and adds these consequences to its surviving rank-two row.
The binary-triality ambient exclusion and the other containing-component
and inverted-cubic branches still need proof. In particular the fixed
span is not identified with its image modulo the containing two-core.

Source: Aschbacher--Smith 5.1.10--13, printed pp.634--638, with the
B.2.14 omega-span and E.2.13(4) constituent bound, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.BinaryOmega
variable {G : Type*} [Group G] [Finite G]

private theorem right_cartan_equiv_units
    {T : Sylow 2 G} {L H A B R : Subgroup G} {m : ℕ}
    (d : Prime.RightData T L H B R) (c : CartanPair T L H A B)
    (hm : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 (2 ^ m)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
      Nat.card F = 2 ^ m ∧ Nonempty ((B ⊓ R : Subgroup G) ≃* Fˣ) := by
  obtain ⟨P,hP⟩ := d.right_sylow
  have hPlit : (P : Subgroup R) = (Global.sourceS L H ⊓ R).subgroupOf R := by
    apply map_injective R.subtype_injective
    rw [map_subgroupOf_eq_of_le (show Global.sourceS L H ⊓ R ≤ R from inf_le_right)]
    exact hP
  have hN : (normalizer (P : Set R)).map R.subtype =
      ChapterF.Source.borel R (Global.sourceS L H) := by
    change (normalizer ((P : Subgroup R) : Set R)).map R.subtype = _
    rw [hPlit,←subgroupOf_normalizer_eq (show Global.sourceS L H ⊓ R ≤ R from inf_le_right),
      subgroupOf_map_subtype, inf_comm]
    rfl
  let C := (B ⊓ R).subgroupOf R
  have hCN : C ≤ normalizer (P : Set R) := by
    apply (map_le_map_iff_of_injective R.subtype_injective).mp
    rw [map_subgroupOf_eq_of_le inf_le_right,hN,d.right_borel]
    exact le_sup_right
  have hgen : (P : Subgroup R) ⊔ C = normalizer (P : Set R) := by
    apply map_injective R.subtype_injective
    rw [Subgroup.map_sup,hP,map_subgroupOf_eq_of_le inf_le_right,hN,d.right_borel]
  have hBo : Odd (Nat.card B) := by
    rw [←Nat.card_congr (subgroupOfEquivOfLe c.right_le).toEquiv]
    exact OddHall.odd_hall_odd c.right_hall
  have hCo : Odd (Nat.card C) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (show B ⊓ R ≤ R from inf_le_right)).toEquiv]
    exact hBo.of_dvd_nat (card_dvd_of_le (show B ⊓ R ≤ B from inf_le_left))
  obtain ⟨k,hk⟩ := P.isPGroup'.exists_card_eq
  have hd : Disjoint (P : Subgroup R) C := disjoint_of_coprime_natCard (by
    rw [hk]
    exact (Nat.coprime_two_left.mpr hCo).pow_left k)
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := m) (by
    simpa only [Nat.card_eq_fintype_card] using hF)
  let e' := e.trans (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := F)).symm
  let q := e'.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 R))
  have hq : Function.Surjective q := e'.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : q.ker = pCore 2 R := by
    ext x
    exact e'.map_eq_one_iff.trans (QuotientGroup.eq_one_iff _)
  obtain ⟨f⟩ := Matrix.SpecialLinearGroup.sylow_normalizer_complement_equiv_units
    q hq P (hker ▸ pCore_isPGroup.le_sylow_of_normal P) C hCN hd hgen
  exact ⟨F,inferInstance,inferInstance,inferInstance,hF,
    ⟨(subgroupOfEquivOfLe (show B ⊓ R ≤ R from inf_le_right)).symm.trans f⟩⟩


/-- The actual rank-one residual and the original right Hall condition give
its field torus, without the global prime-pair or zero-core hypothesis. -/
theorem right_hall_card_of_linear_residual
    {T : Sylow 2 G} {L H A B : Subgroup G} {m : ℕ}
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hm : 1 < m)
    (hr : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 (2^m)) :
    Nat.card B = 2^m-1 := by
  have hqs : IsQuasisimple ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) := by
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hr
    have hl : 3 < Nat.card F := by
      rw [hF]
      exact (by decide : 3 < 2^2).trans_le
        (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 2 ≤ m))
    let : IsQuasisimple SL(2,F) := {
      toIsPerfect := GorensteinWalter.sl2_isPerfect_of_card_gt_three F hl
      simple := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hl }
    let : IsQuasisimple PSL(2,F) := IsQuasisimple.of_surjective
      (QuotientGroup.mk' (center SL(2,F))) (QuotientGroup.mk'_surjective _)
    exact IsQuasisimple.of_mulEquiv e.symm
  let d := Prime.rankOne_residual_rightData hTL hH c (.linear m (by omega) hr) hqs
  let e := (pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective
  let q := QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
  obtain ⟨F,_,_,_,hF,⟨a⟩⟩ := right_cartan_equiv_units d c (hr.of_mulEquiv q.symm)
  have he : B ⊓ residual H = B := inf_eq_left.mpr (Global.right_cartan_le_residual c)
  rw [he] at a
  rw [Nat.card_congr a.toEquiv,Nat.card_units,hF]

/-- The surviving triality row has its full original left moved module,
and the original right Hall subgroup has order seven and fixes the L-span
of omega. The two source field degrees are kept distinct. -/
theorem original_binary_triality_module_and_hall
    {T : Sylow 2 G} {L W H A B K Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hKH : K ≤ H) (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (hKT : K ⊔ (T : Subgroup G) = H)
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) (hKC : K ≤ C.map Y.subtype)
    (hm : Triality.Standard.IsTrialityGroupAt 2 (C ⧸ pCore 2 C)) :
    n = 2 ∧ Nat.card A = 3 ∧ A ≤ C.map Y.subtype ∧
      localBorel T L ≤ omegaCentralizer T ∧
      IsOneOrTwoA5Modules L (layer L W) ∧ Nat.card B = 7 ∧
      B ≤ centralizer
        (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L : Set G) := by
  have hn := original_binary_triality_degree_two h hH hgen c hKH hK hKT horbit
    hY hescape C hC hKC hm
  have ha : Nat.card A = 3 := by
    simpa [hn] using (c.left_cyclic_and_card h.sylow_normalizes h.linear).2
  have hc := original_container_centralizes h hH c hKH hK hKT horbit hY hescape C hC hKC hm
  obtain ⟨hKR,hCn,hr⟩ := LocalSieve.binaryTriality_residual_section h.qtke hKH
    hH.1.1.2 hK hKT horbit hY hescape C hC hKC hm
  have hHC := (residual_le_omegaCentralizer_iff hH.1.1.2).mp ((hKR ▸ hKC).trans hc)
  obtain ⟨D,hDA,hDC,hDc,_⟩ := LocalSieve.binaryTriality_escape_cubic h hH hgen c
    hKH hK hKT horbit hY hescape C hC hKC hm
  have hDAeq : D = A := eq_of_le_of_card_ge hDA (by rw [hDc,ha])
  have hAC : A ≤ C.map Y.subtype := hDAeq ▸ hDC
  have hBorel : localBorel T L ≤ omegaCentralizer T := by
    rw [←c.left_sup_intersection h.sylow_normalizes]
    exact sup_le (inf_le_left.trans sylow_le_omegaCentralizer) (hAC.trans hc)
  obtain ⟨F,_,_,hF,⟨f⟩⟩ := h.linear
  obtain ⟨a⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
    (show Nat.card F = 4 by simpa [hn] using hF)
  have hmodule := h.layer_oneOrTwoA5_of_marked_borel hH hHC (f.trans a) hBorel
  have hb : Nat.card B = 7 := by
    simpa using right_hall_card_of_linear_residual h.sylow_normalizes hH c
      (m := 3) (by decide) (by simpa using hr)
  exact ⟨hn,ha,hAC,hBorel,hmodule,hb,
    (c.seven_centralizes_omega_span_iff h (.inl hn) le_rfl hb).mpr
      ((c.right_le.trans inf_le_right).trans hHC)⟩

/-- The same original seven-group fixes a noncentral reduced omega-span
of order at least sixteen. This retains the whole span, including its
possible intersection with the containing two-core. -/
theorem original_binary_triality_fixed_omega_span
    {T : Sylow 2 G} {L W H A B K Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hKH : K ≤ H) (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (hKT : K ⊔ (T : Subgroup G) = H)
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) (hKC : K ≤ C.map Y.subtype)
    (hm : Triality.Standard.IsTrialityGroupAt 2 (C ⧸ pCore 2 C)) :
    let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L
    Input KnownSimple.IsKnownSimple T L U 2 ∧
      16 ≤ Nat.card U ∧ Nat.card B = 7 ∧ B ≤ centralizer (U : Set G) ∧
      ∃ e : ((L ⊓ centralizer (B : Set G) : Subgroup G) ⧸
          pCore 2 (L ⊓ centralizer (B : Set G) : Subgroup G)) ≃* (L ⧸ pCore 2 L),
        ∀ x : (L ⊓ centralizer (B : Set G) : Subgroup G),
          e (QuotientGroup.mk' (pCore 2 (L ⊓ centralizer (B : Set G) : Subgroup G)) x) =
            QuotientGroup.mk' (pCore 2 L) (inclusion inf_le_left x) := by
  obtain ⟨hn,_,_,_,_,hb,hfix⟩ := original_binary_triality_module_and_hall
    h hH hgen c hKH hK hKT horbit hY hescape C hC hKC hm
  have hHC := (original_container_module_restrictions h hH hgen c hKH hK hKT horbit
    hY hescape C hC hKC hm).2.1
  have hfixed := h.centralOmega_disjoint_of_outside_centralizes hH hHC
  have hLC : ¬ L ≤ omegaCentralizer T := by
    intro hc
    have hW : W ≠ ⊥ := fun he => h.noncentral (by rw [he,commutator_bot_left])
    obtain ⟨z,hz1⟩ := ne_bot_iff_exists_ne_one.mp
      (inf_centerIn_ne_bot T.isPGroup' hW h.reduced_le_sylow
        (le_sup_right.trans (reduced_normalizes h.reduced)))
    let := h.reduced.2.1
    have hz : (z : G) ∈ omegaOneCenterAmbient (T : Subgroup G) :=
      (mem_omegaOneCenterAmbient_iff _ _).mpr
        ⟨h.reduced_le_sylow z.property.1,
          elemPow_eq_one_of_isElementaryAbelian (p := 2) (z : G) z.property.1,
          z.property.2.2⟩
    exact hz1 (Subtype.ext (mem_bot.mp (hfixed.le ⟨hz,(le_centralizer_iff.mp hc) hz⟩)))
  let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L
  have hu : Input KnownSimple.IsKnownSimple T L U 2 := hn ▸ h.omega_span_input hLC
  have hsize := hu.moved_reduced_size.2.2
  have hle : ⁅U,L⁆ ≤ U := le_normalizer_iff_commutator_le_left.mp
    (le_sup_left.trans (reduced_normalizes hu.reduced))
  refine ⟨hu,?_,hb,hfix,c.seven_centralizer_quotient h (.inl hn) le_rfl hb⟩
  exact hsize.trans (Nat.card_le_card_of_injective (inclusion hle) (inclusion_injective hle))

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.BinaryOmega

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
open Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]

/-- The original component sieve retains every earlier exclusion and
recognizes the whole left module and both original Hall orders in its
remaining binary-triality row. No extra source premise is supplied. -/
theorem localCartan_escape_seed_binary_endpoint_reduction
    {T : Sylow 2 G} {L W H A B Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G)) :
    ∃ K : Subgroup G, K ≤ H ∧ (K.subgroupOf H).IsCComponent ∧
      IsQuasisimple (K ⧸ pCore 2 K) ∧ K ⊔ (T : Subgroup G) = H ∧
      K ∈ Chapter1.L G (T : Subgroup G) ∧
      componentOrbit K (T : Subgroup G) = residual H ∧
      ∃ C : Subgroup Y, C.IsCComponent ∧ K ≤ C.map Y.subtype ∧
        residual H < componentOrbit (C.map Y.subtype) (T : Subgroup G) ∧
        ((componentOrbit (C.map Y.subtype) (T : Subgroup G)).subgroupOf Y).Normal ∧
        (K.subgroupOf Y).map (QuotientGroup.mk' (pCore 2 Y)) <
          C.map (QuotientGroup.mk' (pCore 2 Y)) ∧
        ¬ SolvableSylowOvergroups (C ⧸ pCore 2 C) ∧
        (∀ m : ℕ, 0 < m → ¬ (ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 3 (2 ^ m) ∨
          IsSL (C ⧸ pCore 2 C) 3 (2 ^ m) ∨ IsSU (C ⧸ pCore 2 C) 3 (2 ^ m))) ∧
        (RankTwoTheoremC (C ⧸ pCore 2 C) →
          K = residual H ∧ C.Normal ∧
          Triality.Standard.IsTrialityGroupAt 2 (C ⧸ pCore 2 C) ∧
          ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 8 ∧
          n = 2 ∧ Nat.card A = 3 ∧ A ≤ C.map Y.subtype ∧
          localBorel T L ≤ omegaCentralizer T ∧
          IsOneOrTwoA5Modules L (layer L W) ∧ Nat.card B = 7 ∧
          B ≤ centralizer
            (conjugateSpanBy (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) L : Set G)) ∧
        (∀ p : ℕ, p.Prime → Odd p →
          ¬ ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 2 p) ∧
        ¬ ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 2 25 ∧
        C.Normal ∧
        ¬ Nonempty ((C ⧸ pCore 2 C) ≃* Janko1.Model) ∧
        (∀ p : ℕ, p.Prime → Odd p →
          ¬ (ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 3 p ∨
            ClassicalGroup.IsPSU (C ⧸ pCore 2 C) 3 p ∨
            IsSL (C ⧸ pCore 2 C) 3 p ∨ IsSU (C ⧸ pCore 2 C) 3 p)) ∧
        ¬ Nonempty ((C ⧸ pCore 2 C) ≃* Janko4.Model) := by
  obtain ⟨K,hKH,hK,hqs,hKT,hKL,hR,C,hC,hKC,hlt,hn,hqlt,hsol,hternary,hrank,hprime,h25,hCn,hJ,hOdd,hJ4⟩ :=
    localCartan_escape_seed_jankoFour_excluded h hH hgen c hY hescape
  refine ⟨K,hKH,hK,hqs,hKT,hKL,hR,C,hC,hKC,hlt,hn,hqlt,hsol,hternary,?_,hprime,h25,hCn,hJ,hOdd,hJ4⟩
  intro hm
  obtain ⟨he,hnormal,ht,hsection⟩ := hrank hm
  exact ⟨he,hnormal,ht,hsection,BinaryOmega.original_binary_triality_module_and_hall
    h hH hgen c hKH hKL hKT hR hY hescape C hC hKC ht⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
