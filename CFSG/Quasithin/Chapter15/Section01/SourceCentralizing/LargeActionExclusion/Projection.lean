module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.SourceInterface
public import Theory.GroupTheory.NormalizedSupCard

/-!+# The projected seed distinguishes the two surviving Case-I rows

Every nonidentity element of the exchanged seed gives a nonidentity central
involution of T by multiplication with its conjugate in Z1. If that seed
element centralized L, the actual singleton-centralizer hypothesis would
put L in Mc. Thus the projection of Z2 to the moved module is faithful.
When that projection is a line, Z1 has order two, eliminating source row (6).

Source: Aschbacher--Smith 15.1.29, first paragraph, printed p.1103.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open ChapterD ChapterD.UniqueFactor Section03 Section03.InitialSource ChapterA.Section05To06 ChapterB
variable {G : Type*} [Group G] [Finite G]
namespace CaseIComponentData
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- The exchanged seed has no nonidentity element centralizing the same L. -/
theorem ExchangedSource.seed_inf_centralizer_eq_bot
    {d : CaseIComponentData T M Mc V} (s : d.ExchangedSource)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (t : G) (ht : t ∈ (T : Subgroup G)) (htS : t ∉ d.S) :
    d.Z2 t ⊓ centralizer (d.L : Set G) = ⊥ := by
  let := h.elementary
  apply bot_unique
  rintro b ⟨⟨a,ha,rfl⟩,hc⟩
  by_cases ha1 : a = 1
  · simp [ha1]
  exfalso
  have hZV := d.Z1_le_fixed.trans inf_le_left
  have hZT : d.Z1 ≤ (T : Subgroup G) := by
    intro z hz
    exact thompsonJ_le _ _ ((mem_omegaOneCenterAmbient_iff _ _).mp
      (h.thompsonFixed_le_omega T hM (d.Z1_le_fixed hz))).1
  have haS : a ∈ d.S := ⟨hZT ha,fun z hz =>
    (V.le_centralizer (hZV ha)) z (hZV hz)⟩
  have haOm : a ∈ omegaOneCenterAmbient d.S :=
    (mem_omegaOneCenterAmbient_iff _ _).mpr
      ⟨haS,elemPow_eq_one_of_isElementaryAbelian a (hZV ha),fun x hx => (hx.2 a ha).symm⟩
  have hbP : t*a*t⁻¹ ∈ d.nineMovingPlane := by
    rw [←(s.exchanges t ht htS).1]
    exact mem_map_of_mem _ (s.marked_le_fixed ha)
  have hbV : t*a*t⁻¹ ∈ V :=
    (le_sup_right.trans_eq s.planes_sup) hbP
  have hz := indexTwo_diagonal_mem_omegaCenter d.S (T : Subgroup G) d.S_le_T s.index t ht htS a haOm
    (V.le_centralizer (hZV ha) _ hbV).symm
  have hzne : a*(t*a*t⁻¹) ≠ 1 := by
    intro he
    have haa : t*a*t⁻¹ = a := by
      have ha2 := elemPow_eq_one_of_isElementaryAbelian (p := 2) a (hZV ha)
      have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using ha2)
      exact (eq_inv_of_mul_eq_one_right he).trans hai
    have habot : a ∈ (⊥ : Subgroup G) := by
      rw [←s.planes_inf]
      exact ⟨s.marked_le_fixed ha,haa ▸ hbP⟩
    exact ha1 (mem_bot.mp habot)
  apply d.L_not_le_Mc
  apply le_trans _ (central_involution_centralizer_le_partner T hu hz hzne)
  intro l hl
  rw [mem_centralizer_singleton_iff]
  have hla := d.L_component.1 hl a ha
  have hlb := hc l hl
  change l*(t*a*t⁻¹) = (t*a*t⁻¹)*l at hlb
  calc
    l*(a*(t*a*t⁻¹)) = (l*a)*(t*a*t⁻¹) := by group
    _ = (a*l)*(t*a*t⁻¹) := by rw [hla.symm]
    _ = a*((t*a*t⁻¹)*l) := by rw [mul_assoc,hlb]
    _ = (a*(t*a*t⁻¹))*l := by group

/-- A line projection of the literal Z2 has the same order as Z1.
Consequently only the four-dimensional Nine row remains. -/
theorem ExchangedSource.row_four_of_line_projection
    {d : CaseIComponentData T M Mc V} (s : d.ExchangedSource)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (t : G) (ht : t ∈ (T : Subgroup G)) (htS : t ∉ d.S)
    (hU : IsElementaryAbelian 2 (d.U t))
    {ZU : Subgroup G} (hZU : ZU ≤ d.UL t) (hcard : Nat.card ZU = 2)
    (hsplit : d.UL t ⊔ (d.U t ⊓ centralizer (d.L : Set G)) = d.U t)
    (hdis : d.UL t ⊓ (d.U t ⊓ centralizer (d.L : Set G)) = ⊥)
    (hproj : d.Z2 t ⊔ (d.U t ⊓ centralizer (d.L : Set G)) =
      ZU ⊔ (d.U t ⊓ centralizer (d.L : Set G))) :
    d.row = .four ∧ Nat.card d.Z1 = 2 ∧
      Nat.card d.nineFixedPlane = 4 ∧ Nat.card d.nineMovingPlane = 4 := by
  let := hU
  let C := d.U t ⊓ centralizer (d.L : Set G)
  have hZ2U : d.Z2 t ≤ d.U t := le_conjugateSpanBy _ _
  have hZUU : ZU ≤ d.U t := hZU.trans (le_sup_left.trans_eq hsplit)
  have hnorm (A : Subgroup G) (hA : A ≤ d.U t) : C ≤ normalizer (A : Set G) :=
    (show C ≤ d.U t from inf_le_left).trans
      ((d.U t).le_centralizer.trans ((centralizer_le hA).trans
        (Subgroup.centralizer_le_normalizer _)))
  have hZ2C : Disjoint (d.Z2 t) C := disjoint_iff_inf_le.mpr (by
    exact (inf_le_inf_left _ (show C ≤ centralizer (d.L : Set G) from inf_le_right)).trans
      (s.seed_inf_centralizer_eq_bot hM hu h t ht htS).le)
  have hZUC : Disjoint ZU C := disjoint_iff_inf_le.mpr
    ((inf_le_inf_right C hZU).trans hdis.le)
  have hcards : Nat.card (d.Z2 t) * Nat.card C = Nat.card ZU * Nat.card C := by
    rw [←card_sup_eq_mul_of_normalizes_of_disjoint _ _ (hnorm _ hZ2U) hZ2C,
      hproj,card_sup_eq_mul_of_normalizes_of_disjoint _ _ (hnorm _ hZUU) hZUC]
  have he : Nat.card (d.Z2 t) = Nat.card ZU :=
    Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := C)) hcards
  have hZ1 : Nat.card d.Z1 = 2 :=
    (card_map_of_injective (MulAut.conj t).injective).symm.trans (he.trans hcard)
  rcases s.sizes with hs | hs
  · exact hs
  · have := hs.2.1
    omega

/-- The actual natural-module conclusion of 15.1.28 removes row (6)
before the remaining parabolic contradiction of 15.1.29. -/
theorem ExchangedSource.row_four_of_natural_moved_module
    {d : CaseIComponentData T M Mc V} (s : d.ExchangedSource)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (t : G) (ht : t ∈ (T : Subgroup G)) (htS : t ∉ d.S)
    (hnatural : d.HasNaturalMovedModule t) :
    d.row = .four ∧ Nat.card d.Z1 = 2 ∧
      Nat.card d.nineFixedPlane = 4 ∧ Nat.card d.nineMovingPlane = 4 := by
  obtain ⟨hU,hE,hn,n,hn',e,x,hact,hsplit,hdis,ZU,hZU,hcard,hZS,hproj,hML⟩ := hnatural
  exact s.row_four_of_line_projection hM hu h t ht htS hU hZU hcard hsplit hdis hproj

/-- The same source component now satisfies the existing Nine interface,
so the final parabolic argument can use its original source controls. -/
theorem ExchangedSource.nineSource_of_natural_moved_module
    {d : CaseIComponentData T M Mc V} (s : d.ExchangedSource)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (t : G) (ht : t ∈ (T : Subgroup G)) (htS : t ∉ d.S)
    (hnatural : d.HasNaturalMovedModule t) : d.NineSource := by
  obtain ⟨hr,hz,hf,hm⟩ := s.row_four_of_natural_moved_module hM hu h t ht htS hnatural
  exact {
    row := hr
    marked_card := hz
    fixed_card := hf
    moving_card := hm
    odd_core := s.odd_core
    quasisimple := s.quasisimple
    local_component := s.local_component
    component_sylow := s.component_sylow
    centralizer_sylow := s.centralizer_sylow
    outside_M := s.outside_M
    ordinary := s.ordinary
    planes_sup := s.planes_sup
    planes_inf := s.planes_inf
    marked_le_fixed := s.marked_le_fixed
    index := s.index
    sylow_normal := s.sylow_normal
    fixes_planes := s.fixes_planes
    fixed_centralizer_index := s.fixed_centralizer_index
    exchanges := s.exchanges
    exchange_exists := s.exchange_exists
    cubic_escape := s.cubic_escape
    cubic_idempotent := s.cubic_idempotent
    cubic_two_perfect := s.cubic_two_perfect
    cubic_normalizes := s.cubic_normalizes
    cubic_commutator := s.cubic_commutator
    cubic_moving := s.cubic_moving
    fixed_noncentral := s.fixed_noncentral
    seed_bound := s.seed_bound
    moving_noncentral := s.moving_noncentral
    core_nontrivial := s.core_nontrivial
    characteristic_control := s.characteristic_control
    core_normalizer := s.core_normalizer
    sylow_normalizes_MZ := s.sylow_normalizes_MZ
    sylow_normalizes_Q1 := s.sylow_normalizes_Q1 }

end CaseIComponentData
end CFSG.Quasithin.Chapter15.Section01
