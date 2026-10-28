module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI.GlobalParameter.FactorInvolutions
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI.Inputs
public import CFSG.Quasithin.ChapterE.Section03.Parameters.AutomizerFF
public import Theory.GroupTheory.CentralizerResidualProducts

/-!
# The full automizer bound in the nonzero-fixed branch

Every nontrivial automizer moves one of the two original factors. Conjugating
by the specified exchange reduces to an actor moving the first factor. Its
fixed subgroup has index at least four, both for preserving and exchanging
actors. Relative-index monotonicity transfers this to the full module, and
the literal automizer fixed-space formula gives m>1 and hence s>1.

Source: Aschbacher--Smith 10.3.1, printed p.755, using I.1.6 and B.4.8(2).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI.GlobalParameter
open Chapter3.Section02 ChapterE
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  (s : SourceLinearThreeSurvivor T D)

include s

/-- The full-module index bound includes actors which move only the exchanged
factor and actors which exchange the factors. -/
theorem full_index_ge_four
    (hfix : D.fullModule ⊓ centralizer (localOrbit T L : Set G) ≠ ⊥)
    {n : G} (hn : n ∈ D.maximalLocal)
    (hsq : ∀ w ∈ D.fullModule, n*(n*w*n⁻¹)*n⁻¹ = w)
    (hmove : n ∉ centralizer (D.fullModule : Set G)) :
    4 ≤ (centralizer ({n} : Set G)).relIndex D.fullModule := by
  have hfirst {m : G} (hm : m ∈ D.maximalLocal)
      (hm2 : ∀ w ∈ D.fullModule, m*(m*w*m⁻¹)*m⁻¹ = w)
      (hmW : m ∉ centralizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G)) :
      4 ≤ (centralizer ({m} : Set G)).relIndex D.fullModule :=
    (moving_factor_index_ge_four D s hfix hm
      (fun w hw => hm2 w (survivor_moved_le s hw)) hmW).trans
      (relIndex_le_of_le_right (survivor_moved_le s) (by
        change Nat.card (D.fullModule ⧸ (centralizer ({m} : Set G)).subgroupOf D.fullModule) ≠ 0
        exact Nat.card_pos.ne'))
  by_cases hnW : n ∈ centralizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G)
  · let t := s.exchange
    let k := t⁻¹*n*t
    have ht : t ∈ D.maximalLocal := le_normalizer_componentOrbit L T s.exchange_mem
    have hk : k ∈ D.maximalLocal := D.maximalLocal.mul_mem
      (D.maximalLocal.mul_mem (D.maximalLocal.inv_mem ht) hn) ht
    have hkt : (MulAut.conj t) k = n := by dsimp [k]; simp [mul_assoc]
    have hk2 : ∀ w ∈ D.fullModule, k*(k*w*k⁻¹)*k⁻¹ = w := by
      intro w hw
      apply (MulAut.conj t).injective
      simp only [map_mul,map_inv,hkt]
      exact hsq _ ((mem_normalizer_iff.mp (D.maximalLocal_normalizes_fullModule ht) w).mp hw)
    have hkW : k ∉ centralizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) := by
      intro hc
      apply hmove
      have hVC : D.fullModule ≤ centralizer ({n} : Set G) := by
        rw [s.generated]
        apply sup_le
        · intro w hw
          exact mem_centralizer_singleton_iff.mpr (hnW w hw)
        · rintro _ ⟨w,hw,rfl⟩
          apply mem_centralizer_singleton_iff.mpr
          change (MulAut.conj t) w * n = n * (MulAut.conj t) w
          have hh := congrArg (MulAut.conj t) (hc w hw)
          simpa only [map_mul,hkt] using hh
      intro w hw
      exact mem_centralizer_singleton_iff.mp (hVC hw)
    have hi := hfirst hk hk2 hkW
    have he := relIndex_map_map_of_injective (f := (MulAut.conj t).toMonoidHom) (centralizer ({k} : Set G)) D.fullModule
      (MulAut.conj t).injective
    have hVt : D.fullModule.map (MulAut.conj t).toMonoidHom = D.fullModule :=
      mem_normalizer_iff_map_conj_eq.mp (D.maximalLocal_normalizes_fullModule ht)
    rw [map_centralizer_singleton,hkt,hVt] at he
    exact he.symm ▸ hi
  · exact hfirst hn hsq hnW

omit D s in
private theorem automizer_cyclic_fixedCodim (V : Subgroup G) [IsElementaryAbelian 2 V]
    (n : normalizer (V : Set G)) :
    fixedCodim (automizerRepresentation V)
      (zpowers (V.normalizerMonoidHom.rangeRestrict n)) =
      Nat.log 2 ((centralizer ({(n : G)} : Set G)).relIndex V) := by
  have hz : (zpowers (n : G)).subgroupOf (normalizer (V : Set G)) = zpowers n := by
    apply map_injective (normalizer (V : Set G)).subtype_injective
    rw [map_subgroupOf_eq_of_le (zpowers_le.mpr n.property),MonoidHom.map_zpowers]
    rfl
  have he : inducedAutomizer V (zpowers (n : G)) =
      zpowers (V.normalizerMonoidHom.rangeRestrict n) := by
    rw [inducedAutomizer,hz,MonoidHom.map_zpowers]
  rw [←he,fixedCodim_inducedAutomizer V _ (zpowers_le.mpr n.property),subgroupCorank,
    inf_relIndex_left,zpowers_eq_closure,centralizer_closure]

/-- Every involution of the literal full automizer has fixed codimension at least two. -/
theorem automizer_involution_codim_ge_two
    (hfix : D.fullModule ⊓ centralizer (localOrbit T L : Set G) ≠ ⊥) :
    letI : IsElementaryAbelian 2 D.fullModule := s.full_eq_local.symm ▸ D.module_elementary
    ∀ a : Automizer D.fullModule, orderOf a = 2 →
      2 ≤ fixedCodim (automizerRepresentation D.fullModule) (zpowers a) := by
  let : IsElementaryAbelian 2 D.fullModule := s.full_eq_local.symm ▸ D.module_elementary
  change ∀ a : Automizer D.fullModule, orderOf a = 2 →
    2 ≤ fixedCodim (automizerRepresentation D.fullModule) (zpowers a)
  intro a ha
  obtain ⟨n,hn⟩ := a.property
  have he : D.fullModule.normalizerMonoidHom.rangeRestrict n = a := Subtype.ext hn
  have ha2 : a*a=1 := by simpa [pow_two,ha] using pow_orderOf_eq_one a
  have hn2 : ∀ w ∈ D.fullModule, (n:G)*((n:G)*w*(n:G)⁻¹)*(n:G)⁻¹=w := by
    intro w hw
    have hh := congrArg (fun b : Automizer D.fullModule => (b.val ⟨w,hw⟩ : G)) ha2
    rw [←he] at hh
    exact hh
  have hmove : (n:G) ∉ centralizer (D.fullModule : Set G) := by
    intro hc
    have ha1 : a = 1 := by
      rw [←he]
      apply Subtype.ext
      apply MulEquiv.ext
      intro w
      apply Subtype.ext
      change (n:G)*w*(n:G)⁻¹ = w
      exact mul_inv_eq_iff_eq_mul.mpr (hc w w.property).symm
    simp [ha1] at ha
  have hfour := full_index_ge_four D s hfix
    ((source_fullModule_normalizer D).le n.property) hn2 hmove
  rw [←he,automizer_cyclic_fixedCodim]
  exact (show 2 ≤ Nat.log 2 4 by decide).trans (Nat.log_mono_right hfour)

/-- The source local m-bound on the actual full automizer. -/
theorem localM_gt_one
    (hfix : D.fullModule ⊓ centralizer (localOrbit T L : Set G) ≠ ⊥) :
    letI : IsElementaryAbelian 2 D.fullModule := s.full_eq_local.symm ▸ D.module_elementary
    1 < localM D.fullModule := by
  let : IsElementaryAbelian 2 D.fullModule := s.full_eq_local.symm ▸ D.module_elementary
  have hdim : 2 ≤ Module.finrank (ZMod 2) (Additive D.fullModule) := by
    have hc := Nat.card_le_card_of_injective (inclusion (survivor_moved_le s))
      (inclusion_injective (survivor_moved_le s))
    rw [moved_card_sixteen D s hfix] at hc
    have he := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive D.fullModule)
    rw [Nat.card_zmod] at he
    change Nat.card D.fullModule = _ at he
    rw [he] at hc
    by_contra h
    have hl : Module.finrank (ZMod 2) (Additive D.fullModule) ≤ 1 := by omega
    have hp := Nat.pow_le_pow_right (by decide : 0 < 2) hl
    norm_num at hp
    omega
  have hbound : 2 ≤ localM D.fullModule := by
    apply le_csInf ⟨_,Set.mem_insert _ _⟩
    rintro j (rfl | ⟨a,ha,rfl⟩)
    · exact hdim
    · exact automizer_involution_codim_ge_two D s hfix a ha
  omega

omit s in
/-- The global parameter input to the original fixed-space contradiction,
with every full-automizer displacement premise discharged. -/
theorem globalSAt (T : Sylow 2 G) : GlobalSAt T := by
  intro _hmany L D s hfix
  exact globalS_gt_one_of_localM_gt_one D s hfix (localM_gt_one D s hfix)

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI.GlobalParameter
