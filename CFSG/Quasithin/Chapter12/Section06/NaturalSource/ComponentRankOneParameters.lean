module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.ComponentRankOneFixedRadical
public import Theory.SpecificGroups.PSL2.QuadraticFieldRadical
public import Theory.SpecificGroups.PSL2.OuterSolvable.SmallDegreeTwoGroup
public import Theory.SpecificGroups.PSL2.CubicNormalizerCongruence
public import Theory.GroupTheory.TwoThreeSolvable

/-!
# The inner action and congruence of the original PSL2 parameter

The small ternary fields give a solvable group or the already excluded
alternating-six model. For larger odd fields, a Sylow-fixing involution
is inner or a quadratic field involution. The latter has radical-free
fixed group, contradicting the original condition (*).

The same original module involution fixes both the transported cubic
intersection and a full Sylow two-subgroup. Its inner centralizer has
order q minus one or q plus one, divisible by twelve. Thus q is congruent
to plus or minus one modulo twelve, with every original marking retained.
Source: Aschbacher--Smith, proof of 12.6.26, printed p.833.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)
  (hz : z ≠ 1)
  (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
  (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
  (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
    Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
  {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
  (hn : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH H))
  (c : (D.fullSetup hZ T z).SelectedComponent H) (a : c.ActionMarking)



include hz hTV hTz hbound hH hn a in
private theorem original_linearTwo_field_large
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    {F : Type*} [Field F] [Finite F] {p n : ℕ}
    (hp : p.Prime) (ho : Odd p) (hn2 : n ≤ 2) (hF : Nat.card F = p^n)
    (e : Nonabelian.Setup.star H c.K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :
    3 < p ∧ 0 < n := by
  have hn0 : 0 < n := by
    have h := Finite.one_lt_card (α := F)
    rw [hF] at h
    by_contra hh
    have : n = 0 := by omega
    simp [this] at h
  have hp2 := hp.two_le
  have hpodd := Nat.odd_iff.mp ho
  by_contra hh
  have hp3 : p = 3 := by omega
  subst p
  have hcase : n = 1 ∨ n = 2 := by omega
  rcases hcase with rfl | rfl
  · have hcard := Matrix.ProjectiveSpecialLinearGroup.psl2_card_twice (F := F)
      (hF ▸ ho.pow)
    have hc : Nat.card (Nonabelian.Setup.star H c.K) = 12 := by
      rw [←Nat.card_congr e.toEquiv,hF] at hcard
      norm_num at hcard
      omega
    let : Group.IsSolvable (Nonabelian.Setup.star H c.K) :=
      isSolvable_of_prime_dvd_card_eq_two_or_three _ (by
        intro r hr hd
        rw [hc] at hd
        have hdiv : r ∣ 2^2 * 3 := hd
        rcases hr.dvd_mul.mp hdiv with h | h
        · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow h))
        · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp h))
    let := c.component.2
    let : IsSimpleGroup (Nonabelian.Setup.star H c.K) :=
      S.original_selectedComponent_simple D hZ z hz hTV hTz hbound hH hn c a hTI hns
    exact Group.IsPerfect.not_isSolvable (Nonabelian.Setup.star H c.K) inferInstance
  · exact S.original_selectedComponent_not_alternatingSix D hZ z hz hTz hH c a
      ⟨e.trans (Atlas.Comparisons.Exceptional.psl2Card9EquivAlt6 hF)⟩

include hz hTV hTz hbound hH hn a in
/-- Every nonidentity original module action is inner on its actual odd PSL2 model. -/
theorem SourceHypothesis.original_linearTwo_module_inner
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    {F : Type*} [Field F] [Finite F] {p n : ℕ}
    (hp : p.Prime) (ho : Odd p) (hn2 : n ≤ 2) (hF : Nat.card F = p^n)
    (e : Nonabelian.Setup.star H c.K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
    (b : MulAut (Nonabelian.Setup.star H c.K))
    (hb : b ∈ (V.subgroupOf c.localActor).map a.action) (hb2 : orderOf b = 2) :
    ∃ x, MulAut.congr e b = MulAut.conj x := by
  obtain ⟨hp3,hn0⟩ := original_linearTwo_field_large S D hZ z hz hTV hTz hbound hH hn c a
    hTI hns hp ho hn2 hF e
  have hl : 3 < Nat.card F := by
    rw [hF]
    exact hp3.trans_le (Nat.le_pow hn0)
  have hodd : GorensteinWalter.IsOddPrimePower (Nat.card F) := ⟨p,n,hp,ho,hn0,hF⟩
  obtain ⟨R,hR⟩ := S.original_action_module_fixes_component_sylow D hZ z hz hTV hTz hbound hH hn c a
  let P := R.mapSurjective (f := e.toMonoidHom) e.surjective
  let α := MulAut.congr e b
  have hα : orderOf α = 2 := ((MulAut.congr e).orderOf_eq b).trans hb2
  have hP : ∀ x ∈ P, α x = x := by
    rintro _ ⟨x,hx,rfl⟩
    change e (b (e.symm (e x))) = e x
    rw [e.symm_apply_apply,hR b hb x hx]
  rcases Theory.PSL2.odd_sylow_fixed_involution_inner_or_field hodd hl P α hα hP with hi | ⟨σ,β,hσ,he⟩
  · exact hi
  · have hnEq : n = 2 := by
      have hd := orderOf_dvd_natCard σ
      rw [hσ,FiniteField.card_ringAut_of_card_prime_pow hp hF] at hd
      have htwo := Nat.le_of_dvd hn0 hd
      omega
    subst n
    have hrad := Theory.PSL2.quadratic_field_involution_radical_bot hp ho hp3 hF σ hσ
    let j := MulAut.fixedSubgroupCongr β α
    let jR := (j.subgroupMap (solvableRadical α.fixedSubgroup)).trans
      (MulEquiv.subgroupCongr (map_solvableRadical_equiv j))
    have htwo : IsPGroup 2 (solvableRadical (MulAut.congr β α).fixedSubgroup) := by
      rw [he,hrad]
      exact IsPGroup.of_subsingleton 2 _
    exact (S.original_model_fixed_radical_not_two D hZ z hz hTV hTz hbound hH hn c a hTI hns e
      (Theory.PSL2.OuterSolvable.SmallDegreeSquares.outer_isPGroup_two hp ho (by decide) hF)
      b hb hb2 (htwo.of_equiv jR.symm)).elim

include hz hTV hTz hbound hH hn a in
/-- The same original involution fixes the cubic line and a full Sylow two,
forcing the source congruence q = plus or minus one modulo twelve. -/
theorem SourceHypothesis.original_linearTwo_parameter_mod_twelve
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    {F : Type*} [Field F] [Finite F] {p n : ℕ}
    (hp : p.Prime) (ho : Odd p) (hn2 : n ≤ 2) (hF : Nat.card F = p^n)
    (e : Nonabelian.Setup.star H c.K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :
    3 < p ∧ 0 < n ∧ ((p^n) % 12 = 1 ∨ (p^n) % 12 = 11) := by
  obtain ⟨hp3,hn0⟩ := original_linearTwo_field_large S D hZ z hz hTV hTz hbound hH hn c a hTI hns hp ho hn2 hF e
  refine ⟨hp3,hn0,?_⟩
  obtain ⟨b,hb,hb2,⟨P,hP⟩,hthree⟩ := S.original_selectedComponent_model_fixed_cubic
    D hZ z hz hTV hTz hbound hH hn c a hTI hns e
  have hb2' : orderOf b = 2 := ((MulAut.congr e).orderOf_eq b).symm.trans hb2
  obtain ⟨x,hx⟩ := S.original_linearTwo_module_inner D hZ z hz hTV hTz hbound hH hn c a hTI hns hp ho hn2 hF e b hb hb2'
  have hoX : orderOf x = 2 :=
    (MulAut.conj_orderOf_of_center_eq_bot (GorensteinWalter.psl2_center_eq_bot F) x).symm.trans (hx ▸ hb2)
  rw [hx,MulAut.fixedSubgroup_conj] at hthree
  have hPC : (P : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)) ≤ centralizer ({x} : Set _) := by
    intro y hy
    have h := hP y hy
    rw [hx] at h
    exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp h).symm
  have hodd : GorensteinWalter.IsOddPrimePower (Nat.card F) := ⟨p,n,hp,ho,hn0,hF⟩
  obtain ⟨m,hm,⟨eP⟩⟩ := GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model F hodd P
  obtain ⟨W,hWP,hW⟩ := GorensteinWalter.exists_kleinFour_le_of_dihedral_subgroup_mulEquiv
    (P : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)) hm eP
  have hfour : 4 ∣ Nat.card (centralizer ({x} : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F))) :=
    hW.card_four ▸ card_dvd_of_le (hWP.trans hPC)
  have htwelve := (by decide : Nat.Coprime 3 4).mul_dvd_of_dvd_of_dvd hthree hfour
  have hxc : GorensteinWalter.IsInvolution x := ⟨by intro h; rw [h,orderOf_one] at hoX; omega,
    by simpa only [hoX] using pow_orderOf_eq_one x⟩
  rcases Theory.PSL2.involution_centralizer_card_cases hodd x hxc with hc | hc
  all_goals rw [hc,hF] at htwelve
  all_goals have hlarge : 3 < p^n := hp3.trans_le (Nat.le_pow hn0)
  all_goals omega

end CFSG.Quasithin.Chapter12.Section06
