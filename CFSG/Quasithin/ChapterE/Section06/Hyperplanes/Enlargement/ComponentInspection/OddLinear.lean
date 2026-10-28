module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.ComponentInspection.Transport
public import Theory.SpecificGroups.PSL2.PrimeSylowFixers
public import GorensteinWalter.PSL2Center
public import CFSG.Quasithin.MainConverse.OddClassicalLocal.PSL2Even
public import Theory.SpecificGroups.SL2.SmallOddComparisons
public import Theory.SpecificGroups.PSL3Three.SylowFixers
public import Theory.SpecificGroups.PSL3Three.Cardinality
public import Theory.SpecificGroups.PSL3Three.InnerInvolutionCentralizer
public import Theory.SpecificGroups.GL2.ThreeSolvable
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support

/-!
# Odd-linear fixed-component inspections for E.6.22

For Fermat–Mersenne PSL₂, perfection excludes parameter three, and the
prime-field Sylow-fixer theorem makes every pointwise fixer inner. Triviality
of the center retains the involution order of its conjugator. The independent
matrix centralizer calculation then makes its fixed subgroup a two-group.

For PSL₃(3), a central Sylow involution supplies a subgroup of order two of
inner pointwise fixers. The full fixer has order at most two, so every fixer
is inner. Its actual fixed subgroup is GL₂(3), which is solvable. Field and
automorphism transport preserve the actual order-two action and its common
fixed subgroup; solvability excludes every ordinary component.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, E.6.8(5), printed pp.247–248, and the component
inspection in the proof of E.6.22, printed p.254 (PDF p.265).
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.ComponentInspection

variable {Y : Type*} [Group Y] [Finite Y]

omit [Finite Y] in
private theorem parameter_ge_five [Group.IsPerfect Y] {p : ℕ}
    (hp : IsFermatOrMersennePrime p) (hY : ClassicalGroup.IsPSL Y 2 p) : 5 ≤ p := by
  have hp2 : p ≠ 2 := by
    rintro rfl
    rcases hp.2 with ⟨k, hk⟩ | ⟨k, hk⟩
    · have hh : 2 ≤ 2 ^ (2 ^ k) := Nat.le_pow (by positivity)
      omega
    · have hk0 : k ≠ 0 := by intro he; simp [he] at hk
      have hh := dvd_pow_self 2 hk0
      rw [← hk] at hh
      norm_num at hh
  have hp3 : p ≠ 3 := by
    intro h
    obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hY
    exact Matrix.ProjectiveSpecialLinearGroup.not_perfect_of_card_three (hF.trans h)
      (Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective)
  have ho : Odd p := hp.1.odd_of_ne_two hp2
  have hmin := hp.1.two_le
  obtain ⟨k, hk⟩ := ho
  omega

/-- The Fermat–Mersenne PSL₂ alternatives have no ordinary component in a
Sylow-central involution fixed group, including parameters five and seven. -/
theorem fermatMersenne_noCentralInvolutionComponent [Group.IsPerfect Y] {p : ℕ}
    (hp : IsFermatOrMersennePrime p) (hY : ClassicalGroup.IsPSL Y 2 p) :
    NoCentralInvolutionComponent Y := by
  have hp5 := parameter_ge_five hp hY
  let : Fact p.Prime := ⟨hp.1⟩
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hY
  let : Fintype F := Fintype.ofFinite F
  let eF : F ≃+* ZMod p := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hF)
  apply noCentralInvolutionComponent_of_fixedSubgroup (e.trans (Atlas.fieldEquivPSL 2 eF))
  intro a ha S hS D
  obtain ⟨g, _, rfl⟩ := Theory.PSL2.primeField_sylow_fixed_inner
    (hp.1.odd_of_ne_two (by omega)) (by omega) S a hS
  have hg : orderOf g = 2 :=
    (orderOf_injective MulAut.conj
      (MulAut.conj_injective_of_center_eq_bot (GorensteinWalter.psl2_center_eq_bot (ZMod p))) g).symm.trans ha
  have hc := CFSG.Quasithin.MainConverse.psl2_fermatMersenne_involution_centralizer_isPGroup
    (ZMod p) (by simp) hp hp5 g hg
  have hf : IsPGroup 2 (MulAut.conj g).fixedSubgroup := by
    rw [MulAut.fixedSubgroup_conj]
    exact hc
  let : Group.IsNilpotent (MulAut.conj g).fixedSubgroup := hf.isNilpotent
  exact not_isComponent_of_solvable D

private theorem pslThree_sylow_fixed_inner
    (S : Sylow 2 Matrix.PSL3Three.PSL) (a : MulAut Matrix.PSL3Three.PSL)
    (ha : ∀ x ∈ (S : Subgroup Matrix.PSL3Three.PSL), a x = x) :
    ∃ g, a = MulAut.conj g := by
  classical
  let H := Matrix.PSL3Three.PSL
  have hc : center H = ⊥ := by
    apply (center H).eq_bot_iff_card.mpr
    calc
      Nat.card (center H) = Nat.card (center Matrix.PSL3Three.SL) :=
        Nat.card_congr (centerCongr Matrix.PSL3Three.equiv.symm).toEquiv
      _ = 1 := (center Matrix.PSL3Three.SL).eq_bot_iff_card.mp Matrix.PSL3Three.center_eq_bot
  let : Nontrivial S := (S : Subgroup H).nontrivial_iff_ne_bot.mpr
    (S.ne_bot_of_dvd_card (by rw [Matrix.PSL3Three.card_PSL]; decide))
  let : Nontrivial (center S) := S.isPGroup'.center_nontrivial
  have hd : 2 ∣ Nat.card (center S) :=
    (S.isPGroup'.to_subgroup (center S)).card_eq_or_dvd.resolve_left
      (ne_of_gt Finite.one_lt_card)
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := center S) 2 hd
  let t : H := (z : S)
  have ht : orderOf t = 2 :=
    (Subgroup.orderOf_coe (z : S)).trans ((Subgroup.orderOf_coe z).trans hz)
  let A := fixingSubgroup (MulAut H) (S : Set H)
  have htA : MulAut.conj t ∈ A := by
    rw [mem_fixingSubgroup_iff]
    intro x hx
    change t * x * t⁻¹ = x
    have hcomm : t * x = x * t :=
      (congrArg Subtype.val (mem_center_iff.mp z.property ⟨x, hx⟩)).symm
    rw [hcomm, mul_inv_cancel_right]
  have hbound : Nat.card A ≤ 2 :=
    Matrix.PSL3Three.SylowFixers.sylow_fixer_card_le_two S A
      (fun b hb => (mem_fixingSubgroup_iff (MulAut H)).mp hb)
  have htord : orderOf (MulAut.conj t) = 2 :=
    (orderOf_injective MulAut.conj (MulAut.conj_injective_of_center_eq_bot hc) t).trans ht
  have he : zpowers (MulAut.conj t) = A :=
    eq_of_le_of_card_ge (zpowers_le.mpr htA) (by rwa [Nat.card_zpowers, htord])
  have hinner : zpowers (MulAut.conj t) ≤ MulAut.innerSubgroup H :=
    zpowers_le.mpr ⟨t, rfl⟩
  have haA : a ∈ A := (mem_fixingSubgroup_iff (MulAut H)).mpr ha
  obtain ⟨g, hg⟩ := hinner (he.symm ▸ haA)
  exact ⟨g, hg.symm⟩

/-- The actual PSL₃(3) alternative has solvable Sylow-central involution
fixed groups, hence no ordinary component. -/
theorem linear_three_noCentralInvolutionComponent (hY : ClassicalGroup.IsPSL Y 3 3) :
    NoCentralInvolutionComponent Y := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hY
  let : Fintype F := Fintype.ofFinite F
  let eF : F ≃+* ZMod 3 := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hF)
  apply noCentralInvolutionComponent_of_fixedSubgroup (e.trans (Atlas.fieldEquivPSL 3 eF))
  intro a ha S hS D
  let c := Matrix.PSL3Three.innerInvolutoryAutFixedEquiv a ha (pslThree_sylow_fixed_inner S a hS)
  let : Group.IsSolvable (Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :=
    Matrix.GeneralLinearGroup.three_isSolvable
  let : Group.IsSolvable a.fixedSubgroup :=
    Group.isSolvable_of_isSolvable_injective (f := c.toMonoidHom) c.injective
  exact not_isComponent_of_solvable D

/-- The two odd-linear alternatives in E.6.8(5) satisfy the precise
nonexceptional component inspection used by E.6.22. -/
theorem oddLinear_noCentralInvolutionComponent {G : Type*} [Group G] [Finite G]
    (X : Subgroup G) (hX : IsQuasisimple X)
    (hmodel : (∃ p, IsFermatOrMersennePrime p ∧ ClassicalGroup.IsPSL X 2 p) ∨
      ClassicalGroup.IsPSL X 3 3) : NoCentralInvolutionComponent X := by
  let := hX
  rcases hmodel with ⟨p, hp, hm⟩ | hm
  · exact fermatMersenne_noCentralInvolutionComponent hp hm
  · exact linear_three_noCentralInvolutionComponent hm

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.ComponentInspection
