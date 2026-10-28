module

public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NoncentralFitting.CoreShapes.Common
public import CFSG.Quasithin.ChapterA.Section01.RankActions.Supercritical
public import Theory.GroupTheory.PGroup.SupercriticalExistence
public import Theory.GroupTheory.CyclicNormalCentralizer
public import Theory.AtlasPort.LinearGroups.SL2Order

/-!
# Prime support of the noncentral Fitting subgroup

Every prime divisor p of F(L) gives a noncentral Oₚ(L), by the existing
central-supplement rigidity. Choose a supercritical subgroup of this actual
prime core. Its automorphism detection preserves noncentrality, while A.1.25
and perfectness exclude rank one. The actual relative Frattini action in
A.1.29 yields SL₂(p), or SL₂(5) with p congruent to 1 or 4 modulo five.

The C-component cover-kernel comparison identifies this action kernel with
the kernel of the supplied map L → L/F(L) ≃ SL₂(r). The resulting genuine
SL₂ isomorphism, and the order formula q(q² − 1), identify the model primes.
No construction of the Fitting quotient or classification of its primary
cores is assumed beyond the supplied actual quotient equivalence.

`prime_support_contract` discharges exactly the `hsupport` argument of
`CoreShapes.structure_of_prime_core_data`. This leaf does not import that
parent: the parent retains assembly of the independent core-shape and
natural-action branches. The exact `PrimeSL2CoverRigidity` input remains at
the authorized source boundary. The support proof itself does not need a
separate noncentral-Fitting premise once the quotient model is supplied.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
A.3.6, printed pp.43–45, using A.1.21, A.1.25 and A.1.29.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterA.RankActions
namespace CFSG.Quasithin.ChapterA.Section03.NoncentralFitting.CoreShapes.PrimeSupport
universe u
variable {A : Type u} [Group A] [Finite A]

/-- A perfect actor cannot have nontrivial image in the supercritical p-kernel. -/
private theorem noncentral_supercritical [Group.IsPerfect A]
    {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (S : Subgroup A) [S.Characteristic] (hS : IsPGroup p S)
    (X : Subgroup S) (hX : IsSupercriticalPSubgroup p X)
    (hn : ¬ S ≤ center A) : ¬ X.map S.subtype ≤ center A := by
  let : X.Characteristic := hX.characteristic
  intro hc
  let a : A →* MulAut S := MulAut.conjNormal
  have hrange : a.range ≤ (MulAut.characteristic X).ker := by
    rintro _ ⟨g, rfl⟩
    apply MonoidHom.mem_ker.mpr
    ext x
    change g * ((x : S) : A) * g⁻¹ = ((x : S) : A)
    have hx : ((x : S) : A) ∈ X.map S.subtype := mem_map.mpr ⟨x, x.property, rfl⟩
    rw [mem_center_iff.mp (hc hx) g, mul_inv_cancel_right]
  have hpg : IsPGroup p a.range := (hX.isPGroup_restriction_kernel hS hp).to_le hrange
  let : Group.IsNilpotent a.range := hpg.isNilpotent
  let : Group.IsPerfect a.range := Group.IsPerfect.range a
  have hs : Subsingleton a.range := by
    by_contra! hne
    exact Group.IsPerfect.not_isNilpotent a.range inferInstance
  apply hn
  intro x hx
  apply mem_center_iff.mpr
  intro g
  have he := congrArg (fun f : a.range => ((f : MulAut S) ⟨x,hx⟩ : A))
    (Subsingleton.elim (a.rangeRestrict g) 1)
  change g * x * g⁻¹ = x at he
  exact mul_inv_eq_iff_eq_mul.mp he

/-- Keep the congruence information in the actual supercritical action models. -/
private theorem active_core_models [Group.IsPerfect A]
    (hA : CFSG.Quasithin.IsStronglyQuasithin A)
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (hn : ¬ pCore p A ≤ center A) :
    3 < p ∧
      ((∃ f : A →* Matrix.SpecialLinearGroup (Fin 2) (ZMod p), Function.Surjective f) ∨
        ((p % 5 = 1 ∨ p % 5 = 4) ∧
          ∃ f : A →* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5), Function.Surjective f)) := by
  have hp2 : p ≠ 2 := by rintro rfl; obtain ⟨k, hk⟩ := hp; omega
  obtain ⟨X, hX⟩ := (pCore_isPGroup (p := p) (G := A)).exists_supercriticalPSubgroup hp2
  let : X.Characteristic := hX.characteristic
  let P := X.map (pCore p A).subtype
  let e : X ≃* P := X.equivMapOfInjective _ (pCore p A).subtype_injective
  have hP : IsPGroup p P := (pCore_isPGroup.to_subgroup X).map (pCore p A).subtype
  have hnc : ¬ P ≤ center A := noncentral_supercritical hp _ pCore_isPGroup X hX hn
  have ho : omega₁ P (p := p) = ⊤ := by
    apply top_unique
    intro y _
    apply Subgroup.subset_closure
    change y ^ (p ^ 1) = 1
    obtain ⟨x, rfl⟩ := e.surjective y
    simpa only [pow_one, ← map_pow, map_one] using congrArg e (hX.pow_eq_one x)
  have hc : _root_.commutator P ≤ center P := by
    apply Subgroup.commutator_le.mpr
    intro x _ y _
    apply mem_center_iff.mpr
    intro z
    apply e.symm.injective
    have hh := mem_center_iff.mp (hX.derived_le_center
      (commutator_mem_commutator (mem_top (e.symm x)) (mem_top (e.symm y)))) (e.symm z)
    simpa only [map_mul, map_commutatorElement] using hh
  have hr : primeRank p P = 2 := by
    have hle : primeRank p (pCore p A) ≤ 2 :=
      (_root_.primeRank_subgroup_le p _).trans (hA p Fact.out hp)
    have hgt : 1 < primeRank p (pCore p A) := by
      by_contra! hh
      let : IsCyclic (pCore p A) := pCore_isPGroup.isCyclic_of_odd_of_elementary_card_le hp
        (fun E hE => by
          let : IsElementaryAbelian p E := hE
          exact IsElementaryAbelian.card_le_prime_of_primeRank_le_one hh E)
      have hz : (⊤ : Subgroup A) ≤ centralizer (pCore p A : Set A) := by
        simpa only [Group.IsPerfect.commutator_eq_top] using
          commutator_le_centralizer_of_isCyclic_normal (pCore p A)
      apply hn
      intro x hx
      apply mem_center_iff.mpr
      intro g
      exact (hz (mem_top g) x hx).symm
    rw [← primeRank_congr p e, hX.primeRank_eq_of_le_two pCore_isPGroup hp hle]
    omega
  have hnon : ⁅P, (⊤ : Subgroup A)⁆ ≠ ⊥ := fun h =>
    hnc (commutator_top_right_eq_bot_iff_le_center.mp h)
  refine ⟨three_lt_of_perfect_action P ⊤ hp2 hP ho hc hr hnon, ?_⟩
  have hm := CFSG.Quasithin.ChapterA.lemma_A_1_29_1 P ⊤ hp hP ho hc hr hnon
  have step {r : ℕ}
      (j : ((⊤ : Subgroup A) ⧸ frattiniCentralizer P ⊤) ≃*
        Matrix.SpecialLinearGroup (Fin 2) (ZMod r)) :
      ∃ f : A →* Matrix.SpecialLinearGroup (Fin 2) (ZMod r), Function.Surjective f := by
    let q : A →* (⊤ : Subgroup A) := topEquiv.symm.toMonoidHom
    exact ⟨j.toMonoidHom.comp ((QuotientGroup.mk' (frattiniCentralizer P ⊤)).comp q),
      j.surjective.comp ((QuotientGroup.mk'_surjective _).comp topEquiv.symm.surjective)⟩
  exact hm.imp (fun hj => step hj.some) (fun ⟨hm, hj⟩ => ⟨hm, step hj.some⟩)

/-- The order q(q² − 1) strictly increases for field orders q ≥ 2. -/
private theorem prime_eq_of_SL2_equiv {p r : ℕ} [Fact p.Prime] [Fact r.Prime]
    (e : Matrix.SpecialLinearGroup (Fin 2) (ZMod p) ≃*
      Matrix.SpecialLinearGroup (Fin 2) (ZMod r)) : p = r := by
  have h := Nat.card_congr e.toEquiv
  rw [Atlas.card_sl_two, Atlas.card_sl_two, Nat.card_zmod, Nat.card_zmod] at h
  have hp := (Fact.out : p.Prime).two_le
  have hr := (Fact.out : r.Prime).two_le
  have mono {a b : ℕ} (ha : 2 ≤ a) (hab : a < b) : a * (a ^ 2 - 1) < b * (b ^ 2 - 1) := by
    have hpos : 0 < a ^ 2 - 1 := Nat.sub_pos_of_lt (by nlinarith)
    have hle : a ^ 2 - 1 ≤ b ^ 2 - 1 := Nat.sub_le_sub_right (Nat.pow_le_pow_left (Nat.le_of_lt hab) 2) 1
    exact lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right hab hpos) (Nat.mul_le_mul_left b hle)
  rcases lt_trichotomy p r with hl | he | hg
  · exact False.elim ((ne_of_lt (mono hp hl)) h)
  · exact he
  · exact False.elim ((ne_of_lt (mono hr hg)) h.symm)

variable {G : Type u} [Group G] [Finite G] {L : Subgroup G}

/-- Equal actual kernels give isomorphic SL₂ models and hence equal primes. -/
private theorem model_prime_eq (hrigid : PrimeSL2CoverRigidity.{u})
    (hL : L.IsCComponent) {p r : ℕ} [Fact p.Prime] [Fact r.Prime]
    (hp : 3 < p) (hr : 3 < r)
    (f : L →* Matrix.SpecialLinearGroup (Fin 2) (ZMod p))
    (g : L →* Matrix.SpecialLinearGroup (Fin 2) (ZMod r))
    (hf : Function.Surjective f) (hg : Function.Surjective g) : p = r := by
  have hk := cComponent_SL2_kernels_eq hrigid hL hp hr f g hf hg
  exact prime_eq_of_SL2_equiv (((QuotientGroup.quotientKerEquivOfSurjective f hf).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hk)).trans
      (QuotientGroup.quotientKerEquivOfSurjective g hg))

/-- Prime support of the actual Fitting subgroup, retaining both exceptional congruences. -/
theorem prime_support (hrigid : PrimeSL2CoverRigidity.{u})
    {𝒦 : CFSG.Quasithin.GroupClass.{u}} (hG : CFSG.Quasithin.IsSQTK 𝒦 G)
    (hO : pCore 2 G = ⊥) (hL : L.IsCComponent)
    {r : ℕ} [Fact r.Prime] (hr : 3 < r)
    (e : (L ⧸ fittingSubgroup L) ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod r))
    {p : ℕ} (hp : p.Prime) (hd : p ∣ Nat.card (fittingSubgroup L)) :
    p = r ∨ (r = 5 ∧ (p % 5 = 1 ∨ p % 5 = 4)) := by
  let : Fact p.Prime := ⟨hp⟩
  let : Group.IsPerfect L := hL.perfect
  have hquot : PrimeSL2FittingQuotient L := ⟨r, Fact.out, hr, ⟨e⟩⟩
  have hnc := core_not_central_of_dvd hrigid hL hquot hd
  have hodd : Odd p := (fitting_odd_card hL hO).of_dvd_nat hd
  obtain ⟨hp3, hm⟩ := active_core_models (hG.stronglyQuasithin.subgroup L) hodd hnc
  let g := e.toMonoidHom.comp (QuotientGroup.mk' (fittingSubgroup L))
  have hg : Function.Surjective g := e.surjective.comp (QuotientGroup.mk'_surjective _)
  rcases hm with ⟨f, hf⟩ | ⟨hmod, f, hf⟩
  · exact Or.inl (model_prime_eq hrigid hL hp3 hr f g hf hg)
  · let : Fact (Nat.Prime 5) := ⟨by decide⟩
    exact Or.inr ⟨(model_prime_eq hrigid hL (by decide) hr f g hf hg).symm, hmod⟩

/-- The support argument of `CoreShapes.structure_of_prime_core_data`, with
all prime-support premises discharged from the SQTK source hypotheses. -/
theorem prime_support_contract (hrigid : PrimeSL2CoverRigidity.{u})
    {𝒦 : CFSG.Quasithin.GroupClass.{u}} (hG : CFSG.Quasithin.IsSQTK 𝒦 G)
    (hO : pCore 2 G = ⊥) (hL : L.IsCComponent) :
    ∀ (r : ℕ) [Fact r.Prime], 3 < r →
      Nonempty ((L ⧸ fittingSubgroup L) ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod r)) →
      ∀ p : ℕ, p.Prime → p ∣ Nat.card (fittingSubgroup L) →
        p = r ∨ (r = 5 ∧ (p % 5 = 1 ∨ p % 5 = 4)) := by
  intro r _ hr he p hp hd
  exact prime_support hrigid hG hO hL hr he.some hp hd

end CFSG.Quasithin.ChapterA.Section03.NoncentralFitting.CoreShapes.PrimeSupport
