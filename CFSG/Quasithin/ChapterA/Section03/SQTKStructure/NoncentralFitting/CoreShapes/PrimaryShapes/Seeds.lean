module

public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NoncentralFitting.CoreShapes.Common
public import CFSG.Quasithin.ChapterA.Section01.RankActions.Supercritical
public import Theory.GroupTheory.PGroup.SupercriticalExistence
public import Theory.GroupTheory.OddPrimeRankOneSylow
public import Theory.GroupTheory.CyclicNormalCentralizer

/-!
# Actual supercritical seeds for primary Fitting cores

Every prime dividing F(L) has a noncentral core by central-supplement rigidity.
Choose a supercritical subgroup of that core. Its automorphism detection and
perfectness make it noncentral; cyclic-normal centralization and the strong
quasithin bound force rank two. A.1.24 then gives the two small seed models.

A.1.29 recognizes the literal Frattini-action quotient. Comparing its kernel
with the given Fitting quotient by prime-field cover rigidity identifies it
with F(L). The comparison between the nested subgroup and its ambient image
is proved on the actual conjugation maps, in both directions.

`PrimarySeed` records this constructed intermediate object, without asserting
a shape for the whole core. The full-core branches must still prove saturation
or abelian homocyclic recognition. The elementary alternative retains its
actual isomorphism and the extraspecial alternative retains exponent p.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, A.3.6,
printed pp.43–45. The noncentrality and rank arguments adapt the local proofs
in `NoncentralFitting/KernelIdentification.lean`, retaining the subgroup here.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterA.RankActions
open CFSG.Quasithin.Chapter1.Section02 LocalModels
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterA.Section03.NoncentralFitting.CoreShapes.PrimaryShapes
universe u

variable {A : Type u} [Group A]

/-- The actual action of the ambient group on a characteristic subgroup of its p-core. -/
def coreAction {p : ℕ} (X : Subgroup (pCore p A)) [X.Characteristic] : A →* MulAut X :=
  (MulAut.characteristic X).comp MulAut.conjNormal

/-- The actual action on the Frattini quotient of that subgroup. -/
def coreFrattiniAction {p : ℕ} (X : Subgroup (pCore p A)) [X.Characteristic] :
    A →* MulAut (X ⧸ frattini X) :=
  (quotientAut (frattini X)).comp (coreAction X)

/-- A supercritical seed, with its literal action kernel identified. No full-core
shape is included: saturation and abelian homocyclic recognition remain separate. -/
structure PrimarySeed (p : ℕ) (A : Type u) [Group A] where
  X : Subgroup (pCore p A)
  supercritical : IsSupercriticalPSubgroup p X
  odd : Odd p
  rank_two : primeRank p X = 2
  noncentral : ¬ X.map (pCore p A).subtype ≤ center A
  kernel_eq : letI : X.Characteristic := supercritical.characteristic
    (coreFrattiniAction X).ker = fittingSubgroup A

namespace PrimarySeed
variable {p : ℕ} (s : PrimarySeed p A)
instance characteristic : s.X.Characteristic := s.supercritical.characteristic

/-- F(L) fixes the literal supercritical Frattini quotient. -/
theorem frattini_fixed (g : A) (hg : g ∈ fittingSubgroup A) :
    quotientAut (frattini s.X) (coreAction s.X g) = 1 :=
  show g ∈ (coreFrattiniAction s.X).ker from s.kernel_eq.symm ▸ hg

/-- The small models supplied by A.1.24 retain the exponent-p assertion. -/
theorem models [Finite A] [Fact p.Prime] :
    (Nat.card s.X = p ^ 2 ∧
      Nonempty (s.X ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p)))) ∨
    OddExtraspecialThree p s.X := by
  have hp2 : p ≠ 2 := by rintro rfl; exact s.odd.not_two_dvd_nat (dvd_refl 2)
  rcases CFSG.Quasithin.ChapterA.lemma_A_1_24 hp2
    (pCore_isPGroup.to_subgroup s.X) s.supercritical.omega₁_eq_top
    s.supercritical.derived_le_center s.rank_two with he | ⟨hc, hx, _⟩
  · exact Or.inl he
  · exact Or.inr ⟨⟨hx, hc⟩, s.supercritical.pow_eq_one⟩
end PrimarySeed

variable [Finite A]

omit [Finite A] in
private theorem perfect_hom_eq_one_of_pgroup_range
    [Group.IsPerfect A] {B : Type*} [Group B] [Finite B] {p : ℕ} [Fact p.Prime]
    (a : A →* B) (hp : IsPGroup p a.range) : a = 1 := by
  let : Group.IsNilpotent a.range := hp.isNilpotent
  let : Group.IsPerfect a.range := Group.IsPerfect.range a
  have hs : Subsingleton a.range := by
    by_contra! hn
    exact Group.IsPerfect.not_isNilpotent a.range inferInstance
  ext x
  exact congrArg Subtype.val (Subsingleton.elim (a.rangeRestrict x) 1)

private theorem noncentral_supercritical
    [Group.IsPerfect A] {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (X : Subgroup (pCore p A)) (hX : IsSupercriticalPSubgroup p X)
    (hn : ¬ pCore p A ≤ center A) : ¬ X.map (pCore p A).subtype ≤ center A := by
  let : X.Characteristic := hX.characteristic
  intro hc
  let a : A →* MulAut (pCore p A) := MulAut.conjNormal
  have hi : a.range ≤ (MulAut.characteristic X).ker := by
    rintro _ ⟨g, rfl⟩
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    apply Subtype.ext
    change g * ((x : pCore p A) : A) * g⁻¹ = x
    have hh : g * ((x : pCore p A) : A) = ((x : pCore p A) : A) * g :=
      mem_center_iff.mp (hc (mem_map_of_mem _ x.property)) g
    rw [hh, mul_inv_cancel_right]
  have hpgroup := (hX.isPGroup_restriction_kernel pCore_isPGroup hp).to_le hi
  have he := perfect_hom_eq_one_of_pgroup_range a hpgroup
  apply hn
  intro x hx
  apply mem_center_iff.mpr
  intro g
  have hh := congrArg (fun f : MulAut (pCore p A) => (f ⟨x,hx⟩ : A))
    (DFunLike.congr_fun he g)
  change g * x * g⁻¹ = x at hh
  exact mul_inv_eq_iff_eq_mul.mp hh

private theorem image_rank_two
    [Group.IsPerfect A] {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (X : Subgroup (pCore p A)) (hX : IsSupercriticalPSubgroup p X)
    (hr : primeRank p A ≤ 2) (hn : ¬ pCore p A ≤ center A) :
    primeRank p (X.map (pCore p A).subtype) = 2 := by
  let : X.Characteristic := hX.characteristic
  let P := X.map (pCore p A).subtype
  have hP : IsPGroup p P := (pCore_isPGroup.to_subgroup X).map (pCore p A).subtype
  have hle : primeRank p P ≤ 2 :=
    (Theory.GroupTheory.primeRank_le_of_injective p P.subtype P.subtype_injective).trans hr
  have hgt : 1 < primeRank p P := by
    by_contra! hh
    let : IsCyclic P := hP.isCyclic_of_odd_of_elementary_card_le hp
      (fun E hE => by
        let : IsElementaryAbelian p E := hE
        exact IsElementaryAbelian.card_le_prime_of_primeRank_le_one hh E)
    have hc : (⊤ : Subgroup A) ≤ centralizer (P : Set A) := by
      simpa only [Group.IsPerfect.commutator_eq_top] using
        commutator_le_centralizer_of_isCyclic_normal P
    apply noncentral_supercritical hp X hX hn
    intro x hx
    apply mem_center_iff.mpr
    intro g
    exact (hc (mem_top g) x hx).symm
  exact le_antisymm hle hgt

omit [Finite A] in
private theorem restriction_frattini_fixed_iff
    {p : ℕ} (X : Subgroup (pCore p A)) [X.Characteristic] (g : A) :
    quotientAut (frattini X) (coreAction X g) = 1 ↔
      (⟨g, mem_top g⟩ : (⊤ : Subgroup A)) ∈
        frattiniCentralizer (X.map (pCore p A).subtype) ⊤ := by
  let P := X.map (pCore p A).subtype
  let e : X ≃* P := X.equivMapOfInjective _ (pCore p A).subtype_injective
  have he (x : X) : MulAut.conjNormal g (e x) = e (coreAction X g x) := by
    apply Subtype.ext
    rfl
  constructor
  · intro hg
    apply (mem_frattiniCentralizer_iff P ⊤ ⟨g, mem_top g⟩).mpr
    intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [he]
    have hx := DFunLike.congr_fun hg (QuotientGroup.mk' (frattini X) x)
    rw [quotientAut_apply_mk, MulAut.one_apply] at hx
    have hm := (frattini_le_comap_frattini_of_surjective (φ := e.toMonoidHom) e.surjective)
      (QuotientGroup.eq.mp hx)
    apply QuotientGroup.eq.mpr
    simpa only [mem_comap, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
      map_mul, map_inv] using hm
  · intro hg
    ext q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (frattini X) q
    rw [quotientAut_apply_mk, MulAut.one_apply]
    have hx := (mem_frattiniCentralizer_iff P ⊤ ⟨g, mem_top g⟩).mp hg (e x)
    rw [he] at hx
    have hm := (frattini_le_comap_frattini_of_surjective (φ := e.symm.toMonoidHom) e.symm.surjective)
      (QuotientGroup.eq.mp hx)
    apply QuotientGroup.eq.mpr
    simpa only [mem_comap, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
      map_mul, map_inv, MulEquiv.symm_apply_apply] using hm

variable {G : Type u} [Group G] [Finite G] {L : Subgroup G}

/-- Each prime in F(L) supplies an actual rank-two supercritical subgroup.
Cover rigidity identifies its action kernel with F(L), without identifying
its full primary core with either small supercritical model. -/
theorem exists_primarySeed
    (hrigid : PrimeSL2CoverRigidity.{u})
    {𝒦 : GroupClass.{u}} (hG : IsSQTK 𝒦 G) (hO : pCore 2 G = ⊥)
    (hL : L.IsCComponent) (hquot : PrimeSL2FittingQuotient L)
    {p : ℕ} [Fact p.Prime] (hd : p ∣ Nat.card (fittingSubgroup L)) :
    Nonempty (PrimarySeed p L) := by
  let : Group.IsPerfect L := hL.perfect
  have hn := core_not_central_of_dvd hrigid hL hquot hd
  have hp : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by
    intro he
    apply hn
    rw [he, twoCore_eq_bot hL hO]
    exact bot_le)
  have hp2 : p ≠ 2 := by rintro rfl; exact hp.not_two_dvd_nat (dvd_refl 2)
  obtain ⟨X, hX⟩ := (pCore_isPGroup (p := p) (G := L)).exists_supercriticalPSubgroup hp2
  let : X.Characteristic := hX.characteristic
  let P := X.map (pCore p L).subtype
  let e : X ≃* P := X.equivMapOfInjective _ (pCore p L).subtype_injective
  have hP : IsPGroup p P := (pCore_isPGroup.to_subgroup X).map (pCore p L).subtype
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
  have hr : primeRank p P = 2 :=
    image_rank_two hp X hX ((hG.subgroup L).stronglyQuasithin p Fact.out hp) hn
  have hnon := noncentral_supercritical hp X hX hn
  have hcomm : ⁅P, (⊤ : Subgroup L)⁆ ≠ ⊥ := by
    intro hh
    exact hnon (commutator_top_right_eq_bot_iff_le_center.mp hh)
  have hp3 := three_lt_of_perfect_action P ⊤ hp2 hP ho hc hr hcomm
  have hm := CFSG.Quasithin.ChapterA.lemma_A_1_29_1 P ⊤ hp hP ho hc hr hcomm
  have step {r : ℕ} [Fact r.Prime] (hr3 : 3 < r)
      (j : ((⊤ : Subgroup L) ⧸ frattiniCentralizer P ⊤) ≃*
        Matrix.SpecialLinearGroup (Fin 2) (ZMod r)) :
      (coreFrattiniAction X).ker = fittingSubgroup L := by
    let q : L →* (⊤ : Subgroup L) := topEquiv.symm.toMonoidHom
    let f := j.toMonoidHom.comp ((QuotientGroup.mk' (frattiniCentralizer P ⊤)).comp q)
    have hf : Function.Surjective f := j.surjective.comp
      ((QuotientGroup.mk'_surjective _).comp topEquiv.symm.surjective)
    have hk : (coreFrattiniAction X).ker = f.ker := by
      ext g
      rw [show g ∈ (coreFrattiniAction X).ker ↔
        quotientAut (frattini X) (coreAction X g) = 1 from Iff.rfl,
        restriction_frattini_fixed_iff]
      change _ ↔ j (QuotientGroup.mk' (frattiniCentralizer P ⊤) (q g)) = 1
      rw [← j.map_one, j.injective.eq_iff]
      exact (QuotientGroup.eq_one_iff (q g)).symm
    obtain ⟨s, hs, hs3, ⟨i⟩⟩ := hquot
    let : Fact s.Prime := ⟨hs⟩
    let f₀ := i.toMonoidHom.comp (QuotientGroup.mk' (fittingSubgroup L))
    have hsame := cComponent_SL2_kernels_eq hrigid hL hr3 hs3 f f₀ hf
      (i.surjective.comp (QuotientGroup.mk'_surjective _))
    rw [hsame] at hk
    simpa only [f₀, MonoidHom.ker_comp_of_injective _ i.toMonoidHom i.injective,
      QuotientGroup.ker_mk'] using hk
  have hk : (coreFrattiniAction X).ker = fittingSubgroup L := by
    rcases hm with hj | ⟨_, hj⟩
    · exact step hp3 hj.some
    · let : Fact (Nat.Prime 5) := ⟨by decide⟩
      exact step (by decide) hj.some
  refine ⟨⟨X, hX, hp, ?_, hnon, hk⟩⟩
  exact (primeRank_equiv p e).trans hr

end CFSG.Quasithin.ChapterA.Section03.NoncentralFitting.CoreShapes.PrimaryShapes
