module

public import Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.Basic
public import Theory.SpecificGroups.SymplecticFour.Sylow.AmbientOrder
public import Theory.GroupTheory.PerfectCentralCover
import Theory.Representation.NonsplitFour
import Theory.Representation.EndFieldRep
import Mathlib.Tactic

/-!
# Quartic-prime Sylow subgroups in odd symplectic four-space

Let p and r be primes with r odd, r ≠ p and r dividing p²+1. Every r-subgroup
of GL₄(p) is cyclic: choose an order-r subgroup of its nontrivial center.
The faithful action of this subgroup on four-space is irreducible, since r
is coprime to the orders of GL₁(p), GL₂(p) and GL₃(p). Maschke's theorem and
the two possible kernels of a prime-order action exclude every proper
invariant subspace. Schur's lemma and the finite division ring theorem make
the commuting algebra a finite field. Its cyclic unit group contains the
ambient centralizer, hence the original r-subgroup.

Apply this to the faithful matrix realization of the actual Sp₄(p), then
use cyclic Sylow transfer to exclude r from every finite perfect central
kernel. The large-prime hypothesis in the public Sylow interface matches
the multiplier calculation; the linear argument itself works for any p.

The local linear proofs adapt the characteristic-independent parts of
`Theory.Representation.NonsplitFour` and `Theory.Representation.SingerFour`.
Here coprimality concerns the odd prime r, not the whole integer p²+1.
Source: Huppert--Blackburn, *Finite Groups III*, XI.3.10(a), pp.190–191,
and II.7.3; Aschbacher--Smith I.1.2, printed p.407; GLS3 §6.1, C₂ row.
-/

noncomputable section
open Representation
namespace Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.LargeSections.OddNondefining.Quartic

private theorem coprime_factors {q r : ℕ} (hq : 2 ≤ q) (hr : r.Prime)
    (hr2 : r ≠ 2) (hd : r ∣ q^2 + 1) :
    Nat.Coprime r q ∧ Nat.Coprime r (q - 1) ∧
      Nat.Coprime r (q^2 - 1) ∧ Nat.Coprime r (q^3 - 1) := by
  have hnotq : ¬ r ∣ q := by
    intro h
    have hh := Nat.dvd_sub hd (h.trans (dvd_pow_self q (by decide : 2 ≠ 0)))
    exact hr.not_dvd_one (by simpa using hh)
  have hnot2 : ¬ r ∣ 2 := fun h =>
    hr2 ((Nat.dvd_prime Nat.prime_two).mp h |>.resolve_left hr.ne_one)
  have hnot_sq : ¬ r ∣ q^2 - 1 := by
    intro h
    have hh := Nat.dvd_sub hd h
    have hq2 : 1 ≤ q^2 := Nat.one_le_pow _ _ (by omega)
    rw [show q^2 + 1 - (q^2 - 1) = 2 by omega] at hh
    exact hnot2 hh
  have hnot_minus : ¬ r ∣ q - 1 := fun h =>
    hnot_sq (h.trans (by simpa using Nat.sub_dvd_pow_sub_pow q 1 2))
  have hnot_sum : ¬ r ∣ q^2 + q + 1 := by
    intro h
    apply hnotq
    have hh := Nat.dvd_sub h hd
    rwa [show q^2 + q + 1 - (q^2 + 1) = q by omega] at hh
  have hf : q^3 - 1 = (q - 1) * (q^2 + q + 1) := by
    rw [Nat.sub_mul]
    have he : q * (q^2 + q + 1) = q^3 + q^2 + q := by ring
    rw [he, one_mul]
    omega
  exact ⟨hr.coprime_iff_not_dvd.mpr hnotq,
    hr.coprime_iff_not_dvd.mpr hnot_minus,
    hr.coprime_iff_not_dvd.mpr hnot_sq,
    hr.coprime_iff_not_dvd.mpr (by rw [hf]; exact hr.not_dvd_mul hnot_minus hnot_sum)⟩

private theorem coprime_card_GL
    {K : Type*} [Field K] [Fintype K] {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) (hd : r ∣ Fintype.card K^2 + 1)
    (d : ℕ) (hdpos : 1 ≤ d) (hdle : d ≤ 3) :
    Nat.Coprime r (Nat.card (GL (Fin d) K)) := by
  let q := Fintype.card K
  obtain ⟨hcopq, hcop1, hcop2, hcop3⟩ :=
    coprime_factors (show 2 ≤ q from Fintype.one_lt_card) hr hr2 hd
  interval_cases d
  · rw [Matrix.card_GL_field]
    simpa [q] using hcop1
  · rw [Matrix.card_GL_field]
    have hq2q : q ^ 2 - q = q * (q - 1) := by
      rw [Nat.mul_sub_left_distrib]
      ring_nf
    simpa [Fin.prod_univ_two, q, hq2q] using
      hcop2.mul_right (hcopq.mul_right hcop1)
  · rw [Matrix.card_GL_field]
    have hq3q : q ^ 3 - q = q * (q ^ 2 - 1) := by
      rw [Nat.mul_sub_left_distrib]
      ring_nf
    have hq3q2 : q ^ 3 - q ^ 2 = q ^ 2 * (q - 1) := by
      rw [Nat.mul_sub_left_distrib]
      ring_nf
    simpa [Fin.prod_univ_three, q, hq3q, hq3q2] using
      hcop3.mul_right
        (hcopq.mul_right hcop2) |>.mul_right
          (by simpa [pow_two] using
            (hcopq.mul_right hcopq).mul_right hcop1)

private theorem exists_isCompl_invariant
    {A K V : Type*} [Group A] [Fintype A]
    [Field K] [NeZero (Fintype.card A : K)]
    [AddCommGroup V] [Module K V]
    (rho : Representation K A V)
    (U : Submodule K V)
    (hU : ∀ a : A, ∀ v ∈ U, rho a v ∈ U) :
    ∃ W, IsCompl U W ∧ ∀ a : A, ∀ v ∈ W, rho a v ∈ W := by
  classical
  have hUinv : U ∈ rho.invtSubmodule := by
    rw [Representation.mem_invtSubmodule]
    intro a
    rw [Module.End.mem_invtSubmodule_iff_forall_mem_of_mem]
    exact hU a
  let Upack : rho.invtSubmodule := ⟨U, hUinv⟩
  let instAdd : AddCommGroup rho.asModule :=
    Representation.instAddCommGroupAsModule rho
  let : AddCommGroup rho.asModule := instAdd
  let instMod : Module (MonoidAlgebra K A) rho.asModule :=
    Representation.instModuleMonoidAlgebraAsModule rho
  let : Module (MonoidAlgebra K A) rho.asModule := instMod
  let Umod : @Submodule (MonoidAlgebra K A) rho.asModule _
      instAdd.toAddCommMonoid instMod :=
    rho.mapSubmodule Upack
  obtain ⟨Wmod, hUWmod⟩ := @MonoidAlgebra.Submodule.exists_isCompl'
    K inferInstance A inferInstance inferInstance rho.asModule
      instAdd instMod inferInstance Umod
  let Wpack : rho.invtSubmodule := rho.mapSubmodule.symm Wmod
  let W : Submodule K V := Wpack
  refine ⟨W, ?_, ?_⟩
  · have hcompl_pack : IsCompl Upack Wpack := by
      exact (rho.mapSubmodule.isCompl_iff).2
        (by simpa [Umod, Wpack] using hUWmod)
    rw [isCompl_iff, disjoint_iff, codisjoint_iff] at hcompl_pack ⊢
    constructor
    · simpa [Upack, W] using congrArg Subtype.val hcompl_pack.1
    · simpa [Upack, W] using congrArg Subtype.val hcompl_pack.2
  · intro a v hv
    have hmem := (Representation.mem_invtSubmodule (ρ := rho)).1 Wpack.2 a
    exact
      (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem (rho a)).1 hmem v
        (by simpa [W] using hv)

private theorem invariant_eq_bot_or_top
    {A K V : Type*} [Group A] [Fintype A]
    [Field K] [Fintype K] [NeZero (Fintype.card A : K)]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (r : ℕ) (hr : r.Prime) (hrne2 : r ≠ 2)
    (hAcard : Nat.card A = r)
    (rho : Representation K A V) (hrho : Function.Injective rho)
    (hfinrank : Module.finrank K V = 4)
    (hrdiv : r ∣ Fintype.card K ^ 2 + 1)
    (U : Submodule K V)
    (hUinv : ∀ a : A, ∀ v ∈ U, rho a v ∈ U) :
    U = ⊥ ∨ U = ⊤ := by
  classical
  by_cases hUbot : U = ⊥
  · exact Or.inl hUbot
  by_cases hUtop : U = ⊤
  · exact Or.inr hUtop
  exfalso
  obtain ⟨W, hUW, hWinv⟩ :=
    exists_isCompl_invariant rho U hUinv
  have hWbot : W ≠ ⊥ := by
    intro hbot
    apply hUtop
    have hsup : U ⊔ W = ⊤ := codisjoint_iff.mp hUW.2
    simpa [hbot] using hsup
  have hUpos : 1 ≤ Module.finrank K U :=
    Submodule.one_le_finrank_iff.mpr hUbot
  have hWpos : 1 ≤ Module.finrank K W :=
    Submodule.one_le_finrank_iff.mpr hWbot
  have hsum : Module.finrank K U + Module.finrank K W = 4 := by
    simpa [hfinrank] using Submodule.finrank_add_eq_of_isCompl hUW
  have hUle : Module.finrank K U ≤ 3 := by omega
  have hWle : Module.finrank K W ≤ 3 := by omega
  let rhoU : Representation K A U :=
    rho.subrepresentation U (by
      intro a v hv
      exact hUinv a v hv)
  let rhoW : Representation K A W :=
    rho.subrepresentation W (by
      intro a v hv
      exact hWinv a v hv)
  let : Fact (Nat.Prime (Nat.card A)) := ⟨by rw [hAcard]; exact hr⟩
  rcases rhoU.ker.eq_bot_or_eq_top_of_prime_card with hkerU | hkerU
  · have hinjU : Function.Injective rhoU :=
      (MonoidHom.ker_eq_bot_iff rhoU).mp hkerU
    have hdvd :=
      Representation.card_dvd_card_GL_of_injective rhoU hinjU
    rw [hAcard] at hdvd
    have hcop := coprime_card_GL hr hrne2 hrdiv
      (Module.finrank K U) hUpos hUle
    exact hr.ne_one (Nat.eq_one_of_dvd_coprimes hcop (dvd_refl r) hdvd)
  · have hUfix (a : A) (u : U) : rho a (u : V) = (u : V) := by
      have ha : a ∈ rhoU.ker := by
        rw [hkerU]
        trivial
      have ha' : rhoU a = (1 : Module.End K U) := ha
      have hau := congrArg (fun f : Module.End K U => f u) ha'
      exact congrArg Subtype.val (by simpa [rhoU] using hau)
    have hinjW : Function.Injective rhoW := by
      intro a b hab
      apply hrho
      apply LinearMap.ext
      intro v
      have hv : v ∈ U ⊔ W := by
        rw [codisjoint_iff.mp hUW.2]
        trivial
      rcases Submodule.mem_sup.mp hv with ⟨u, hu, w, hw, huw⟩
      rw [← huw]
      have hu_a := hUfix a ⟨u, hu⟩
      have hu_b := hUfix b ⟨u, hu⟩
      have hw_ab : rho a w = rho b w := by
        have habw := congrArg
          (fun f : Module.End K W => f ⟨w, hw⟩) hab
        exact congrArg Subtype.val (by simpa [rhoW] using habw)
      calc
        rho a (u + w) = rho a u + rho a w := map_add _ _ _
        _ = u + rho a w := by rw [hu_a]
        _ = u + rho b w := by rw [hw_ab]
        _ = rho b u + rho b w := by rw [hu_b]
        _ = rho b (u + w) := (map_add _ _ _).symm
    have hdvd :=
      Representation.card_dvd_card_GL_of_injective rhoW hinjW
    rw [hAcard] at hdvd
    have hcop := coprime_card_GL hr hrne2 hrdiv
      (Module.finrank K W) hWpos hWle
    exact hr.ne_one (Nat.eq_one_of_dvd_coprimes hcop (dvd_refl r) hdvd)

open scoped MonoidAlgebra IsMulCommutative

section CommutingAlgebra

variable {K A V : Type*} [Field K] [Monoid A] [AddCommGroup V] [Module K V]
    (ρ : Representation K A V)

private abbrev commutingAlgebra := Subalgebra.centralizer K (Set.range ρ)

private def commutingIntertwiner (f : commutingAlgebra ρ) : IntertwiningMap ρ ρ where
  toLinearMap := f.val
  isIntertwining' a := (f.property (ρ a) ⟨a, rfl⟩).symm

private def commutingToEnd : commutingAlgebra ρ →ₐ[K] Module.End K[A] ρ.asModule :=
  (IntertwiningMap.equivAlgEnd (ρ := ρ)).toAlgHom.comp
    { toFun := commutingIntertwiner ρ
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }

private theorem commutingToEnd_injective : Function.Injective (commutingToEnd ρ) := by
  intro f g h
  apply Subtype.ext
  exact congrArg IntertwiningMap.toLinearMap
    ((IntertwiningMap.equivAlgEnd (ρ := ρ)).injective h)

variable [Finite K] [FiniteDimensional K V]

private instance commuting_finite : Finite (commutingAlgebra ρ) :=
  Finite.of_injective (commutingToEnd ρ) (commutingToEnd_injective ρ)

variable [IsIrreducible ρ]

@[instance_reducible]
private noncomputable def commutingField : Field (commutingAlgebra ρ) := by
  let : IsDomain (commutingAlgebra ρ) :=
    Function.Injective.isDomain (commutingToEnd ρ) (commutingToEnd_injective ρ)
  exact (Finite.isDomain_to_isField (commutingAlgebra ρ)).toField

end CommutingAlgebra

variable {K : Type*} [Field K] [Fintype K]

private abbrev matrixAction : GL (Fin 4) K →* Module.End K (Fin 4 → K) :=
  (Units.coeHom _).comp Matrix.GeneralLinearGroup.toLin.toMonoidHom

private abbrev subgroupAction (C : Subgroup (GL (Fin 4) K)) :
    Representation K C (Fin 4 → K) := matrixAction.comp C.subtype

omit [Fintype K] in
private theorem matrixAction_injective : Function.Injective (matrixAction (K := K)) := by
  intro a b h
  apply Matrix.GeneralLinearGroup.toLin.injective
  exact Units.ext h

private theorem subgroupAction_irreducible {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (C : Subgroup (GL (Fin 4) K)) (hcard : Nat.card C = r)
    [Fintype C] [NeZero (Fintype.card C : K)] (hd : r ∣ Fintype.card K^2 + 1) :
    Representation.IsIrreducible (subgroupAction C) := by
  refine ⟨fun U => ?_⟩
  have h := invariant_eq_bot_or_top r hr hr2 hcard
    (subgroupAction C) (matrixAction_injective.comp C.subtype_injective)
    (by simp) hd U.toSubmodule (fun a v hv => U.apply_mem_toSubmodule a hv)
  rcases h with h | h
  · exact Or.inl (Subrepresentation.toSubmodule_injective h)
  · exact Or.inr (Subrepresentation.toSubmodule_injective h)

private def centralizerToAlgebra (C : Subgroup (GL (Fin 4) K)) :
    Subgroup.centralizer (C : Set (GL (Fin 4) K)) →* commutingAlgebra (subgroupAction C) where
  toFun g := ⟨matrixAction g.val, by
    rintro _ ⟨u, rfl⟩
    simpa only [map_mul, subgroupAction, MonoidHom.comp_apply, Subgroup.subtype_apply] using
      congrArg matrixAction (Subgroup.mem_centralizer_iff.mp g.property u.val u.property)⟩
  map_one' := Subtype.ext (map_one matrixAction)
  map_mul' g h := Subtype.ext (map_mul matrixAction g.val h.val)

private theorem isCyclic_centralizer {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (C : Subgroup (GL (Fin 4) K)) (hcard : Nat.card C = r)
    [Fintype C] [NeZero (Fintype.card C : K)] (hd : r ∣ Fintype.card K^2 + 1) :
    IsCyclic (Subgroup.centralizer (C : Set (GL (Fin 4) K))) := by
  let := subgroupAction_irreducible hr hr2 C hcard hd
  let := commutingField (subgroupAction C)
  let f := (centralizerToAlgebra C).toHomUnits
  apply isCyclic_of_injective f
  intro a b h
  apply Subtype.ext
  apply matrixAction_injective
  exact congrArg (fun u => (u.val : commutingAlgebra (subgroupAction C)).val) h

private theorem isCyclic_of_isPGroup
    {p r : ℕ} [Fact p.Prime] [Fact r.Prime]
    (hr2 : r ≠ 2) (hrp : r ≠ p) (hd : r ∣ p^2 + 1)
    {G : Type*} [Group G] [Finite G] (hG : IsPGroup r G)
    (f : G →* GL (Fin 4) (ZMod p)) (hf : Function.Injective f) : IsCyclic G := by
  classical
  rcases subsingleton_or_nontrivial G with htriv | hnontriv
  · infer_instance
  let := hG.center_nontrivial
  have hZ := hG.to_subgroup (Subgroup.center G)
  obtain ⟨n, hn, hnc⟩ := hZ.nontrivial_iff_card.mp inferInstance
  have hrZ : r ∣ Nat.card (Subgroup.center G) := by
    rw [hnc]
    exact dvd_pow_self r (ne_of_gt hn)
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' r hrZ
  let A := Subgroup.zpowers z
  let j : A →* GL (Fin 4) (ZMod p) :=
    f.comp ((Subgroup.center G).subtype.comp A.subtype)
  have hj : Function.Injective j :=
    hf.comp ((Subgroup.center G).subtype_injective.comp A.subtype_injective)
  let C := j.range
  have hC : Nat.card C = r := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hj).toEquiv, Nat.card_zpowers, hz]
  have : NeZero (Fintype.card C : ZMod p) := by
    constructor
    rw [← Nat.card_eq_fintype_card, hC]
    intro h
    have hdiv := (ZMod.natCast_eq_zero_iff r p).mp h
    exact hrp (((Nat.dvd_prime (Fact.out : r.Prime)).mp hdiv).resolve_left
      (Fact.out : p.Prime).ne_one).symm
  let := isCyclic_centralizer (Fact.out : r.Prime) hr2 C hC
    (by simpa only [ZMod.card] using hd)
  let k : G →* Subgroup.centralizer (C : Set (GL (Fin 4) (ZMod p))) :=
    f.codRestrict _ (by
      intro g
      apply Subgroup.mem_centralizer_iff.mpr
      rintro _ ⟨a, rfl⟩
      simpa only [map_mul, j, MonoidHom.comp_apply, Subgroup.subtype_apply] using
        (congrArg f (Subgroup.mem_center_iff.mp a.val.property g)).symm)
  exact isCyclic_of_injective k (fun a b h => hf (congrArg Subtype.val h))

/-- An odd prime dividing p²+1 has cyclic Sylow subgroups in the actual
symplectic four-space matrix group. -/
public theorem sylow_isCyclic_of_dvd_sq_add_one
    {p r : ℕ} [Fact p.Prime] [Fact r.Prime]
    (_hp : 3 < p) (hr2 : r ≠ 2) (hrp : r ≠ p) (hd : r ∣ p^2 + 1)
    (P : Sylow r (Sp (ZMod p))) : IsCyclic P := by
  classical
  let μ : Sp (ZMod p) →* Matrix (Fin 4) (Fin 4) (ZMod p) :=
    (Matrix.reindexRingEquiv (ZMod p)
      (finSumFinEquiv : Fin 2 ⊕ Fin 2 ≃ Fin 4)).toMonoidHom.comp
        (Matrix.symplecticGroup (Fin 2) (ZMod p)).subtype
  have hμ : Function.Injective μ :=
    (Matrix.reindexRingEquiv (ZMod p) finSumFinEquiv).injective.comp Subtype.val_injective
  let ρ : Sp (ZMod p) →* GL (Fin 4) (ZMod p) := μ.toHomUnits
  have hρ : Function.Injective ρ := fun a b h => hμ (congrArg Units.val h)
  exact isCyclic_of_isPGroup hr2 hrp hd P.isPGroup'
    (ρ.comp (P : Subgroup (Sp (ZMod p))).subtype)
    (hρ.comp (P : Subgroup (Sp (ZMod p))).subtype_injective)

/-- Cyclic Sylow transfer excludes the quartic primes from every finite
perfect central cover of the actual Sp₄(p). This supplies the quartic branch
of the I.1.2 application in the odd-prime multiplier calculation. -/
public theorem not_dvd_card_kernel_of_dvd_sq_add_one
    {p r : ℕ} [Fact p.Prime] [Fact r.Prime]
    (hp : 3 < p) (hr2 : r ≠ 2) (hrp : r ≠ p) (hd : r ∣ p^2 + 1)
    {E : Type*} [Group E] [Finite E]
    (f : PerfectCentralCovering.Cover E (Sp (ZMod p))) :
    ¬ r ∣ Nat.card f.toMonoidHom.ker :=
  f.not_dvd_card_multiplier_of_isCyclic_sylow
    (sylow_isCyclic_of_dvd_sq_add_one hp hr2 hrp hd)

end Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.LargeSections.OddNondefining.Quartic
