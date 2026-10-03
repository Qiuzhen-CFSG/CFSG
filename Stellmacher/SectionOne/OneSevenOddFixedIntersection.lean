module
public import Stellmacher.SectionOne.OneSevenIdentification
public import Theory.GroupTheory.OddCyclicThreeNormalizer
public import Theory.GroupTheory.CardFourAutomorphismStabilizer
public import Theory.GroupAction.NormalizingActor

/-!
# Odd fixed spaces meet two-group fixed spaces in a one-seven family

Let a family of one-seven factors generate `E`, and let a two-subgroup `B ≤ E`
normalize every factor. If a subgroup `F` of the ambient odd core has a
nontrivial fixed space on the elementary two-module, then that space contains
a nonidentity vector fixed by `B`. No normality of `F` or invariance of its
fixed space under `B` is assumed, and the factor index type need not be finite.
The global corollary specializes to `B = oneJ(V,S)` and the actual canonical
one-seven factors, with no nontriviality assumption on `oneJ`.

Choose a nonidentity `F`-fixed vector. If every factor fixes it, then `B` does.
Otherwise some factor's derived C3 moves it. The odd core normalizes, hence
centralizes, that C3. Its nontrivial displacement is therefore `F`-fixed and
lies in the factor's four-element support. The odd action image of `F` on that
support fixes a nonidentity point, so has order at most two and must be
trivial. The two-group `B` preserves this support and has a nonidentity fixed
point on it, which is the required common fixed vector.

This is the fixed-space argument behind the use of (2.2) in Stellmacher
(9.1), Journal of Algebra 190 (1997), p.47. It uses the actual one-seven
factor predicate and exact supplied action; no full local classification or
independence stronger than that supplied by the factor definitions is used.
-/

namespace Stellmacher.SectionOne
universe u v
open Subgroup

public theorem oneSeven_odd_fixed_inf_two_fixed_ne_bot
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    {ι : Type v} (D : ι → Subgroup G)
    (hD : ∀ i, IsOneSevenFactor (V := V) (D i))
    (E B F : Subgroup G) (hE : E = ⨆ i, D i) (hBE : B ≤ E)
    (hB : IsPGroup 2 B) (hBD : ∀ i, B ≤ normalizer (D i : Set G))
    (hF : F ≤ oddCore G) (hfix : FixedPoints.subgroup F V ≠ ⊥) :
    FixedPoints.subgroup F V ⊓ FixedPoints.subgroup B V ≠ ⊥ := by
  classical
  obtain ⟨y,hy,hyne⟩ : ∃ y ∈ FixedPoints.subgroup F V, y ≠ 1 := by
    by_contra! hh
    exact hfix (eq_bot_iff.mpr hh)
  have hFodd : Nat.Coprime 2 (Nat.card F) :=
    (pPrimeCore_coprime_card (p := 2) (G := G)).of_dvd_right (card_dvd_of_le hF)
  by_cases hall : ∀ i, y ∈ FixedPoints.subgroup (D i) V
  · have hEy : E ≤ fixingSubgroup G ({y} : Set V) := by
      rw [hE]
      apply iSup_le
      intro i d hd
      rw [mem_fixingSubgroup_iff]
      intro z hz
      rw [Set.mem_singleton_iff.mp hz]
      exact hall i ⟨d,hd⟩
    have hyB : y ∈ FixedPoints.subgroup B V := by
      intro b
      exact (mem_fixingSubgroup_iff (M := G)).mp (hEy (hBE b.property)) y (Set.mem_singleton y)
    intro hh
    have hhmem : y ∈ FixedPoints.subgroup F V ⊓ FixedPoints.subgroup B V := ⟨hy,hyB⟩
    rw [hh,mem_bot] at hhmem
    exact hyne hhmem
  · push Not at hall
    obtain ⟨i,hi⟩ := hall
    let K := (commutator (D i)).map (D i).subtype
    let U := commutatorAction (D i) V
    have hKy : y ∉ FixedPoints.subgroup K V := by
      intro hyK
      apply hi
      intro d
      exact oneSevenFactor_fixes_derived_fixedPoints (D i) (hD i) d d.property y hyK
    obtain ⟨k,hk⟩ : ∃ k : K, (k : G) • y ≠ y := by
      by_contra! hh
      exact hKy hh
    have hFK : K ≤ centralizer (F : Set G) :=
      commutator_eq_bot_iff_le_centralizer.mp
        (commutator_eq_bot_of_odd_normalizes_card_three K F (hD i).2.1.2.1 hFodd
          (hF.trans (oneSevenFactor_oddCore_normalizes_derived (D i) (hD i))))
    let d := y⁻¹ * (k : G) • y
    have hdU : d ∈ U := by
      rw [show U = commutatorAction K V from oneSevenFactor_full_commutator_eq_derived (D i) (hD i),
        commutatorAction_eq_closure]
      exact subset_closure ⟨k,y,rfl⟩
    have hdne : d ≠ 1 := by
      intro hh
      exact hk (inv_mul_eq_one.mp hh).symm
    have hdF : d ∈ FixedPoints.subgroup F V := by
      intro f
      change (f : G) • (y⁻¹ * (k : G) • y) = y⁻¹ * (k : G) • y
      rw [smul_mul',smul_inv',show (f : G) • y = y from hy f]
      congr 1
      rw [← mul_smul,hFK k.property f f.property,mul_smul]
      rw [show (f : G) • y = y from hy f]
    have hFD : F ≤ normalizer (D i : Set G) := hF.trans
      ((show oddCore G ≤ oddCore G ⊔ D i from le_sup_left).trans
        ((normal_subgroupOf_iff_le_normalizer le_sup_right).mp (hD i).2.2.2))
    let _ : IsInvariant F V U := commutatorAction_isInvariant_of_normalizing_actor F (D i) hFD
    let f := MulDistribMulAction.toMulAut F U
    have himage : Nat.card f.range ≤ 2 :=
      card_mulAut_subgroup_le_two_of_fixed_point (hD i).2.2.1 ⟨d,hdU⟩
        (fun hh => hdne (congrArg Subtype.val hh)) f.range (by
          rintro a ⟨a,rfl⟩
          exact Subtype.ext (hdF a))
    have himageodd : Nat.Coprime 2 (Nat.card f.range) :=
      hFodd.of_dvd_right (card_range_dvd f)
    have himage1 : Nat.card f.range = 1 := by
      have hp : 0 < Nat.card f.range := Nat.card_pos
      have hc : Nat.card f.range = 1 ∨ Nat.card f.range = 2 := by omega
      rcases hc with hc | hc
      · exact hc
      · rw [hc] at himageodd
        norm_num at himageodd
    have hUF : U ≤ FixedPoints.subgroup F V := by
      intro u hu a
      have hf : f a = 1 := by
        have hh : f a ∈ f.range := ⟨a,rfl⟩
        rwa [Subgroup.card_eq_one.mp himage1,mem_bot] at hh
      exact congrArg Subtype.val (DFunLike.congr_fun hf (⟨u,hu⟩ : U))
    let _ : IsInvariant B V U := commutatorAction_isInvariant_of_normalizing_actor B (D i) (hBD i)
    have hdiv : 2 ∣ Nat.card U := by rw [show Nat.card U = 4 from (hD i).2.2.1]; decide
    have hone : (1 : U) ∈ MulAction.fixedPoints B U := by intro b; exact smul_one b
    obtain ⟨u,hu,hune⟩ := hB.exists_fixed_point_of_prime_dvd_card_of_fixed_point U hdiv hone
    have huB : (u : V) ∈ FixedPoints.subgroup B V := fun b => congrArg Subtype.val (hu b)
    intro hh
    have hu1 : (u : V) ∈ FixedPoints.subgroup F V ⊓ FixedPoints.subgroup B V :=
      ⟨hUF u.property,huB⟩
    rw [hh,mem_bot] at hu1
    exact hune (Subtype.ext hu1.symm)

/-- The global one-seven Sylow intersection fixes a nonidentity vector in
every nontrivial odd-core fixed space. -/
public theorem oneSeven_odd_fixed_inf_oneJ_ne_bot
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) (S : Sylow 2 G) (F : Subgroup G)
    (hF : F ≤ oddCore G) (hfix : FixedPoints.subgroup F V ≠ ⊥) :
    FixedPoints.subgroup F V ⊓
      FixedPoints.subgroup (oneJ (V := V) (S : Subgroup G)) V ≠ ⊥ := by
  let E := oneSevenGenerated (G := G) (V := V)
  let factors := oneSevenFactors (G := G) (V := V)
  let I := {D : Subgroup G // D ∈ factors}
  let D : I → Subgroup G := Subtype.val
  obtain ⟨_,hprod,hJE⟩ := oneSeven_global_product h S
  have hJS : oneJ (V := V) (S : Subgroup G) ≤ (S : Subgroup G) :=
    sSup_le fun A hA => hA.1
  apply oneSeven_odd_fixed_inf_two_fixed_ne_bot D
    (fun i => (mem_oneSevenFactors_iff i.val).mp i.property) E
    (oneJ (V := V) (S : Subgroup G)) F hprod.1 hJE (S.isPGroup'.to_le hJS) ?_ hF hfix
  intro i
  have hDE : D i ≤ E := by rw [show E = ⨆ i : I, D i from hprod.1]; exact le_iSup D i
  exact hJE.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hDE).mp
    (hprod.2.1 i.val i.property))

end Stellmacher.SectionOne
