module
public import Theory.GroupTheory.PGroup.Omega
public import Theory.Frattini.PGroup
public import Theory.GroupTheory.CyclicNormalCentralizer
public import Mathlib.GroupTheory.IsPerfect
public import Theory.GroupTheory.Fitting.Core

/-!
# Central intersections detected by the first omega layer

In a perfect finite group a cyclic normal subgroup is central. Suppose
P is a normal p-group, either abelian or of exponent p, and Φ(Ω₁(P)) is
cyclic. A subgroup meeting Ω₁(P) only in Φ(Ω₁(P)) meets P centrally.
In the abelian branch Cauchy's theorem makes the intersection trivial;
in the exponent-p branch Ω₁(P)=P. No bound on an abelian P's exponent
is used. Primewise central intersections then assemble inside the Fitting
subgroup using its nilpotent Sylow decomposition.

Source application: Aschbacher--Smith 13.1.9, printed p.869. The actual
canonical radicals use Ω₁(Oₚ), including higher homocyclic exponents.
-/

public section
open Subgroup
open scoped IsMulCommutative

namespace Subgroup
variable {G : Type*} [Group G] [Finite G] [Group.IsPerfect G]
variable {p : ℕ} [Fact p.Prime]

/-- A subgroup meeting the first omega group only in its cyclic Frattini
subgroup has central intersection with the normal prime group. The
abelian branch retains arbitrary exponent. -/
theorem inf_le_center_of_omega_frattini (D P : Subgroup G) [P.Normal]
    (hp : IsPGroup p P)
    (hshape : IsMulCommutative P ∨ ∀ x : P, x ^ p = 1)
    (hcyc : IsCyclic (frattini (omega P (p := p) 1)))
    (hD : D ⊓ (omega P (p := p) 1).map P.subtype ≤
      ((frattini (omega P (p := p) 1)).map (omega P (p := p) 1).subtype).map P.subtype) :
    D ⊓ P ≤ center G := by
  let W := omega P (p := p) 1
  let A := (frattini W).map W.subtype
  let Z := A.map P.subtype
  let : W.Characteristic := omega_characteristic P 1
  let : A.Characteristic := characteristic_of_characteristic_of_characteristic
  let : Z.Normal := inferInstance
  let : IsCyclic (frattini W) := hcyc
  let : IsCyclic A := isCyclic_of_surjective ((frattini W).equivMapOfInjective
    W.subtype W.subtype_injective).toMonoidHom
    ((frattini W).equivMapOfInjective W.subtype W.subtype_injective).surjective
  let : IsCyclic Z := isCyclic_of_surjective (A.equivMapOfInjective
    P.subtype P.subtype_injective).toMonoidHom
    (A.equivMapOfInjective P.subtype P.subtype_injective).surjective
  have hZ : Z ≤ center G := by
    have hc := commutator_le_centralizer_of_isCyclic_normal Z
    rw [Group.IsPerfect.commutator_eq_top] at hc
    intro z hz
    exact mem_center_iff.mpr (fun g => (hc (mem_top g) z hz).symm)
  rcases hshape with hab | hexp
  · let := hab
    let : IsElementaryAbelian p W := IsElementaryAbelian.omega₁_of_isMulCommutative P
    let : Fact (IsPGroup p W) := ⟨IsElementaryAbelian.isPGroup p W⟩
    have hz : Z = ⊥ := by
      dsimp only [Z,A]
      rw [frattini_eq_bot_of_isElementaryAbelian (p := p),map_bot,map_bot]
    have hzero : D ⊓ P = ⊥ := by
      apply eq_bot_of_card_eq
      rcases (hp.to_le (show D ⊓ P ≤ P from inf_le_right)).card_eq_or_dvd with hc | hd
      · exact hc
      · obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(D ⊓ P)) p hd
        have hxpow : (x : G) ^ p = 1 := by
          have he := pow_orderOf_eq_one x
          rw [hx] at he
          exact congrArg Subtype.val he
        have hxm : (x : G) ∈ W.map P.subtype := by
          refine ⟨⟨x,x.property.2⟩,subset_closure ?_,rfl⟩
          change (⟨x,x.property.2⟩ : P) ^ (p ^ 1) = 1
          exact Subtype.ext (by simpa only [coe_pow,coe_one,pow_one] using hxpow)
        have he : (x : G) = 1 := mem_bot.mp (hz ▸ hD ⟨x.property.1,hxm⟩)
        have he' : x = 1 := Subtype.ext he
        have hbad : p = 1 := by simpa only [he',orderOf_one] using hx.symm
        exact ((Fact.out : p.Prime).ne_one hbad).elim
    rw [hzero]
    exact bot_le
  · have hW : W = ⊤ := by
      apply top_unique
      intro x _
      exact subset_closure (by simpa only [Set.mem_ofPred_eq,pow_one] using hexp x)
    have hm : W.map P.subtype = P := by
      rw [hW,← MonoidHom.range_eq_map,range_subtype]
    exact (hm ▸ hD).trans hZ

omit [Group.IsPerfect G] in
/-- Central prime-core intersections give a central Fitting intersection,
by the Sylow decomposition inside the actual nilpotent intersection. -/
theorem inf_fitting_le_center_of_prime_intersections (D : Subgroup G)
    (hc : ∀ p : ℕ, p.Prime → p ∣ Nat.card (fittingSubgroup G) →
      D ⊓ pCore p G ≤ center G) : D ⊓ fittingSubgroup G ≤ center G := by
  let F := fittingSubgroup G
  let E := D.subgroupOf F
  let f : E →* G := F.subtype.comp E.subtype
  have hg : (⊤ : Subgroup E).map f ≤ center G := by
    rw [← fitting_eq_top_of_nilpotent E, fitting_eq_sup_pCore, map_iSup]
    apply iSup_le
    intro r
    let p := r.val.val
    have hprime : p.Prime := Nat.prime_of_mem_primeFactors r.val.property
    let : Fact p.Prime := ⟨hprime⟩
    have hdiv : p ∣ Nat.card F :=
      (Nat.dvd_of_mem_primeFactors r.val.property).trans (card_subgroup_dvd_card E)
    obtain ⟨S,hS⟩ := (pCore_isPGroup.map E.subtype :
      IsPGroup p ((pCore p E).map E.subtype)).exists_le_sylow
    have hle : (pCore p E).map f ≤ pCore p G := by
      change ((pCore p E).map (F.subtype.comp E.subtype)) ≤ _
      rw [← map_map]
      exact (map_mono hS).trans (S.map_le_pCore inferInstance inferInstance p)
    apply le_trans (le_inf ?_ hle) (hc p hprime hdiv)
    rintro x ⟨a,ha,rfl⟩
    exact a.property
  intro x hx
  exact hg (mem_map_of_mem f (show (⟨⟨x,hx.2⟩,hx.1⟩ : E) ∈ ⊤ from mem_top _))
end Subgroup
