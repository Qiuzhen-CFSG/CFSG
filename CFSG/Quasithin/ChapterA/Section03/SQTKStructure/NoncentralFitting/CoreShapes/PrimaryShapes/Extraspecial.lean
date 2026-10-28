module

public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NoncentralFitting.CoreShapes.PrimaryShapes.Seeds
public import Theory.ElementaryAbelian.ExtraspecialEquiv
import Mathlib.Tactic.Group

/-!
# Saturation of an extraspecial supercritical seed

The order-p centralizer condition puts each elementary abelian subgroup of
C_S(X) into Z(X), which has order p. The odd-prime rank-one theorem makes
C_S(X) cyclic. Its characteristic image in the perfect ambient component is
therefore central. A.1.23, applied to the actual Fitting action kernel,
gives S ≤ Z(L)X.

To apply cover rigidity without a single-prime support assumption, adjoin
the complementary factor F(L) ∩ O_{p'}(L) to X. The resulting normal subgroup
centrally supplements F(L), so rigidity makes it all of F(L). Intersecting
with O_p(L) removes the complementary factor and proves X = O_p(L).
The final theorem transports extraspeciality, order p³ and exponent p.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
A.3.6, printed pp.44–45, the extraspecial argument using (*) and (!).
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterA.RankActions
open CFSG.Quasithin.Chapter1.Section02 LocalModels
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterA.Section03.NoncentralFitting.CoreShapes.PrimaryShapes
universe u
variable {A : Type u} [Group A] [Finite A] {p : ℕ} [Fact p.Prime]

private theorem seed_centralizer_cyclic (s : PrimarySeed p A)
    [IsExtraspecial p s.X] : IsCyclic (centralizer (s.X : Set (pCore p A))) := by
  let S := pCore p A
  let C := centralizer (s.X : Set S)
  apply (pCore_isPGroup.to_subgroup C).isCyclic_of_odd_of_elementary_card_le s.odd
  intro E hE
  let : IsElementaryAbelian p E := hE
  have hm (z : E) : ((z : C) : S) ∈ s.X := by
    by_cases hz : ((z : C) : S) = 1
    · exact hz ▸ s.X.one_mem
    · apply s.supercritical.order_p_mem _ (z : C).property
      apply orderOf_eq_prime_iff.mpr
      refine ⟨?_, hz⟩
      exact congrArg (fun y : E => ((y : C) : S))
        (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p p E) z)
  let f : E →* center s.X := {
    toFun z := ⟨⟨((z : C) : S), hm z⟩, by
      apply mem_center_iff.mpr
      intro y
      apply Subtype.ext
      exact (z : C).property y y.property⟩
    map_one' := by apply Subtype.ext; apply Subtype.ext; rfl
    map_mul' _ _ := by apply Subtype.ext; apply Subtype.ext; rfl }
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : center s.X => ((z : s.X) : S)) h
  exact (Nat.card_le_card_of_injective f hf).trans_eq
    (IsExtraspecial.center_order_p p s.X)

/-- A.1.23 expresses every element of the primary core as a seed element
and an element of its centralizer. Perfectness centralizes that cyclic factor. -/
theorem core_le_center_sup_seed [Group.IsPerfect A]
    (s : PrimarySeed p A) [IsExtraspecial p s.X] :
    pCore p A ≤ center A ⊔ s.X.map (pCore p A).subtype := by
  let S := pCore p A
  let C := centralizer (s.X : Set S)
  let D := C.map S.subtype
  let : IsCyclic C := seed_centralizer_cyclic s
  let : IsCyclic D := isCyclic_of_surjective
    (C.equivMapOfInjective S.subtype S.subtype_injective).toMonoidHom
    (C.equivMapOfInjective S.subtype S.subtype_injective).surjective
  have hcentral : D ≤ center A := by
    have hc : (⊤ : Subgroup A) ≤ centralizer (D : Set A) := by
      simpa only [Group.IsPerfect.commutator_eq_top] using
        commutator_le_centralizer_of_isCyclic_normal D
    intro x hx
    apply mem_center_iff.mpr
    intro g
    exact (hc (mem_top g) x hx).symm
  intro g hg
  let gS : S := ⟨g,hg⟩
  have hinner : coreAction s.X g ∈ (MulAut.conj : s.X →* MulAut s.X).range := by
    rw [CFSG.Quasithin.ChapterA.lemma_A_1_23 (p := p)]
    exact s.frattini_fixed g (pCore_le_fitting A p hg)
  obtain ⟨x, hx⟩ := hinner
  have hcx : (x : S)⁻¹ * gS ∈ C := by
    intro y hy
    let yX : s.X := ⟨y,hy⟩
    have he := congrArg (fun f : MulAut s.X => (f yX : S)) hx.symm
    change gS * y * gS⁻¹ = (x : S) * y * (x : S)⁻¹ at he
    have hh := congrArg (fun z : S => (x : S)⁻¹ * z * gS) he
    group at hh
    simpa only [zpow_neg_one, mul_assoc] using hh.symm
  have hD : (((x : S)⁻¹ * gS : S) : A) ∈ center A :=
    hcentral (mem_map_of_mem S.subtype hcx)
  have hxP : ((x : S) : A) ∈ s.X.map S.subtype := mem_map_of_mem S.subtype x.property
  have hm := (center A ⊔ s.X.map S.subtype).mul_mem
    (mem_sup_right hxP) (mem_sup_left hD)
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left] using hm

variable {G : Type u} [Group G] [Finite G] {L : Subgroup G}

private theorem primary_eq_of_central_supplement
    (hrigid : PrimeSL2CoverRigidity.{u}) (hL : L.IsCComponent)
    (hquot : PrimeSL2FittingQuotient L)
    (P : Subgroup L) [P.Normal] (hP : P ≤ pCore p L)
    (hs : pCore p L ≤ center L ⊔ P) : pCore p L = P := by
  let F := fittingSubgroup L
  let D := F ⊓ pPrimeCore p L
  let N := P ⊔ D
  have hsplit : F ≤ pCore p L ⊔ D := by
    dsimp [F]
    rw [fitting_eq_sup_pCore]
    refine iSup_le fun r => ?_
    let : Fact r.val.val.Prime := ⟨Nat.prime_of_mem_primeFactors r.val.property⟩
    by_cases heq : r.val.val = p
    · rw [heq]
      exact le_sup_left
    · apply le_trans (show pCore r.val.val L ≤ D from ?_) le_sup_right
      apply le_inf (pCore_le_fitting L _)
      apply le_sSup
      refine ⟨inferInstance, ?_⟩
      obtain ⟨n, hn⟩ := (pCore_isPGroup (p := r.val.val) (G := L)).exists_card_eq
      rw [hn]
      exact ((Nat.coprime_primes (Fact.out : p.Prime)
        (Fact.out : r.val.val.Prime)).mpr (fun hh => heq hh.symm)).pow_right n
  have hS : pCore p L ≤ center L ⊔ N :=
    hs.trans (sup_le le_sup_left (le_sup_left.trans le_sup_right))
  have hF : F = center L ⊔ N := le_antisymm
    (hsplit.trans (sup_le hS (le_sup_right.trans le_sup_right)))
    (sup_le (le_sSup ⟨inferInstance, inferInstance⟩)
      (sup_le (hP.trans (pCore_le_fitting L p)) inf_le_left))
  have heq := fitting_central_supplement hrigid hL hquot N hF
  have hSN : pCore p L ≤ N := (pCore_le_fitting L p).trans heq.le
  have hdis : Disjoint (pCore p L) (pPrimeCore p L) := by
    obtain ⟨n, hn⟩ := (pCore_isPGroup (p := p) (G := L)).exists_card_eq
    apply disjoint_of_coprime_natCard
    rw [hn]
    exact (pPrimeCore_coprime_card (p := p) (G := L)).pow_left n
  apply le_antisymm ?_ hP
  intro g hg
  obtain ⟨x, hx, y, hy, hxy⟩ := mem_sup_of_normal_right.mp (hSN hg)
  have hyS : y ∈ pCore p L := by
    have hm := (pCore p L).mul_mem ((pCore p L).inv_mem (hP hx)) hg
    rw [← hxy, inv_mul_cancel_left] at hm
    exact hm
  have hy1 : y = 1 := Subgroup.disjoint_def.mp hdis hyS hy.2
  simpa only [hy1, mul_one] using hxy ▸ (show x * y ∈ P from by simpa [hy1] using hx)

/-- The extraspecial supercritical subgroup fills the entire primary core.
This is the full-core conclusion, including order p³ and exponent p. -/
theorem extraspecial_core
    (hrigid : PrimeSL2CoverRigidity.{u}) (hL : L.IsCComponent)
    (hquot : PrimeSL2FittingQuotient L)
    (s : PrimarySeed p L) (he : OddExtraspecialThree p s.X) :
    OddExtraspecialThree p (pCore p L) := by
  let : Group.IsPerfect L := hL.perfect
  let : IsExtraspecial p s.X := he.1.1
  have heq := primary_eq_of_central_supplement hrigid hL hquot
    (s.X.map (pCore p L).subtype)
    (by rintro _ ⟨x, _, rfl⟩; exact x.property)
    (core_le_center_sup_seed s)
  have htop : s.X = ⊤ := by
    apply top_unique
    intro x _
    have hm : (x : L) ∈ s.X.map (pCore p L).subtype := heq ▸ x.property
    obtain ⟨y, hy, hyx⟩ := hm
    exact (Subtype.ext hyx : y = x) ▸ hy
  let e : s.X ≃* pCore p L := (MulEquiv.subgroupCongr htop).trans topEquiv
  refine ⟨⟨IsExtraspecial.of_mulEquiv e he.1.1, ?_⟩, ?_⟩
  · exact (Nat.card_congr e.toEquiv).symm.trans he.1.2
  · intro x
    obtain ⟨y, rfl⟩ := e.surjective x
    rw [← map_pow, he.2, map_one]

end CFSG.Quasithin.ChapterA.Section03.NoncentralFitting.CoreShapes.PrimaryShapes
