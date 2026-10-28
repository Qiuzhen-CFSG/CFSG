module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.SylowOvergroups.EvenLieOvergroups.Transport
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Lifting.Transport
public import Theory.GroupTheory.NormalSylowCoreCentralizer
public import Theory.GroupTheory.GeneralizedFitting.SolvableNormalKernel

/-!
# Proper Sylow overgroups in the even Lie rank-one branch

The source bound on a proper Sylow overgroup is a characteristic-two
calculation.  The rank-one model supplies the two ingredients which are
independent of the component recognition argument: every proper overgroup of
the chosen Sylow lies in its solvable normalizer, and the ambient centralizer
of that Sylow is contained in its Sylow subgroup together with the centre.
The latter is retained as an explicit model calculation, so central covers
are handled by the displayed centre factor rather than by the invalid raw
identity `F*(X) = O₂(X)`.

Source: Aschbacher–Smith, combined manuscript, B.1.13, printed p.74
(PDF p.85), with the concrete rank-one calculations from F.1.3(1), printed
pp.259–260.
-/

public section

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups

variable {L : Type*} [Group L] [Finite L]

/-- The model-specific centralizer clause used in the proper-overgroup proof.
It is stated in the ambient model, so a central factor is preserved when the
result is transported to a covering component. -/
@[expose] def SylowCenterControl (L : Type*) [Group L] : Prop :=
  ∀ S : Sylow 2 L,
    centralizer (S : Set L) ≤ center L ⊔ (S : Subgroup L)

private theorem pPrimeCore_le_target (S : Sylow 2 L) (X : Subgroup L)
    (hSX : (S : Subgroup L) ≤ X) (hXN : X ≤ normalizer (S : Set L))
    (hcenter : SylowCenterControl L) :
    pPrimeCore 2 X ≤ (center L).subgroupOf X ⊔ pCore 2 X := by
  let SX : Sylow 2 X := S.subtype hSX
  let : (SX : Subgroup X).Normal := by
    apply (normal_subgroupOf_iff_le_normalizer hSX).mpr
    exact hXN
  have hcentral : pPrimeCore 2 X ≤ centralizer (SX : Set X) :=
    Sylow.pPrimeCore_le_centralizer_of_normal SX
  intro x hx
  have hcentralL : (x : L) ∈ centralizer (S : Set L) := by
    intro s hs
    have hsX : (⟨s, hSX hs⟩ : X) ∈ (SX : Subgroup X) := by
      change s ∈ S
      exact hs
    have hc := hcentral hx (⟨s, hSX hs⟩ : X) hsX
    exact congrArg Subtype.val hc
  obtain ⟨z, hz, s, hs, hzs⟩ :=
    (mem_sup_of_normal_left.mp (hcenter S hcentralL))
  have hsX : s ∈ X := hSX hs
  have hzX : z ∈ X := by
    have hzEq : (x : L) * s⁻¹ = z := by
      rw [← hzs]
      simp
    rw [← hzEq]
    exact X.mul_mem x.property (X.inv_mem hsX)
  have hsCore : (⟨s, hsX⟩ : X) ∈ pCore 2 X := by
    have hSXcore : (SX : Subgroup X) ≤ pCore 2 X :=
      le_sSup ⟨inferInstance, SX.isPGroup'⟩
    apply hSXcore
    change s ∈ S
    exact hs
  refine (mem_sup_of_normal_left.mpr ?_)
  refine ⟨⟨z, hzX⟩, ?_, ⟨s, hsX⟩, hsCore, ?_⟩
  · exact hz
  · apply Subtype.ext
    exact hzs

set_option linter.unusedSectionVars false in
private theorem fitting_le_target (S : Sylow 2 L) (X : Subgroup L)
    (hSX : (S : Subgroup L) ≤ X) (hXN : X ≤ normalizer (S : Set L))
    (hsolv : Group.IsSolvable (normalizer (S : Set L)))
    (hcenter : SylowCenterControl L) :
    generalizedFitting X ≤ (center L).subgroupOf X ⊔ pCore 2 X := by
  let : Group.IsSolvable (normalizer (S : Set L)) := hsolv
  let : Group.IsSolvable X :=
    Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion hXN) (Subgroup.inclusion_injective hXN)
  have hcomponent : componentLayer X = ⊥ := by
    apply sSup_eq_bot.mpr
    intro K hK
    let : (fittingSubgroup X).Normal := inferInstance
    let : Group.IsSolvable (fittingSubgroup X) :=
      Group.isSolvable_of_isSolvable_injective
        (f := (fittingSubgroup X).subtype) (fittingSubgroup X).subtype_injective
    exact (not_isComponent_of_solvable_normal_selfCentralizing
      (Q := fittingSubgroup X)
      (centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable inferInstance)
      K hK).elim
  rw [generalizedFitting, hcomponent, sup_bot_eq]
  rw [fitting_eq_sup_pCore X]
  refine iSup_le fun q => ?_
  let : Fact q.1.1.Prime := ⟨Nat.prime_of_mem_primeFactors q.1.property⟩
  by_cases hq : q.1.1 = 2
  · rw [hq]
    exact le_sup_right
  · have hqcore : pCore q.1.1 X ≤ pPrimeCore 2 X := by
      apply le_sSup
      have hcard := (pCore_isPGroup (p := q.1.1) (G := X)).exists_card_eq
      obtain ⟨n, hn⟩ := hcard
      exact ⟨inferInstance, by
        rw [hn]
        exact (Nat.coprime_primes (by decide : Nat.Prime 2)
          (Fact.out : q.1.1.Prime)).mpr (Ne.symm hq) |>.pow_right n⟩
    exact hqcore.trans (pPrimeCore_le_target S X hSX hXN hcenter)

/-- Proper Sylow overgroups satisfy the source Fitting bound once the actual
model supplies its Sylow-centralizer containment. -/
public theorem properSylowFittingBound_of_rankOne
    (hrank : ∀ S : Sylow 2 L, CFSG.Quasithin.ChapterF.Source.RankOneSylowFacts S)
    (hcenter : SylowCenterControl L) :
    ProperSylowFittingBound L := by
  intro S X hSX hX
  have hXN : X ≤ normalizer (S : Set L) :=
    (hrank S).unique_maximal X hSX (lt_top_iff_ne_top.mpr hX)
  simpa only [sup_comm] using fitting_le_target S X hSX hXN (hrank S).solvable hcenter

private theorem selfCentralizing_sylow_transport {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (S : Sylow 2 G) (T : Sylow 2 H)
    (hST : (S : Subgroup G).map e.toMonoidHom = (T : Subgroup H))
    (hc : centralizer (S : Set G) ≤ (S : Subgroup G)) :
    centralizer (T : Set H) ≤ (T : Subgroup H) := by
  intro x hx
  have hx' : e.symm x ∈ centralizer (S : Set G) := by
    intro y hy
    have hey : e y ∈ (T : Subgroup H) := by
      rw [← hST]
      exact ⟨y, hy, rfl⟩
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using
      hx (e y) hey
  rw [← hST]
  exact ⟨e.symm x, hc hx', e.apply_symm_apply x⟩

/-- A self-centralizing standard Sylow gives the centralizer bound for every Sylow. -/
theorem sylowCenterControl_of_selfCentralizing_sylow {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (hc : centralizer (S : Set G) ≤ (S : Subgroup G)) :
    SylowCenterControl G := by
  intro T
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S T
  have hST : (S : Subgroup G).map (MulAut.conj g).toMonoidHom = (T : Subgroup G) := by
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  exact (selfCentralizing_sylow_transport (MulAut.conj g) S T hST hc).trans le_sup_right

/-- Pull the Sylow-centralizer bound back along an actual model equivalence. -/
theorem sylowCenterControl_of_equiv {G H : Type*} [Group G] [Group H] [Finite G]
    (e : G ≃* H) (hc : SylowCenterControl H) : SylowCenterControl G := by
  intro S x hx
  let T := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hx' : e x ∈ centralizer (T : Set H) := by
    rintro _ ⟨y, hy, rfl⟩
    change e y * e x = e x * e y
    simpa only [map_mul] using congrArg e (hx y hy)
  obtain ⟨z, hz, s, hs, hzs⟩ := mem_sup_of_normal_left.mp (hc T hx')
  obtain ⟨s, hs, rfl⟩ := hs
  have hz' : e.symm z ∈ center G := by
    apply mem_center_iff.mpr
    intro y
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using mem_center_iff.mp hz (e y)
  refine mem_sup_of_normal_left.mpr ⟨e.symm z, hz', s, hs, ?_⟩
  apply e.injective
  change z * e s = e x at hzs
  simpa only [map_mul, e.apply_symm_apply] using hzs

/-- Transport the rank-one model calculation without changing the ambient centre. -/
theorem properSylowFittingBound_of_rankOne_equiv {G H : Type*}
    [Group G] [Group H] [Finite G]
    (e : G ≃* H)
    (hrank : ∀ S : Sylow 2 H, CFSG.Quasithin.ChapterF.Source.RankOneSylowFacts S)
    (hcenter : SylowCenterControl H) : ProperSylowFittingBound G := by
  let : Finite H := Finite.of_surjective e e.surjective
  exact properSylowFittingBound_of_equiv e
    (properSylowFittingBound_of_rankOne hrank hcenter)

end CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups
