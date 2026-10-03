module
public import Stellmacher.SectionOne.OneSevenIdentification
public import Stellmacher.SectionOne.OneSevenModuleProduct

/-!
# Covering the one-seven fixed space by fixed and commutator parts

For the faithful elementary two-group action satisfying the Section One
hypotheses, the fixed space of the canonical subgroup J(V,S) is contained
in the join of the E(V,S)-fixed space and the J-action commutator. This also
covers the case J = 1 and supplies the fixed-closure reduction in (8.4).

For each natural SL₂(2) factor, coprime action gives the fixed complement
of its four-element support. Its Sylow involution has a commutator line of
order two and fixes exactly twice the full factor's fixed space, so these
two subgroups span the involution-fixed space. Given a vector fixed by J,
choose the resulting commutator correction in each factor. Distinct factors
fix each other's supports; subtracting the product of these corrections
therefore leaves a vector fixed by every factor and hence by E. The global
identification supplies the actual Sylow intersections, with no auxiliary
action or nontriviality assumptions.

Source: Stellmacher (1.7), journal p19, and the fixed-space decomposition
used in (8.4), journal p39; refs/latex/stellmacher-n-group.tex.
-/

open scoped IsMulCommutative
open Stellmacher.SectionOne.RankOneThreeGroupAssembly
namespace Stellmacher.SectionOne
universe u

private theorem actor_commutator_mono
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    {D E : Subgroup G} (hDE : D ≤ E) :
    commutatorAction D V ≤ commutatorAction E V := by
  rw [commutatorAction_eq_closure, commutatorAction_eq_closure]
  refine Subgroup.closure_mono ?_
  rintro z ⟨d, v, rfl⟩
  exact ⟨⟨d, hDE d.property⟩, v, rfl⟩

private theorem factor_fixed_cover
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (hfaith : fixingSubgroup G (Set.univ : Set V) = ⊥)
    (D Q : Subgroup G) (hD : IsOneSevenFactor (V := V) D)
    (hQD : Q ≤ D) (hQcard : Nat.card Q = 2) :
    FixedPoints.subgroup Q V ≤ FixedPoints.subgroup D V ⊔ commutatorAction Q V := by
  let C := FixedPoints.subgroup D V
  let U := commutatorAction D V
  let K := commutatorAction Q V
  have hC : C = FixedPoints.subgroup ((commutator D).map D.subtype) V := by
    apply le_antisymm
    · intro v hv d
      exact hv ⟨d, Subgroup.map_subtype_le _ d.property⟩
    · intro v hv d
      exact oneSevenFactor_fixes_derived_fixedPoints D hD d d.property v hv
  have hcop : Nat.Coprime (Nat.card ((commutator D).map D.subtype)) (Nat.card V) := by
    obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 V).exists_card_eq
    rw [hD.2.1.2.1, hn]
    exact (show Nat.Coprime 3 2 by decide).pow_right n
  have hcompl : IsCompl C U := by
    rw [hC]
    dsimp only [U]
    rw [oneSevenFactor_full_commutator_eq_derived D hD]
    exact isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
      (G := V) (A := ((commutator D).map D.subtype))
      (Group.isSolvable_of_comm fun x y => (IsMulCommutative.is_comm (M := V)).comm x y)
      hcop inferInstance
  have hKcard : Nat.card K = 2 :=
    oneSevenFactor_involution_commutator_card_two hfaith D Q hD hQD hQcard
  have hCfix : C ≤ FixedPoints.subgroup Q V := by
    intro v hv q
    exact hv ⟨q, hQD q.property⟩
  have hVcard : 4 ≤ Nat.card V := by
    rw [← hD.2.2.1]
    exact Nat.card_le_card_of_injective _ (commutatorAction D V).subtype_injective
  let _ : Nontrivial V := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨x, hxne, huniq⟩ := (Nat.card_eq_two_iff' (1 : Q)).mp hQcard
  have hxinv : x⁻¹ = x := (huniq x⁻¹ (by simpa using hxne)).trans (huniq x hxne).symm
  have hxx : x ^ 2 = 1 := by
    calc
      x ^ 2 = x * x := pow_two x
      _ = x⁻¹ * x := by rw [hxinv]
      _ = 1 := inv_mul_cancel x
  have hKfix : K ≤ FixedPoints.subgroup Q V :=
    (card_two_action_fixed_commutator_card_data (U := V) x ⟨hxne, hxx⟩ hQcard).2
  have hcardSup : Nat.card (↥(C ⊔ K)) = Nat.card C * 2 := by
    rw [natCard_sup_eq_mul_of_disjoint_of_le_centralizer C K
      (hcompl.disjoint.mono_right (actor_commutator_mono hQD)) ?_, hKcard]
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    exact fun c hc => (IsMulCommutative.is_comm (M := V)).comm c k
  have hrel := oneSevenFactor_involution_fixed_relIndex hfaith D Q hD hQD hQcard
  have hcardFix := (C.subgroupOf (FixedPoints.subgroup Q V)).index_mul_card
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCfix).toEquiv] at hcardFix
  change C.relIndex (FixedPoints.subgroup Q V) * Nat.card C = _ at hcardFix
  rw [show C.relIndex (FixedPoints.subgroup Q V) = 2 from hrel] at hcardFix
  have heq := Subgroup.eq_of_le_of_card_ge (sup_le hCfix hKfix)
    (show Nat.card (FixedPoints.subgroup Q V) ≤ Nat.card (↥(C ⊔ K)) by
      rw [hcardSup, ← hcardFix, Nat.mul_comm])
  exact heq.ge

/-- The fixed space of J is covered by the fixed complement and its commutator. -/
public theorem oneSeven_fixed_le_fixed_sup_commutator
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) (S : Sylow 2 G) :
    FixedPoints.subgroup (oneJ (V := V) (S : Subgroup G)) V ≤
      FixedPoints.subgroup (oneE (V := V) (S : Subgroup G)) V ⊔
        commutatorAction (oneJ (V := V) (S : Subgroup G)) V := by
  classical
  let E := oneSevenGenerated (G := G) (V := V)
  let F := oneSevenFactors (G := G) (V := V)
  let I := {D : Subgroup G // D ∈ F}
  let Q (i : I) : Subgroup G := (S : Subgroup G) ⊓ i.val
  let J := oneJ (V := V) (S : Subgroup G)
  obtain ⟨hEnormal, hprod, _⟩ := oneSeven_global_product h S
  obtain ⟨hJid, hEid⟩ := oneSeven_global_identification h S
  change J = (S : Subgroup G) ⊓ E at hJid
  change IsInternalDirectProduct E F at hprod
  have hF (i : I) : IsOneSevenFactor (V := V) i.val :=
    (mem_oneSevenFactors_iff i.val).mp i.property
  obtain ⟨_, _, _, hQcard⟩ := sl2_product_sylow_coordinates S E hEnormal F hprod
    (fun D hD => ((mem_oneSevenFactors_iff D).mp hD).1)
  have hQiJ (i : I) : Q i ≤ J := by
    rw [hJid]
    exact inf_le_inf_left _ (by rw [hprod.1]; exact le_iSup (fun i : I => i.val) i)
  intro v hv
  have hlocal (i : I) : ∃ c ∈ FixedPoints.subgroup i.val V,
      ∃ k ∈ commutatorAction (Q i) V, c * k = v := by
    apply Subgroup.mem_sup.mp
    apply factor_fixed_cover h.action_faithful i.val (Q i) (hF i) inf_le_right
      (hQcard i.val i.property)
    intro q
    exact hv ⟨q, hQiJ i q.property⟩
  choose c hc k hk hck using hlocal
  let kAll : V := ∏ i : I, k i
  have hkAll : kAll ∈ commutatorAction J V := by
    apply Subgroup.prod_mem
    intro i hi
    exact actor_commutator_mono (hQiJ i) (hk i)
  have hcross (i j : I) (hij : i ≠ j) : k j ∈ FixedPoints.subgroup i.val V := by
    apply oneSevenFactor_commutatorAction_le_fixedPoints h i.val j.val (hF i) (hF j)
      (fun he => hij (Subtype.ext he))
    exact actor_commutator_mono (inf_le_right : Q j ≤ j.val) (hk j)
  have hfixed (i : I) : v * kAll⁻¹ ∈ FixedPoints.subgroup i.val V := by
    let r : V := ∏ j ∈ Finset.univ.erase i, k j
    have hr : r ∈ FixedPoints.subgroup i.val V := by
      apply Subgroup.prod_mem
      intro j hj
      exact hcross i j (Ne.symm (Finset.mem_erase.mp hj).1)
    have hprodK : kAll = k i * r :=
      (Finset.mul_prod_erase Finset.univ k (Finset.mem_univ i)).symm
    have heq : v * kAll⁻¹ = c i * r⁻¹ := by
      rw [← hck i, hprodK]
      simp only [mul_inv_rev]
      calc
        c i * k i * (r⁻¹ * (k i)⁻¹) = c i * r⁻¹ * (k i * (k i)⁻¹) := by ac_rfl
        _ = c i * r⁻¹ := by rw [mul_inv_cancel, mul_one]
    rw [heq]
    exact (FixedPoints.subgroup i.val V).mul_mem (hc i)
      ((FixedPoints.subgroup i.val V).inv_mem hr)
  have hEfixed : v * kAll⁻¹ ∈ FixedPoints.subgroup E V := by
    have hle : E ≤ fixingSubgroup G ({v * kAll⁻¹} : Set V) := by
      rw [hprod.1]
      refine iSup_le fun i => ?_
      intro d hd
      rw [mem_fixingSubgroup_iff]
      intro w hw
      obtain rfl := Set.mem_singleton_iff.mp hw
      exact hfixed i ⟨d, hd⟩
    intro e
    exact (mem_fixingSubgroup_iff (M := G)).mp (hle e.property) _ (Set.mem_singleton _)
  rw [hEid]
  exact Subgroup.mem_sup.mpr ⟨v * kAll⁻¹, hEfixed, kAll, hkAll, by group⟩

end Stellmacher.SectionOne
