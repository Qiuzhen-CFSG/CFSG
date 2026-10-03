module
public import Stellmacher.SectionOne.OneSevenDihedralQuotient
public import Stellmacher.SectionOne.OneSevenModuleProduct
public import Stellmacher.CentralizerQuotientAction
public import Theory.SpecificGroups.DihedralSolvable

/-!
# A central four-factor in an elementary dihedral core

Let Q = O₂(P) be elementary abelian and self-centralizing in the finite group P.
If P/Q is dihedral of order twice a power of three, and a Sylow two-subgroup
has fixed-core index two, then Q is the direct product of a normal subgroup
of order four and Z(P). This graph-independent full-core result supplies the
decomposition needed in the last paragraph of Stellmacher (8.2).

Conjugation gives the actual quotient P/Q a faithful action on all of Q. Its
projected Sylow has order two, is an offender, and normally generates P/Q.
The proved global factor identification from (1.7) and its Sylow cardinality
formula force exactly one factor. The module product splits its four-element
support from the global fixed subgroup. The centralizer-quotient transport
identifies their ambient images with [Q,P] and Z(P), respectively; this also
gives normality of the support. No bound on the order of Z(P) is needed.

Source: `refs/latex/stellmacher-n-group.tex`, Stellmacher (1.7)(c), journal
p.19, and the final paragraph of (8.2), journal p.38.
-/

namespace Stellmacher.SectionOne
universe u

private theorem elementary_dihedral_rank_one_action_split
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) (S : Sylow 2 G)
    (hS : Nat.card S = 2) (hA : oneA (V := V) (S : Subgroup G) S)
    (hgen : Subgroup.normalClosure ((S : Subgroup G) : Set G) = ⊤) :
    IsCompl (FixedPoints.subgroup (⊤ : Subgroup G) V)
      (commutatorAction (⊤ : Subgroup G) V) ∧
      Nat.card (commutatorAction (⊤ : Subgroup G) V) = 4 := by
  classical
  have hJ : oneJ (V := V) (S : Subgroup G) = (S : Subgroup G) :=
    le_antisymm (sSup_le fun _ hY => hY.1) (le_sSup hA)
  have hE : oneE (V := V) (S : Subgroup G) = ⊤ := by
    change Subgroup.normalClosure (oneJ (V := V) (S : Subgroup G) : Set G) = ⊤
    rw [hJ, hgen]
  let F := oneSevenFactors (G := G) (V := V)
  let E := oneSevenGenerated (G := G) (V := V)
  obtain ⟨hEnormal, hprod, _⟩ := oneSeven_global_product h S
  change IsInternalDirectProduct E F at hprod
  have hEtop : E = ⊤ := (oneSeven_global_identification h S).2.symm.trans hE
  have hF : ∀ D ∈ F, IsOneSevenFactor (V := V) D :=
    fun D hD => (mem_oneSevenFactors_iff D).mp hD
  have hcard := (sl2_product_sylow_coordinates S E hEnormal F hprod
    (fun D hD => (hF D hD).1)).2.2.1
  rw [hEtop, inf_top_eq, hS] at hcard
  have hFcard : F.card = 1 := by
    apply Nat.pow_right_injective (by decide : 1 < 2)
    simpa using hcard.symm
  obtain ⟨D, hFD⟩ := Finset.card_eq_one.mp hFcard
  have hDin : D ∈ F := by rw [hFD]; simp
  have hDE : D = E := by
    apply le_antisymm
    · rw [hprod.1]
      exact le_iSup (fun K : {K : Subgroup G // K ∈ F} => K.val) ⟨D, hDin⟩
    · rw [hprod.1]
      apply iSup_le
      intro K
      have hKD : K.val = D := by simpa [hFD] using K.property
      rw [hKD]
  have htop : IsOneSevenFactor (V := V) (⊤ : Subgroup G) := by
    simpa only [hDE, hEtop] using hF D hDin
  have hmodule := oneSevenFactor_module_product h
    (fun _ : Fin 1 => (⊤ : Subgroup G)) (fun _ => htop)
    (fun _ _ _ => Subsingleton.elim _ _) ⊤ (by simp)
  have hsup : FixedPoints.subgroup (⊤ : Subgroup G) V ⊔
      commutatorAction (⊤ : Subgroup G) V = ⊤ := by
    simpa only [iSup_option, iSup_const] using hmodule.1.symm
  have hdisj : Disjoint (FixedPoints.subgroup (⊤ : Subgroup G) V)
      (commutatorAction (⊤ : Subgroup G) V) :=
    hmodule.2.1 none (some 0) (by simp)
  exact ⟨⟨hdisj, codisjoint_iff.mpr hsup⟩, htop.2.2.1⟩

public theorem elementary_dihedral_core_four_factor
    {P : Type u} [Group P] [Finite P]
    [IsElementaryAbelian 2 (pCore 2 P)]
    (hself : Subgroup.centralizer (pCore 2 P : Set P) ≤ pCore 2 P)
    (hdihedral : ∃ n : ℕ, Nonempty ((P ⧸ pCore 2 P) ≃* DihedralGroup (3 ^ n)))
    (T : Sylow 2 P)
    (hindex : (Subgroup.centralizer (T : Set P)).relIndex (pCore 2 P) = 2) :
    ∃ U : Subgroup P, U.Normal ∧
      pCore 2 P = U ⊔ Subgroup.center P ∧
      U ⊓ Subgroup.center P = ⊥ ∧ Nat.card U = 4 := by
  classical
  let Q := pCore 2 P
  let X := P ⧸ Q
  let projection : P →* X := QuotientGroup.mk' Q
  have hsurj : Function.Surjective projection := QuotientGroup.mk'_surjective Q
  have hnormal : Q.Normal := inferInstance
  have hcentralizer : Subgroup.centralizer (Q : Set P) = Q :=
    le_antisymm hself (Subgroup.le_centralizer_iff_isMulCommutative.mpr inferInstance)
  have hkernel : projection.ker = Subgroup.centralizer (Q : Set P) := by
    rw [hcentralizer]
    exact QuotientGroup.ker_mk' Q
  let _ := centralizerQuotientAction Q hnormal projection hsurj hkernel
  let S : Sylow 2 X := T.mapSurjective hsurj
  obtain ⟨n, ⟨equiv⟩⟩ := hdihedral
  have hXcard : Nat.card X = 2 * 3 ^ n :=
    (Nat.card_congr equiv.toEquiv).trans DihedralGroup.nat_card
  have heven : Even (Nat.card X) := by rw [hXcard]; exact even_two.mul_right _
  have hSylow := odd_dihedral_quotient_sylow (3 ^ n)
    ((by decide : Odd 3).pow) equiv.symm.toMonoidHom equiv.symm.surjective S
  have hS : Nat.card S = 2 := by
    have hdiv := S.dvd_card_of_dvd_card (even_iff_two_dvd.mp heven)
    exact le_antisymm hSylow.1 (Nat.le_of_dvd Nat.card_pos hdiv)
  have hcore : pCore 2 X = ⊥ := by
    have hmap := pCore_map_mk'_eq_of_normal_isPGroup
      (G := P) (p := 2) Q (pCore_isPGroup (G := P) (p := 2))
    have hmapbot : (pCore 2 P).map projection = ⊥ := by
      apply (Subgroup.map_eq_bot_iff _ (f := projection)).mpr
      exact (QuotientGroup.ker_mk' Q).symm.le
    exact hmap.symm.trans hmapbot
  have h : Hypotheses X Q := {
    G_solvable := by
      let _ := GLS3.Chapter5.dihedralGroup_isSolvable (3 ^ n)
      exact Group.isSolvable_of_surjective (f := equiv.symm.toMonoidHom) equiv.symm.surjective
    G_even := heven
    action_faithful := centralizerQuotientAction_faithful Q hnormal projection hsurj hkernel
    twoCore_eq_bot := hcore }
  have hfixmap : (FixedPoints.subgroup (S : Subgroup X) Q).map Q.subtype =
      Q ⊓ Subgroup.centralizer (T : Set P) :=
    centralizerQuotientAction_fixedPoints_image_map Q hnormal projection hsurj hkernel T
  have hfixindex : (FixedPoints.subgroup (S : Subgroup X) Q).index = 2 := by
    calc
      _ = (FixedPoints.subgroup (S : Subgroup X) Q).relIndex ⊤ :=
        (Subgroup.relIndex_top_right _).symm
      _ = ((FixedPoints.subgroup (S : Subgroup X) Q).map Q.subtype).relIndex
          ((⊤ : Subgroup Q).map Q.subtype) :=
        (Subgroup.relIndex_map_map_of_injective _ _ Q.subtype_injective).symm
      _ = 2 := by
        rw [hfixmap, ← MonoidHom.range_eq_map, Subgroup.range_subtype,
          Subgroup.inf_relIndex_left]
        exact hindex
  have hA : oneA (V := Q) (S : Subgroup X) S := by
    have hcyclic : IsCyclic S := isCyclic_of_prime_card hS
    let _ := hcyclic
    have helementary : IsElementaryAbelian 2 S := {
      toIsMulCommutative := inferInstance
      exponent_dvd_p := by
        rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
        intro element
        simpa only [hS] using pow_card_eq_one' (x := element) }
    refine ⟨le_rfl, helementary, ?_⟩
    have hcard := (FixedPoints.subgroup (S : Subgroup X) Q).card_mul_index
    rw [hfixindex] at hcard
    unfold m
    have hpos : 0 < (Nat.card (FixedPoints.subgroup (S : Subgroup X) Q) : ℚ) *
        (Nat.card S : ℚ) := by
      exact_mod_cast Nat.mul_pos Nat.card_pos Nat.card_pos
    apply (div_le_one hpos).mpr
    rw [hS]
    exact_mod_cast hcard.ge
  obtain ⟨hsplit, hfour⟩ := elementary_dihedral_rank_one_action_split h S hS hA hSylow.2
  have htopmap : (⊤ : Subgroup P).map projection = ⊤ :=
    Subgroup.map_top_of_surjective projection hsurj
  have hcenterle : Subgroup.center P ≤ Q :=
    (Subgroup.center_le_centralizer (Q : Set P)).trans hself
  have hfixed : (FixedPoints.subgroup (⊤ : Subgroup X) Q).map Q.subtype =
      Subgroup.center P := by
    have hmap := centralizerQuotientAction_fixedPoints_image_map
      Q hnormal projection hsurj hkernel (⊤ : Subgroup P)
    rw [htopmap] at hmap
    simpa only [Subgroup.coe_top, Subgroup.centralizer_univ,
      inf_eq_right.mpr hcenterle] using hmap
  let U := (commutatorAction (⊤ : Subgroup X) Q).map Q.subtype
  have hU : U = ⁅Q, (⊤ : Subgroup P)⁆ := by
    have hmap := centralizerQuotientAction_commutatorSubgroup_image_map
      Q hnormal projection hsurj hkernel (⊤ : Subgroup P) (⊤ : Subgroup Q)
    rw [htopmap] at hmap
    simpa only [← MonoidHom.range_eq_map, Subgroup.range_subtype] using hmap
  refine ⟨U, ?_, ?_, ?_, ?_⟩
  · rw [hU]
    infer_instance
  · have hmap := congrArg (Subgroup.map Q.subtype) hsplit.sup_eq_top
    rw [Subgroup.map_sup, hfixed, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at hmap
    exact (sup_comm _ _).trans hmap |>.symm
  · rw [← hfixed, ← Subgroup.map_inf _ _ _ Q.subtype_injective,
      hsplit.disjoint.symm.eq_bot, Subgroup.map_bot]
  · exact (Subgroup.card_map_of_injective Q.subtype_injective).trans hfour

end Stellmacher.SectionOne
