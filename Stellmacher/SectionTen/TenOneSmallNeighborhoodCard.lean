module
public import Stellmacher.SectionTen.TenOneSmallDerived
public import Stellmacher.SectionNine.CubicLocalAction
public import Theory.GroupTheory.CenterSmallIndex
public import Theory.GroupTheory.Commutator.CentralDihedral
public import Mathlib.GroupTheory.SpecificGroups.KleinFour

/-!
# The small-case neighborhood order in Stellmacher (10.1)

When the first neighbor module has order eight, the generated neighborhood at
the offset-two middle vertex has order thirty-two. Its three neighbor modules
have order eight and a common pairwise intersection equal to the central
four-subgroup. The existing derived-equality theorem identifies that same
four-subgroup as the neighborhood's derived subgroup.

Two subgroup-product counts bound the threefold join by thirty-two, while any
distinct pair already has order sixteen. The order-sixteen possibility would
make the central quotient a Klein four-group; the central-dihedral extension
bound then forces a derived group of order at most two, contradicting the
derived equality. The final corollary uses the proved equality of the actual
conjugate closure W and the middle center to obtain |Wnext/W| = 8.

Source: Stellmacher, Journal of Algebra 190 (1997), proof of (10.1),
printed p.60 / PDF p.50, the small case |V_{a+1}| = 2^3.
-/


open scoped commutatorElement
namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

private theorem quotient_klein_four {K : Type*} [Group K] [Finite K]
    (hcard : Nat.card (K ⧸ Subgroup.center K) = 4)
    (hncyc : ¬ IsCyclic (K ⧸ Subgroup.center K)) :
    IsKleinFour (K ⧸ Subgroup.center K) := by
  let _ : Nontrivial (K ⧸ Subgroup.center K) :=
    (Finite.one_lt_card_iff_nontrivial).mp (by rw [hcard]; omega)
  refine ⟨hcard, (Monoid.exponent_eq_prime_iff Nat.prime_two).mpr ?_⟩
  intro x hx
  have hxdvd : orderOf x ∣ 4 := by
    rw [← hcard]
    exact orderOf_dvd_natCard x
  have hxone : orderOf x ≠ 1 := by simpa using hx
  have hxnotfour : orderOf x ≠ 4 := by
    intro hfour
    exact hncyc (isCyclic_of_orderOf_eq_card x (hfour.trans hcard.symm))
  obtain ⟨k, hk, hpow⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    (show orderOf x ∣ 2 ^ 2 by simpa using hxdvd)
  interval_cases k
  · exact (hxone hpow).elim
  · exact hpow
  · exact (hxnotfour hpow).elim

private theorem not_sixteen_of_central_derived_four
    (whole C : Subgroup G) (hCwhole : C ≤ whole)
    (hCcentral : C ≤ Subgroup.centralizer (whole : Set G))
    (hCcard : Nat.card C = 4)
    (hderived : DerivedAmbient whole = C) :
    Nat.card whole ≠ 16 := by
  intro hwhole
  let Z : Subgroup whole := C.subgroupOf whole
  have hZcard : Nat.card Z = 4 := by
    dsimp [Z]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCwhole).toEquiv]
    exact hCcard
  have hZcenter : Z ≤ Subgroup.center whole := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have hc := hCcentral hx
    exact (Subgroup.mem_centralizer_iff.mp hc) y y.property
  have hZderived : Z = _root_.commutator whole := by
    apply Subgroup.map_injective (f := whole.subtype) whole.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hCwhole]
    exact hderived.symm
  have hnon : _root_.commutator whole ≠ ⊥ := by
    intro heq
    have hcard := hZcard
    rw [hZderived, heq] at hcard
    simp at hcard
  have hZindex : Z.index ≤ 4 := by
    have hcount := Z.card_mul_index
    rw [hZcard, hwhole] at hcount
    omega
  have hcenterEq := Subgroup.center_eq_and_index_four_of_central_small_index
    Z hZcenter hZindex hnon
  have hquotCard : Nat.card (whole ⧸ Subgroup.center whole) = 4 := by
    rw [← (Subgroup.center whole).index_eq_card, hcenterEq.1, hcenterEq.2]
  let Q := whole ⧸ Subgroup.center whole
  let _ : IsKleinFour Q := quotient_klein_four hquotCard (fun hcyc =>
    hnon ((_root_.commutator_eq_bot_iff whole).mpr
      (isMulCommutative_of_isCyclic_quotient_center_self whole)))
  let e : Q ≃* DihedralGroup 2 := IsKleinFour.nonempty_mulEquiv.some
  let f : whole →* DihedralGroup 2 :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center whole))
  have hf : Function.Surjective f :=
    e.surjective.comp (QuotientGroup.mk'_surjective (Subgroup.center whole))
  have hker : f.ker ≤ Subgroup.center whole := by
    intro x hx
    apply (QuotientGroup.eq_one_iff x).mp
    change e (QuotientGroup.mk' (Subgroup.center whole) x) = 1 at hx
    exact e.injective (hx.trans e.map_one.symm)
  have hbound := CentralExtension.card_center_inf_commutator_le_two_of_dihedral f hf hker
  have hcommCenter : _root_.commutator whole ≤ Subgroup.center whole := by
    rw [← hZderived, ← hcenterEq.1]
  rw [inf_eq_right.mpr hcommCenter, ← hZderived, hZcard] at hbound
  omega

private theorem three_eight_join_card_le
    (left middle right C whole : Subgroup G)
    (hwhole : whole = left ⊔ middle ⊔ right)
    (hcardL : Nat.card left = 8) (hcardM : Nat.card middle = 8)
    (hcardR : Nat.card right = 8) (hCcard : Nat.card C = 4)
    (hCL : C ≤ left) (hCM : C ≤ middle) (hCR : C ≤ right)
    (hderived : DerivedAmbient whole = C) :
    Nat.card whole ≤ 32 := by
  have hLwhole : left ≤ whole := hwhole ▸ le_sup_of_le_left le_sup_left
  have hMwhole : middle ≤ whole := hwhole ▸ le_sup_of_le_left le_sup_right
  have hRwhole : right ≤ whole := hwhole ▸ le_sup_right
  have hpairwhole : left ⊔ middle ≤ whole := sup_le hLwhole hMwhole
  have hcomm : ⁅whole, whole⁆ ≤ C := by
    rw [← Subgroup.map_subtype_commutator]
    exact hderived.le
  have hnormM : middle ≤ Subgroup.normalizer (left : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mpr
      ((Subgroup.commutator_mono hLwhole hMwhole).trans (hcomm.trans hCL))
  have hnormR : right ≤ Subgroup.normalizer ((left ⊔ middle : Subgroup G) : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mpr
      ((Subgroup.commutator_mono hpairwhole hRwhole).trans
        (hcomm.trans (hCL.trans le_sup_left)))
  have hfirst : 4 ≤ Nat.card (left ⊓ middle : Subgroup G) := by
    rw [← hCcard]
    exact Subgroup.card_le_of_le (le_inf hCL hCM)
  have hsecond : 4 ≤ Nat.card ((left ⊔ middle) ⊓ right : Subgroup G) := by
    rw [← hCcard]
    exact Subgroup.card_le_of_le
      (le_inf (hCL.trans le_sup_left) hCR)
  have hpair := Subgroup.card_mul_eq_card_inf_mul_card_sup_of_normalizes
    left middle hnormM
  have hwholeCount := Subgroup.card_mul_eq_card_inf_mul_card_sup_of_normalizes
    (left ⊔ middle) right hnormR
  rw [hcardL, hcardM] at hpair
  rw [hcardR, ← hwhole] at hwholeCount
  have hpairBound : Nat.card (left ⊔ middle : Subgroup G) ≤ 16 := by nlinarith
  nlinarith

public theorem ten_one_small_neighborhood_card
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hsmall : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) = 8) :
    Nat.card (GeneratedNeighborhoodV ctx.Γ middle) = 32 := by
  let W := GeneratedNeighborhoodV ctx.Γ middle
  let C := ZAt ctx.Γ middle
  have hopen := sectionTenOpeningData ctx middle hpath
  have hD : DerivedAmbient W = C := by
    change DerivedAmbient W = ZAt ctx.Γ middle
    rw [ten_one_small_derived ctx middle hpath hsmall,
      ten_one_small_intersection ctx middle hpath hsmall]
  have hCW : C ≤ W := by
    rw [← hD]
    exact Subgroup.map_subtype_le _
  have hcentral : C ≤ Subgroup.centralizer (W : Set G) := by
    change ZAt ctx.Γ middle ≤
      Subgroup.centralizer (GeneratedNeighborhoodV ctx.Γ middle : Set G)
    rw [← ten_one_small_intersection ctx middle hpath hsmall]
    exact ten_one_common_intersection_centralizes ctx middle hpath
  let : Finite ctx.Γ.Vertex := ctx.Γ.finiteVertex
  let : Fintype {neighbor // ctx.Γ.adjacent middle neighbor} := Fintype.ofFinite _
  have hdeg : Fintype.card {neighbor // ctx.Γ.adjacent middle neighbor} = 3 := by
    rw [← Nat.card_eq_fintype_card]
    exact (cubic_local_action_of_sl2Two_quotient ctx.Γ ctx.sectionSeven middle
      hopen.quotient_model).degree
  let e : Fin 3 ≃ {neighbor // ctx.Γ.adjacent middle neighbor} :=
    (Fintype.equivFinOfCardEq hdeg).symm
  let v (i : Fin 3) := (e i).val
  let V (i : Fin 3) : Subgroup G := VAt ctx.Γ (v i)
  have hvadj (i : Fin 3) : ctx.Γ.adjacent middle (v i) := (e i).property
  have hvcard (i : Fin 3) : Nat.card (V i) = 8 := by
    obtain ⟨actor, hactor⟩ := (lemma_seven_one ctx.sectionSeven ctx.Γ).local_transitivity
      middle ((mem_neighborhood_iff_adjacent ctx.Γ).mpr
        (sectionTenOpeningGeometry ctx middle hpath).2.1)
      ((mem_neighborhood_iff_adjacent ctx.Γ).mpr (hvadj i))
    change Nat.card (VAt ctx.Γ (v i)) = 8
    rw [← hactor, VAt, v_act]
    exact (Subgroup.card_map_of_injective (MulAut.conj (actor : G)⁻¹).injective).trans hsmall
  have hvcommon (i j : Fin 3) (hne : i ≠ j) : V i ⊓ V j = C := by
    change VAt ctx.Γ (v i) ⊓ VAt ctx.Γ (v j) = C
    rw [ten_one_neighbor_intersection ctx middle hpath (hvadj i) (hvadj j)
      (fun heq => hne (e.injective (Subtype.ext heq))),
      ten_one_small_intersection ctx middle hpath hsmall]
  have hCVi (i : Fin 3) : C ≤ V i := by
    rw [← hvcommon i (if i = 0 then 1 else 0) (by split_ifs <;> omega)]
    exact inf_le_left
  have hW : W = V 0 ⊔ V 1 ⊔ V 2 := by
    dsimp [W, GeneratedNeighborhoodV]
    apply le_antisymm
    · apply sSup_le
      rintro subgroup ⟨neighbor, hneighbor, rfl⟩
      obtain ⟨i, hi⟩ := e.surjective
        (⟨neighbor, (mem_neighborhood_iff_adjacent ctx.Γ).mp hneighbor⟩ :
          {n // ctx.Γ.adjacent middle n})
      have heq : neighbor = v i := congrArg Subtype.val hi.symm
      rw [heq]
      fin_cases i
      · exact le_sup_of_le_left le_sup_left
      · exact le_sup_of_le_left le_sup_right
      · exact le_sup_right
    · apply sup_le (sup_le ?_ ?_) ?_
      all_goals
        apply le_sSup
        exact ⟨_, (mem_neighborhood_iff_adjacent ctx.Γ).mpr (hvadj _), rfl⟩
  have hbound := three_eight_join_card_le (V 0) (V 1) (V 2) C W hW
    (hvcard 0) (hvcard 1) (hvcard 2) hopen.center_card
    (hCVi 0) (hCVi 1) (hCVi 2) hD
  have hpair : Nat.card (V 0 ⊔ V 1 : Subgroup G) = 16 := by
    have hnorm : V 1 ≤ Subgroup.normalizer (V 0 : Set G) := by
      apply Subgroup.le_normalizer_iff_commutator_le_left.mpr
      have hcomm : ⁅W, W⁆ ≤ C := by
        rw [← Subgroup.map_subtype_commutator]
        exact hD.le
      exact (Subgroup.commutator_mono
        (hW ▸ le_sup_of_le_left le_sup_left)
        (hW ▸ le_sup_of_le_left le_sup_right)).trans
          (hcomm.trans (hCVi 0))
    have hcount := Subgroup.card_mul_eq_card_inf_mul_card_sup_of_normalizes
      (V 0) (V 1) hnorm
    rw [hvcard 0, hvcard 1, hvcommon 0 1 (by decide), hopen.center_card] at hcount
    omega
  have hle16 : 16 ≤ Nat.card W := by
    rw [← hpair]
    exact Subgroup.card_le_of_le (hW ▸ sup_le
      (le_sup_of_le_left le_sup_left) (le_sup_of_le_left le_sup_right))
  have hdiv16 : 16 ∣ Nat.card W := by
    rw [← hpair]
    exact Subgroup.card_dvd_of_le (hW ▸ sup_le
      (le_sup_of_le_left le_sup_left) (le_sup_of_le_left le_sup_right))
  have hnot16 := not_sixteen_of_central_derived_four W C hCW hcentral
    hopen.center_card hD
  obtain ⟨factor, hfactor⟩ := hdiv16
  have hfactorle : factor ≤ 2 := by nlinarith
  interval_cases factor <;> omega


public theorem ten_one_small_neighborhood_quotient
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hsmall : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) = 8) :
    QuotientCardEq (GeneratedNeighborhoodV ctx.Γ middle)
      (conjugateClosure
        (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ ctx.criticalPath.a')
        (GAt ctx.Γ middle)) (2 ^ 3) := by
  change Nat.card (GeneratedNeighborhoodV ctx.Γ middle) =
    2 ^ 3 * Nat.card (conjugateClosure
      (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ ctx.criticalPath.a')
      (GAt ctx.Γ middle))
  rw [ten_one_small_neighborhood_card ctx middle hpath hsmall,
    ten_one_small_generated_eq_center ctx middle hpath hsmall,
    (sectionTenOpeningData ctx middle hpath).center_card]
  norm_num

end Stellmacher.SectionTen
