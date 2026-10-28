module
public import Theory.GroupAction.FiveActionMinimalOrder
public import Theory.GroupAction.ParrottQuotientBounds
public import Theory.GroupAction.FiveOnAbelian32
public import Theory.GroupTheory.PGroup.NormalSubgroups
public import Theory.GroupTheory.Commutator.NilpotentSaturation

/-!
# Parrott’s two-group of order 512

Let an order-five group act by automorphisms on a two-group V of order 512,
with nilpotency class at least three and all common fixed points central.
Then V has class three and center of order two. Its derived subgroup is
both the Frattini subgroup and the second upper central subgroup, and is
elementary abelian of order 32. The action is the supplied action throughout.

Coprime fixed-point lifting makes the Frattini quotient action nontrivial
and the derived subgroup modulo its central intersection fixed-free.
A nontrivial five-action on a two-group needs at least sixteen elements.
The derived subgroup also meets the center nontrivially, so the two factors
of at least sixteen and this intersection exhaust the order 512. This
identifies the Frattini subgroup with the derived subgroup, of order 32.

On a group of order sixteen a fixed-free five-action has no proper
nontrivial invariant subgroup. Apply this first to the Frattini quotient:
the center has trivial image, since a central Frattini supplement would
make V abelian. Apply it next to the derived quotient. If the commutator
with V surjected onto that quotient, nilpotent commutator saturation would
force the derived subgroup into the center. Thus the third lower central
subgroup is central, giving class three. The same Frattini argument
identifies the second upper central subgroup. The three-subgroups lemma
makes the derived subgroup abelian; its fixed subgroup has order two by
orbit counting, so the coprime splitting lemma makes it elementary.

The public `invariant_frattini_dichotomy_of_five` also exposes the invariant
subgroup step for later centralizer arguments with the same quotient action.

This is the intrinsic two-group part of Lemma 1, p.672, in D. Parrott,
*A characterization of the Tits’ simple group* (1972), also used at the
start of *On the simple group of J. Tits* (1973), p.87. The ambient
centralizer, Sylow, and recognition conclusions belong to later modules.
-/

open scoped commutatorElement
open Subgroup
namespace Theory.GroupAction

private theorem cardinal_squeeze
    {V : Type*} [Group V] [Finite V] (hV : IsPGroup 2 V)
    (hcard : Nat.card V = 512)
    (hPhi : 16 ≤ Nat.card (V ⧸ frattini V))
    (hDquot : 16 ≤ Nat.card (commutator V ⧸ (center V).subgroupOf (commutator V))) :
    Nat.card (V ⧸ frattini V) = 16 ∧ frattini V = commutator V ∧
    Nat.card (commutator V) = 32 ∧
    Nat.card ((center V).subgroupOf (commutator V)) = 2 ∧
    Nat.card (commutator V ⧸ (center V).subgroupOf (commutator V)) = 16 := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : Fact (IsPGroup 2 V) := ⟨hV⟩
  let D := commutator V
  let ZD := (center V).subgroupOf D
  change 16 ≤ Nat.card (D ⧸ ZD) at hDquot
  have hDpos : 1 < Nat.card D := by
    have := Nat.card_le_card_of_surjective (QuotientGroup.mk' ZD)
      (QuotientGroup.mk'_surjective ZD)
    omega
  let _ : Nontrivial D := Finite.one_lt_card_iff_nontrivial.mp hDpos
  obtain ⟨z, hzne, hzcenter⟩ := exists_nontrivial_center_mem_normal D (p := 2)
  have hZDne : ZD ≠ ⊥ := by
    intro hzbot
    have hz : z ∈ ZD := hzcenter
    have hz1 : z = 1 := by simpa only [hzbot, Subgroup.mem_bot] using hz
    exact hzne hz1
  have hZDtwo : 2 ≤ Nat.card ZD := by
    have : Nontrivial ZD := (Subgroup.nontrivial_iff_ne_bot ZD).mpr hZDne
    exact Finite.one_lt_card_iff_nontrivial.mpr this
  have hDle : D ≤ frattini V := commutator_le_frattini_of_isPGroup (p := 2)
  have hDcard : Nat.card D ≤ Nat.card (frattini V) := card_le_of_le hDle
  have hmulPhi : Nat.card (V ⧸ frattini V) * Nat.card (frattini V) = 512 := by
    simpa only [hcard, Subgroup.index_eq_card] using (frattini V).index_mul_card
  have hmulD : Nat.card (D ⧸ ZD) * Nat.card ZD = Nat.card D :=
    ZD.index_mul_card
  have hD32 : 32 ≤ Nat.card D := by nlinarith
  have hPhi32 : Nat.card (frattini V) = 32 := by nlinarith
  have hD32eq : Nat.card D = 32 := by omega
  have hPhi16 : Nat.card (V ⧸ frattini V) = 16 := by nlinarith
  have hZD2 : Nat.card ZD = 2 := by nlinarith
  have hQ16 : Nat.card (D ⧸ ZD) = 16 := by nlinarith
  refine ⟨hPhi16, ?_, hD32eq, hZD2, hQ16⟩
  exact (eq_of_le_of_card_ge hDle (by omega)).symm

/-- An invariant subgroup has trivial or full image in a fixed-point-free
Frattini quotient of order sixteen under an order-five action. -/
public theorem invariant_frattini_dichotomy_of_five
    {A V : Type*} [Group A] [Finite A] [Group V] [Finite V]
    [MulDistribMulAction A V]
    (hA : Nat.card A = 5) (hcard : Nat.card (V ⧸ frattini V) = 16)
    (hfixed :
      let : MulDistribMulAction A (V ⧸ frattini V) :=
        quotientMulDistribMulAction (frattini V)
          (isInvariant_of_characteristic (frattini V))
      FixedPoints.subgroup A (V ⧸ frattini V) = ⊥)
    (H : Subgroup V) [IsInvariant A V H] :
    H ≤ frattini V ∨ H ⊔ frattini V = ⊤ := by
  let : IsInvariant A V (frattini V) := isInvariant_of_characteristic (frattini V)
  let : MulDistribMulAction A (V ⧸ frattini V) :=
    quotientMulDistribMulAction (frattini V) inferInstance
  let q := QuotientGroup.mk' (frattini V)
  let : IsInvariant A (V ⧸ frattini V) (H.map q) := isInvariant_map_quotient H
  rcases invariant_eq_bot_or_top_of_five_actor hA hcard hfixed (H.map q) with hbot | htop
  · left
    simpa only [q, QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff H).mp hbot
  · right
    have heq := congrArg (Subgroup.comap q) htop
    simpa only [Subgroup.comap_map_eq, q, QuotientGroup.ker_mk', Subgroup.comap_top] using heq

private theorem commutator_central_of_irreducible_quotient
    {A V : Type*} [Group A] [Finite A] [Group V] [Finite V]
    [MulDistribMulAction A V] [Group.IsNilpotent V]
    (D : Subgroup V) [D.Normal] [IsInvariant A V D]
    [IsInvariant A V (center V)]
    (hA : Nat.card A = 5)
    (hcard : Nat.card (D ⧸ (center V).subgroupOf D) = 16)
    (hfixed :
      let : MulDistribMulAction A (D ⧸ (center V).subgroupOf D) :=
        quotientMulDistribMulAction ((center V).subgroupOf D)
          (isInvariant_subgroupOf (center V) D)
      FixedPoints.subgroup A (D ⧸ (center V).subgroupOf D) = ⊥) :
    ⁅D, (⊤ : Subgroup V)⁆ ≤ center V := by
  let ZD := (center V).subgroupOf D
  let : IsInvariant A D ZD := isInvariant_subgroupOf (center V) D
  let : MulDistribMulAction A (D ⧸ ZD) := quotientMulDistribMulAction ZD inferInstance
  let L := ⁅D, (⊤ : Subgroup V)⁆
  have hLD : L ≤ D := commutator_le_left D ⊤
  let LD := L.subgroupOf D
  let q := QuotientGroup.mk' ZD
  let : IsInvariant A V (⊤ : Subgroup V) := isInvariant_of_characteristic ⊤
  let : IsInvariant A V L := isInvariant_commutator D ⊤
  let : IsInvariant A D LD := isInvariant_subgroupOf L D
  let : IsInvariant A (D ⧸ ZD) (LD.map q) := isInvariant_map_quotient LD
  rcases invariant_eq_bot_or_top_of_five_actor hA hcard hfixed (LD.map q) with hbot | htop
  · have hle : LD ≤ ZD := by
      simpa only [q, QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff LD).mp hbot
    intro x hx
    exact hle (show (⟨x, hLD hx⟩ : D) ∈ LD from hx)
  · have hcover : LD ⊔ ZD = ⊤ := by
      have hh := congrArg (Subgroup.comap q) htop
      simpa only [Subgroup.comap_map_eq, q, QuotientGroup.ker_mk', Subgroup.comap_top] using hh
    have hDcover : D ≤ center V ⊔ ⁅D, (⊤ : Subgroup V)⁆ := by
      intro x hx
      have hxx : (⟨x, hx⟩ : D) ∈ LD ⊔ ZD := hcover ▸ Subgroup.mem_top _
      have hm := Subgroup.mem_map_of_mem D.subtype hxx
      rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hLD] at hm
      have hmapZ : ZD.map D.subtype ≤ center V := by
        rintro _ ⟨z, hz, rfl⟩
        exact hz
      exact (show L ⊔ ZD.map D.subtype ≤ center V ⊔ L from
        sup_le le_sup_right (hmapZ.trans le_sup_left)) hm
    have hDZ : D ≤ center V :=
      Subgroup.le_of_le_sup_commutator_of_isNilpotent ⊤ D (center V) ⊤
        (inferInstance : Group.IsNilpotent (⊤ : Subgroup V)) le_top le_top le_rfl
        (by rw [Subgroup.normalizer_eq_top]) hDcover
    exact hLD.trans hDZ
private theorem structure_from_quotients
    {A V : Type*} [Group A] [Finite A] [Group V] [Finite V]
    [MulDistribMulAction A V] [Group.IsNilpotent V]
    [IsInvariant A V (commutator V)] [IsInvariant A V (center V)]
    (hA : Nat.card A = 5) (hclass : 3 ≤ Group.nilpotencyClass V)
    (hPhiD : frattini V = commutator V)
    (hPhi16 : Nat.card (V ⧸ frattini V) = 16)
    (hZD2 : Nat.card ((center V).subgroupOf (commutator V)) = 2)
    (hQ16 : Nat.card (commutator V ⧸ (center V).subgroupOf (commutator V)) = 16)
    (hPhifixed :
      let : MulDistribMulAction A (V ⧸ frattini V) :=
        quotientMulDistribMulAction (frattini V)
          (isInvariant_of_characteristic (frattini V))
      FixedPoints.subgroup A (V ⧸ frattini V) = ⊥)
    (hDfixed :
      let : MulDistribMulAction A (commutator V ⧸ (center V).subgroupOf (commutator V)) :=
        quotientMulDistribMulAction ((center V).subgroupOf (commutator V))
          (isInvariant_subgroupOf (center V) (commutator V))
      FixedPoints.subgroup A (commutator V ⧸ (center V).subgroupOf (commutator V)) = ⊥) :
    Group.nilpotencyClass V = 3 ∧ Nat.card (center V) = 2 ∧
    commutator V = Subgroup.upperCentralSeries V 2 ∧ IsMulCommutative (commutator V) := by
  have hZD : center V ≤ commutator V := by
    rcases invariant_frattini_dichotomy_of_five hA hPhi16 hPhifixed (center V) with hle | htop
    · simpa only [hPhiD] using hle
    · have hcenter : center V = ⊤ := frattini_nongenerating htop
      have hclassle : Group.nilpotencyClass V ≤ 1 :=
        Subgroup.upperCentralSeries_eq_top_iff_nilpotencyClass_le.mp (by simpa using hcenter)
      omega
  have hZ2 : Nat.card (center V) = 2 := by
    rw [← hZD2]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZD).toEquiv).symm
  have hLcentral : ⁅commutator V, (⊤ : Subgroup V)⁆ ≤ center V :=
    commutator_central_of_irreducible_quotient (commutator V) hA hQ16 hDfixed
  have hL3bot : (⊤ : Subgroup V).lowerCentralSeries 3 = ⊥ := by
    change ⁅⁅commutator V, (⊤ : Subgroup V)⁆, (⊤ : Subgroup V)⁆ = ⊥
    exact commutator_top_right_eq_bot_iff_le_center.mpr hLcentral
  have hclass3 : Group.nilpotencyClass V = 3 := by
    have hle := Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mp hL3bot
    omega
  have hDupper : commutator V ≤ Subgroup.upperCentralSeries V 2 := by
    intro x hx
    rw [Subgroup.mem_upperCentralSeries_succ_iff]
    intro y
    rw [Subgroup.upperCentralSeries_one]
    exact hLcentral (commutator_mem_commutator hx (Subgroup.mem_top y))
  have hupperD : Subgroup.upperCentralSeries V 2 ≤ commutator V := by
    let : IsInvariant A V (Subgroup.upperCentralSeries V 2) := isInvariant_of_characteristic _
    rcases invariant_frattini_dichotomy_of_five hA hPhi16 hPhifixed (Subgroup.upperCentralSeries V 2) with hle | htop
    · simpa only [hPhiD] using hle
    · have hupper : Subgroup.upperCentralSeries V 2 = ⊤ := frattini_nongenerating htop
      have hclassle : Group.nilpotencyClass V ≤ 2 :=
        Subgroup.upperCentralSeries_eq_top_iff_nilpotencyClass_le.mp hupper
      omega
  have hDD : ⁅commutator V, commutator V⁆ = ⊥ := by
    change ⁅⁅(⊤ : Subgroup V), (⊤ : Subgroup V)⁆, commutator V⁆ = ⊥
    apply commutator_commutator_eq_bot_of_rotate
    · rw [commutator_comm (⊤ : Subgroup V) (commutator V)]
      exact hL3bot
    · exact hL3bot
  exact ⟨hclass3, hZ2, le_antisymm hDupper hupperD, commutator_self_eq_bot_iff.mp hDD⟩
/-- Parrott’s intrinsic structure theorem for the two-group of order 512. -/
public theorem parrott_twoGroup_structure
    {A V : Type*} [Group A] [Finite A] [Group V] [Finite V]
    [MulDistribMulAction A V]
    (hV : IsPGroup 2 V) (hcard : Nat.card V = 512)
    (hclass : 3 ≤ Group.nilpotencyClass V) (hA : Nat.card A = 5)
    (hfixed : FixedPoints.subgroup A V ≤ center V) :
    Group.nilpotencyClass V = 3 ∧ Nat.card (center V) = 2 ∧
    commutator V = frattini V ∧ commutator V = Subgroup.upperCentralSeries V 2 ∧
    IsElementaryAbelian 2 (commutator V) ∧ Nat.card (commutator V) = 32 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Group.IsNilpotent V := hV.isNilpotent
  let : IsInvariant A V (commutator V) := isInvariant_of_characteristic (commutator V)
  let : IsInvariant A V (center V) := isInvariant_of_characteristic (center V)
  let : MulDistribMulAction A (V ⧸ frattini V) :=
    quotientMulDistribMulAction (frattini V) (isInvariant_of_characteristic (frattini V))
  let : MulDistribMulAction A (commutator V ⧸ (center V).subgroupOf (commutator V)) :=
    quotientMulDistribMulAction ((center V).subgroupOf (commutator V))
      (isInvariant_subgroupOf (center V) (commutator V))
  obtain ⟨hPhiNontriv, hQfixed, hQnontriv⟩ := parrott_quotient_actions hV hclass hA hfixed
  have hPhiNe : FixedPoints.subgroup A (V ⧸ frattini V) ≠ ⊤ := by
    intro htop
    apply hPhiNontriv
    intro a x
    have hx : x ∈ FixedPoints.subgroup A (V ⧸ frattini V) := htop ▸ Subgroup.mem_top x
    exact hx a
  have hQNe : FixedPoints.subgroup A
      (commutator V ⧸ (center V).subgroupOf (commutator V)) ≠ ⊤ := by
    rw [hQfixed]
    let : Nontrivial (commutator V ⧸ (center V).subgroupOf (commutator V)) := hQnontriv
    exact bot_ne_top
  have hPhiBound := sixteen_le_card_of_five_action_nontrivial hA
    (hV.to_quotient (frattini V)) hPhiNe
  have hQBound := sixteen_le_card_of_five_action_nontrivial hA
    ((hV.to_subgroup (commutator V)).to_quotient ((center V).subgroupOf (commutator V))) hQNe
  obtain ⟨hPhi16, hPhiD, hD32, hZD2, hQ16⟩ := cardinal_squeeze hV hcard hPhiBound hQBound
  have hPhifixed := fixed_eq_bot_of_five_action_card_sixteen hA hPhi16 hPhiNe
  obtain ⟨hclass3, hZ2, hDupper, hDcomm⟩ :=
    structure_from_quotients hA hclass hPhiD hPhi16 hZD2 hQ16 hPhifixed hQfixed
  let : IsMulCommutative (commutator V) := hDcomm
  have hCcard : Nat.card (FixedPoints.subgroup A (commutator V)) = 2 := by
    have hCle : FixedPoints.subgroup A (commutator V) ≤ (center V).subgroupOf (commutator V) := by
      intro x hx
      apply hfixed
      intro a
      exact congrArg Subtype.val (hx a)
    have hCbound : Nat.card (FixedPoints.subgroup A (commutator V)) ≤ 2 :=
      hZD2 ▸ card_le_of_le hCle
    let : Fact (Nat.Prime 5) := ⟨by decide⟩
    have hfive : IsPGroup 5 A := IsPGroup.of_card (p := 5) (n := 1) (by simpa using hA)
    have hmod := hfive.card_modEq_card_fixedPoints (commutator V)
    change Nat.ModEq 5 (Nat.card (commutator V))
      (Nat.card (FixedPoints.subgroup A (commutator V))) at hmod
    rw [hD32] at hmod
    change 32 % 5 = Nat.card (FixedPoints.subgroup A (commutator V)) % 5 at hmod
    omega
  exact ⟨hclass3, hZ2, hPhiD.symm, hDupper,
    elementaryAbelian_of_card32_five_action hA hD32 hCcard, hD32⟩
end Theory.GroupAction
