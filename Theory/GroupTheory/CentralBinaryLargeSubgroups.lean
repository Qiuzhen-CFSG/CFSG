module
public import Theory.GroupTheory.CentralBinarySelfCentralizer
public import Theory.GroupTheory.Commutator.CentralQuotientPairing
/-!
# Large class-two subgroups with binary commutator duality

Let U be a normal elementary abelian subgroup of order 32, equal to its
centralizer, containing the derived subgroup, with [G,U] in a central line Z.
Suppose commuting modulo Z with any b outside U forces the other element
into U or b⁻¹U. Then every class-two subgroup of order at least 128 which
contains Z contains U.

For such a subgroup A, put r=|A:A∩U|. Binary commutator duality gives
|C_U(A)|=32/r. A commutator row modulo Z has kernel of relative index
at most two over A∩U, whereas its image lies in C_U(A)/Z. Thus r²≤32.
If U is not contained in A, |A∩U|≤16, contradicting |A|≥128.
A central commutator can first be cancelled by an element of U, so the
coset hypothesis also follows from its ordinary commuting version.

This is the intrinsic counting step for the order-512 core in the
Aschbacher--Smith cubic--quintic amalgam. The commutator duality is F.9.7,
printed p.321; the five-action coset property is Parrott (1972), pp.673–674.
-/

public section
namespace Subgroup
open scoped commutatorElement IsMulCommutative
variable {G : Type*} [Group G] [Finite G]

/-- Cancel a central commutator without changing either derived coset. -/
theorem central_commutator_cosets
    (U Z : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (hZ : Z ≤ center G) (hZcard : Nat.card Z = 2)
    (hcomm : ⁅(⊤ : Subgroup G), U⁆ ≤ Z)
    (hself : centralizer (U : Set G) = U)
    (hcosets : ∀ b x : G, b ∉ U → Commute b x → x ∈ U ∨ b * x ∈ U)
    (b x : G) (hb : b ∉ U) (hx : ⁅b,x⁆ ∈ Z) : x ∈ U ∨ b*x ∈ U := by
  let f : U →* Z := {
    toFun u := ⟨⁅b,(u:G)⁆,hcomm (commutator_mem_commutator (mem_top b) u.property)⟩
    map_one' := Subtype.ext (by simp)
    map_mul' u v := by
      apply Subtype.ext
      change ⁅b,(u:G)*(v:G)⁆ = ⁅b,(u:G)⁆ * ⁅b,(v:G)⁆
      rw [commutatorElement_mul_right_eq_mul_conj]
      have hc := hZ (hcomm (commutator_mem_commutator (mem_top b) v.property))
      calc
        _ = ⁅b,(u:G)⁆ * ((u:G)*⁅b,(v:G)⁆) * (u:G)⁻¹ := by group
        _ = _ := by rw [mem_center_iff.mp hc u]; group }
  have hf : f.range = ⊤ := by
    have hd := f.range.card_subgroup_dvd_card
    rw [hZcard] at hd
    rcases Nat.prime_two.eq_one_or_self_of_dvd _ hd with h1 | h2
    · have hf1 : ∀ u : U, f u = 1 := by
        intro u
        have hh := card_eq_one.mp h1
        exact mem_bot.mp (hh ▸ (show f u ∈ f.range from ⟨u,rfl⟩))
      apply (hb ?_).elim
      rw [←hself]
      intro u hu
      exact (commutatorElement_eq_one_iff_mul_comm.mp
        (congrArg Subtype.val (hf1 ⟨u,hu⟩))).symm
    · exact f.range.eq_top_of_card_eq (h2.trans hZcard.symm)
  obtain ⟨u,hu⟩ := MonoidHom.range_eq_top.mp hf ⟨⁅b,x⁆⁻¹,Z.inv_mem hx⟩
  have hu' : ⁅b,(u:G)⁆ = ⁅b,x⁆⁻¹ := congrArg Subtype.val hu
  have hc : Commute b (x*(u:G)) := by
    apply commutatorElement_eq_one_iff_mul_comm.mp
    rw [commutatorElement_mul_right_eq_mul_conj,hu']
    have hz := hZ (Z.inv_mem hx)
    calc
      _ = ⁅b,x⁆ * (x * ⁅b,x⁆⁻¹) * x⁻¹ := by group
      _ = 1 := by rw [mem_center_iff.mp hz x]; group
  rcases hcosets b (x*u) hb hc with h | h
  · exact Or.inl ((U.mul_mem_cancel_right u.property).mp h)
  · exact Or.inr ((U.mul_mem_cancel_right u.property).mp (by simpa only [mul_assoc] using h))

/-- Every sufficiently large class-two subgroup contains the elementary self-centralizer. -/
theorem large_class_two_contains_selfCentralizer
    (U Z A : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (hZU : Z ≤ U) (hZA : Z ≤ A) (hZ : Z ≤ center G)
    (hZcard : Nat.card Z = 2) (hUcard : Nat.card U = 32)
    (hcomm : ⁅(⊤ : Subgroup G), U⁆ ≤ Z)
    (hderived : _root_.commutator G ≤ U)
    (hself : centralizer (U : Set G) = U)
    (hcosets : ∀ b x : G, b ∉ U → ⁅b,x⁆ ∈ Z → x ∈ U ∨ b*x ∈ U)
    (hclass : ⁅⁅A,A⁆,A⁆ = ⊥) (hAcard : 128 ≤ Nat.card A) : U ≤ A := by
  classical
  let C := U ⊓ centralizer (A : Set G)
  have hZC : Z ≤ C := le_inf hZU (hZ.trans (center_le_centralizer _))
  let ZU := Z.subgroupOf U
  let CU := C.subgroupOf U
  let q := QuotientGroup.mk' ZU
  let : ZU.Normal := normal_of_isMulCommutative _
  have hthird : ⁅U,(⊤ : Subgroup G)⁆ ≤ Z := by simpa only [commutator_comm] using hcomm
  obtain ⟨f,hf⟩ := exists_central_quotient_commutator_pairing U Z hderived hthird
  have hidx := centralizer_relIndex_eq_of_central_binary_commutators A U Z hZA hZ
    ((commutator_mono le_top le_rfl).trans hcomm) hZcard
  rw [hself] at hidx
  have hCcard : U.relIndex A * Nat.card C = 32 := by
    have hh := ((centralizer (A : Set G)).subgroupOf U).index_mul_card
    rw [←inf_subgroupOf_left,
      Nat.card_congr (subgroupOfEquivOfLe (show C ≤ U from inf_le_left)).toEquiv] at hh
    change (U ⊓ centralizer (A : Set G)).relIndex U * Nat.card C = Nat.card U at hh
    rw [inf_relIndex_left] at hh
    rwa [←hidx,hUcard] at hh
  have hqcard : Nat.card (CU.map q) * 2 = Nat.card C := by
    have hi := relIndex_ker (K := CU) q
    rw [QuotientGroup.ker_mk'] at hi
    have hh := (ZU.subgroupOf CU).index_mul_card
    have hZZ : ZU ≤ CU := fun z hz => hZC hz
    rw [Nat.card_congr (subgroupOfEquivOfLe hZZ).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe hZU).toEquiv,hZcard,
      Nat.card_congr (subgroupOfEquivOfLe (show C ≤ U from inf_le_left)).toEquiv] at hh
    change ZU.relIndex CU * 2 = Nat.card C at hh
    rwa [hi] at hh
  by_cases hAU : A ≤ U
  · have he : A = U := eq_of_le_of_card_ge hAU (by omega)
    exact he.ge
  obtain ⟨b,hbA,hbU⟩ : ∃ b ∈ A, b ∉ U := by
    simpa only [SetLike.le_def,not_forall,exists_prop] using hAU
  let row := (f b).comp A.subtype
  have hrange : row.range ≤ CU.map q := by
    rintro _ ⟨a,rfl⟩
    have hd : ⁅b,(a:G)⁆ ∈ ⁅A,A⁆ := commutator_mem_commutator hbA a.property
    have hu : ⁅b,(a:G)⁆ ∈ U := hderived
      (commutator_mem_commutator (mem_top b) (mem_top a))
    have hc : ⁅b,(a:G)⁆ ∈ centralizer (A : Set G) :=
      (commutator_eq_bot_iff_le_centralizer.mp hclass) hd
    exact ⟨⟨⁅b,(a:G)⁆,hu⟩,⟨hu,hc⟩, (hf b a).symm⟩
  let K := row.ker.map A.subtype
  have hKA : K ≤ A := map_subtype_le _
  have hUK : U ⊓ A ≤ K := by
    intro u hu
    refine ⟨⟨u,hu.2⟩,?_,rfl⟩
    change f b u = 1
    rw [hf]
    exact (QuotientGroup.eq_one_iff _).mpr
      (hcomm (commutator_mem_commutator (mem_top b) hu.1))
  let π := QuotientGroup.mk' U
  have hKsmall : Nat.card (K.map π) ≤ 2 := by
    have htwo (y : K.map π) : (y : G ⧸ U) = 1 ∨ (y : G ⧸ U) = (π b)⁻¹ := by
      obtain ⟨x,hx,he⟩ := y.property
      obtain ⟨a,ha,rfl⟩ := hx
      have hz : ⁅b,(a:G)⁆ ∈ Z := by
        have hh : f b a = 1 := ha
        rw [hf] at hh
        exact (QuotientGroup.eq_one_iff (N := Z.subgroupOf U) _).mp hh
      rcases hcosets b a hbU hz with h | h
      · exact Or.inl (he.symm.trans ((QuotientGroup.eq_one_iff _).mpr h))
      · right
        have hh : π b * π a = 1 := by
          rw [←map_mul]
          exact (QuotientGroup.eq_one_iff _).mpr h
        exact he.symm.trans (eq_inv_of_mul_eq_one_right hh)
    let tag : K.map π → Bool := fun y => decide ((y:G ⧸ U) = 1)
    have hinj : Function.Injective tag := by
      intro y z h
      apply Subtype.ext
      rcases htwo y with hy | hy <;> rcases htwo z with hz | hz
      · exact hy.trans hz.symm
      · have hz1 : (z:G ⧸ U) = 1 := by simpa only [tag,hy,decide_true,decide_eq_true_eq] using h.symm
        exact hy.trans hz1.symm
      · have hy1 : (y:G ⧸ U) = 1 := by simpa only [tag,hz,decide_true,decide_eq_true_eq] using h
        exact hy1.trans hz.symm
      · exact hy.trans hz.symm
    simpa only [Nat.card_eq_fintype_card,Fintype.card_bool] using Nat.card_le_card_of_injective tag hinj
  have hKidx : U.relIndex K ≤ 2 := by
    have hh := relIndex_ker (K := K) π
    rw [QuotientGroup.ker_mk'] at hh
    exact hh ▸ hKsmall
  have hrowidx : K.relIndex A = Nat.card row.range := by
    have hh := relIndex_map_map_of_injective row.ker (⊤ : Subgroup A) A.subtype_injective
    rw [←MonoidHom.range_eq_map,range_subtype,relIndex_top_right,index_ker] at hh
    exact hh
  have hprod : U.relIndex A = U.relIndex K * Nat.card row.range := by
    have hh := relIndex_mul_relIndex (U ⊓ A) K A hUK hKA
    rw [hrowidx, inf_relIndex_right] at hh
    have hk : (U ⊓ A).relIndex K = U.relIndex K := by
      change ((U ⊓ A).subgroupOf K).index = (U.subgroupOf K).index
      congr 1
      ext k
      exact ⟨fun h => h.1,fun h => ⟨h,hKA k.property⟩⟩
    rw [hk] at hh
    exact hh.symm
  have hbound : U.relIndex A ≤ 2 * Nat.card (CU.map q) := by
    rw [hprod]
    exact Nat.mul_le_mul hKidx (card_le_of_le hrange)
  have hsquare : U.relIndex A * U.relIndex A ≤ 32 := by
    calc
      _ ≤ U.relIndex A * (2 * Nat.card (CU.map q)) := Nat.mul_le_mul_left _ hbound
      _ = 32 := by rw [mul_comm 2, hqcard, hCcard]
  have hr : U.relIndex A ≤ 5 := by nlinarith
  by_contra hUA
  have hproper : U ⊓ A ≠ U := fun he => hUA (he ▸ inf_le_right)
  have hint : Nat.card (U ⊓ A : Subgroup G) ≤ 16 := by
    have hh := ((U ⊓ A).subgroupOf U).index_mul_card
    rw [Nat.card_congr (subgroupOfEquivOfLe (show U ⊓ A ≤ U from inf_le_left)).toEquiv,hUcard] at hh
    have hn : (U ⊓ A).relIndex U ≠ 1 := fun he =>
      hproper (le_antisymm inf_le_left (relIndex_eq_one.mp he))
    have hp : 0 < (U ⊓ A).relIndex U := Nat.pos_of_ne_zero index_ne_zero_of_finite
    change (U ⊓ A).relIndex U * Nat.card (U ⊓ A : Subgroup G) = 32 at hh
    have htwo : 2 ≤ (U ⊓ A).relIndex U := by omega
    nlinarith
  have hh := ((U ⊓ A).subgroupOf A).index_mul_card
  rw [Nat.card_congr (subgroupOfEquivOfLe (show U ⊓ A ≤ A from inf_le_right)).toEquiv] at hh
  change (U ⊓ A).relIndex A * Nat.card (U ⊓ A : Subgroup G) = Nat.card A at hh
  rw [inf_relIndex_right] at hh
  nlinarith
end Subgroup
