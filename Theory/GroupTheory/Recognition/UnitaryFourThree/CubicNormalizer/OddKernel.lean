module

public import Theory.GroupTheory.Recognition.UnitaryFourThree.Orbit
public import Theory.GroupTheory.OddFixedKernelInvolution
public import Theory.GroupTheory.PrimeOrderCentralizerSylow
public import Theory.GroupTheory.CyclicSylowTwoComplement
public import Theory.GroupTheory.OddCentralizerProduct
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# Odd kernels of the cubic centralizer

Once the centralizer inside the marked involution centralizer is X⟨z⟩,
its Sylow two-subgroups have order two and admit their canonical odd normal
complement. The involution fixes exactly X in that complement; consequently
it inverts the abelian quotient by X. All maps and subgroups remain in G.

Source: Aschbacher, *Sporadic Groups* (1994), Lemma 45.7, printed pp.245–246.
-/

@[expose] public section
open Subgroup
namespace Theory.GroupTheory.Recognition.UnitaryFourThree
variable {G : Type*} [Group G] [Finite G] {z : G}
namespace CubicNormalizer

def oddKernel (X : Subgroup G) : Subgroup G :=
  (pPrimeCore 2 (Subgroup.centralizer (X : Set G))).map (Subgroup.centralizer (X : Set G)).subtype

variable (h : CentralizerHypothesis z) (X : Subgroup G)
  (hX : Nat.card X = 9) (hXH : X ≤ centralizer z)
  (hfixed : centralizer z ⊓ Subgroup.centralizer (X : Set G) = X ⊔ zpowers z)

include h hX hXH hfixed in
theorem exists_centralizer_sylow :
    ∃ S : Sylow 2 (Subgroup.centralizer (X:Set G)),
      (S : Subgroup (Subgroup.centralizer (X:Set G))).map
        (Subgroup.centralizer (X:Set G)).subtype = zpowers z := by
  let C := Subgroup.centralizer (X : Set G)
  have hzC : z∈C := fun x hx => mem_centralizer_singleton_iff.mp (hXH hx)
  let zz : C := ⟨z,hzC⟩
  have hz : orderOf zz=2 := (orderOf_coe zz).symm.trans h.involution
  have hCY : C ⊓ centralizer z = X ⊔ zpowers z := by rw [inf_comm,hfixed]
  have hprod : Nat.card (X ⊔ zpowers z : Subgroup G) = 18 := by
    have hc : zpowers z ≤ Subgroup.centralizer (X : Set G) := zpowers_le.mpr hzC
    have hd : Disjoint X (zpowers z) := disjoint_of_coprime_natCard (by
      rw [hX,Nat.card_zpowers,h.involution]; decide)
    rw [card_sup_eq_mul_of_normalizes_of_disjoint X (zpowers z)
      (hc.trans (centralizer_le_normalizer _)) hd,hX,Nat.card_zpowers,h.involution]
  have hc : Nat.card (Subgroup.centralizer ({zz}:Set C)) = 18 := by
    have he : (Subgroup.centralizer ({zz}:Set C)).map C.subtype = C ⊓ centralizer z := by
      ext x
      constructor
      · rintro ⟨y,hy,rfl⟩
        exact ⟨y.property,mem_centralizer_singleton_iff.mpr
          (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hy))⟩
      · rintro ⟨hx,hxz⟩
        exact ⟨⟨x,hx⟩,mem_centralizer_singleton_iff.mpr
          (Subtype.ext (mem_centralizer_singleton_iff.mp hxz)),rfl⟩
    rw [← card_map_of_injective C.subtype_injective,he,hCY,hprod]
  obtain ⟨S,hS⟩ := (IsPGroup.of_card (p:=2) (n:=1)
    (show Nat.card (zpowers zz)=2^1 by simp [Nat.card_zpowers,hz])).exists_le_sylow
  have hcard : Nat.card S=2 := sylow_card_eq_prime_of_centralizer zz hz (by rw [hc]; decide) S
  have he : (S : Subgroup C)=zpowers zz :=
    (eq_of_le_of_card_ge hS (by rw [hcard,Nat.card_zpowers,hz])).symm
  refine ⟨S,?_⟩
  rw [he,MonoidHom.map_zpowers]
  rfl

include h hX hXH hfixed in
theorem centralizer_split : Subgroup.centralizer (X : Set G) = oddKernel X ⊔ zpowers z := by
  let C := Subgroup.centralizer (X : Set G)
  obtain ⟨S,hS⟩ := exists_centralizer_sylow h X hX hXH hfixed
  have hcard : Nat.card S=2 := by
    rw [←card_map_of_injective C.subtype_injective,hS,Nat.card_zpowers,h.involution]
  let : IsCyclic S := isCyclic_of_prime_card hcard
  have hcomp := S.isComplement'_pPrimeCore_of_isCyclic inferInstance
    (hcard ▸ (S : Subgroup C).card_subgroup_dvd_card)
  have hh := congrArg (fun K:Subgroup C=>K.map C.subtype) hcomp.sup_eq_top
  rw [Subgroup.map_sup,hS,← MonoidHom.range_eq_map,C.range_subtype] at hh
  exact hh.symm.trans (sup_comm _ _)

include hX hfixed in
omit [Finite G] in
theorem le_oddKernel : X≤oddKernel X := by
  let C := Subgroup.centralizer (X:Set G)
  have hXC : X≤C := (show X≤X⊔zpowers z from le_sup_left).trans hfixed.ge |>.trans inf_le_right
  have hcen : X.subgroupOf C ≤ center C := by
    intro x hx
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext (y.property x hx).symm
  have hn : (X.subgroupOf C).Normal := ⟨fun x hx g=>by
    rw [mem_center_iff.mp (hcen hx) g,mul_inv_cancel_right]
    exact hx⟩
  have ho : Nat.Coprime 2 (Nat.card (X.subgroupOf C)) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hXC).toEquiv,hX]
    decide
  have hi : X.subgroupOf C ≤ pPrimeCore 2 C := le_sSup ⟨hn,ho⟩
  have hm := map_mono (f:=C.subtype) hi
  rwa [map_subgroupOf_eq_of_le hXC] at hm

include h hX hXH hfixed in
theorem fixed_oddKernel : oddKernel X ⊓ centralizer z = X := by
  let V := oddKernel X
  have hVX : V≤Subgroup.centralizer (X:Set G) := map_subtype_le _
  apply le_antisymm
  · apply odd_centralizer_le_of_commuting_product X (zpowers z) V
      (by
        change Odd (Nat.card ((pPrimeCore 2 (Subgroup.centralizer (X:Set G))).map _))
        rw [card_map_of_injective (Subgroup.centralizer (X:Set G)).subtype_injective]
        exact Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p:=2)))
      (zpowers_le.mpr (fun x hx=>mem_centralizer_singleton_iff.mp (hXH hx)))
      (fun e he=>by
        obtain ⟨n,rfl⟩:=mem_zpowers_iff.mp he
        have hz2 : z^2=1 := h.involution ▸ pow_orderOf_eq_one z
        calc
          (z^n)^2 = (z^n)^(2:ℤ) := (zpow_natCast _ _).symm
          _ = z^(n*2) := (zpow_mul z n 2).symm
          _ = (z^(2:ℤ))^n := by rw [Int.mul_comm,zpow_mul]
          _ = 1 := by
            have hi : z^(2:ℤ)=1 := by exact_mod_cast hz2
            rw [hi,one_zpow]) hVX
      (by simpa only [inf_comm,centralizer] using hfixed)
  · exact le_inf (le_oddKernel X hX hfixed) hXH

include hfixed in
omit [Finite G] in
theorem X_le_centralizer : X ≤ Subgroup.centralizer (X:Set G) :=
  (show X≤X⊔zpowers z from le_sup_left).trans hfixed.ge |>.trans inf_le_right

theorem oddKernel_odd (X : Subgroup G) : Odd (Nat.card (oddKernel X)) := by
  change Odd (Nat.card ((pPrimeCore 2 (Subgroup.centralizer (X:Set G))).map _))
  rw [card_map_of_injective (Subgroup.centralizer (X:Set G)).subtype_injective]
  exact Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p:=2))

omit [Finite G] in
theorem normalizer_normalizes_oddKernel (X : Subgroup G) :
    normalizer (X:Set G) ≤ normalizer (oddKernel X:Set G) :=
  (normalizer_le_normalizer_centralizer X).trans
    (normalizer_le_normalizer_characteristic_image (Subgroup.centralizer (X:Set G))
      (pPrimeCore 2 (Subgroup.centralizer (X:Set G))))

include h hX hXH hfixed in
theorem oddKernel_quotient_inversion :
    (∀ v∈oddKernel X, z*v*z⁻¹*v∈X) ∧
      ⁅oddKernel X,oddKernel X⁆≤X := by
  let V := oddKernel X
  have hn : z∈normalizer (V:Set G) := normalizer_normalizes_oddKernel X
    ((centralizer_le_normalizer (X:Set G)) (fun x hx=>mem_centralizer_singleton_iff.mp (hXH hx)))
  let a := V.normalizerMonoidHom ⟨z,hn⟩
  let C := X.subgroupOf V
  have hXV : X≤V := le_oddKernel X hX hfixed
  have hcen : C≤center V := by
    intro x hx
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext (((map_subtype_le _ : V≤Subgroup.centralizer (X:Set G)) y.property) x hx).symm
  let : C.Normal := ⟨fun x hx g=>by
    rw [mem_center_iff.mp (hcen hx) g,mul_inv_cancel_right]
    exact hx⟩
  have hao : Function.Involutive a := by
    intro v
    apply Subtype.ext
    change z*(z*(v:G)*z⁻¹)*z⁻¹=(v:G)
    have hz2 : z*z=1 := by simpa only [pow_two,h.involution] using pow_orderOf_eq_one z
    have hzI : z⁻¹=z := inv_eq_of_mul_eq_one_left hz2
    rw [hzI]
    calc
      z*(z*(v:G)*z)*z = (z*z)*(v:G)*(z*z) := by group
      _ = v := by rw [hz2,one_mul,mul_one]
  have hfix (x:V) : a x=x ↔ x∈C := by
    constructor
    · intro hx
      have hh : z*(x:G)*z⁻¹=(x:G) := congrArg Subtype.val hx
      exact (fixed_oddKernel h X hX hXH hfixed).le
        ⟨x.property,mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hh).symm⟩
    · intro hx
      apply Subtype.ext
      change z*(x:G)*z⁻¹=(x:G)
      have hh : (x:G)*z=z*(x:G) := mem_centralizer_singleton_iff.mp (hXH hx)
      rw [←hh,mul_inv_cancel_right]
  have hco : Odd (Nat.card C) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hXV).toEquiv,hX]
    decide
  obtain ⟨hi,hc⟩ := a.quotient_inversion_of_odd_fixed_kernel hao C hco hfix
  constructor
  · intro v hv
    exact hi ⟨v,hv⟩
  · have hm := map_mono (f:=V.subtype) hc
    rw [map_commutator_eq,map_subgroupOf_eq_of_le hXV] at hm
    simpa only [V.range_subtype] using hm

end CubicNormalizer
end Theory.GroupTheory.Recognition.UnitaryFourThree
