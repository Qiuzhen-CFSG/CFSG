module

public import CFSG.Quasithin.ChapterJ.Section01To02.SpecialCore.QuaternionFixed.Basic
public import CFSG.Quasithin.ChapterJ.Section01To02.SpecialCore.SingerCentralizers.Choice
public import CFSG.Quasithin.ChapterJ.Section01To02.SpecialCore.SingerCentralizers.Restriction
public import CFSG.Quasithin.ChapterJ.Section01To02.ParabolicStructure.QuotientModule.Natural
public import CFSG.Quasithin.ChapterJ.Section01To02.ParabolicStructure.QuotientModule.FixedPlane
public import CFSG.Quasithin.ChapterJ.Section01To02.Fusion.Commutators.CentralDecomposition.CubicAction
public import Theory.SpecificGroups.SL2.CubicFixedVectors
public import Theory.Representation.PSL3Two.SteinbergStructure.ParabolicFactors.CubicFixed

/-!
# The orders of the literal cubic fixed subgroups in J.2.3(7)

The natural Q/HC section puts C_Q(B) inside HC. Cubic fixed-point freeness
on U/Z gives C_U(B)=Z. Every coset in HC/U is B-invariant, and the coprime
fiber argument lifts it to C_HC(B), which consequently has order eight.
The Steinberg coordinates similarly identify C_S(B)/C_V(B) with the cubic
fixed plane; equality of orders then gives C_Q(B)=C_S(B).

Source: Aschbacher–Smith J.2.2(3) and J.2.3(7), printed pp.432–434
(PDF pp.443–445), combined manuscript of 1 March 2004.
-/

@[expose] public section
noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterJ.SpecialCore
variable {G : Type*} [Group G] [Finite G]

/-- The literal cubic is contained in the two-residual K of H. -/
theorem cubicSubgroup_le_K (d : TypeRuSetup G) (B : Sylow 3 d.L₁) :
    cubicSubgroup d B ≤ d.K := by
  let f : (d.L ⊓ d.H : Subgroup G) →* d.H := inclusion inf_le_right
  rintro x ⟨b, _, rfl⟩
  obtain ⟨a, ha, he⟩ := b.property
  change (b : G) ∈ d.K
  rw [← he]
  exact ⟨f a, map_pResidual_le 2 f (mem_map_of_mem f ha), rfl⟩

/-- Cubic elements remain cubic under the actual H/Q marking. -/
theorem cubic_ru2_injective (d : TypeRuSetup G) (B : Sylow 3 d.L₁) :
    Function.Injective (d.ru2.quotientMap.comp
      (inclusion ((cubicSubgroup_le_K d B).trans d.K_le_H))) := by
  have hdis : Disjoint (cubicSubgroup d B) d.Q :=
    (B.isPGroup'.map d.L₁.subtype).disjoint_of_coprime
      (isPGroup_pCoreIn 2 d.H) (by decide)
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rw [eq_bot_iff_forall]
  intro b hb
  apply Subtype.ext
  apply hdis.le_bot
  refine ⟨b.property, ?_⟩
  have hh : inclusion ((cubicSubgroup_le_K d B).trans d.K_le_H) b ∈
      d.ru2.quotientMap.ker := hb
  rwa [d.ru2.quotient_kernel] at hh

/-- C_U(B)=Z, with both sides in the original ambient group. -/
theorem cubicFixedU_eq_Z (d : LocalSetup G) (B : Sylow 3 d.toTypeRuSetup.L₁) :
    d.toTypeRuSetup.U ⊓ centralizer (cubicSubgroup d.toTypeRuSetup B : Set G) =
      d.toTypeRuSetup.Z := by
  let D := d.toTypeRuSetup
  have hB := cubicSubgroup_card D B d.card_Z (d.center_eq.le.trans inf_le_left)
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' 3 (show 3 ∣ Nat.card (cubicSubgroup D B) by rw [hB])
  have hBH := (cubicSubgroup_le_K D B).trans D.K_le_H
  have ho : orderOf (D.ru2.quotientMap (inclusion hBH b)) = 3 :=
    (orderOf_injective _ (cubic_ru2_injective D B) b).trans hb
  apply le_antisymm (D.ru2.naturalAction.centralizer_le_kernel_of_cubic_image
    D.ru2.quotientMap D.ru2.natural hBH b ho)
  exact le_inf D.ru2.natural.kernel_le (fun z hz a ha => (hBH ha z hz).symm)

/-- The natural Q/HC section forces cubic fixed points into HC. -/
theorem cubicFixedQ_le_HC (d : LocalSetup G) (B : Sylow 3 d.toTypeRuSetup.L₁)
    (hQK : d.toTypeRuSetup.Q ≤ d.toTypeRuSetup.K) :
    cubicFixedQ d.toTypeRuSetup B ≤ d.toTypeRuSetup.HC := by
  let D := d.toTypeRuSetup
  let n := d.naturalQuotientSection hQK
  have hB := cubicSubgroup_card D B d.card_Z (d.center_eq.le.trans inf_le_left)
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' 3 (show 3 ∣ Nat.card (cubicSubgroup D B) by rw [hB])
  let k : D.K := inclusion (cubicSubgroup_le_K D B) b
  have hoH : orderOf (D.ru2.quotientMap (inclusion D.K_le_H k)) = 3 :=
    (orderOf_injective _ (cubic_ru2_injective D B) b).trans hb
  have ho : orderOf (D.naturalQuotientMap k) = 3 := by
    rw [← D.ru2.naturalAction.marking.orderOf_eq, ← Subgroup.orderOf_coe,
      D.naturalQuotientMap_marking]
    exact hoH
  intro q hq
  apply (n.coordinates_eq_one_iff ⟨q, hq.1⟩).mp
  apply Matrix.SL2.cubic_fixed_eq_zero (D.naturalQuotientMap k) ho
  have he := n.equivariant k ⟨q, hq.1⟩
  have hc : (k : G) * q * (k : G)⁻¹ = q :=
    mul_inv_eq_iff_eq_mul.mpr (hq.2 b b.property)
  have hx : (⟨(k : G) * q * (k : G)⁻¹,
      (mem_normalizer_iff.mp (n.normalized k.property) q).mp hq.1⟩ : D.Q) = ⟨q,hq.1⟩ :=
    Subtype.ext hc
  rw [hx] at he
  exact he.symm

/-- The cubic fixed subgroup lies in S, since HC centralizes V≤U. -/
theorem cubicFixedQ_le_S (d : LocalSetup G) (B : Sylow 3 d.toTypeRuSetup.L₁)
    (hQK : d.toTypeRuSetup.Q ≤ d.toTypeRuSetup.K) :
    cubicFixedQ d.toTypeRuSetup B ≤ d.toTypeRuSetup.S := by
  change cubicFixedQ d.toTypeRuSetup B ≤ d.L.pCoreIn 2
  rw [← d.ru1.centralizer_V]
  exact (cubicFixedQ_le_HC d B hQK).trans
    (inf_le_right.trans (centralizer_le (le_conjugateSpan _ _)))

/-- The intersection with the central natural module is exactly Z. -/
theorem cubicFixedQ_inf_V (d : LocalSetup G) (B : Sylow 3 d.toTypeRuSetup.L₁) :
    cubicFixedQ d.toTypeRuSetup B ⊓ d.V = d.toTypeRuSetup.Z := by
  let D := d.toTypeRuSetup
  apply le_antisymm
  · intro x hx
    have hh : x ∈ D.U ⊓ centralizer (cubicSubgroup D B : Set G) :=
      ⟨le_conjugateSpan D.H d.V hx.2, hx.1.2⟩
    rwa [cubicFixedU_eq_Z d B] at hh
  · refine le_inf (le_inf (D.ru2.natural.kernel_le.trans D.ru2.six.kernel_le) ?_)
      (d.center_eq.le.trans inf_le_left)
    intro z hz b hb
    exact (((cubicSubgroup_le_K D B).trans D.K_le_H) hb z hz).symm



omit [Finite G] in
/-- Coprime orbit counting in a single invariant coordinate fiber. -/
private theorem fixed_preimage {W : Type*} [Group W]
    (A P : Subgroup G) (hn : A ≤ normalizer P) (hA : IsPGroup 3 A)
    (f : P →* W) (hf : Function.Surjective f) (hker : ¬ 3 ∣ Nat.card f.ker)
    (w : W)
    (hinv : ∀ (a : A) (x : P), f x = w →
      f ⟨(a : G) * x * (a : G)⁻¹,
        (mem_normalizer_iff.mp (hn a.property) x).mp x.property⟩ = w) :
    ∃ x : P, (x : G) ∈ centralizer (A : Set G) ∧ f x = w := by
  let _ : MulDistribMulAction A P := conjMulDistribMulActionOfLeNormalizer A P hn
  let F := {x : P // f x = w}
  let _ : MulAction A F := {
    smul a x := ⟨a • x.val, hinv a x.val x.property⟩
    one_smul x := Subtype.ext (one_smul A x.val)
    mul_smul a b x := Subtype.ext (mul_smul a b x.val) }
  have hF : ¬ 3 ∣ Nat.card F := by
    have hc : Nat.card F = Nat.card f.ker :=
      Nat.card_congr (MonoidHom.fiberEquivKerOfSurjective hf w)
    rwa [hc]
  obtain ⟨x, hx⟩ := hA.nonempty_fixed_point_of_prime_not_dvd_card F hF
  refine ⟨x.val, ?_, x.property⟩
  intro a ha
  exact mul_inv_eq_iff_eq_mul.mp (congrArg (fun y : F => (y.val : G)) (hx ⟨a,ha⟩))

/-- Every HC/U coordinate has a lift in the actual cubic centralizer. -/
theorem cubicFixedHC_onto (d : LocalSetup G) (B : Sylow 3 d.toTypeRuSetup.L₁) :
    Function.Surjective (d.hcSixMap.rangeRestrict.comp
      (inclusion (show d.toTypeRuSetup.HC ⊓
        centralizer (cubicSubgroup d.toTypeRuSetup B : Set G) ≤ d.toTypeRuSetup.HC
        from inf_le_left))) := by
  let D := d.toTypeRuSetup
  have hn : cubicSubgroup D B ≤ normalizer D.HC :=
    ((cubicSubgroup_le_K D B).trans D.K_le_H).trans
      ((normal_subgroupOf_iff_le_normalizer inf_le_left).mp D.HC_normal)
  have hk : d.hcSixMap.rangeRestrict.ker = D.U.subgroupOf D.HC := by
    rw [MonoidHom.ker_rangeRestrict, d.hcSixMap_kernel]
  have hkcard : Nat.card d.hcSixMap.rangeRestrict.ker = 32 := by
    rw [hk, Nat.card_congr (subgroupOfEquivOfLe d.U_le_HC).toEquiv, d.ru2.card_U d.card_Z]
  intro w
  obtain ⟨x,hx,he⟩ := fixed_preimage (cubicSubgroup D B) D.HC hn
    (B.isPGroup'.map D.L₁.subtype) d.hcSixMap.rangeRestrict d.hcSixMap.rangeRestrict_surjective
    (by rw [hkcard]; decide) w (by
      intro a x hx
      let y : D.HC := ⟨(a : G) * x * (a : G)⁻¹,
        (mem_normalizer_iff.mp (hn a.property) x).mp x.property⟩
      have hcomm := d.HC_commutator_K_mem_U x (inclusion (cubicSubgroup_le_K D B) a)
      have he : d.hcSixMap (y * x⁻¹) = 1 := by
        apply MonoidHom.mem_ker.mp
        rw [d.hcSixMap_kernel]
        exact hcomm
      rw [map_mul, map_inv, mul_inv_eq_one] at he
      exact (Subtype.ext he).trans hx)
  exact ⟨⟨x, x.property, hx⟩, he⟩

/-- J.2.2(3) gives the order eight asserted at the start of J.2.3(7). -/
theorem cubicFixedQ_card (d : LocalSetup G) (B : Sylow 3 d.toTypeRuSetup.L₁)
    (hQK : d.toTypeRuSetup.Q ≤ d.toTypeRuSetup.K) :
    Nat.card (cubicFixedQ d.toTypeRuSetup B) = 8 := by
  let D := d.toTypeRuSetup
  let C := D.HC ⊓ centralizer (cubicSubgroup D B : Set G)
  have hC : cubicFixedQ D B = C := le_antisymm
    (le_inf (cubicFixedQ_le_HC d B hQK) inf_le_right)
    (inf_le_inf D.HC_le_Q le_rfl)
  let f := d.hcSixMap.rangeRestrict.comp (inclusion (inf_le_left : C ≤ D.HC))
  have hZC : D.Z ≤ C := le_inf (D.ru2.natural.kernel_le.trans d.U_le_HC)
    (fun z hz a ha => (((cubicSubgroup_le_K D B).trans D.K_le_H) ha z hz).symm)
  have hk : f.ker = D.Z.subgroupOf C := by
    ext x
    change f x = 1 ↔ (x : G) ∈ D.Z
    rw [Subtype.ext_iff]
    change d.hcSixMap (inclusion inf_le_left x) = 1 ↔ (x : G) ∈ D.Z
    rw [← MonoidHom.mem_ker, d.hcSixMap_kernel]
    change (x : G) ∈ D.U ↔ (x : G) ∈ D.Z
    constructor
    · intro hx
      have hh : (x : G) ∈ D.U ⊓ centralizer (cubicSubgroup D B : Set G) := ⟨hx,x.property.2⟩
      rwa [cubicFixedU_eq_Z d B] at hh
    · intro hx
      exact D.ru2.natural.kernel_le hx
  have hc := card_eq_card_quotient_mul_card_subgroup f.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f (cubicFixedHC_onto d B)).toEquiv,
    d.card_hcSixMap_range, hk, Nat.card_congr (subgroupOfEquivOfLe hZC).toEquiv, d.card_Z] at hc
  rw [hC]
  exact hc



/-- The cubic fixed subgroup of S intersects its natural kernel in Z. -/
theorem cubicFixedS_inf_V (d : LocalSetup G) (B : Sylow 3 d.toTypeRuSetup.L₁) :
    (d.toTypeRuSetup.S ⊓ centralizer (cubicSubgroup d.toTypeRuSetup B : Set G)) ⊓ d.V =
      d.toTypeRuSetup.Z := by
  apply le_antisymm
  · intro x hx
    have hh : x ∈ d.toTypeRuSetup.U ⊓ centralizer (cubicSubgroup d.toTypeRuSetup B : Set G) :=
      ⟨le_conjugateSpan _ _ hx.2, hx.1.2⟩
    rwa [cubicFixedU_eq_Z d B] at hh
  · have hz := (cubicFixedQ_inf_V d B).ge
    exact fun z h => ⟨⟨d.ru1.steinberg.kernel_le (hz h).2, (hz h).1.2⟩, (hz h).2⟩

/-- Restriction of the original Steinberg map to the literal cubic fixed subgroup. -/
def cubicFixedSCoordinates (d : TypeRuSetup G) (B : Sylow 3 d.L₁) :
    (d.S ⊓ centralizer (cubicSubgroup d B : Set G) : Subgroup G) →*
      Multiplicative (fixedSpace BinaryLinearThree.S (cubicImage d B)) where
  toFun x := Multiplicative.ofAdd ⟨(d.ru1.steinberg.coordinates ⟨x,x.property.1⟩).toAdd, by
    intro h
    obtain ⟨b,hb⟩ := h.property
    change BinaryLinearThree.S h.val _ = _
    rw [← hb]
    have he := d.ru1.steinberg.equivariant (inclusion (cubicSubgroup_le_L d B) b)
      ⟨x,x.property.1⟩
    have hc : (b : G) * (x : G) * (b : G)⁻¹ = x :=
      mul_inv_eq_iff_eq_mul.mpr (x.property.2 b b.property)
    exact he.symm.trans (congrArg (fun y : d.S => (d.ru1.steinberg.coordinates y).toAdd)
      (Subtype.ext hc))⟩
  map_one' := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    exact map_one d.ru1.steinberg.coordinates
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    exact map_mul d.ru1.steinberg.coordinates ⟨x,x.property.1⟩ ⟨y,y.property.1⟩

/-- Every cubic fixed Steinberg vector lifts to an actual cubic fixed element. -/
theorem cubicFixedSCoordinates_surjective (d : TypeRuSetup G) (B : Sylow 3 d.L₁) :
    Function.Surjective (cubicFixedSCoordinates d B) := by
  intro w
  have hk : Nat.card d.ru1.steinberg.coordinates.ker = 8 := by
    rw [d.ru1.steinberg.kernel_eq,
      Nat.card_congr (subgroupOfEquivOfLe d.ru1.steinberg.kernel_le).toEquiv, d.ru1.card_V]
  obtain ⟨x,hx,he⟩ := fixed_preimage (cubicSubgroup d B) d.S
    ((cubicSubgroup_le_L d B).trans d.ru1.steinberg.normalized)
    (B.isPGroup'.map d.L₁.subtype) d.ru1.steinberg.coordinates d.ru1.steinberg.onto
    (by rw [hk]; decide) (Multiplicative.ofAdd w.toAdd.val) (by
      intro a x hx
      apply Multiplicative.toAdd.injective
      have heq := d.ru1.steinberg.equivariant (inclusion (cubicSubgroup_le_L d B) a) x
      rw [hx] at heq
      exact heq.trans (w.toAdd.property ⟨modelMap d (cubicSubgroup d B) (cubicSubgroup_le_L d B) a,
        ⟨a,rfl⟩⟩))
  exact ⟨⟨x,x.property,hx⟩, Multiplicative.toAdd.injective (Subtype.ext he)⟩

/-- The literal fixed subgroup C_S(B) has order eight. -/
theorem cubicFixedS_card (d : LocalSetup G) (B : Sylow 3 d.toTypeRuSetup.L₁) :
    Nat.card (d.toTypeRuSetup.S ⊓ centralizer (cubicSubgroup d.toTypeRuSetup B : Set G) :
      Subgroup G) = 8 := by
  let D := d.toTypeRuSetup
  let C := D.S ⊓ centralizer (cubicSubgroup D B : Set G)
  let f := cubicFixedSCoordinates D B
  have hk : f.ker = D.Z.subgroupOf C := by
    ext x
    change f x = 1 ↔ (x : G) ∈ D.Z
    rw [← cubicFixedS_inf_V d B]
    change f x = 1 ↔ (x : G) ∈ C ∧ (x : G) ∈ d.V
    rw [and_iff_right x.property]
    change ((f x).toAdd : fixedSpace BinaryLinearThree.S (cubicImage D B)) = 0 ↔ _
    rw [Subtype.ext_iff]
    exact D.ru1.steinberg.coordinates_eq_one_iff ⟨x,x.property.1⟩
  have hZC : D.Z ≤ C := (cubicFixedS_inf_V d B).ge.trans inf_le_left
  have hc := card_eq_card_quotient_mul_card_subgroup f.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f
    (cubicFixedSCoordinates_surjective D B)).toEquiv, hk,
    Nat.card_congr (subgroupOfEquivOfLe hZC).toEquiv, d.card_Z] at hc
  have hB := cubicSubgroup_card D B d.card_Z (d.center_eq.le.trans inf_le_left)
  have hW : Nat.card (Multiplicative (fixedSpace BinaryLinearThree.S (cubicImage D B))) = 4 := by
    change Nat.card (fixedSpace BinaryLinearThree.S (cubicImage D B)) = 4
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
      BinaryLinearThree.SteinbergStructure.ParabolicFactors.finrank_fixedSpace_order_three
        _ (cubicImage_card D B hB)]
    norm_num
  rw [hW] at hc
  exact hc

/-- The source equality C_Q(B)=C_S(B), derived from J.2.2(3). -/
theorem cubicFixedQ_eq_cubicFixedS (d : LocalSetup G) (B : Sylow 3 d.toTypeRuSetup.L₁)
    (hQK : d.toTypeRuSetup.Q ≤ d.toTypeRuSetup.K) :
    cubicFixedQ d.toTypeRuSetup B =
      d.toTypeRuSetup.S ⊓ centralizer (cubicSubgroup d.toTypeRuSetup B : Set G) := by
  apply eq_of_le_of_card_ge (le_inf (cubicFixedQ_le_S d B hQK) inf_le_right)
  rw [cubicFixedQ_card d B hQK, cubicFixedS_card d B]

end CFSG.Quasithin.ChapterJ.SpecialCore
