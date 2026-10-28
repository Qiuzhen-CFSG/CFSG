module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.FrattiniRadical
public import Theory.GroupAction.ElementaryFixedQuotient
public import Theory.GroupAction.FourthPowerFixed

/-!
# The binary quintic centralizer in the whole source radical

For an automorphism of order five, orbit counting makes any nontrivial
fixed index on a finite two-group at least sixteen. Fixed points in a
characteristic extension inject fiberwise into the fixed quotient and
fixed kernel. Thus movement on both the Frattini subgroup and its quotient
forces fixed index at least 256 on the whole radical.

On the actual octagonal quotient the constructed reflection--involution
product moves Φ(V) by (6.3); local characteristic two makes its action on
V/Φ(V) faithful. Since |V| = 64 |U_j|^4 in the binary Suzuki row, its
centralizer has order at most |U_j|^4/4. At |U_j|=2, orbit counting gives
exactly four fixed elements. The fields remain independent in the bound.

Source: Fong--Seitz I (1973), proof of (6H), printed p.53, the equality
|C(s₂x) ∩ U_s₂|=4 in the binary case. The proof uses the two already
constructed Frattini layers; it does not assert derived-section effectivity
or identify Φ(V) with [V,V]. The original-endpoint leaf discharges (6.3)
and local characteristic two on the same marked quotient.
-/

@[expose] public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open RootCoordinates HexagonStructure

/-- A nontrivial quintic automorphism of a finite two-group has fixed index at least sixteen. -/
theorem quintic_fixed_index_ge {V : Type*} [Group V] [Finite V]
    (hV : IsPGroup 2 V) (a : MulAut V) (ha : a^5 = 1) (hne : a ≠ 1) :
    16 ≤ a.fixedSubgroup.index := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have ho : orderOf a = 5 := orderOf_eq_prime ha hne
  have hA : IsPGroup 5 (zpowers a) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers,ho]; rfl)
  have he : FixedPoints.subgroup (zpowers a) V = a.fixedSubgroup := by
    ext x
    exact (MulAut.mem_fixed_zpowers_iff a x).trans (MulAut.mem_fixedSubgroup a x).symm
  have hc := hA.card_modEq_card_fixedPoints V
  change Nat.card V % 5 = Nat.card (FixedPoints.subgroup (zpowers a) V) % 5 at hc
  rw [he,←a.fixedSubgroup.index_mul_card] at hc
  obtain ⟨m,hm⟩ := (hV.to_subgroup a.fixedSubgroup).exists_card_eq
  have hcop : Nat.Coprime 5 (Nat.card a.fixedSubgroup) := by
    rw [hm]; exact (by decide : Nat.Coprime 5 2).pow_right m
  have hi : a.fixedSubgroup.index ≡ 1 [MOD 5] := by
    apply Nat.ModEq.cancel_right_of_coprime hcop
    simpa only [Nat.ModEq,one_mul] using hc
  obtain ⟨n,hn⟩ := hV.index a.fixedSubgroup
  by_contra h
  have hnlt : n < 4 := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp
    (by simpa only [hn] using (Nat.lt_of_not_ge h))
  rw [hn] at hi
  interval_cases n
  · have ht : a.fixedSubgroup = ⊤ := (index_eq_one).mp (by simpa using hn)
    apply hne
    ext x
    exact (MulAut.mem_fixedSubgroup a x).mp (ht ▸ mem_top x)
  · norm_num [Nat.ModEq] at hi
  · norm_num [Nat.ModEq] at hi
  · norm_num [Nat.ModEq] at hi

/-- Fixed points in a characteristic extension are bounded by the two literal fixed groups. -/
theorem fixed_card_le_quotient_mul {V : Type*} [Group V] [Finite V]
    (N : Subgroup V) [N.Characteristic] (a : MulAut V) :
    Nat.card a.fixedSubgroup ≤ Nat.card (quotientAut N a).fixedSubgroup *
      Nat.card (MulAut.characteristic N a).fixedSubgroup := by
  let f := MulAut.fixedQuotientProjection N a
  let e : f.ker ≃ (MulAut.characteristic N a).fixedSubgroup := {
    toFun := fun x => ⟨⟨x.val.val,by
      exact (QuotientGroup.eq_one_iff x.val.val).mp (congrArg Subtype.val x.property)⟩,by
      apply (MulAut.mem_fixedSubgroup _ _).mpr
      apply Subtype.ext
      exact (MulAut.mem_fixedSubgroup _ _).mp x.val.property⟩
    invFun := fun x => ⟨⟨x.val.val,by
      apply (MulAut.mem_fixedSubgroup _ _).mpr
      exact congrArg Subtype.val ((MulAut.mem_fixedSubgroup _ _).mp x.property)⟩,by
      rw [MulAut.fixedQuotientProjection_kernel]
      exact x.val.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have hc := f.ker.card_mul_index
  rw [index_ker,Nat.card_congr e] at hc
  calc
    Nat.card a.fixedSubgroup = Nat.card (MulAut.characteristic N a).fixedSubgroup *
        Nat.card f.range := hc.symm
    _ ≤ Nat.card (MulAut.characteristic N a).fixedSubgroup *
        Nat.card (quotientAut N a).fixedSubgroup := Nat.mul_le_mul_left _
          (Nat.card_le_card_of_injective _ f.range.subtype_injective)
    _ = _ := Nat.mul_comm _ _

/-- Two nontrivial quintic layers give fixed index at least 256 on the whole group. -/
theorem quintic_two_layers_fixed_card {V : Type*} [Group V] [Finite V]
    (hV : IsPGroup 2 V) (N : Subgroup V) [N.Characteristic] (a : MulAut V)
    (ha : a^5 = 1) (hquot : quotientAut N a ≠ 1)
    (hsub : MulAut.characteristic N a ≠ 1) :
    Nat.card a.fixedSubgroup * 256 ≤ Nat.card V := by
  let b := quotientAut N a
  let c := MulAut.characteristic N a
  have hb := quintic_fixed_index_ge (hV.to_quotient N) b
    (by rw [←map_pow,ha,map_one]) hquot
  have hc := quintic_fixed_index_ge (hV.to_subgroup N) c
    (by rw [←map_pow,ha,map_one]) hsub
  have hfix := fixed_card_le_quotient_mul N a
  calc
    Nat.card a.fixedSubgroup * 256 ≤
        Nat.card a.fixedSubgroup * (b.fixedSubgroup.index*c.fixedSubgroup.index) :=
      Nat.mul_le_mul_left _ (by nlinarith)
    _ ≤ (Nat.card b.fixedSubgroup*Nat.card c.fixedSubgroup) *
        (b.fixedSubgroup.index*c.fixedSubgroup.index) := Nat.mul_le_mul_right _ hfix
    _ = (Nat.card b.fixedSubgroup*b.fixedSubgroup.index) *
        (Nat.card c.fixedSubgroup*c.fixedSubgroup.index) := by ring
    _ = Nat.card (V ⧸ N) * Nat.card N := by rw [card_mul_index,card_mul_index]
    _ = Nat.card V := N.index_mul_card

variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) (i : Fin 2)
  (hV : simpleRemainder Q split i ≤ localKernel Q i)
  (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* SuzukiMatrixGroup 0)
  (hB : (quotientBorel Q i).map μ.toMonoidHom =
    normalizer (SuzukiRootSubgroup 0 : Set (SuzukiMatrixGroup 0)))

include hB in
/-- The actual quintic product moves the characteristic Frattini subgroup of the radical. -/
theorem binary_mover_frattini_restriction_ne_one (hm : rotationOrder Q = 8)
    (j : Fin 2) (hij : i ≠ j)
    (hcomm : ⁅omegaOneAmbient (simpleRoot Q split i),
      rootAt Q split i (Q.simple j*Q.simple i)⁆ = ⊥) :
    MulAut.characteristic (frattini (simpleRemainder Q split i))
      ((radicalSection Q split i hV).numeratorAction (frattiniMover Q split i 0 μ hB)) ≠ 1 := by
  intro hz
  apply frattiniMover_moves Q split i hV 0 μ hB hm j hij hcomm
  let f := frattiniRadicalSection Q split i hV
  let c := frattiniMover Q split i 0 μ hB
  apply MulEquiv.ext
  intro z
  obtain ⟨v,rfl⟩ := QuotientGroup.mk'_surjective f.denominator z
  change f.action c (QuotientGroup.mk v) = QuotientGroup.mk v
  rw [f.action_mk]
  have hv : f.numeratorAction c v = v := by
    obtain ⟨w,hw,he⟩ := v.property
    have hh := congrArg (fun a : MulAut (frattini (simpleRemainder Q split i)) =>
      ((a ⟨w,hw⟩).val : X ⧸ Q.D)) hz
    apply Subtype.ext
    change (c : X ⧸ Q.D)*(v : X ⧸ Q.D)*(c : X ⧸ Q.D)⁻¹ = v
    rw [←he]
    exact hh
  rw [hv]

include hB in
/-- The same quintic product moves the radical modulo its Frattini subgroup. -/
theorem binary_mover_frattini_quotient_ne_one
    (hc : centralizer (pCore 2 (Endpoint Q i) : Set (Endpoint Q i)) ≤ pCore 2 (Endpoint Q i))
    (hm : rotationOrder Q = 8) (j : Fin 2) (hij : i ≠ j)
    (hcomm : ⁅omegaOneAmbient (simpleRoot Q split i),
      rootAt Q split i (Q.simple j*Q.simple i)⁆ = ⊥) :
    quotientAut (frattini (simpleRemainder Q split i))
      ((radicalSection Q split i hV).numeratorAction (frattiniMover Q split i 0 μ hB)) ≠ 1 := by
  intro hz
  let d := radicalSection Q split i hV
  let c := frattiniMover Q split i 0 μ hB
  have he : d.effectiveAction c = 1 := by
    apply MulEquiv.ext
    intro z
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective d.effectiveDenominator z
    change d.effectiveAction c (QuotientGroup.mk x) = QuotientGroup.mk x
    rw [d.effectiveAction_mk]
    apply QuotientGroup.eq_iff_div_mem.mpr
    have hh := congrArg (fun a : MulAut (d.numerator ⧸ frattini d.numerator) =>
      a (QuotientGroup.mk' (frattini d.numerator) x)) hz
    change quotientAut (frattini d.numerator) (d.numeratorAction c)
      (QuotientGroup.mk' (frattini d.numerator) x) = QuotientGroup.mk' (frattini d.numerator) x at hh
    rw [quotientAut_apply_mk] at hh
    have hh' : d.numeratorAction c x / x ∈ frattini d.numerator :=
      QuotientGroup.eq_iff_div_mem.mp hh
    rw [d.effectiveDenominator_eq]
    exact (show frattini d.numerator ≤ frattini d.numerator ⊔ d.denominator from le_sup_left) hh'
  have hec : c = 1 := radical_effectiveAction_injective Q split i hV hc (he.trans (map_one _).symm)
  have ho := binary_frattiniMover_order Q split i hV μ hB hm j hij hcomm
  change orderOf c = 5 at ho
  rw [hec,orderOf_one] at ho
  norm_num at ho

/-- The literal source centralizer is the fixed subgroup of the radical action. -/
def radicalFixedEquiv (r : rankOne Q split i) :
    ((radicalSection Q split i hV).numeratorAction r).fixedSubgroup ≃*
      (simpleRemainder Q split i ⊓ centralizer ({(r : X ⧸ Q.D)} : Set (X ⧸ Q.D)) :
        Subgroup (X ⧸ Q.D)) where
  toFun x := ⟨x.val, x.val.property, mem_centralizer_singleton_iff.mpr (by
    have hh := congrArg Subtype.val ((MulAut.mem_fixedSubgroup _ _).mp x.property)
    change (r : X ⧸ Q.D)*(x.val : X ⧸ Q.D)*(r : X ⧸ Q.D)⁻¹ = x.val at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm)⟩
  invFun x := ⟨⟨x,x.property.1⟩,(MulAut.mem_fixedSubgroup _ _).mpr (by
    apply Subtype.ext
    change (r : X ⧸ Q.D)*(x : X ⧸ Q.D)*(r : X ⧸ Q.D)⁻¹ = x
    exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp x.property.2).symm)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

@[simp] theorem radicalFixedEquiv_apply (r : rankOne Q split i)
    (x : ((radicalSection Q split i hV).numeratorAction r).fixedSubgroup) :
    (radicalFixedEquiv Q split i hV r x : X ⧸ Q.D) = x.val := rfl

include hV hB in
/-- The p.53 odd-actor estimate on the WHOLE radical, before field synchronization. -/
theorem binary_mover_centralizer_weighted_card_le
    (hc : centralizer (pCore 2 (Endpoint Q i) : Set (Endpoint Q i)) ≤ pCore 2 (Endpoint Q i))
    (hm : rotationOrder Q = 8) (j : Fin 2) (hij : i ≠ j)
    (hcomm : ⁅omegaOneAmbient (simpleRoot Q split i),
      rootAt Q split i (Q.simple j*Q.simple i)⁆ = ⊥) :
    Nat.card (simpleRemainder Q split i ⊓
      centralizer ({(frattiniMover Q split i 0 μ hB : X ⧸ Q.D)} : Set (X ⧸ Q.D)) :
        Subgroup (X ⧸ Q.D)) * 4 ≤ Nat.card (simpleRoot Q split j)^4 := by
  let d := radicalSection Q split i hV
  let c := frattiniMover Q split i 0 μ hB
  have ho := binary_frattiniMover_order Q split i hV μ hB hm j hij hcomm
  have hb := quintic_two_layers_fixed_card d.isTwo (frattini d.numerator) (d.numeratorAction c)
    (by rw [←map_pow,←ho,pow_orderOf_eq_one,map_one])
    (binary_mover_frattini_quotient_ne_one Q split i hV μ hB hc hm j hij hcomm)
    (binary_mover_frattini_restriction_ne_one Q split i hV μ hB hm j hij hcomm)
  rw [Nat.card_congr (radicalFixedEquiv Q split i hV c).toEquiv] at hb
  have hv := suzuki_octagon_radical_card Q split i j 0 μ hB hm hij
  change Nat.card d.numerator = _ at hv
  rw [hv] at hb
  norm_num at hb
  change Nat.card (simpleRemainder Q split i ⊓ centralizer ({(c : X ⧸ Q.D)} : Set _) :
    Subgroup (X ⧸ Q.D)) * 256 ≤ 64 * Nat.card (simpleRoot Q split j)^4 at hb
  change Nat.card (simpleRemainder Q split i ⊓ centralizer ({(c : X ⧸ Q.D)} : Set _) :
    Subgroup (X ⧸ Q.D)) * 4 ≤ Nat.card (simpleRoot Q split j)^4
  omega

include hV hB in
/-- At binary field order the same actual quintic element fixes exactly four radical elements. -/
theorem binary_mover_centralizer_card
    (hc : centralizer (pCore 2 (Endpoint Q i) : Set (Endpoint Q i)) ≤ pCore 2 (Endpoint Q i))
    (hm : rotationOrder Q = 8) (j : Fin 2) (hij : i ≠ j)
    (hcomm : ⁅omegaOneAmbient (simpleRoot Q split i),
      rootAt Q split i (Q.simple j*Q.simple i)⁆ = ⊥)
    (hlinear : Nat.card (simpleRoot Q split j) = 2) :
    Nat.card (simpleRemainder Q split i ⊓
      centralizer ({(frattiniMover Q split i 0 μ hB : X ⧸ Q.D)} : Set (X ⧸ Q.D)) :
        Subgroup (X ⧸ Q.D)) = 4 := by
  let d := radicalSection Q split i hV
  let c := frattiniMover Q split i 0 μ hB
  let A := zpowers c
  let : MulDistribMulAction (rankOne Q split i) d.numerator :=
    MulDistribMulAction.compHom _ d.numeratorAction
  let : MulDistribMulAction A d.numerator := MulDistribMulAction.compHom _ A.subtype
  have ho := binary_frattiniMover_order Q split i hV μ hB hm j hij hcomm
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hA : IsPGroup 5 A := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers,ho]; rfl)
  have he : FixedPoints.subgroup A d.numerator = (d.numeratorAction c).fixedSubgroup := by
    ext x
    constructor
    · intro hx
      exact (MulAut.mem_fixedSubgroup _ _).mpr (hx ⟨c,mem_zpowers c⟩)
    · intro hx a
      exact smul_eq_self_of_mem_zpowers a.property ((MulAut.mem_fixedSubgroup _ _).mp hx)
  have hmod := hA.card_modEq_card_fixedPoints d.numerator
  change Nat.card d.numerator % 5 = Nat.card (FixedPoints.subgroup A d.numerator) % 5 at hmod
  rw [he,Nat.card_congr (radicalFixedEquiv Q split i hV c).toEquiv] at hmod
  have hv := suzuki_octagon_radical_card Q split i j 0 μ hB hm hij
  change Nat.card d.numerator = _ at hv
  rw [hlinear] at hv
  rw [hv] at hmod
  have hle := binary_mover_centralizer_weighted_card_le Q split i hV μ hB hc hm j hij hcomm
  rw [hlinear] at hle
  norm_num at hmod hle
  change Nat.card (simpleRemainder Q split i ⊓ centralizer ({(c : X ⧸ Q.D)} : Set _) :
    Subgroup (X ⧸ Q.D)) = 4
  change Nat.card (simpleRemainder Q split i ⊓ centralizer ({(c : X ⧸ Q.D)} : Set _) :
    Subgroup (X ⧸ Q.D)) * 4 ≤ 16 at hle
  change 4 = Nat.card (simpleRemainder Q split i ⊓ centralizer ({(c : X ⧸ Q.D)} : Set _) :
    Subgroup (X ⧸ Q.D)) % 5 at hmod
  omega

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
