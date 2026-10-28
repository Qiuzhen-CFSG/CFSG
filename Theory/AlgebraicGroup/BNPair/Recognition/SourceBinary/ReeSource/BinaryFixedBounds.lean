module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.BinaryCentralizers
public import Theory.GroupAction.AutomorphismFixedTransport

/-!
# Binary Suzuki fixed indices on literal effective sections

An involution in Sz(2) has a commutator of order five. The intersection of
its fixed group and a conjugate fixed group fixes that commutator. The
quintic index bound therefore forces involution fixed index at least four.
On an elementary binary group an order-four actor has strictly fewer fixed
points than its square, so its fixed index is at least eight.

These arguments apply to every faithful binary Suzuki module, with no
irreducibility or dimension hypothesis. The final theorem applies them to
the actual effective action of an invariant source section and identifies
that action with its literal Frattini quotient when the denominator is one.

Source: Fong--Seitz I (1973), the binary case of the module estimates
preceding (6.1), printed p.52. This elementary five-group argument replaces
the use of Hall--Higman for these two binary fixed-index inequalities.
-/

@[expose] public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource

private instance fiveFour_decEq : DecidableEq FiveFour.Group := fun a b =>
  decidable_of_iff (a.left = b.left ∧ a.right = b.right) SemidirectProduct.ext_iff.symm

private theorem fiveFour_involution_commutator :
    ∀ t : FiveFour.Group, t^2 = 1 → t ≠ 1 → ∃ x : FiveFour.Group,
      (t*x*t⁻¹*x⁻¹)^5 = 1 ∧ t*x*t⁻¹*x⁻¹ ≠ 1 := by decide +kernel

/-- Every binary Suzuki involution has a quintic commutator. -/
theorem binary_suzuki_involution_commutator (t : SuzukiMatrixGroup 0)
    (ht : t^2 = 1) (hne : t ≠ 1) : ∃ x : SuzukiMatrixGroup 0,
      (t*x*t⁻¹*x⁻¹)^5 = 1 ∧ t*x*t⁻¹*x⁻¹ ≠ 1 := by
  let e := FiveFour.suzukiZeroEquiv
  obtain ⟨x,hx,hn⟩ := fiveFour_involution_commutator (e.symm t)
    (by rw [←map_pow,ht,map_one]) (e.symm.map_ne_one_iff.mpr hne)
  refine ⟨e x,?_,?_⟩
  · apply e.symm.injective
    simpa only [map_pow,map_mul,map_inv,map_one,e.symm_apply_apply] using hx
  · intro hz
    apply hn
    simpa only [map_mul,map_inv,map_one,e.symm_apply_apply] using congrArg e.symm hz

private theorem fixed_index_mul_le {V : Type*} [Group V] [Finite V] (a b : MulAut V) :
    (a*b).fixedSubgroup.index ≤ a.fixedSubgroup.index*b.fixedSubgroup.index := by
  have hle : a.fixedSubgroup ⊓ b.fixedSubgroup ≤ (a*b).fixedSubgroup := by
    intro x hx
    rw [MulAut.mem_fixedSubgroup]
    change a (b x) = x
    rw [(MulAut.mem_fixedSubgroup b x).mp hx.2,(MulAut.mem_fixedSubgroup a x).mp hx.1]
  exact (Subgroup.index_antitone hle).trans index_inf_le

private theorem fixed_index_conj {V : Type*} [Group V] [Finite V] (a b : MulAut V) :
    (b*a*b⁻¹).fixedSubgroup.index = a.fixedSubgroup.index := by
  have he : MulAut.congr b a = b*a*b⁻¹ := by ext x; rfl
  have hc := Nat.card_congr (MulAut.fixedSubgroupCongr b a).toEquiv
  rw [he] at hc
  have h1 := a.fixedSubgroup.index_mul_card
  have h2 := (b*a*b⁻¹).fixedSubgroup.index_mul_card
  rw [←hc] at h2
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (h2.trans h1.symm)

/-- A binary Suzuki involution has fixed index at least four on any faithful two-group action. -/
theorem binary_suzuki_involution_fixed_index_ge {V : Type*} [Group V] [Finite V]
    (hV : IsPGroup 2 V) (f : SuzukiMatrixGroup 0 →* MulAut V) (hf : Function.Injective f)
    (t : SuzukiMatrixGroup 0) (ht : t^2 = 1) (hne : t ≠ 1) :
    4 ≤ (f t).fixedSubgroup.index := by
  obtain ⟨x,hx,hn⟩ := binary_suzuki_involution_commutator t ht hne
  have hlo := quintic_fixed_index_ge hV (f (t*x*t⁻¹*x⁻¹))
    (by rw [←map_pow,hx,map_one]) (fun he => hn (hf (he.trans (map_one f).symm)))
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using ht)
  have hh := fixed_index_mul_le (f t) (f x*f t*(f x)⁻¹)
  rw [fixed_index_conj] at hh
  have he : f (t*x*t⁻¹*x⁻¹) = f t*(f x*f t*(f x)⁻¹) := by
    simp only [htinv,map_mul,map_inv,mul_assoc]
  rw [he] at hlo
  nlinarith

/-- An order-four binary Suzuki actor has fixed index at least eight on a faithful binary module. -/
theorem binary_suzuki_four_fixed_index_ge {V : Type*} [Group V] [Finite V]
    [IsElementaryAbelian 2 V] (f : SuzukiMatrixGroup 0 →* MulAut V)
    (hf : Function.Injective f) (u : SuzukiMatrixGroup 0) (hu : orderOf u = 4) :
    8 ≤ (f u).fixedSubgroup.index := by
  have hu4 : u^4 = 1 := by simpa only [hu] using pow_orderOf_eq_one u
  have hu2 : u^2 ≠ 1 := by
    intro hz
    have hh := orderOf_dvd_of_pow_eq_one hz
    rw [hu] at hh
    norm_num at hh
  have hl := binary_suzuki_involution_fixed_index_ge (IsElementaryAbelian.isPGroup 2 V) f hf
    (u^2) (by simpa only [←pow_mul] using hu4) hu2
  let a := f u
  have ha4 : a^4 = 1 := by rw [←map_pow,hu4,map_one]
  have hane : a ≠ 1 := by
    intro he
    have hh : u = 1 := hf (he.trans (map_one f).symm)
    rw [hh,orderOf_one] at hu
    norm_num at hu
  have hlt := MulAut.fixed_card_lt_square_fixed_card_of_fourth_power_eq_one a ha4 hane
  have hfix (b : MulAut V) : FixedPoints.subgroup (zpowers b) V = b.fixedSubgroup := by
    ext v
    exact (MulAut.mem_fixed_zpowers_iff b v).trans (MulAut.mem_fixedSubgroup b v).symm
  rw [hfix,hfix] at hlt
  rw [map_pow] at hl
  change 4 ≤ (a^2).fixedSubgroup.index at hl
  have h1 := a.fixedSubgroup.index_mul_card
  have h2 := (a^2).fixedSubgroup.index_mul_card
  have hi : 4 < a.fixedSubgroup.index := by
    have hp : 0 < Nat.card a.fixedSubgroup := Nat.card_pos
    nlinarith
  obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 V).index a.fixedSubgroup
  have hn3 : 3 ≤ n := by
    by_contra hz
    have hh := Nat.pow_le_pow_right (by decide : 0 < 2) (show n ≤ 2 by omega)
    rw [hn] at hi
    norm_num at hh
    omega
  change 8 ≤ a.fixedSubgroup.index
  rw [hn]
  exact Nat.pow_le_pow_right (by decide : 0 < 2) hn3

/-- A surjective equivariant homomorphism cannot increase a fixed index. -/
theorem fixed_index_le_of_surjective {V W : Type*} [Group V] [Group W] [Finite V]
    (a : MulAut V) (b : MulAut W) (f : V →* W) (hf : Function.Surjective f)
    (he : ∀ v, f (a v) = b (f v)) : b.fixedSubgroup.index ≤ a.fixedSubgroup.index := by
  have hle : a.fixedSubgroup ≤ b.fixedSubgroup.comap f := by
    intro v hv
    apply (MulAut.mem_fixedSubgroup _ _).mpr
    rw [←he,(MulAut.mem_fixedSubgroup _ _).mp hv]
  rw [←b.fixedSubgroup.index_comap_of_surjective hf]
  exact Subgroup.index_antitone hle

/-- Equivariant multiplicative equivalences preserve the literal fixed index. -/
theorem fixed_index_eq_of_equivariant {V W : Type*} [Group V] [Group W] [Finite V] [Finite W]
    (a : MulAut V) (b : MulAut W) (e : V ≃* W)
    (he : ∀ v, e (a v) = b (e v)) : a.fixedSubgroup.index = b.fixedSubgroup.index := by
  apply le_antisymm
  · apply fixed_index_le_of_surjective b a e.symm.toMonoidHom e.symm.surjective
    intro w
    apply e.injective
    change e (e.symm (b w)) = e (a (e.symm w))
    rw [e.apply_symm_apply,he,e.apply_symm_apply]
  · exact fixed_index_le_of_surjective a b e.toMonoidHom e.surjective he

/-- Multiply lower fixed-index bounds through an arbitrary characteristic kernel. -/
theorem fixed_card_mul_indices_le {V : Type*} [Group V] [Finite V]
    (N : Subgroup V) [N.Characteristic] (a : MulAut V) (k l : ℕ)
    (hk : k ≤ (quotientAut N a).fixedSubgroup.index)
    (hl : l ≤ (MulAut.characteristic N a).fixedSubgroup.index) :
    Nat.card a.fixedSubgroup*(k*l) ≤ Nat.card V := by
  let b := quotientAut N a
  let c := MulAut.characteristic N a
  have hfix := fixed_card_le_quotient_mul N a
  calc
    Nat.card a.fixedSubgroup*(k*l) ≤ Nat.card a.fixedSubgroup*
        (b.fixedSubgroup.index*c.fixedSubgroup.index) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul hk hl)
    _ ≤ (Nat.card b.fixedSubgroup*Nat.card c.fixedSubgroup)*
        (b.fixedSubgroup.index*c.fixedSubgroup.index) := Nat.mul_le_mul_right _ hfix
    _ = (Nat.card b.fixedSubgroup*b.fixedSubgroup.index)*
        (Nat.card c.fixedSubgroup*c.fixedSubgroup.index) := by ring
    _ = Nat.card (V ⧸ N)*Nat.card N := by rw [card_mul_index,card_mul_index]
    _ = Nat.card V := N.index_mul_card

open RootCoordinates HexagonStructure
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) (i : Fin 2)
  (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* SuzukiMatrixGroup 0)
  (hB : (quotientBorel Q i).map μ.toMonoidHom =
    normalizer (SuzukiRootSubgroup 0 : Set (SuzukiMatrixGroup 0)))

/-- At trivial denominator the effective source action is exactly the Frattini action. -/
theorem section_frattini_fixed_index (d : RootSection Q split i) (hd : d.denominator = ⊥)
    (r : rankOne Q split i) :
    (quotientAut (frattini d.numerator) (d.numeratorAction r)).fixedSubgroup.index =
      (d.effectiveAction r).fixedSubgroup.index := by
  have he : d.effectiveDenominator = frattini d.numerator := by
    rw [d.effectiveDenominator_eq,hd,sup_bot_eq]
  let e : d.EffectiveCarrier ≃* (d.numerator ⧸ frattini d.numerator) :=
    QuotientGroup.quotientMulEquivOfEq he
  symm
  apply fixed_index_eq_of_equivariant _ _ e
  intro v
  obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective d.effectiveDenominator v
  change e (d.effectiveAction r (QuotientGroup.mk x)) = _
  rw [d.effectiveAction_mk]
  change QuotientGroup.mk' (frattini d.numerator) (d.numeratorAction r x) =
    quotientAut (frattini d.numerator) (d.numeratorAction r)
      (QuotientGroup.mk' (frattini d.numerator) x)
  exact (quotientAut_apply_mk _ _ _).symm

include hB in
/-- Every faithful binary Suzuki source section has the two required fixed-index bounds. -/
theorem binary_section_fixed_indices (d : RootSection Q split i)
    (hd : d.denominator = ⊥) (hf : Function.Injective d.effectiveAction)
    (r : rankOne Q split i) (hr : orderOf r = 4) :
    8 ≤ (quotientAut (frattini d.numerator) (d.numeratorAction r)).fixedSubgroup.index ∧
      4 ≤ (quotientAut (frattini d.numerator) (d.numeratorAction (r^2))).fixedSubgroup.index := by
  let e := suzukiActorEquiv Q split i 0 μ hB
  let f := d.effectiveAction.comp e.symm.toMonoidHom
  have hfi : Function.Injective f := hf.comp e.symm.injective
  have hr4 : orderOf (e r) = 4 := (e.orderOf_eq r).trans hr
  have hfour := binary_suzuki_four_fixed_index_ge f hfi (e r) hr4
  have hpow : (e r)^4 = 1 := by simpa only [hr4] using pow_orderOf_eq_one (e r)
  have hsqne : (e r)^2 ≠ 1 := by
    intro hz
    have hh := orderOf_dvd_of_pow_eq_one hz
    rw [hr4] at hh
    norm_num at hh
  have htwo := binary_suzuki_involution_fixed_index_ge (IsElementaryAbelian.isPGroup 2 d.EffectiveCarrier) f hfi
    ((e r)^2) (by simpa only [←pow_mul] using hpow) hsqne
  rw [section_frattini_fixed_index Q split i d hd r,
    section_frattini_fixed_index Q split i d hd (r^2)]
  constructor
  · simpa only [f,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,e.symm_apply_apply] using hfour
  · simpa only [f,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,←map_pow,e.symm_apply_apply] using htwo

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
