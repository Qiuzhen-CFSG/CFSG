module
public import Theory.GroupTheory.QuaternionDiagonalMembership
public import Theory.GroupTheory.SubgroupConjugation
public import Theory.GroupTheory.QuaternionCentralProductIntrinsic
public import Theory.GroupTheory.QuaternionFixedEight
public import Theory.GroupTheory.QuaternionCentralProductEightPoint
public import Theory.GroupTheory.QuaternionCentralProductResidualRecognition.Factors.Action

/-!
# Invariant quaternion diagonals and their point stabilizers

Let a cubic element preserve two commuting quaternion factors, and let an
involution interchange the factors while inverting the cubic modulo their
central product. An involution inverting the quaternion cubic action selects
two distinct actual elementary subgroups of order eight normalized by all
these actors. Each automizer contains the full point stabilizer S₄.

The elementary subgroup is self-centralizing in the quaternion core. An
outside element of the two-extension cannot centralize it: the inversion
relation would put the square of a nontrivial cubic automorphism in the
image of a group of exponent four. Thus the two-action has order eight.
The actual cubic has order three on the elementary subgroup, and all actors
fix the shared central involution, giving the point stabilizer of order 24.

This is the local diagonal construction needed in the full Omega branch of
Aschbacher--Smith 15.1.11, printed p.1089. The source application must still
construct the marked cubic and swapping involution and supply a plane actor.
Unlike the moved-diagonal selection in Stellmacher (9.1), this construction
requires no second factor swap. Multiplying the quaternion inverter by the
cubic gives the second diagonal; equality of diagonals would make the cubic
an inner automorphism of order dividing four, contradicting its order three.
-/

open scoped Pointwise
namespace Subgroup
open GLS3.Chapter5.SchurPresentation
private abbrev Q := QuaternionGroup 2
private def inverterMap (a b : Q) : Q → Q
  | .a i => a ^ i.val
  | .xa i => b * a ^ i.val
private theorem inverter_table : ∃ a b : Q,
    (∀ x, inverterMap a b (inverterMap a b x) = x) ∧
    (∀ x y, inverterMap a b (x*y) = inverterMap a b x * inverterMap a b y) ∧
    ∀ x, inverterMap a b (q8Cycle x) = q8Cycle (q8Cycle (inverterMap a b x)) := by
  decide +kernel
private noncomputable def standardInverter : MulAut Q where
  toFun := inverterMap inverter_table.choose inverter_table.choose_spec.choose
  invFun := inverterMap inverter_table.choose inverter_table.choose_spec.choose
  left_inv := inverter_table.choose_spec.choose_spec.1
  right_inv := inverter_table.choose_spec.choose_spec.1
  map_mul' := inverter_table.choose_spec.choose_spec.2.1
private theorem standardInverter_square : standardInverter ^ 2 = 1 := by
  ext x
  exact inverter_table.choose_spec.choose_spec.1 x
private theorem standardInverter_inverts : standardInverter * q8Cycle = q8Cycle ^ 2 * standardInverter := by
  ext x
  exact inverter_table.choose_spec.choose_spec.2.2 x

private theorem exists_inverter {B : Type*} [Group B]
    (model : B ≃* Q) (a : MulAut B) (ha : a^3=1) (hne : a ≠ 1) :
    ∃ f : MulAut B, f^2=1 ∧ ∀x, f (a x)=a (a (f x)) := by
  let ψ := MulAut.congr model
  obtain ⟨e,he⟩ := QuaternionCubicAction.exists_coordinates (ψ a)
    (by rw [←map_pow,ha,map_one]) (fun h => hne (ψ.injective (h.trans ψ.map_one.symm)))
  let φ := ψ.trans (MulAut.congr e)
  have hφa : φ a = q8Cycle := he
  let f := φ.symm standardInverter
  have hφf : φ f = standardInverter := φ.apply_symm_apply _
  refine ⟨f, ?_, ?_⟩
  · apply φ.injective
    rw [map_pow,hφf,standardInverter_square,map_one]
  · have hh : f*a=a^2*f := φ.injective (by
      rw [map_mul,map_mul,map_pow,hφf,hφa]
      exact standardInverter_inverts)
    intro x
    exact DFunLike.congr_fun hh x

private theorem normalizes_diagonal_of_generators
    {G : Type*} [Group G] [Finite G] (B C : Subgroup G) (θ : B ≃* C)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b*c=c*b) (u : G)
    (hI : ∀ z ∈ B⊓C, u*z*u⁻¹ ∈ B⊓C)
    (hD : ∀ z : B, u*((z:G)*(θ z:G))*u⁻¹ ∈ quaternionDiagonal B C θ hcomm) :
    u ∈ normalizer (quaternionDiagonal B C θ hcomm : Set G) := by
  have hmap : (quaternionDiagonal B C θ hcomm).map (MulAut.conj u).toMonoidHom ≤
      quaternionDiagonal B C θ hcomm := by
    change ((quaternionDiagonalHom B C θ hcomm).range ⊔ (B⊓C)).map _ ≤ _
    rw [map_sup]
    apply sup_le
    · intro x hx
      obtain ⟨y,hy,rfl⟩ := hx
      obtain ⟨z,rfl⟩ := hy
      exact hD z
    · intro x hx
      obtain ⟨z,hz,rfl⟩ := hx
      exact (show B⊓C ≤ quaternionDiagonal B C θ hcomm from le_sup_right) (hI z hz)
  apply mem_normalizer_fintype
  intro x hx
  exact hmap ⟨x,hx,rfl⟩

private noncomputable def swappingEquiv {G : Type*} [Group G] (B C : Subgroup G)
    (s : G) (hsB : B.conjBy s = C) : B ≃* C :=
  (B.equivMapOfInjective (MulAut.conj s).toMonoidHom
    (MulAut.conj s).injective).trans (MulEquiv.subgroupCongr hsB)

private theorem diagonal_inverter_data
    {G : Type*} [Group G] [Finite G]
    (B C : Subgroup G) (model : B ≃* QuaternionGroup 2)
    (hinter : Nat.card (B ⊓ C : Subgroup G) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b*c=c*b)
    (g s : G) (hg3 : g^3=1) (hs2 : s^2=1)
    (hgB : g ∈ normalizer (B : Set G)) (hgC : g ∈ normalizer (C : Set G))
    (hsB : B.conjBy s = C) (hsg : s*g*s⁻¹*g ∈ B⊔C)
    (f : MulAut B) (hf2 : f^2=1)
    (hfa : ∀x, f (B.normalizerMonoidHom ⟨g,hgB⟩ x) =
      B.normalizerMonoidHom ⟨g,hgB⟩ (B.normalizerMonoidHom ⟨g,hgB⟩ (f x))) :
    ∃ θ : B ≃* C, ∃ E : Subgroup G,
      θ=f.trans (swappingEquiv B C s hsB) ∧
      E = quaternionDiagonal B C θ hcomm ∧ IsElementaryAbelian 2 E ∧ Nat.card E=8 ∧
      B⊓C ≤ E ∧ E ≤ B⊔C ∧ B⊔C ≤ normalizer (E : Set G) ∧
      g ∈ normalizer (E : Set G) ∧ s ∈ normalizer (E : Set G) := by
  have hsC : C.conjBy s = B := by
    rw [← hsB, conjBy_conjBy, ← pow_two, hs2, conjBy_one]
  let a : MulAut B := B.normalizerMonoidHom ⟨g,hgB⟩
  have ha : a^3=1 := by
    change (B.normalizerMonoidHom ⟨g,hgB⟩)^3=1
    rw [←map_pow]
    have hh : (⟨g,hgB⟩ : normalizer (B : Set G))^3=1 := Subtype.ext hg3
    rw [hh,map_one]
  have ha2 : a^2=a⁻¹ := eq_inv_of_mul_eq_one_left (by simpa [pow_succ] using ha)
  let φ : B ≃* C := (B.equivMapOfInjective (MulAut.conj s).toMonoidHom
    (MulAut.conj s).injective).trans (MulEquiv.subgroupCongr hsB)
  have hφ (z : B) : (φ z : G) = s*(z:G)*s⁻¹ := rfl
  let θ : B ≃* C := f.trans φ
  let U := quaternionDiagonal B C θ hcomm
  obtain ⟨hUelem,hUcard,hIU,hUV⟩ := quaternion_diagonal_elementary_eight B C model θ hinter hcomm
  have hsI (z : G) (hz : z ∈ B⊓C) : s*z*s⁻¹ ∈ B⊓C := by
    constructor
    · rw [← hsC]
      exact ⟨z,hz.2,rfl⟩
    · rw [← hsB]
      exact ⟨z,hz.1,rfl⟩
  have hgI (z : G) (hz : z ∈ B⊓C) : g*z*g⁻¹ ∈ B⊓C :=
    ⟨(mem_normalizer_iff.mp hgB z).mp hz.1, (mem_normalizer_iff.mp hgC z).mp hz.2⟩
  have hainv (z : B) : (a⁻¹ z : G) = g⁻¹*(z:G)*g := by
    change ((B.normalizerMonoidHom ⟨g,hgB⟩)⁻¹ z : G) = _
    rw [← map_inv]
    change g⁻¹*(z:G)*(g⁻¹)⁻¹ = _
    rw [inv_inv]
  have hsinv : s⁻¹=s := inv_eq_of_mul_eq_one_left (by simpa [pow_two] using hs2)
  have hsfφ (z : B) : s*(φ z:G)*s⁻¹=(z:G) := by
    rw [hφ]
    calc
      s*(s*(z:G)*s⁻¹)*s⁻¹ = (s*s)*(z:G)*(s*s)⁻¹ := by group
      _ = (z:G) := by rw [← pow_two, hs2]; simp
  have hCg (z : B) : (φ (a⁻¹ z):G)⁻¹ * (g*(φ z:G)*g⁻¹) ∈ B⊓C := by
    have hh := factor_central_difference_of_mem_sup B C model hinter hcomm
      (s*g*s⁻¹*g) hsg (a⁻¹ z) (a⁻¹ z).property
    have hhS := hsI _ hh
    convert hhS using 1
    rw [hφ, hφ, hainv]
    group
    simp only [zpow_neg_one, hsinv,
      show s ^ (-2 : ℤ) = 1 by simp [zpow_neg, hs2], mul_one]
  refine ⟨θ,U,rfl,rfl,hUelem,hUcard,hIU,hUV,?_,?_,?_⟩
  · exact sup_le_normalizer_quaternionDiagonal B C model θ hinter hcomm
  · apply normalizes_diagonal_of_generators B C θ hcomm g hgI
    intro z
    let az : B := a z
    let gz : C := C.normalizerMonoidHom ⟨g,hgC⟩ (θ z)
    have hprod : g*((z:G)*(θ z:G))*g⁻¹ = (az:G)*(gz:G) := by
      change _ = (g*(z:G)*g⁻¹)*(g*(θ z:G)*g⁻¹)
      group
    rw [hprod]
    apply (mem_quaternionDiagonal_mul_iff B C model θ hinter hcomm az gz).mpr
    change (φ (f (a z)):G)⁻¹ * (g*(φ (f z):G)*g⁻¹) ∈ B⊓C
    have hfa' : f (a z) = a⁻¹ (f z) := by
      simpa only [← ha2, pow_two, MulAut.mul_apply] using hfa z
    rw [hfa']
    exact hCg (f z)
  · apply normalizes_diagonal_of_generators B C θ hcomm s hsI
    intro z
    have hfpoint : f (f z)=z := by simpa [pow_two] using DFunLike.congr_fun hf2 z
    have hprod : s*((z:G)*(θ z:G))*s⁻¹ = (f z:G)*(θ (f z):G) := by
      change s*((z:G)*(φ (f z):G))*s⁻¹ = (f z:G)*(φ (f (f z)):G)
      rw [hfpoint]
      calc
        s*((z:G)*(φ (f z):G))*s⁻¹ = (s*(z:G)*s⁻¹)*(s*(φ (f z):G)*s⁻¹) := by group
        _ = (φ z:G)*(f z:G) := by rw [← hφ, hsfφ]
        _ = (f z:G)*(φ z:G) := (hcomm (f z) (f z).property (φ z) (φ z).property).symm
    rw [hprod]
    exact (show (quaternionDiagonalHom B C θ hcomm).range ≤ U from le_sup_left) ⟨f z,rfl⟩

/-- An inverting involutory factor swap and a cubic preserve an actual quaternion diagonal. -/
public theorem exists_quaternion_diagonal_of_inverting_swap
    {G : Type*} [Group G] [Finite G]
    (B C : Subgroup G) (model : B ≃* QuaternionGroup 2)
    (hinter : Nat.card (B ⊓ C : Subgroup G) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b*c=c*b)
    (g s : G) (hg3 : g^3=1) (hs2 : s^2=1)
    (hgB : g ∈ normalizer (B : Set G)) (hgC : g ∈ normalizer (C : Set G))
    (hgne : ∃ b : B, g*(b:G)*g⁻¹ ≠ b)
    (hsB : B.conjBy s = C) (hsg : s*g*s⁻¹*g ∈ B⊔C) :
    ∃ θ : B ≃* C, ∃ E : Subgroup G,
      E = quaternionDiagonal B C θ hcomm ∧ IsElementaryAbelian 2 E ∧ Nat.card E=8 ∧
      B⊓C ≤ E ∧ E ≤ B⊔C ∧ B⊔C ≤ normalizer (E : Set G) ∧
      g ∈ normalizer (E : Set G) ∧ s ∈ normalizer (E : Set G) := by
  let a : MulAut B := B.normalizerMonoidHom ⟨g,hgB⟩
  have ha : a^3=1 := by
    change (B.normalizerMonoidHom ⟨g,hgB⟩)^3=1
    rw [←map_pow]
    have hh : (⟨g,hgB⟩ : normalizer (B : Set G))^3=1 := Subtype.ext hg3
    rw [hh,map_one]
  have hane : a ≠ 1 := by
    intro hh
    obtain ⟨x,hx⟩ := hgne
    exact hx (congrArg Subtype.val (DFunLike.congr_fun hh x))
  obtain ⟨f,hf2,hfa⟩ := exists_inverter model a ha hane
  obtain ⟨θ,E,_,h⟩ := diagonal_inverter_data B C model hinter hcomm g s hg3 hs2 hgB hgC
    hsB hsg f hf2 hfa
  exact ⟨θ,E,h⟩

/-- A nontrivial cubic action on one quaternion factor remains nontrivial on every normalized eight. -/
public theorem quaternion_cubic_restriction_order_three
    {G : Type*} [Group G] [Finite G] (B C E : Subgroup G)
    (model : B ≃* QuaternionGroup 2) (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hi : Nat.card (B ⊓ C : Subgroup G)=2)
    (hc : ∀ b∈B, ∀c∈C, b*c=c*b)
    [IsElementaryAbelian 2 E] (hE : Nat.card E=8) (hEQ : E≤B⊔C)
    (g : normalizer (E : Set G)) (hg3 : (g:G)^3=1)
    (hgB : (g:G) ∈ normalizer (B : Set G))
    (hgC : (g:G) ∈ normalizer (C : Set G))
    (hne : ∃ b:B, (g:G)*(b:G)*(g:G)⁻¹ ≠ b) :
    orderOf (E.normalizerMonoidHom g)=3 := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hn3 : g^3=1 := Subtype.ext hg3
  apply orderOf_eq_prime (by rw [←map_pow,hn3,map_one])
  intro he
  have hfix : (g:G) ∈ centralizer (E : Set G) := by
    have hk : g ∈ E.normalizerMonoidHom.ker := he
    rwa [normalizerMonoidHom_ker] at hk
  have hb8 : Nat.card B=8 := by
    rw [Nat.card_congr model.toEquiv,Nat.card_eq_fintype_card,QuaternionGroup.card]
  have hc8 : Nat.card C=8 := by
    rw [Nat.card_congr hC.some.toEquiv,Nat.card_eq_fintype_card,QuaternionGroup.card]
  have hQcard : Nat.card (B⊔C:Subgroup G)=32 := by
    have h := card_mul_eq_card_inf_mul_card_sup_of_normalizes B C
      ((show C≤centralizer (B:Set G) from fun c hc' b hb => hc b hb c hc').trans
        (centralizer_le_normalizer _))
    rw [hb8,hc8,hi] at h
    omega
  obtain ⟨b,hb,hact⟩ := factor_inner_of_fixed_eight B C E ⟨model⟩ hC hc
    hQcard hEQ hE (fun x hx => elemPow_eq_one_of_isElementaryAbelian x hx)
    (g:G) hgB hgC (fun x hx => (hfix x hx).symm)
  let a : MulAut B := B.normalizerMonoidHom ⟨g,hgB⟩
  have ha3 : a^3=1 := by
    rw [show a=B.normalizerMonoidHom ⟨g,hgB⟩ from rfl,←map_pow]
    rw [show (⟨(g:G),hgB⟩ : normalizer (B:Set G))^3=1 from Subtype.ext hg3,map_one]
  have ha : a = MulAut.conj (⟨b,hb⟩:B) := by
    ext x
    exact hact x x.property
  have hb4 : (⟨b,hb⟩:B)^4=1 := model.injective (by
    rw [map_pow,map_one]
    exact (by decide +kernel : ∀q:QuaternionGroup 2, q^4=1) _)
  have ha4 : a^4=1 := by rw [ha,←map_pow,hb4,map_one]
  have ha1 : a=1 := by simpa only [show (4:ℕ)=3+1 from rfl,pow_succ,ha3,one_mul] using ha4
  obtain ⟨x,hx⟩ := hne
  exact hx (congrArg Subtype.val (DFunLike.congr_fun ha1 x))


private theorem mem_zpowers_involution {G : Type*} [Group G] (s : G)
    (hs : s^2=1) {y : G} (hy : y∈zpowers s) : y=1 ∨ y=s := by
  obtain ⟨n,rfl⟩ := mem_zpowers_iff.mp hy
  rw [zpow_eq_zpow_emod' n hs]
  have hm : n%2=0 ∨ n%2=1 := by omega
  rcases hm with hm|hm <;> simp [hm]

private theorem centralizer_inverting_extension
    {G : Type*} [Group G] [Finite G] (Q E : Subgroup G)
    (hQE : Q≤normalizer (E:Set G))
    (hcent : Q⊓centralizer (E:Set G)=E)
    (hpow : ∀ x∈Q, x^4=1)
    (g s : normalizer (E:Set G)) (hg : orderOf (E.normalizerMonoidHom g)=3)
    (hgQ : (g:G)∈normalizer (Q:Set G)) (hsQ : (s:G)∈normalizer (Q:Set G))
    (hs2 : (s:G)^2=1) (hsg : (s:G)*g*(s:G)⁻¹*g ∈ Q) :
    (Q⊔zpowers (s:G))⊓centralizer (E:Set G)=E := by
  have hSN : Q⊔zpowers (s:G)≤normalizer (E:Set G) :=
    sup_le hQE (zpowers_le.mpr s.property)
  apply le_antisymm ?_ (le_inf ((show E≤Q from hcent ▸ inf_le_left).trans le_sup_left)
    (show E≤centralizer (E:Set G) from hcent.ge.trans inf_le_right))
  intro x hx
  have hp : x∈(Q:Set G)*(zpowers (s:G):Set G) := by
    rw [←coe_mul_of_right_le_normalizer_left Q (zpowers (s:G)) (zpowers_le.mpr hsQ)]
    exact hx.1
  obtain ⟨p,hp,y,hy,hxy⟩ := hp
  rcases mem_zpowers_involution (s:G) hs2 hy with rfl|rfl
  · apply hcent.le
    refine ⟨?_,hx.2⟩
    rw [←hxy]
    change p*1∈Q
    exact Q.mul_mem hp Q.one_mem
  · exfalso
    have hwQ : x*(g:G)*x⁻¹*g∈Q := by
      rw [←hxy]
      have hi : (g:G)⁻¹*p⁻¹*g∈Q := by
        have hh := (mem_normalizer_iff.mp ((normalizer (Q:Set G)).inv_mem hgQ) p⁻¹).mp
          (Q.inv_mem hp)
        simpa only [inv_inv] using hh
      convert Q.mul_mem (Q.mul_mem hp hsg) hi using 1; group
    let xn : normalizer (E:Set G) := ⟨x,hSN hx.1⟩
    let wn : normalizer (E:Set G) := xn*g*xn⁻¹*g
    have hx1 : E.normalizerMonoidHom xn=1 := by
      change xn∈E.normalizerMonoidHom.ker
      rw [normalizerMonoidHom_ker]
      exact hx.2
    have hw4 : wn^4=1 := Subtype.ext (hpow _ hwQ)
    have hwimage : E.normalizerMonoidHom wn=(E.normalizerMonoidHom g)^2 := by
      dsimp only [wn]
      rw [map_mul,map_mul,map_mul,map_inv,hx1,one_mul,inv_one,mul_one,pow_two]
    have h8 : (E.normalizerMonoidHom g)^8=1 := by
      rw [show (8:ℕ)=2*4 from rfl,pow_mul,←hwimage,←map_pow,hw4,map_one]
    have hh := orderOf_dvd_of_pow_eq_one h8
    rw [hg] at hh
    norm_num at hh

/-- Every elementary eight invariant under the quaternion core and marked S₃ actors has a full point image. -/
public theorem quaternion_eight_geometry_of_inverting_swap
    {G : Type*} [Group G] [Finite G]
    (B C E : Subgroup G) (model : B ≃* QuaternionGroup 2)
    (hC : Nonempty (C≃*QuaternionGroup 2))
    (hi : Nat.card (B⊓C:Subgroup G)=2)
    (hc : ∀b∈B,∀c∈C,b*c=c*b)
    [IsElementaryAbelian 2 E] (hEcard : Nat.card E=8) (hEQ : E≤B⊔C)
    (hQE : B⊔C≤normalizer (E:Set G))
    (g s:G) (hg3:g^3=1) (hs2:s^2=1)
    (hgB:g∈normalizer (B:Set G)) (hgC:g∈normalizer (C:Set G))
    (hgne:∃b:B,g*(b:G)*g⁻¹≠b)
    (hsB:B.conjBy s=C) (hsg:s*g*s⁻¹*g∈B⊔C)
    (hgE : g∈normalizer (E:Set G)) (hsE : s∈normalizer (E:Set G)) :
    ((B⊔C)⊔zpowers s)⊓centralizer (E:Set G)=E ∧
      Nat.card ((B⊔C)⊔zpowers s:Subgroup G)=64 ∧
      Nonempty (ElementaryEightPointImage E) := by
  have hcent : (B⊔C)⊓centralizer (E:Set G)=E :=
    inf_centralizer_elementary_eight_of_quaternion_factors B C E ⟨model⟩ hC hi hc hEcard hEQ
  have hgQ : g∈normalizer (B⊔C:Subgroup G) :=
    normalizer_inf_normalizer_le_normalizer_sup B C ⟨hgB,hgC⟩
  have hsC : C.conjBy s=B := by rw [←hsB,conjBy_conjBy,←pow_two,hs2,conjBy_one]
  have hsQ : s∈normalizer (B⊔C:Subgroup G) := by
    rw [mem_normalizer_iff_map_conj_eq,map_sup]
    change B.conjBy s⊔C.conjBy s=B⊔C
    rw [hsB,hsC,sup_comm]
  have hpow : ∀x∈B⊔C,x^4=1 := by
    intro x hx
    have hz := quaternion_central_product_square_mem_inf B C ⟨model⟩ hC hi hc x hx
    have hh := pow_card_eq_one' (x := (⟨x^2,hz⟩:(B⊓C:Subgroup G)))
    rw [hi] at hh
    simpa only [coe_pow,coe_one,←pow_mul] using congrArg Subtype.val hh
  have horder := quaternion_cubic_restriction_order_three B C E model hC hi hc
    hEcard hEQ ⟨g,hgE⟩ hg3 hgB hgC hgne
  have hcentral := centralizer_inverting_extension (B⊔C) E hQE hcent hpow
    ⟨g,hgE⟩ ⟨s,hsE⟩ horder hgQ hsQ hs2 hsg
  let S := (B⊔C)⊔zpowers s
  have hSN : S≤normalizer (E:Set G) := sup_le hQE (zpowers_le.mpr hsE)
  have hb8 : Nat.card B=8 := by
    rw [Nat.card_congr model.toEquiv,Nat.card_eq_fintype_card,QuaternionGroup.card]
  have hc8 : Nat.card C=8 := by
    rw [Nat.card_congr hC.some.toEquiv,Nat.card_eq_fintype_card,QuaternionGroup.card]
  have hQcard : Nat.card (B⊔C:Subgroup G)=32 := by
    have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes B C
      ((show C≤centralizer (B:Set G) from fun c hc' b hb => hc b hb c hc').trans
        (centralizer_le_normalizer _))
    rw [hb8,hc8,hi] at hh
    omega
  have hout : s∉B⊔C := by
    intro hs
    have hQB : B⊔C≤normalizer (B:Set G) := sup_le B.le_normalizer
      ((show C≤centralizer (B:Set G) from fun c hc' b hb => hc b hb c hc').trans
        (centralizer_le_normalizer _))
    have hBB : B.conjBy s=B := mem_normalizer_iff_map_conj_eq.mp (hQB hs)
    have hBC := hBB.symm.trans hsB
    rw [←hBC,inf_idem,hb8] at hi
    omega
  have hsne : s≠1 := fun he => hout (he ▸ one_mem _)
  have hsorder : orderOf s=2 := by
    let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime hs2 hsne
  have hdisj : Disjoint (B⊔C) (zpowers s) := by
    rw [disjoint_iff]
    apply le_antisymm ?_ bot_le
    intro x hx
    rcases mem_zpowers_involution s hs2 hx.2 with rfl|rfl
    · exact one_mem _
    · exact (hout hx.1).elim
  have hScard : Nat.card S=64 := by
    change Nat.card ((B⊔C)⊔zpowers s:Subgroup G)=64
    rw [card_sup_eq_mul_of_normalizes_of_disjoint _ _ (zpowers_le.mpr hsQ) hdisj,
      hQcard,Nat.card_zpowers,hsorder]
  refine ⟨hcentral,hScard,?_⟩
  exact quaternion_central_product_point_image_of_cubic B C E S ⟨model⟩ hC hi hc
    hEcard hEQ hScard le_sup_left hSN hcentral ⟨g,hgE⟩ hgQ horder
/-- Every elementary eight invariant under the quaternion core and marked S₃ actors has a full point image. -/
public theorem quaternion_eight_point_image_of_inverting_swap
    {G : Type*} [Group G] [Finite G]
    (B C E : Subgroup G) (model : B ≃* QuaternionGroup 2)
    (hC : Nonempty (C≃*QuaternionGroup 2))
    (hi : Nat.card (B⊓C:Subgroup G)=2)
    (hc : ∀b∈B,∀c∈C,b*c=c*b)
    [IsElementaryAbelian 2 E] (hEcard : Nat.card E=8) (hEQ : E≤B⊔C)
    (hQE : B⊔C≤normalizer (E:Set G))
    (g s:G) (hg3:g^3=1) (hs2:s^2=1)
    (hgB:g∈normalizer (B:Set G)) (hgC:g∈normalizer (C:Set G))
    (hgne:∃b:B,g*(b:G)*g⁻¹≠b)
    (hsB:B.conjBy s=C) (hsg:s*g*s⁻¹*g∈B⊔C)
    (hgE : g∈normalizer (E:Set G)) (hsE : s∈normalizer (E:Set G)) :
    Nonempty (ElementaryEightPointImage E) := by
  exact (quaternion_eight_geometry_of_inverting_swap B C E model hC hi hc hEcard hEQ hQE
    g s hg3 hs2 hgB hgC hgne hsB hsg hgE hsE).2.2

/-- Construct the elementary eight together with its actual full point-stabilizer image. -/
public theorem exists_quaternion_eight_point_image_of_inverting_swap
    {G : Type*} [Group G] [Finite G]
    (B C : Subgroup G) (model : B ≃* QuaternionGroup 2)
    (hi : Nat.card (B⊓C:Subgroup G)=2)
    (hc : ∀b∈B,∀c∈C,b*c=c*b)
    (g s:G) (hg3:g^3=1) (hs2:s^2=1)
    (hgB:g∈normalizer (B:Set G)) (hgC:g∈normalizer (C:Set G))
    (hgne:∃b:B,g*(b:G)*g⁻¹≠b)
    (hsB:B.conjBy s=C) (hsg:s*g*s⁻¹*g∈B⊔C) :
    ∃ E:Subgroup G, IsElementaryAbelian 2 E ∧ Nat.card E=8 ∧ E≤B⊔C ∧
      (B⊔C)⊔zpowers s≤normalizer (E:Set G) ∧
      g∈normalizer (E:Set G) ∧ Nonempty (ElementaryEightPointImage E) := by
  obtain ⟨θ,E,hEeq,hElem,hEcard,hIE,hEQ,hQE,hgE,hsE⟩ :=
    exists_quaternion_diagonal_of_inverting_swap B C model hi hc g s hg3 hs2 hgB hgC hgne hsB hsg
  let := hElem
  have hC : Nonempty (C≃*QuaternionGroup 2) := ⟨θ.symm.trans model⟩
  exact ⟨E,hElem,hEcard,hEQ,sup_le hQE (zpowers_le.mpr hsE),hgE,
    quaternion_eight_point_image_of_inverting_swap B C E model hC hi hc hEcard hEQ hQE
      g s hg3 hs2 hgB hgC hgne hsB hsg hgE hsE⟩

private theorem diagonal_ne_cubic_rotate
    {G : Type*} [Group G] [Finite G]
    (B C : Subgroup G) (model : B≃*QuaternionGroup 2)
    (hi : Nat.card (B⊓C:Subgroup G)=2)
    (hc : ∀b∈B,∀c∈C,b*c=c*b)
    (φ : B≃*C) (a f : MulAut B) (ha : a^3=1) (hne : a≠1) :
    quaternionDiagonal B C (f.trans φ) hc ≠
      quaternionDiagonal B C ((a*f).trans φ) hc := by
  intro heq
  have hd : ∀x:B, x⁻¹*a x∈center B := by
    intro x
    let b := f.symm x
    have hm : (b:G)*(φ (f b):G)∈quaternionDiagonal B C (f.trans φ) hc :=
      (show (quaternionDiagonalHom B C (f.trans φ) hc).range≤_ from le_sup_left) ⟨b,rfl⟩
    rw [heq] at hm
    have hh := (mem_quaternionDiagonal_mul_iff B C model ((a*f).trans φ) hi hc
      b (φ (f b))).mp hm
    have hI : ((φ (a x)):G)⁻¹*(φ x:G)∈B⊓C := by
      simpa only [MulEquiv.trans_apply,MulAut.mul_apply,b,f.apply_symm_apply] using hh
    have hcen : (a x)⁻¹*x∈center B := by
      apply mem_center_iff.mpr
      intro y
      apply φ.injective
      apply Subtype.ext
      simpa only [map_mul,map_inv,coe_mul,coe_inv] using
        (hc _ hI.1 (φ y) (φ y).property).symm
    have hinv := (center B).inv_mem hcen
    simpa only [mul_inv_rev,inv_inv] using hinv
  obtain ⟨b,hb⟩ := QuaternionGroup.exists_conj_of_central_difference_of_equiv model a hd
  have hb4 : b^4=1 := model.injective (by
    rw [map_pow,map_one]
    exact (by decide +kernel : ∀q:QuaternionGroup 2,q^4=1) _)
  have ha4 : a^4=1 := by rw [hb,←map_pow,hb4,map_one]
  apply hne
  simpa only [show (4:ℕ)=3+1 from rfl,pow_succ,ha,one_mul] using ha4

/-- Two distinct invariant eights with actual point-stabilizer images are available.
This leaves at most one exceptional direction when the Omega Sylow four is marked. -/
public theorem exists_two_quaternion_eights_point_image_of_inverting_swap
    {G : Type*} [Group G] [Finite G]
    (B C : Subgroup G) (model : B ≃* QuaternionGroup 2)
    (hi : Nat.card (B⊓C:Subgroup G)=2)
    (hc : ∀b∈B,∀c∈C,b*c=c*b)
    (g s:G) (hg3:g^3=1) (hs2:s^2=1)
    (hgB:g∈normalizer (B:Set G)) (hgC:g∈normalizer (C:Set G))
    (hgne:∃b:B,g*(b:G)*g⁻¹≠b)
    (hsB:B.conjBy s=C) (hsg:s*g*s⁻¹*g∈B⊔C) :
    ∃ E F:Subgroup G, E≠F ∧
      (∀ U∈({E,F}:Set (Subgroup G)), IsElementaryAbelian 2 U ∧ Nat.card U=8 ∧
        U≤B⊔C ∧ (B⊔C)⊔zpowers s≤normalizer (U:Set G) ∧
        g∈normalizer (U:Set G) ∧ Nonempty (ElementaryEightPointImage U)) := by
  let a : MulAut B := B.normalizerMonoidHom ⟨g,hgB⟩
  have ha : a^3=1 := by
    change (B.normalizerMonoidHom ⟨g,hgB⟩)^3=1
    rw [←map_pow]
    have hh : (⟨g,hgB⟩ : normalizer (B : Set G))^3=1 := Subtype.ext hg3
    rw [hh,map_one]
  have hane : a≠1 := by
    intro he
    obtain ⟨x,hx⟩ := hgne
    exact hx (congrArg Subtype.val (DFunLike.congr_fun he x))
  obtain ⟨f,hf2,hfa⟩ := exists_inverter model a ha hane
  have hanti : f*a=a^2*f := by
    apply MulEquiv.ext
    intro x
    exact hfa x
  have ha2 : a^2=a⁻¹ := eq_inv_of_mul_eq_one_left (by simpa [pow_succ] using ha)
  have haf2 : (a*f)^2=1 := by
    calc
      (a*f)^2=a*(f*a)*f := by rw [pow_two]; group
      _=a*(a⁻¹*f)*f := by rw [hanti,ha2]
      _=(a*a⁻¹)*(f*f) := by group
      _=1 := by rw [mul_inv_cancel,←pow_two,hf2,one_mul]
  have hafanti : ∀x, (a*f) (a x)=a (a ((a*f) x)) := by
    have hh : (a*f)*a=a^2*(a*f) := by
      rw [mul_assoc,hanti]
      group
    exact fun x => DFunLike.congr_fun hh x
  obtain ⟨θ,E,hθ,hEeq,hEe,hEc,hIE,hEQ,hQE,hgE,hsE⟩ :=
    diagonal_inverter_data B C model hi hc g s hg3 hs2 hgB hgC hsB hsg f hf2 hfa
  obtain ⟨θ',F,hθ',hFeq,hFe,hFc,hIF,hFQ,hQF,hgF,hsF⟩ :=
    diagonal_inverter_data B C model hi hc g s hg3 hs2 hgB hgC hsB hsg (a*f) haf2 hafanti
  have hC : Nonempty (C≃*QuaternionGroup 2) := ⟨θ.symm.trans model⟩
  refine ⟨E,F,?_,?_⟩
  · rw [hEeq,hFeq,hθ,hθ']
    exact diagonal_ne_cubic_rotate B C model hi hc (swappingEquiv B C s hsB) a f ha hane
  · intro U hU
    rcases Set.mem_insert_iff.mp hU with hU|hU
    · subst U
      let := hEe
      exact ⟨hEe,hEc,hEQ,sup_le hQE (zpowers_le.mpr hsE),hgE,
        quaternion_eight_point_image_of_inverting_swap B C E model hC hi hc hEc hEQ hQE
          g s hg3 hs2 hgB hgC hgne hsB hsg hgE hsE⟩
    · have hu : U=F := Set.mem_singleton_iff.mp hU
      subst U
      let := hFe
      exact ⟨hFe,hFc,hFQ,sup_le hQF (zpowers_le.mpr hsF),hgF,
        quaternion_eight_point_image_of_inverting_swap B C F model hC hi hc hFc hFQ hQF
          g s hg3 hs2 hgB hgC hgne hsB hsg hgF hsF⟩
end Subgroup
