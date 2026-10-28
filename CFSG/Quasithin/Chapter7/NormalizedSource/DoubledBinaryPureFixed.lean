module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryComponentGeometry
import all CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPlanes

/-!
# Pointwise fixers of singular-free subspaces through a pure line

A subspace of dimension at least three with no singular diagonal vector
cannot contain nonzero pure vectors on both axes: their pairing is either
zero, giving a singular sum, or one, giving a paired plane whose proper
extensions contain singular vectors. Thus, through a pure natural line,
projection to the natural factor is a bijection; through a pure dual line,
projection to the dual factor is a bijection. The pure line excludes graph
operators and the bijection makes every inner pointwise fixer trivial.

The ambient result retains the original marking and full centralizer kernel.
DoubledBinaryPureFaithful uses it with E.6.11's proved moving-element
consequence to bound the actual component fixed subgroup and eliminate the
H1 kernel. This avoids needing the stronger normal-seven conclusion of
E.6.11 in this particular natural–dual representation.
Source: Aschbacher–Smith, H.4.2 and the H1 faithfulness argument in 7.7.3,
printed pp.380,705–706, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPureFixed
open ChapterE BinaryLinearThree NaturalDual DoubledBinaryPlanes
open DoubledBinaryComponentGeometry

private theorem no_pure_pair
    (S : Submodule (ZMod 2) Space) (hS : 3 ≤ Module.finrank (ZMod 2) S)
    (hs : ∀ x ∈ S, ¬ IsSingular x)
    (v : Vector) (f : Module.Dual (ZMod 2) Vector)
    (hv : v ≠ 0) (hf : f ≠ 0) (hvS : (v,0) ∈ S) (hfS : (0,f) ∈ S) : False := by
  by_cases hz : f v = 0
  · exact hs ((v,0)+(0,f)) (S.add_mem hvS hfS) ⟨by simpa using hv,by simpa using hf,by simpa using hz⟩
  have hfv : f v = 1 := (by decide : ∀ c : ZMod 2, c ≠ 0 → c = 1) _ hz
  have hlt : pairedPlane v f < S := by
    apply lt_of_le_of_ne ((pairedPlane_le_iff v f S).mpr ⟨hvS,hfS⟩)
    intro he
    have hh := pairedPlane_finrank v f hfv
    rw [he] at hh
    omega
  obtain ⟨x,hx,hxs⟩ := pairedPlane_lt_singular v f hfv S hlt
  exact hs x hx hxs

private theorem natural_projection
    (S : Submodule (ZMod 2) Space) (hS : 3 ≤ Module.finrank (ZMod 2) S)
    (hs : ∀ x ∈ S, ¬ IsSingular x)
    (v : Vector) (hv : v ≠ 0) (hvS : (v,0) ∈ S) :
    Function.Bijective ((LinearMap.fst (ZMod 2) Vector _).comp S.subtype) := by
  let p := (LinearMap.fst (ZMod 2) Vector (Module.Dual (ZMod 2) Vector)).comp S.subtype
  have hi : Function.Injective p := by
    intro x y hxy
    have hx1 : x.val.1 - y.val.1 = 0 := sub_eq_zero.mpr hxy
    have hx2 : x.val.2 - y.val.2 = 0 := by
      by_contra hn
      apply no_pure_pair S hS hs v (x.val.2-y.val.2) hv hn hvS
      have he : x.val - y.val = (0,x.val.2-y.val.2) := Prod.ext hx1 rfl
      exact he ▸ S.sub_mem x.property y.property
    exact Subtype.ext (Prod.ext hxy (sub_eq_zero.mp hx2))
  have hd : Module.finrank (ZMod 2) S = Module.finrank (ZMod 2) Vector := by
    have hh := LinearMap.finrank_le_finrank_of_injective hi
    have hd : Module.finrank (ZMod 2) Vector = 3 := by simp [BinaryLinearThree.Vector,Matrix.PSL3Two.Fano.Vector]
    omega
  exact ⟨hi,(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).mp hi⟩

private theorem dual_projection
    (S : Submodule (ZMod 2) Space) (hS : 3 ≤ Module.finrank (ZMod 2) S)
    (hs : ∀ x ∈ S, ¬ IsSingular x)
    (f : Module.Dual (ZMod 2) Vector) (hf : f ≠ 0) (hfS : (0,f) ∈ S) :
    Function.Bijective ((LinearMap.snd (ZMod 2) Vector _).comp S.subtype) := by
  let p := (LinearMap.snd (ZMod 2) Vector (Module.Dual (ZMod 2) Vector)).comp S.subtype
  have hi : Function.Injective p := by
    intro x y hxy
    have hx2 : x.val.2 - y.val.2 = 0 := sub_eq_zero.mpr hxy
    have hx1 : x.val.1 - y.val.1 = 0 := by
      by_contra hn
      apply no_pure_pair S hS hs (x.val.1-y.val.1) f hn hf _ hfS
      have he : x.val - y.val = (x.val.1-y.val.1,0) := Prod.ext rfl hx2
      exact he ▸ S.sub_mem x.property y.property
    exact Subtype.ext (Prod.ext (sub_eq_zero.mp hx1) hxy)
  have hd : Module.finrank (ZMod 2) S = Module.finrank (ZMod 2) (Module.Dual (ZMod 2) Vector) := by
    have hh := LinearMap.finrank_le_finrank_of_injective hi
    have hd : Module.finrank (ZMod 2) (Module.Dual (ZMod 2) Vector) = 3 := by
      simp [BinaryLinearThree.Vector,Matrix.PSL3Two.Fano.Vector]
    omega
  exact ⟨hi,(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).mp hi⟩

/-- A singular-free three-space containing a pure line has trivial pointwise
fixer in the full marked automizer, for either original axis. -/
theorem large_pure_singularFree_fixer
    (S : Submodule (ZMod 2) Space) (hS : 3 ≤ Module.finrank (ZMod 2) S)
    (hs : ∀ x ∈ S, ¬ IsSingular x)
    (hp : (∃ v : Vector, v ≠ 0 ∧ (v,0) ∈ S) ∨
      (∃ f : Module.Dual (ZMod 2) Vector, f ≠ 0 ∧ (0,f) ∈ S))
    (α : MulAut Group) (e : Space ≃ₗ[ZMod 2] Space)
    (he : ∀ g x, e (action g x) = action (α g) (e x))
    (hfix : ∀ x ∈ S, e x = x) : e = LinearEquiv.refl _ _ := by
  have hi : α ∈ MulAut.innerSubgroup Group := by
    by_contra ho
    rcases hp with ⟨v,hv,hvS⟩ | ⟨f,hf,hfS⟩
    · have hh := (outer_swaps α e he ho).1 v
      rw [hfix _ hvS] at hh
      exact hv hh
    · have hh := (outer_swaps α e he ho).2 f
      rw [hfix _ hfS] at hh
      exact hf hh
  obtain ⟨g,rfl⟩ := inner_operator α e he hi
  have hn : Function.Injective W := by
    intro g h hh
    apply Subtype.ext
    exact Matrix.toLin'.injective hh
  have hg : g = 1 := by
    rcases hp with ⟨v,hv,hvS⟩ | ⟨f,hf,hfS⟩
    · apply hn
      apply LinearMap.ext
      intro x
      obtain ⟨y,hy⟩ := (natural_projection S hS hs v hv hvS).surjective x
      have hh := congrArg Prod.fst (hfix y y.property)
      change W g y.val.1 = y.val.1 at hh
      change y.val.1 = x at hy
      simpa only [hy,map_one,Module.End.one_apply] using hh
    · have hall (f : Module.Dual (ZMod 2) Vector) : W.dual g f = f := by
        obtain ⟨y,hy⟩ := (dual_projection S hS hs _ hf hfS).surjective f
        have hh := congrArg Prod.snd (hfix y y.property)
        change W.dual g y.val.2 = y.val.2 at hh
        change y.val.2 = f at hy
        rwa [hy] at hh
      have hgi : g⁻¹ = 1 := by
        apply hn
        apply LinearMap.ext
        intro x
        funext i
        have hh : (W g⁻¹ x) i = x i := LinearMap.congr_fun (hall (LinearMap.proj i)) x
        simpa only [map_one,Module.End.one_apply] using hh
      exact inv_eq_one.mp hgi
  subst g
  apply LinearEquiv.ext
  intro x
  change action 1 x = x
  rw [map_one]
  rfl



private theorem coordinate_card {G : Type*} [_root_.Group G]
    (W₀ X : Subgroup G) [IsElementaryAbelian 2 W₀]
    (E : Additive W₀ ≃ₗ[ZMod 2] Space) (hXW : X ≤ W₀) :
    Nat.card (coordinateSubspace W₀ E X) = Nat.card X := by
  let P := (Chapter7.moduleSubgroup W₀).symm (X.subgroupOf W₀)
  have hh := Nat.card_congr (Submodule.equivMapOfInjective E.toLinearMap E.injective P).toEquiv
  change Nat.card P = Nat.card (coordinateSubspace W₀ E X) at hh
  rw [← hh]
  change Nat.card (X.subgroupOf W₀) = Nat.card X
  exact Nat.card_congr (subgroupOfEquivOfLe hXW).toEquiv

/-- On an actual singular-free subgroup of order greater than four containing
an original pure line, the point centralizer has trivial induced action. -/
theorem large_pure_singularFree_centralizer
    {G : Type*} [_root_.Group G] [Finite G]
    (W₀ X Z M : Subgroup G) [IsElementaryAbelian 2 W₀]
    (E : Additive W₀ ≃ₗ[ZMod 2] Space)
    (a : Automizer W₀ ≃* MulAut Group)
    (hcov : ∀ b g w, E (automizerRepresentation W₀ b (E.symm (action g (E w)))) =
      action (a b g) (E (automizerRepresentation W₀ b w)))
    (hMN : M ≤ normalizer (W₀ : Set G)) (hXW : X ≤ W₀)
    (hZX : Z ≤ X) (hZ : Z ≠ ⊥)
    (hp : (∀ w : Additive W₀, (w.toMul : G) ∈ Z → (E w).2 = 0) ∨
      (∀ w : Additive W₀, (w.toMul : G) ∈ Z → (E w).1 = 0))
    (hs : ∀ w : Additive W₀, (w.toMul : G) ∈ X → ¬ IsSingular (E w))
    (hcard : 4 < Nat.card X) :
    M ⊓ centralizer (X : Set G) = M ⊓ centralizer (W₀ : Set G) := by
  let S := coordinateSubspace W₀ E X
  have hS : 3 ≤ Module.finrank (ZMod 2) S := by
    have hc : Nat.card X = 2 ^ Module.finrank (ZMod 2) S := by
      rw [← coordinate_card W₀ X E hXW,Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
    by_contra! hn
    have hh := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (show Module.finrank (ZMod 2) S ≤ 2 by omega)
    rw [← hc] at hh
    omega
  have hsing (x : Space) (hx : x ∈ S) : ¬ IsSingular x := by
    have hw : ((E.symm x).toMul : G) ∈ X := (coordinate_mem W₀ E X (E.symm x)).mp (by
      simpa only [E.apply_symm_apply] using hx)
    simpa only [E.apply_symm_apply] using hs (E.symm x) hw
  obtain ⟨z,hz,hzn⟩ := SetLike.not_le_iff_exists.mp (show ¬ Z ≤ ⊥ from fun hh => hZ (le_bot_iff.mp hh))
  let w : Additive W₀ := Additive.ofMul ⟨z,hXW (hZX hz)⟩
  have hw : E w ≠ 0 := by
    intro he
    have hh := E.map_eq_zero_iff.mp he
    exact hzn (mem_bot.mpr (congrArg (fun x : Additive W₀ => (x.toMul : G)) hh))
  have hwS : E w ∈ S := (coordinate_mem W₀ E X w).mpr (hZX hz)
  have hpure : (∃ v : Vector, v ≠ 0 ∧ (v,0) ∈ S) ∨
      (∃ f : Module.Dual (ZMod 2) Vector, f ≠ 0 ∧ (0,f) ∈ S) := by
    rcases hp with hn | hd
    · have hh := hn w hz
      exact Or.inl ⟨(E w).1,fun he => hw (Prod.ext he hh),by rwa [← show ((E w).1,0) = E w from Prod.ext rfl hh.symm] at hwS⟩
    · have hh := hd w hz
      exact Or.inr ⟨(E w).2,fun he => hw (Prod.ext hh he),by rwa [← show (0,(E w).2) = E w from Prod.ext hh.symm rfl] at hwS⟩
  apply le_antisymm _ (inf_le_inf_left M (centralizer_le hXW))
  intro m hm
  let n : normalizer (W₀ : Set G) := ⟨m,hMN hm.1⟩
  have he := large_pure_singularFree_fixer S hS hsing hpure
    (a (W₀.normalizerMonoidHom.rangeRestrict n)) (coordinateOperator W₀ E n)
    (operator_covariance W₀ E a hcov n) (operator_fixed W₀ E n X hm.2)
  refine ⟨hm.1,?_⟩
  intro x hx
  let y : Additive W₀ := Additive.ofMul ⟨x,hx⟩
  have hh := LinearEquiv.congr_fun he (E y)
  change E (automizerRepresentation W₀ (W₀.normalizerMonoidHom.rangeRestrict n)
    (E.symm (E y))) = E y at hh
  rw [E.symm_apply_apply] at hh
  have hc := congrArg (fun z : Additive W₀ => (z.toMul : G)) (E.injective hh)
  change m * x * m⁻¹ = x at hc
  exact (mul_inv_eq_iff_eq_mul.mp hc).symm

end CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPureFixed
