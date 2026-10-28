module

public import Theory.GroupTheory.Gaschutz
public import Theory.Representation.SL2FourNaturalBorelFixedLifting
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Quotient.Defs

/-!
# Fixed-vector lifting from Gaschütz splitting

For a finite binary representation with trivial action modulo N, a vector
fixed by a Sylow two-subgroup has a globally fixed representative modulo N.
Restrict to W = N + span{y}. In W ⋊ A the embedded N is an abelian normal
two-subgroup. The fixed line together with the actual Sylow subgroup gives
a complement in the Sylow preimage. Gaschütz supplies a global complement.
Its element above (y + N, 1) is central in the complement, and its vector
coordinate is therefore fixed by every actor.

The natural and binary-dual applications use a subgroup B containing the
Sylow subgroup and mapping onto the literal upper Borel of SL₂(4). The
parent module supplies the Borel fixed-space calculations; this module
discharges its independent fixed-lift premise by subgroup splitting.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, A.1.39
and the first paragraph of 14.7.74, printed p.1077 (PDF p.1094), manuscript
of 1 March 2004.
-/

noncomputable section
open Subgroup Representation SemidirectProduct Representation.BinaryOffender
open Matrix.SpecialLinearGroup
open scoped IsMulCommutative

namespace Representation.SL2FourNaturalBorelFixedLifting
variable {A Y : Type*} [Group A] [AddCommGroup Y] [Module (ZMod 2) Y]

namespace Gaschutz

private def action (ρ : Representation (ZMod 2) A Y) : A →* MulAut (Multiplicative Y) where
  toFun a := (LinearEquiv.ofBijective (ρ a) (ρ.apply_bijective a)).toAddEquiv.toMultiplicative
  map_one' := by ext x; exact congrArg Multiplicative.ofAdd (by simp)
  map_mul' a b := by ext x; exact congrArg Multiplicative.ofAdd (by simp)

private abbrev Extension (ρ : Representation (ZMod 2) A Y) := Multiplicative Y ⋊[action ρ] A

private theorem binary_pgroup : IsPGroup 2 (Multiplicative Y) := by
  intro x
  refine ⟨1, ?_⟩
  rw [pow_one, pow_two]
  change x.toAdd + x.toAdd = 0
  have h := congrArg (fun c : ZMod 2 => c • x.toAdd) (show (2 : ZMod 2) = 0 by decide)
  simpa only [two_smul, zero_smul] using h

private def quotientHom (ρ : Representation (ZMod 2) A Y) (N : Submodule (ZMod 2) Y)
    (hd : ∀ a y, ρ a y - y ∈ N) : Extension ρ →* Multiplicative (Y ⧸ N) × A where
  toFun x := (Multiplicative.ofAdd (N.mkQ x.left.toAdd), x.right)
  map_one' := by ext <;> simp
  map_mul' x z := by
    apply Prod.ext
    · apply Multiplicative.toAdd.injective
      change N.mkQ (x.left.toAdd + ρ x.right z.left.toAdd) =
        N.mkQ x.left.toAdd + N.mkQ z.left.toAdd
      rw [map_add]
      congr 1
      apply sub_eq_zero.mp
      rw [← map_sub]
      exact (Submodule.Quotient.mk_eq_zero N).mpr (hd _ _)
    · rfl

private theorem mem_kernel (ρ : Representation (ZMod 2) A Y) (N : Submodule (ZMod 2) Y)
    (hd : ∀ a y, ρ a y - y ∈ N) (x : Extension ρ) :
    x ∈ (quotientHom ρ N hd).ker ↔ x.left.toAdd ∈ N ∧ x.right = 1 := by
  change (Multiplicative.ofAdd (N.mkQ x.left.toAdd), x.right) = (1, 1) ↔ _
  rw [Prod.mk.injEq]
  change N.mkQ x.left.toAdd = 0 ∧ x.right = 1 ↔ _
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]

private theorem lift_spanning [Finite A] [Finite Y]
    (ρ : Representation (ZMod 2) A Y) (N : Submodule (ZMod 2) Y)
    (hd : ∀ a z, ρ a z - z ∈ N) (S : Sylow 2 A) (y : Y)
    (hy : ∀ s : S, ρ s y = y) (hyN : y ∉ N)
    (hspan : ∀ z : Y, ∃ n ∈ N, ∃ c : ZMod 2, n + c • y = z) :
    ∃ w, (∀ a, ρ a w = w) ∧ y - w ∈ N := by
  -- The kernel is precisely the embedded additive subgroup N.
  let G := Extension ρ
  let : Finite G := Finite.of_equiv (Multiplicative Y × A) SemidirectProduct.equivProd.symm
  let π := quotientHom ρ N hd
  let V := π.ker
  have hv (x : G) : x ∈ V ↔ x.left.toAdd ∈ N ∧ x.right = 1 := mem_kernel ρ N hd x
  have hright (x : V) : (x : G).right = 1 := (hv x).mp x.property |>.2
  let : IsMulCommutative V := ⟨⟨fun x z => by
    apply Subtype.ext
    apply SemidirectProduct.ext
    · change x.val.left * action ρ x.val.right z.val.left =
        z.val.left * action ρ z.val.right x.val.left
      rw [hright, hright, map_one]
      exact mul_comm _ _
    · simp [hright]⟩⟩
  have hV : IsPGroup 2 V := by
    intro x
    refine ⟨1, Subtype.ext ?_⟩
    rw [pow_one, pow_two]
    apply SemidirectProduct.ext
    · change x.val.left * action ρ x.val.right x.val.left = 1
      rw [hright, map_one, MulAut.one_apply]
      change x.val.left.toAdd + x.val.left.toAdd = 0
      have h := congrArg (fun c : ZMod 2 => c • x.val.left.toAdd) (show (2 : ZMod 2) = 0 by decide)
      simpa only [two_smul, zero_smul] using h
    · simp [hright]
  -- The actor projection has a two-group kernel, so its Sylow preimage is Sylow.
  let r : G →* A := SemidirectProduct.rightHom
  have hr : IsPGroup 2 r.ker := by
    rw [← SemidirectProduct.range_inl_eq_ker_rightHom]
    exact (binary_pgroup (Y := Y)).of_surjective
      (SemidirectProduct.inl : Multiplicative Y →* G).rangeRestrict
      (SemidirectProduct.inl : Multiplicative Y →* G).rangeRestrict_surjective
  let P : Sylow 2 G := S.comapOfKerIsPGroup r hr (by
    rw [MonoidHom.range_eq_top.mpr SemidirectProduct.rightHom_surjective]
    exact le_top)
  have hP (x : G) : x ∈ (P : Subgroup G) ↔ x.right ∈ (S : Subgroup A) := Iff.rfl
  let L := Submodule.span (ZMod 2) {y}
  have hfix (a : A) (ha : a ∈ (S : Subgroup A)) (z : Y) (hz : z ∈ L) : ρ a z = z := by
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
    rw [map_smul, hy ⟨a, ha⟩]
  -- The fixed line and S supply the local subgroup complement.
  let C : Subgroup P :=
    { carrier := {x | x.val.left.toAdd ∈ L}
      one_mem' := L.zero_mem
      mul_mem' := by
        intro x z hx hz
        change x.val.left.toAdd + ρ x.val.right z.val.left.toAdd ∈ L
        rw [hfix _ ((hP _).mp x.property) _ hz]
        exact L.add_mem hx hz
      inv_mem' := by
        intro x hx
        change ρ x.val.right⁻¹ (-x.val.left.toAdd) ∈ L
        rw [map_neg, hfix _ (S.inv_mem ((hP _).mp x.property)) _ hx]
        exact L.neg_mem hx }
  have hdis : Disjoint N L := Submodule.disjoint_span_singleton_of_notMem hyN
  have hlocal : (V.subgroupOf (P : Subgroup G)).IsComplement' C := by
    apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
    · apply Subgroup.disjoint_def.mpr
      intro x hxV hxC
      have hxN := (hv x.val).mp hxV
      have hz : x.val.left.toAdd = 0 := (Submodule.disjoint_def.mp hdis) _ hxN.1 hxC
      apply Subtype.ext
      exact SemidirectProduct.ext (Multiplicative.toAdd.injective hz) hxN.2
    · apply Set.eq_univ_iff_forall.mpr
      intro x
      obtain ⟨n, hn, c, hc⟩ := hspan x.val.left.toAdd
      let v : P := ⟨SemidirectProduct.inl (Multiplicative.ofAdd n), S.one_mem⟩
      let k : P := ⟨⟨Multiplicative.ofAdd (c • y), x.val.right⟩, x.property⟩
      refine ⟨v, (hv v.val).mpr ⟨hn, rfl⟩, k, ?_, ?_⟩
      · exact Submodule.mem_span_singleton.mpr ⟨c, rfl⟩
      · apply Subtype.ext
        apply SemidirectProduct.ext
        · apply Multiplicative.toAdd.injective
          change n + ρ 1 (c • y) = x.val.left.toAdd
          simpa only [map_one, Module.End.one_apply] using hc
        · exact one_mul _
  -- Apply the genuine splitting theorem, retaining its subgroup witness.
  obtain ⟨K, hK⟩ := (Subgroup.exists_complement_iff_sylow V hV P).mpr ⟨C, hlocal⟩
  have hkinj : Function.Injective (π.comp K.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff]
    apply eq_bot_iff.mpr
    intro k hk
    apply Subtype.ext
    exact Subgroup.disjoint_def.mp hK.disjoint hk k.property
  obtain ⟨⟨n, k⟩, he⟩ := hK.2 (SemidirectProduct.inl (Multiplicative.ofAdd y))
  have hkπ : π k = π (SemidirectProduct.inl (Multiplicative.ofAdd y)) := by
    rw [← he, map_mul, show π n = 1 from n.property, one_mul]
  have hkr : k.val.right = 1 := congrArg Prod.snd hkπ
  -- The class of (y,1) is central in (Y/N) × A. Injectivity on K lifts this
  -- centrality, and the actor coordinates of K cover A.
  have hqcentral (c : K) : π (k.val * c.val) = π (c.val * k.val) := by
    rw [map_mul, map_mul, hkπ]
    apply Prod.ext
    · exact mul_comm _ _
    · change 1 * c.val.right = c.val.right * 1
      simp
  have hkcentral (c : K) : k.val * c.val = c.val * k.val :=
    congrArg Subtype.val (hkinj (show (π.comp K.subtype) (k * c) =
      (π.comp K.subtype) (c * k) from hqcentral c))
  refine ⟨k.val.left.toAdd, ?_, ?_⟩
  · intro a
    obtain ⟨⟨n', c⟩, hec⟩ := hK.2 (SemidirectProduct.inr a)
    have hcr : c.val.right = a := by
      have hr' := congrArg SemidirectProduct.right hec
      simpa only [mul_right, hright, one_mul, right_inr] using hr'
    have heq := congrArg (fun x : G => x.left.toAdd) (hkcentral c)
    change k.val.left.toAdd + ρ k.val.right c.val.left.toAdd =
      c.val.left.toAdd + ρ c.val.right k.val.left.toAdd at heq
    rw [hkr, hcr, map_one, Module.End.one_apply, add_comm] at heq
    exact (add_left_cancel heq).symm
  · have heq := congrArg (fun x : G => x.left.toAdd) he
    change n.val.left.toAdd + ρ n.val.right k.val.left.toAdd = y at heq
    rw [hright, map_one, Module.End.one_apply] at heq
    rw [← heq, add_sub_cancel_right]
    exact ((hv n.val).mp n.property).1

end Gaschutz

/-- Genuine Gaschütz fixed-vector lifting for a finite binary representation.
The displacement premise expresses trivial action on the quotient by N. -/
public theorem exists_fixed_lift [Finite A] [Finite Y]
    (ρ : Representation (ZMod 2) A Y) (N : Submodule (ZMod 2) Y)
    (hd : ∀ a z, ρ a z - z ∈ N) (S : Sylow 2 A) (y : Y)
    (hy : y ∈ fixedSpace ρ (S : Subgroup A)) :
    ∃ w, (∀ a, ρ a w = w) ∧ y - w ∈ N := by
  by_cases hyN : y ∈ N
  · exact ⟨0, fun a => map_zero (ρ a), by simpa only [sub_zero] using hyN⟩
  let W : Submodule (ZMod 2) Y := N ⊔ Submodule.span (ZMod 2) {y}
  have hNW : N ≤ W := le_sup_left
  have hyW : y ∈ W :=
    (le_sup_right : Submodule.span (ZMod 2) {y} ≤ W) (Submodule.mem_span_singleton_self y)
  have hstable : ∀ a, W ≤ W.comap (ρ a) := by
    intro a z hz
    change ρ a z ∈ W
    simpa only [sub_add_cancel] using W.add_mem (hNW (hd a z)) hz
  let σ := ρ.subrepresentation W hstable
  let N' := N.comap W.subtype
  let y' : W := ⟨y, hyW⟩
  obtain ⟨w, hw, hn⟩ := Gaschutz.lift_spanning σ N' (fun a z => hd a z) S y'
    (fun s => Subtype.ext (hy s)) (fun h => hyN h) (by
      intro z
      obtain ⟨n, hn, v, hv, he⟩ := Submodule.mem_sup.mp z.property
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
      exact ⟨⟨n, hNW hn⟩, hn, c, Subtype.ext he⟩)
  exact ⟨w.val, fun a => congrArg Subtype.val (hw a), hn⟩

/-- On a finite binary module with trivial quotient by a marked natural
`SL₂(4)` section, every vector fixed by a subgroup mapping onto the Borel
and containing a Sylow two-subgroup is globally fixed. -/
public theorem natural_fixed_of_borel
    {A Y : Type*} [Group A] [Finite A]
    [AddCommGroup Y] [Module (ZMod 2) Y] [Finite Y]
    (ρ : Representation (ZMod 2) A Y) (q : A →* SL)
    (_hq : Function.Surjective q)
    (i : IntertwiningMap (SL2FourNatural.naturalRepresentation.comp q) ρ)
    (hi : Function.Injective i)
    (hd : ∀ a y, ρ a y - y ∈ i.toLinearMap.range)
    (B : Subgroup A) (S : Sylow 2 A)
    (hSB : (S : Subgroup A) ≤ B) (hmark : B.map q = rankOneBorel F) :
    ∀ y ∈ fixedSpace ρ B, ∀ a, ρ a y = y :=
  natural_fixed_of_borel_of_fixed_lift ρ q i hi B S hSB hmark
    (exists_fixed_lift ρ i.toLinearMap.range hd S)

/-- The same Gaschütz detector for the actual binary dual of the marked
natural `SL₂(4)` section. The Borel marking is on `B`, which contains `S`. -/
public theorem dual_fixed_of_borel
    {A Y : Type*} [Group A] [Finite A]
    [AddCommGroup Y] [Module (ZMod 2) Y] [Finite Y]
    (ρ : Representation (ZMod 2) A Y) (q : A →* SL)
    (_hq : Function.Surjective q)
    (i : IntertwiningMap (SL2FourNatural.naturalRepresentation.dual.comp q) ρ)
    (hi : Function.Injective i)
    (hd : ∀ a y, ρ a y - y ∈ i.toLinearMap.range)
    (B : Subgroup A) (S : Sylow 2 A)
    (hSB : (S : Subgroup A) ≤ B) (hmark : B.map q = rankOneBorel F) :
    ∀ y ∈ fixedSpace ρ B, ∀ a, ρ a y = y :=
  dual_fixed_of_borel_of_fixed_lift ρ q i hi B S hSB hmark
    (exists_fixed_lift ρ i.toLinearMap.range hd S)

end Representation.SL2FourNaturalBorelFixedLifting
