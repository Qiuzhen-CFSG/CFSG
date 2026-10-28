module

public import Theory.Representation.BinaryNaturalDual.FiveActors.CoreTransport
public import Theory.Representation.DualCommutator

open scoped CharTwo
open BinaryLinear BinaryLinear.OuterCyclic
open BinaryNaturalDual

/-!
# The degree-five radical and its hyperplanes

The displacement map identifies the block-unipotent radical at a three-space
with the additive group Hom(X/U,U), of dimension six. Evaluation at a vector
outside U has kernel of order eight; composition with a functional not
annihilating U has kernel of order sixteen. A subgroup of index two in the
radical has order thirty-two, so these bounds determine both of its fixed
summands. The invariant, nondegenerate evaluation pairing identifies the
paired representation with its dual. Fixed/commutator annihilator duality
then gives the exact commutator subspace, not just a dimension bound.

All final statements concern the actual inner image in Aut(GL₅(2)).
Source: Aschbacher–Smith, combined manuscript (1 March 2004), H.9.2(3–4),
printed pp.390–391 (PDF pp.401–402).
-/

public section

namespace BinaryNaturalDual.FiveActors

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

def disp (U : Submodule (ZMod 2) V) (g : BinaryLinear.radical U) :
    (V ⧸ U) →ₗ[ZMod 2] U :=
  U.liftQ
    ((g.val.toLinearMap - LinearMap.id).codRestrict U g.property.2)
    (by
      intro u hu
      apply LinearMap.mem_ker.mpr
      apply Subtype.ext
      change g.val u - u = 0
      exact sub_eq_zero.mpr (g.property.1 u hu))

@[simp] theorem disp_mk (U : Submodule (ZMod 2) V) (g : BinaryLinear.radical U) (x : V) :
    (disp U g (U.mkQ x) : V) = g.val x - x := by rfl

def shearEquiv (U : Submodule (ZMod 2) V) (f : (V ⧸ U) →ₗ[ZMod 2] U) : V ≃ₗ[ZMod 2] V where
  toLinearMap := LinearMap.id + U.subtype.comp (f.comp U.mkQ)
  invFun x := x - (f (U.mkQ x) : V)
  left_inv x := by
    change x + (f (U.mkQ x) : V) - (f (U.mkQ (x + (f (U.mkQ x) : V))) : V) = x
    have hq : U.mkQ (f (U.mkQ x) : V) = 0 :=
      (Submodule.Quotient.mk_eq_zero U).mpr (f (U.mkQ x)).property
    rw [map_add, hq, add_zero, add_sub_cancel_right]
  right_inv x := by
    change x - (f (U.mkQ x) : V) +
      (f (U.mkQ (x - (f (U.mkQ x) : V))) : V) = x
    have hq : U.mkQ (f (U.mkQ x) : V) = 0 :=
      (Submodule.Quotient.mk_eq_zero U).mpr (f (U.mkQ x)).property
    rw [map_sub, hq, sub_zero, sub_add_cancel]

def shear (U : Submodule (ZMod 2) V) (f : (V ⧸ U) →ₗ[ZMod 2] U) : BinaryLinear.radical U :=
  ⟨shearEquiv U f, by
    intro u hu
    change (u : V) + (f (U.mkQ (u : V)) : V) = u
    have hq : U.mkQ (u : V) = 0 := (Submodule.Quotient.mk_eq_zero U).mpr hu
    simp [hq], by
      apply (show (∀ x, shearEquiv U f x - x ∈ U) from ?_)
      intro x
      change x + (f (U.mkQ x) : V) - x ∈ U
      simpa only [add_sub_cancel_left] using (f (U.mkQ x)).property⟩

def equiv (U : Submodule (ZMod 2) V) : BinaryLinear.radical U ≃* Multiplicative ((V ⧸ U) →ₗ[ZMod 2] U) where
  toFun g := Multiplicative.ofAdd (disp U g)
  invFun f := shear U (Multiplicative.toAdd f)
  left_inv g := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    change x + (disp U g (U.mkQ x) : V) = g.val x
    rw [disp_mk]
    abel
  right_inv f := by
    apply Multiplicative.ext
    change disp U (shear U (Multiplicative.toAdd f)) = Multiplicative.toAdd f
    apply LinearMap.ext
    intro q
    induction q using Submodule.Quotient.induction_on with
    | _ x =>
      apply Subtype.ext
      change (disp U (shear U (Multiplicative.toAdd f)) (U.mkQ x) : V) = _
      rw [disp_mk]
      change (x + (Multiplicative.toAdd f (U.mkQ x) : V) - x : V) = _
      simp
  map_mul' g h := by
    apply congrArg Multiplicative.ofAdd
    change disp U (g * h) = disp U g + disp U h
    apply LinearMap.ext
    intro q
    induction q using Submodule.Quotient.induction_on with
    | _ x =>
      apply Subtype.ext
      change (disp U (g * h) (U.mkQ x) : V) =
        ((disp U g + disp U h) (U.mkQ x) : V)
      change (g.val (h.val x) - x : V) =
        ((disp U g + disp U h) (U.mkQ x) : V)
      change (g.val (h.val x) - x : V) =
        (disp U g (U.mkQ x) : V) + (disp U h (U.mkQ x) : V)
      rw [disp_mk, disp_mk]
      have hh := g.property.1 (h.val x - x) (h.property.2 x)
      rw [map_sub] at hh
      rw [sub_eq_iff_eq_add.mp hh]
      abel

theorem card_radical [FiniteDimensional (ZMod 2) V]
    (U : Submodule (ZMod 2) V) (hV : Module.finrank (ZMod 2) V = 5)
    (hU : Module.finrank (ZMod 2) U = 3) : Nat.card (BinaryLinear.radical U) = 64 := by
  rw [Nat.card_congr (equiv U).toEquiv]
  change Nat.card ((V ⧸ U) →ₗ[ZMod 2] U) = 64
  have hq : Module.finrank (ZMod 2) (V ⧸ U) = 2 := by
    have hsum := Submodule.finrank_quotient_add_finrank U
    rw [hV, hU] at hsum
    omega
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Module.finrank_linearMap, hq, hU]
  norm_num [Nat.card_zmod]

theorem radical_sq (U : Submodule (ZMod 2) V) (g : BinaryLinear.radical U) :
    g ^ 2 = 1 := by
  apply Subtype.ext
  change (g : BinaryLinear.GL V) ^ 2 = 1
  ext v
  have hd := g.property.1 ((g : BinaryLinear.GL V) v - v) (g.property.2 v)
  simp only [map_sub] at hd
  simp only [pow_two, LinearEquiv.mul_apply, LinearEquiv.coe_one, id_eq]
  apply sub_eq_zero.mp
  calc
    (g : BinaryLinear.GL V) ((g : BinaryLinear.GL V) v) - v =
        ((g : BinaryLinear.GL V) ((g : BinaryLinear.GL V) v) -
          (g : BinaryLinear.GL V) v) + ((g : BinaryLinear.GL V) v - v) := by abel
    _ = 0 := by
      rw [hd, ← two_smul (ZMod 2), show (2 : ZMod 2) = 0 by decide, zero_smul]

instance radical_isElementaryAbelian (U : Submodule (ZMod 2) V) :
    IsElementaryAbelian 2 (BinaryLinear.radical U) where
  toIsMulCommutative := ⟨⟨fun (s t : BinaryLinear.radical U) =>
    Subtype.ext (BinaryLinear.OuterCyclic.radical_commute U s.property t.property)⟩⟩
  exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun g => by
    simpa only [Nat.reducePow] using radical_sq U g)

theorem radical_isElementaryAbelian_card [FiniteDimensional (ZMod 2) V]
    (U : Submodule (ZMod 2) V) (hV : Module.finrank (ZMod 2) V = 5)
    (hU : Module.finrank (ZMod 2) U = 3) :
    IsElementaryAbelian 2 (BinaryLinear.radical U) ∧
      Nat.card (BinaryLinear.radical U) = 64 :=
  ⟨inferInstance, card_radical U hV hU⟩

def fixer (U : Submodule (ZMod 2) V) (x : V) : Subgroup (BinaryLinear.radical U) where
  carrier := {g | g.val x = x}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh
    change g.val x = x at hg
    change h.val x = x at hh
    change g.val (h.val x) = x
    rw [hh, hg]
  inv_mem' := by
    intro g hg
    change g.val x = x at hg
    apply g.val.injective
    change g.val (g.val.symm x) = g.val x
    rw [g.val.apply_symm_apply, hg]

theorem card_fixer_le_eight [FiniteDimensional (ZMod 2) V]
    (U : Submodule (ZMod 2) V) (hV : Module.finrank (ZMod 2) V = 5)
    (hU : Module.finrank (ZMod 2) U = 3) {x : V} (hx : x ∉ U) :
    Nat.card (fixer U x) ≤ 8 := by
  let q := U.mkQ x
  have hq : q ≠ 0 := by
    intro h
    exact hx ((Submodule.Quotient.mk_eq_zero U).mp h)
  let ev : (V ⧸ U) →ₗ[ZMod 2] ((V ⧸ U) →ₗ[ZMod 2] U) →ₗ[ZMod 2] U :=
    LinearMap.applyₗ
  have hev : Function.Surjective (ev q) := by
    intro u
    obtain ⟨f, hfq, hf⟩ := (⊥ : Submodule (ZMod 2) (V ⧸ U)).exists_le_ker_of_notMem hq
    refine ⟨f.smulRight u, ?_⟩
    change (f.smulRight u) q = u
    rw [LinearMap.smulRight_apply, show f q = 1 by exact (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) _ hfq]
    simp
  let K : Subgroup (Multiplicative ((V ⧸ U) →ₗ[ZMod 2] U)) :=
    BinaryNaturalDual.subgroupOrderIso ((ev q).ker)
  have hle : (fixer U x).map (equiv U).toMonoidHom ≤ K := by
    rintro y ⟨g, hg, rfl⟩
    change g.val x = x at hg
    change disp U g ∈ (ev q).ker
    rw [LinearMap.mem_ker]
    change disp U g (U.mkQ x) = 0
    apply Subtype.ext
    rw [disp_mk]
    exact sub_eq_zero.mpr hg
  have hker : Module.finrank (ZMod 2) ((ev q).ker) = 3 := by
    have hr := (ev q).finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hev, finrank_top] at hr
    rw [Module.finrank_linearMap] at hr
    have hq : Module.finrank (ZMod 2) (V ⧸ U) = 2 := by
      have hsum := Submodule.finrank_quotient_add_finrank U
      rw [hV, hU] at hsum
      omega
    rw [hq, hU] at hr
    omega
  have hK : Nat.card K = 8 := by
    let e : (ev q).ker ≃ K := {
      toFun z := ⟨Multiplicative.ofAdd z, z.property⟩
      invFun y := ⟨Multiplicative.toAdd y, y.property⟩
      left_inv z := by rfl
      right_inv y := by rfl }
    rw [← Nat.card_congr e]
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), hker, Nat.card_zmod]
    norm_num
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : Finite U := Finite.of_injective (fun z : U => (z : V)) Subtype.val_injective
  let : Finite (V ⧸ U) := Finite.of_surjective U.mkQ U.mkQ_surjective
  let : Finite ((V ⧸ U) →ₗ[ZMod 2] U) :=
    Finite.of_injective (fun z => (z : (V ⧸ U) → U)) DFunLike.coe_injective
  let : Finite K := Finite.of_injective (fun z : K => z.1) Subtype.val_injective
  have hmapcard : Nat.card ((fixer U x).map (equiv U).toMonoidHom) = Nat.card (fixer U x) :=
    Subgroup.card_map_of_injective (equiv U).injective
  exact (hmapcard ▸ (Subgroup.card_le_of_le hle)).trans_eq hK

def dualFixer (U : Submodule (ZMod 2) V) (φ : Module.Dual (ZMod 2) V) :
    Subgroup (BinaryLinear.radical U) where
  carrier := {g | g.val.symm.dualMap φ = φ}
  one_mem' := by
    ext x
    change φ x = φ x
    rfl
  mul_mem' := by
    intro g h hg hh
    ext x
    change φ (h.val.symm (g.val.symm x)) = φ x
    have he := congrArg (fun f => f (g.val.symm x)) hh
    change φ (h.val.symm (g.val.symm x)) = φ (g.val.symm x) at he
    have he' := congrArg (fun f => f x) hg
    change φ (g.val.symm x) = φ x at he'
    exact he.trans he'
  inv_mem' := by
    intro g hg
    ext x
    change φ (g.val x) = φ x
    have he := congrArg (fun f => f (g.val x)) hg
    change φ (g.val.symm (g.val x)) = φ (g.val x) at he
    simpa only [g.val.symm_apply_apply] using he.symm

theorem card_dualFixer_le_sixteen [FiniteDimensional (ZMod 2) V]
    (U : Submodule (ZMod 2) V) (hV : Module.finrank (ZMod 2) V = 5)
    (hU : Module.finrank (ZMod 2) U = 3) {φ : Module.Dual (ZMod 2) V}
    (hφ : φ ∉ U.dualAnnihilator) :
    Nat.card (dualFixer U φ) ≤ 16 := by
  let qdim := V ⧸ U
  let pφ : U →ₗ[ZMod 2] ZMod 2 := φ.comp U.subtype
  have hpφ : pφ ≠ 0 := by
    intro hz
    apply hφ
    apply (Submodule.mem_dualAnnihilator _).mpr
    intro u hu
    have := LinearMap.congr_fun hz ⟨u, hu⟩
    simpa [pφ] using this
  have hex : ∃ u : U, pφ u ≠ 0 := by
    by_contra h
    push Not at h
    apply hpφ
    ext u
    exact h u
  obtain ⟨u, hu⟩ := hex
  have hu1 : pφ u = 1 := by
    exact (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) _ hu
  let ev : ((V ⧸ U) →ₗ[ZMod 2] U) →ₗ[ZMod 2]
      (V ⧸ U →ₗ[ZMod 2] ZMod 2) :=
    LinearMap.compRight (ZMod 2) pφ
  have hev : Function.Surjective ev := by
    intro k
    refine ⟨k.smulRight u, ?_⟩
    ext q
    simp [ev, LinearMap.compRight_apply, hu1]
  let K : Subgroup (Multiplicative ((V ⧸ U) →ₗ[ZMod 2] U)) :=
    BinaryNaturalDual.subgroupOrderIso ((ev).ker)
  have hle : (dualFixer U φ).map (equiv U).toMonoidHom ≤ K := by
    rintro y ⟨g, hg, rfl⟩
    change g.val.symm.dualMap φ = φ at hg
    change disp U g ∈ ev.ker
    rw [LinearMap.mem_ker]
    apply LinearMap.ext
    intro q
    induction q using Submodule.Quotient.induction_on with
    | _ x =>
      rw [LinearMap.compRight_apply]
      change pφ (disp U g (U.mkQ x)) = 0
      change φ (g.val x - x) = 0
      have he := LinearMap.congr_fun hg (g.val x)
      change φ (g.val.symm (g.val x)) = φ (g.val x) at he
      rw [g.val.symm_apply_apply] at he
      rw [map_sub, he]
      simp
  have hker : Module.finrank (ZMod 2) ev.ker = 4 := by
    have hr := ev.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hev, finrank_top] at hr
    simp only [Module.finrank_linearMap] at hr
    have hq : Module.finrank (ZMod 2) (V ⧸ U) = 2 := by
      have hsum := Submodule.finrank_quotient_add_finrank U
      rw [hV, hU] at hsum
      omega
    rw [hq, hU] at hr
    rw [Module.finrank_self] at hr
    omega
  have hK : Nat.card K = 16 := by
    let e : ev.ker ≃ K := {
      toFun z := ⟨Multiplicative.ofAdd z, z.property⟩
      invFun y := ⟨Multiplicative.toAdd y, y.property⟩
      left_inv z := by rfl
      right_inv y := by rfl }
    rw [← Nat.card_congr e]
    change Nat.card ev.ker = 16
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), hker, Nat.card_zmod]
    norm_num
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : Finite U := Finite.of_injective (fun z : U => (z : V)) Subtype.val_injective
  let : Finite (V ⧸ U) := Finite.of_surjective U.mkQ U.mkQ_surjective
  let : Finite ((V ⧸ U) →ₗ[ZMod 2] U) :=
    Finite.of_injective (fun z => (z : (V ⧸ U) → U)) DFunLike.coe_injective
  let : Finite K := Finite.of_injective (fun z : K => z.1) Subtype.val_injective
  have hmapcard : Nat.card ((dualFixer U φ).map (equiv U).toMonoidHom) = Nat.card (dualFixer U φ) :=
    Subgroup.card_map_of_injective (equiv U).injective
  exact (hmapcard ▸ (Subgroup.card_le_of_le hle)).trans_eq hK

theorem fixedSpace_hyperplane [FiniteDimensional (ZMod 2) V]
    (U : Submodule (ZMod 2) V) (hV : Module.finrank (ZMod 2) V = 5)
    (hU : Module.finrank (ZMod 2) U = 3)
    (A : Subgroup (BinaryLinear.GL V)) (hA : A ≤ BinaryLinear.radical U)
    (hidx : A.relIndex (BinaryLinear.radical U) = 2) :
    Representation.BinaryOffender.fixedSpace
        (BinaryNaturalDual.naturalDualRepresentation.comp A.subtype) ⊤ =
      U.prod U.dualAnnihilator := by
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : Finite (BinaryLinear.GL V) :=
    Finite.of_injective (fun g : BinaryLinear.GL V => (g : V → V)) DFunLike.coe_injective
  let : Finite A := Finite.of_injective (fun g : A => (g : BinaryLinear.GL V)) Subtype.val_injective
  let R := BinaryLinear.radical U
  let : Finite R := Finite.of_injective (fun g : R => (g : BinaryLinear.GL V)) Subtype.val_injective
  let hR : A ≤ R := hA
  have hcardA : Nat.card A = 32 := by
    have hm := Subgroup.relIndex_mul_relIndex (⊥ : Subgroup (BinaryLinear.GL V)) A R
      bot_le hR
    rw [Subgroup.relIndex_bot_left A, hidx] at hm
    have hRcard : Nat.card R = 64 := by simpa [R] using card_radical U hV hU
    rw [Subgroup.relIndex_bot_left R] at hm
    rw [hRcard] at hm
    omega
  have hfixer_contra {x : V} (hx : x ∉ U)
      (hfix : A.subgroupOf R ≤ fixer U x) : False := by
    let : Finite (fixer U x) :=
      Finite.of_injective (fun g : fixer U x => (g : R)) Subtype.val_injective
    have hc := Subgroup.card_le_of_le hfix
    rw [show Nat.card (A.subgroupOf R) = Nat.card A by
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR).toEquiv,
      hcardA] at hc
    have hsmall := card_fixer_le_eight U hV hU hx
    have hsmall' : Nat.card (fixer U x) ≤ 8 := by simpa [R] using hsmall
    have hc' : 32 ≤ Nat.card (fixer U x) := by
      simpa [hcardA, R] using hc
    exact (by omega)
  have hdual_contra {φ : Module.Dual (ZMod 2) V} (hf : φ ∉ U.dualAnnihilator)
      (hfix : A.subgroupOf R ≤ dualFixer U φ) : False := by
    let : Finite (dualFixer U φ) :=
      Finite.of_injective (fun g : dualFixer U φ => (g : R)) Subtype.val_injective
    have hc := Subgroup.card_le_of_le hfix
    rw [show Nat.card (A.subgroupOf R) = Nat.card A by
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR).toEquiv,
      hcardA] at hc
    have hsmall := card_dualFixer_le_sixteen U hV hU hf
    have hsmall' : Nat.card (dualFixer U φ) ≤ 16 := by simpa [R] using hsmall
    have hc' : 32 ≤ Nat.card (dualFixer U φ) := by
      simpa [hcardA, R] using hc
    exact (by omega)
  ext v
  change (∀ g : (⊤ : Subgroup A),
      BinaryNaturalDual.naturalDualRepresentation g.val v = v) ↔
      v.1 ∈ U ∧ v.2 ∈ U.dualAnnihilator
  constructor
  · intro hv
    have hx : v.1 ∈ U := by
      by_contra hx
      apply hfixer_contra hx
      intro g hg
      change g.val v.1 = v.1
      let ga : A := ⟨g, hg⟩
      simpa [ga] using congrArg Prod.fst (hv ⟨ga, trivial⟩)
    have hf : v.2 ∈ U.dualAnnihilator := by
      by_contra hf
      apply hdual_contra hf
      intro g hg
      change g.val.symm.dualMap v.2 = v.2
      let ga : A := ⟨g, hg⟩
      simpa [ga] using congrArg Prod.snd (hv ⟨ga, trivial⟩)
    exact ⟨hx, hf⟩
  · rintro ⟨hx, hf⟩ g
    apply Prod.ext
    · rw [BinaryNaturalDual.naturalDualRepresentation_apply]
      change (g.val : BinaryLinear.GL V) v.1 = v.1
      have gr : (g.val : BinaryLinear.GL V) ∈ BinaryLinear.radical U :=
        hA g.val.property
      exact gr.1 _ hx
    · ext x
      rw [BinaryNaturalDual.naturalDualRepresentation_apply]
      change ((g.val : BinaryLinear.GL V).symm.dualMap v.2) x = v.2 x
      have hd := (dual_fixed_radical_iff U (by
        intro he
        have hdim := hU
        rw [he, finrank_top] at hdim
        omega) v.2).mpr hf (g.val : BinaryLinear.GL V) (hA g.val.property)
      exact congrArg (fun f => f x) hd

def polarMap : BinaryNaturalDual.Space V →ₗ[ZMod 2]
    Module.Dual (ZMod 2) (BinaryNaturalDual.Space V) :=
  { toFun := fun v => (BinaryNaturalDual.quadratic.polarBilin v)
    map_add' := by
      intro v w
      apply LinearMap.ext
      intro z
      change (BinaryNaturalDual.quadratic.polarBilin (v + w)) z = _
      rw [map_add]
    map_smul' := by
      intro c v
      apply LinearMap.ext
      intro z
      change (BinaryNaturalDual.quadratic.polarBilin (c • v)) z = _
      rw [map_smul]
      rfl }

theorem polarMap_injective : Function.Injective (polarMap (V := V)) := by
  intro v w h
  apply sub_eq_zero.mp
  apply (BinaryNaturalDual.polar_nondegenerate (V := V)).1 (v - w)
  intro z
  have he := congrArg
    (fun f : Module.Dual (ZMod 2) (BinaryNaturalDual.Space V) => f z) h
  have hz' :
      BinaryNaturalDual.quadratic.polarBilin v z +
        BinaryNaturalDual.quadratic.polarBilin w z = 0 := by
    have he' : BinaryNaturalDual.quadratic.polarBilin v z =
        BinaryNaturalDual.quadratic.polarBilin w z := by
      simpa [polarMap] using he
    rw [he']
    simp
  simpa [polarMap, map_sub] using hz'

noncomputable def polarEquiv [FiniteDimensional (ZMod 2) V] :
    BinaryNaturalDual.Space V ≃ₗ[ZMod 2]
      Module.Dual (ZMod 2) (BinaryNaturalDual.Space V) :=
  LinearMap.linearEquivOfInjective (polarMap (V := V))
    (polarMap_injective (V := V)) (by rw [Subspace.dual_finrank_eq])

theorem polarMap_natural (g : BinaryLinear.GL V)
    (v : BinaryNaturalDual.Space V) :
    polarMap (BinaryNaturalDual.naturalDualRepresentation g v) =
      (BinaryNaturalDual.naturalDualRepresentation.dual g) (polarMap v) := by
  rw [Representation.dual_apply]
  apply LinearMap.ext
  intro w
  change BinaryNaturalDual.quadratic.polarBilin
      (BinaryNaturalDual.naturalDualRepresentation g v) w =
    BinaryNaturalDual.quadratic.polarBilin v
      (BinaryNaturalDual.naturalDualRepresentation g⁻¹ w)
  rw [BinaryNaturalDual.polar_apply, BinaryNaturalDual.polar_apply,
    BinaryNaturalDual.naturalDualRepresentation_apply,
    BinaryNaturalDual.naturalDualRepresentation_apply]
  simp only [LinearEquiv.dualMap_apply]
  have hInv : (g⁻¹ : BinaryLinear.GL V) = g.symm := rfl
  change v.2 (g.symm w.1) + w.2 (g v.1) =
    v.2 ((g⁻¹ : BinaryLinear.GL V) w.1) +
      w.2 ((g⁻¹ : BinaryLinear.GL V).symm v.1)
  rw [hInv, LinearEquiv.symm_symm]

theorem subspaceCommutator_le_prod [FiniteDimensional (ZMod 2) V]
    (U : Submodule (ZMod 2) V) (A : Subgroup (BinaryLinear.GL V))
    (hA : A ≤ BinaryLinear.radical U) :
    Representation.BinaryOffender.subspaceCommutator
        (BinaryNaturalDual.naturalDualRepresentation.comp A.subtype)
        ⊤ (⊤ : Subgroup A) ≤
      U.prod U.dualAnnihilator := by
  apply Submodule.span_le.mpr
  rintro _ ⟨g, hg, w, hw, rfl⟩
  rw [MonoidHom.comp_apply, BinaryNaturalDual.naturalDualRepresentation_apply]
  change ((g : BinaryLinear.GL V) w.1 - w.1,
      (g : BinaryLinear.GL V).symm.dualMap w.2 - w.2) ∈
    U.prod U.dualAnnihilator
  apply Submodule.mem_prod.mpr
  constructor
  · exact (hA g.property).2 _
  · apply (Submodule.mem_dualAnnihilator _).mpr
    intro x hx
    change w.2 ((g : BinaryLinear.GL V).symm x) - w.2 x = 0
    have hfix : (g : BinaryLinear.GL V).symm x = x :=
      ((BinaryLinear.radical U).inv_mem (hA g.property)).1 x hx
    rw [hfix, sub_self]

theorem subspaceCommutator_of_fixedSpace [FiniteDimensional (ZMod 2) V]
    (U : Submodule (ZMod 2) V) (hV : Module.finrank (ZMod 2) V = 5)
    (A : Subgroup (BinaryLinear.GL V)) (hA : A ≤ BinaryLinear.radical U)
    (hfixed : Representation.BinaryOffender.fixedSpace
      (naturalDualRepresentation.comp A.subtype) ⊤ = U.prod U.dualAnnihilator) :
    Representation.BinaryOffender.subspaceCommutator
        (BinaryNaturalDual.naturalDualRepresentation.comp A.subtype)
        ⊤ (⊤ : Subgroup A) =
      U.prod U.dualAnnihilator := by
  let ρ : Representation (ZMod 2) A (BinaryNaturalDual.Space V) :=
    BinaryNaturalDual.naturalDualRepresentation.comp A.subtype
  let E := polarEquiv (V := V)
  have hE : ∀ g v, E (ρ g v) = ρ.dual g (E v) := by
    intro g v
    change polarMap (BinaryNaturalDual.naturalDualRepresentation g.val v) = _
    simpa [ρ, E, polarEquiv] using polarMap_natural (g.val) v
  have hmap := Representation.BinaryOffender.fixedSpace_map_equivariant
    ρ ρ.dual (MonoidHom.id A) E hE (⊤ : Subgroup A)
  have hfdim : Module.finrank (ZMod 2)
      (Representation.BinaryOffender.fixedSpace ρ.dual ⊤) = 5 := by
    have hm := LinearEquiv.finrank_map_eq E
      (Representation.BinaryOffender.fixedSpace ρ (⊤ : Subgroup A))
    have hmap' : (Representation.BinaryOffender.fixedSpace ρ ⊤).map E.toLinearMap =
        Representation.BinaryOffender.fixedSpace ρ.dual ⊤ := by
      simpa using hmap
    rw [hmap'] at hm
    rw [hfixed] at hm
    simpa [finrank_prod_dualAnnihilator U, hV] using hm
  have hinv : Representation.invariants ρ.dual =
      Representation.invariants (ρ.dual.comp (⊤ : Subgroup A).subtype) := by
    ext f
    rw [Representation.mem_invariants, Representation.mem_invariants]
    constructor
    · intro hf g
      exact hf g.val
    · intro hf g
      exact hf ⟨g, Subgroup.mem_top _⟩
  have hqdim : Module.finrank (ZMod 2)
      (Module.Dual (ZMod 2) (BinaryNaturalDual.Space V) ⧸
        Representation.BinaryOffender.fixedSpace ρ.dual ⊤) = 5 := by
    have hs := (Representation.BinaryOffender.fixedSpace ρ.dual ⊤).finrank_quotient_add_finrank
    have hspace : Module.finrank (ZMod 2) (BinaryNaturalDual.Space V) = 10 := by
      rw [Module.finrank_prod, hV, Subspace.dual_finrank_eq, hV]
    rw [Subspace.dual_finrank_eq, hfdim, hspace] at hs
    omega
  have hcdim : Module.finrank (ZMod 2)
      (Representation.Coinvariants.ker ρ) = 5 := by
    have hc := Representation.finrank_quotient_dual_invariants_eq_commutator ρ
    have hqdim' : Module.finrank (ZMod 2)
        (Module.Dual (ZMod 2) (BinaryNaturalDual.Space V) ⧸ ρ.dual.invariants) = 5 := by
      rw [hinv]
      exact hqdim
    have hc' : Module.finrank (ZMod 2)
        (Module.Dual (ZMod 2) (BinaryNaturalDual.Space V) ⧸
          ρ.dual.invariants) =
        Module.finrank (ZMod 2) (Representation.Coinvariants.ker ρ) := by
      simpa [Representation.BinaryOffender.fixedSpace] using hc
    exact hc' ▸ hqdim'
  have hcommdim : Module.finrank (ZMod 2)
      (Representation.BinaryOffender.subspaceCommutator ρ ⊤ (⊤ : Subgroup A)) = 5 := by
    have hker : Representation.Coinvariants.ker ρ =
        Representation.BinaryOffender.subspaceCommutator ρ ⊤ (⊤ : Subgroup A) := by
      apply le_antisymm
      · rw [Representation.Coinvariants.ker]
        apply Submodule.span_le.mpr
        rintro _ ⟨⟨g, w⟩, rfl⟩
        exact Submodule.subset_span ⟨g, Subgroup.mem_top _, w,
          Submodule.mem_top, rfl⟩
      · rw [Representation.BinaryOffender.subspaceCommutator]
        apply Submodule.span_le.mpr
        rintro _ ⟨g, hg, w, hw, rfl⟩
        exact Submodule.subset_span ⟨(g, w), rfl⟩
    rw [← hker]
    exact hcdim
  apply Submodule.eq_of_le_of_finrank_eq
    (subspaceCommutator_le_prod U A hA)
  rw [hcommdim, finrank_prod_dualAnnihilator U, hV]

instance radicalActor_isElementaryAbelian (U : Submodule (ZMod 2) X) :
    IsElementaryAbelian 2 (radicalActor U) := by
  exact IsElementaryAbelian.map (MulAut.conj : G →* M)

theorem radicalActor_card (U : Submodule (ZMod 2) X)
    (hU : Module.finrank (ZMod 2) U = 3) :
    Nat.card (radicalActor U) = 64 := by
  rw [radicalActor, Subgroup.card_map_of_injective
    (MulAut.conj_injective_of_center_eq_bot center_eq_bot)]
  exact card_radical U (by simp [X]) hU

theorem radicalActor_hyperplane_card (U : Submodule (ZMod 2) X)
    (hU : Module.finrank (ZMod 2) U = 3)
    (A : Subgroup M) (hA : A ≤ radicalActor U)
    (hidx : A.relIndex (radicalActor U) = 2) : Nat.card A = 32 := by
  have hm := Subgroup.relIndex_mul_relIndex (⊥ : Subgroup M) A
    (radicalActor U) bot_le hA
  rw [Subgroup.relIndex_bot_left A, hidx] at hm
  rw [Subgroup.relIndex_bot_left (radicalActor U), radicalActor_card U hU] at hm
  omega

theorem fixedSpace_radicalActor_hyperplane (d : CoordinateAction 5)
    (U : Submodule (ZMod 2) X) (hU : Module.finrank (ZMod 2) U = 3)
    (A : Subgroup M) (hA : A ≤ radicalActor U)
    (hidx : A.relIndex (radicalActor U) = 2) :
    Representation.BinaryOffender.fixedSpace d.representation A =
      U.prod U.dualAnnihilator := by
  let B := A.comap (MulAut.conj : G →* M)
  have hmap : B.map (MulAut.conj : G →* M) = A :=
    Subgroup.map_comap_eq_self (hA.trans (radicalActor_le_inner U))
  have hB : B ≤ radical U := by
    apply (Subgroup.map_le_map_iff_of_injective
      (MulAut.conj_injective_of_center_eq_bot center_eq_bot)).mp
    rw [hmap]
    exact hA
  have hidxB : B.relIndex (radical U) = 2 := by
    have hm := Subgroup.relIndex_map_map_of_injective B (radical U)
      (MulAut.conj_injective_of_center_eq_bot center_eq_bot)
    have hradmap : (radical U).map (MulAut.conj : G →* M) = radicalActor U := rfl
    rw [hmap, hradmap, hidx] at hm
    exact hm.symm
  rw [← hmap, fixedSpace_inner_image d B]
  have hfix := fixedSpace_hyperplane U (by simp [X]) hU B hB hidxB
  have htopinv :
      Representation.invariants
          ((naturalDualRepresentation.comp B.subtype).comp
            (⊤ : Subgroup B).subtype) =
        Representation.invariants (naturalDualRepresentation.comp B.subtype) := by
    ext v
    simp only [Representation.mem_invariants]
    constructor
    · intro hv g
      simpa using hv ⟨g, Subgroup.mem_top _⟩
    · intro hv g
      simpa using hv g.1
  rw [Representation.BinaryOffender.fixedSpace] at ⊢
  rw [← htopinv]
  exact hfix

theorem subspaceCommutator_radicalActor (d : CoordinateAction 5)
    (U : Submodule (ZMod 2) X) (hU : Module.finrank (ZMod 2) U = 3) :
    Representation.BinaryOffender.subspaceCommutator d.representation ⊤
        (radicalActor U) = U.prod U.dualAnnihilator := by
  have hUb : U ≠ ⊥ := by
    intro h
    rw [h] at hU
    simp at hU
  have hUt : U ≠ ⊤ := by
    intro h
    rw [h] at hU
    simp [X] at hU
  have hcomm := subspaceCommutator_of_fixedSpace U (by simp [X])
    (radical U) le_rfl (fixedSpace_radical U hUb hUt)
  have hcommG : Representation.BinaryOffender.subspaceCommutator
      naturalDualRepresentation ⊤ (radical U) = U.prod U.dualAnnihilator := by
    simpa [Representation.BinaryOffender.subspaceCommutator] using hcomm
  have htransport := Representation.BinaryOffender.subspaceCommutator_map_embedding
    (naturalDualRepresentation : Representation (ZMod 2) G (Space X))
    d.representation (MulAut.conj : G →* M) LinearMap.id
    (fun g v => (d.on_inner g v).symm) (radical U)
    (⊤ : Submodule (ZMod 2) (Space X))
  rw [Submodule.map_id] at htransport
  have hradmap : (radical U).map (MulAut.conj : G →* M) = radicalActor U := rfl
  rw [hradmap] at htransport
  have hres := htransport.symm.trans hcommG
  simpa only [Submodule.map_id] using hres

theorem subspaceCommutator_radicalActor_hyperplane (d : CoordinateAction 5)
    (U : Submodule (ZMod 2) X) (hU : Module.finrank (ZMod 2) U = 3)
    (A : Subgroup M) (hA : A ≤ radicalActor U)
    (hidx : A.relIndex (radicalActor U) = 2) :
    Representation.BinaryOffender.subspaceCommutator d.representation ⊤ A =
      U.prod U.dualAnnihilator := by
  let B := A.comap (MulAut.conj : G →* M)
  have hmap : B.map (MulAut.conj : G →* M) = A :=
    Subgroup.map_comap_eq_self (hA.trans (radicalActor_le_inner U))
  have hB : B ≤ radical U := by
    apply (Subgroup.map_le_map_iff_of_injective
      (MulAut.conj_injective_of_center_eq_bot center_eq_bot)).mp
    rw [hmap]
    exact hA
  have hidxB : B.relIndex (radical U) = 2 := by
    have hm := Subgroup.relIndex_map_map_of_injective B (radical U)
      (MulAut.conj_injective_of_center_eq_bot center_eq_bot)
    have hradmap : (radical U).map (MulAut.conj : G →* M) = radicalActor U := rfl
    rw [hmap, hradmap, hidx] at hm
    exact hm.symm
  have hcomm := subspaceCommutator_of_fixedSpace U (by simp [X]) B hB
    (fixedSpace_hyperplane U (by simp [X]) hU B hB hidxB)
  have hcommB : Representation.BinaryOffender.subspaceCommutator
      naturalDualRepresentation ⊤ B = U.prod U.dualAnnihilator := by
    simpa [Representation.BinaryOffender.subspaceCommutator] using hcomm
  have htransport := Representation.BinaryOffender.subspaceCommutator_map_embedding
    (naturalDualRepresentation : Representation (ZMod 2) G (Space X))
    d.representation (MulAut.conj : G →* M) LinearMap.id
    (fun g v => (d.on_inner g v).symm) B (⊤ : Submodule (ZMod 2) (Space X))
  rw [Submodule.map_id] at htransport
  rw [hmap] at htransport
  have hres := htransport.symm.trans hcommB
  simpa only [Submodule.map_id] using hres

theorem finrank_fixedSpace_radicalActor_hyperplane (d : CoordinateAction 5)
    (U : Submodule (ZMod 2) X) (hU : Module.finrank (ZMod 2) U = 3)
    (A : Subgroup M) (hA : A ≤ radicalActor U)
    (hidx : A.relIndex (radicalActor U) = 2) :
    Module.finrank (ZMod 2)
        (Representation.BinaryOffender.fixedSpace d.representation A) = 5 := by
  rw [fixedSpace_radicalActor_hyperplane d U hU A hA hidx,
    finrank_prod_dualAnnihilator]
  simp

theorem finrank_subspaceCommutator_radicalActor_hyperplane (d : CoordinateAction 5)
    (U : Submodule (ZMod 2) X) (hU : Module.finrank (ZMod 2) U = 3)
    (A : Subgroup M) (hA : A ≤ radicalActor U)
    (hidx : A.relIndex (radicalActor U) = 2) :
    Module.finrank (ZMod 2)
        (Representation.BinaryOffender.subspaceCommutator d.representation ⊤ A) = 5 := by
  rw [subspaceCommutator_radicalActor_hyperplane d U hU A hA hidx,
    finrank_prod_dualAnnihilator]
  simp

theorem hyperplane_radical_formulas (d : CoordinateAction 5)
    (U : Submodule (ZMod 2) X) (hU : Module.finrank (ZMod 2) U = 3)
    (A : Subgroup M) (hA : A ≤ radicalActor U)
    (hidx : A.relIndex (radicalActor U) = 2) :
    Representation.BinaryOffender.fixedSpace d.representation A =
        Representation.BinaryOffender.subspaceCommutator d.representation ⊤ A ∧
      Representation.BinaryOffender.subspaceCommutator d.representation ⊤ A =
        Representation.BinaryOffender.fixedSpace d.representation (radicalActor U) ∧
      Representation.BinaryOffender.fixedSpace d.representation (radicalActor U) =
        Representation.BinaryOffender.subspaceCommutator d.representation ⊤
          (radicalActor U) ∧
      Representation.BinaryOffender.subspaceCommutator d.representation ⊤
          (radicalActor U) = U.prod U.dualAnnihilator := by
  have hfixA := fixedSpace_radicalActor_hyperplane d U hU A hA hidx
  have hcommA := subspaceCommutator_radicalActor_hyperplane d U hU A hA hidx
  have hfixR := fixedSpace_radicalActor d U (by
    intro h
    rw [h] at hU
    simp at hU) (by
    intro h
    rw [h] at hU
    simp [X] at hU)
  have hcommR := subspaceCommutator_radicalActor d U hU
  exact ⟨hfixA.trans hcommA.symm, hcommA.trans hfixR.symm,
    hfixR.trans hcommR.symm, hcommR⟩

end BinaryNaturalDual.FiveActors
