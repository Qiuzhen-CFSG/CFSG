module
public import Theory.GroupTheory.TransvectionDualIrreducible
public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Theory.GroupTheory.Commutator.SimpleSubnormal
public import Theory.GroupTheory.SylowCentralizerComplement

/-!
# Fixed cosets for a full binary transvection pairing

A nondegenerate binary pairing identifies every central displacement character
of an actor with an actual vector in its seed. Correcting by that vector gives
a fixed coset representative. Perfectness propagates fixed points from a
normal actor to the perfect overgroup; averaging over Sylow cosets then puts
those fixed points in the original binary displacement layer.

The full action kernel and the central line are retained. These elementary
pairing and averaging arguments supply the fixed-subgroup step of
Aschbacher–Smith 8.2.12, printed p.722, without classifying all extensions.
-/

public noncomputable section
open Subgroup
open scoped commutatorElement IsMulCommutative
namespace Theory.GroupTheory
set_option backward.isDefEq.respectTransparency false
variable {G : Type*} [Group G]

/-- A full binary transvection pairing removes a central commutator by an
actual element of the original seed. The entire action kernel is retained. -/
theorem transvection_fixed_coset
    {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] [FiniteDimensional (ZMod 2) M]
    (W X K : Subgroup G) (z : G) (hz : orderOf z = 2)
    (qW : W →* Multiplicative M) (hqW : Function.Surjective qW)
    (qX : X →* Multiplicative (Module.Dual (ZMod 2) M))
    (hqX : Function.Surjective qX) (hkerX : qX.ker = K.subgroupOf X)
    (hpair : ∀ (x : X) (w : W), ⁅(x : G),(w : G)⁆ =
      z ^ ((qX x).toAdd (qW w).toAdd).val)
    (hXZ : X ≤ centralizer ({z} : Set G))
    (d : G) (hd : ∀ x : X, ⁅(x : G),d⁆ ∈ zpowers z)
    (hKd : d ∈ centralizer (K : Set G)) :
    ∃ w ∈ W, w⁻¹*d ∈ centralizer (X : Set G) := by
  let eZ : zpowers z ≃* Multiplicative (ZMod 2) :=
    mulEquivOfCyclicCardEq (by rw [Nat.card_zpowers,hz]; simp)
  have heZ (a : ZMod 2) : eZ ⟨z^a.val,pow_mem (mem_zpowers z) _⟩ = Multiplicative.ofAdd a := by
    have hne : z ≠ 1 := by intro he; simp [he] at hz
    have hnon : (eZ ⟨z,mem_zpowers z⟩).toAdd ≠ 0 := by
      intro hh
      have hh' : eZ ⟨z,mem_zpowers z⟩ = 1 := hh
      exact hne (congrArg Subtype.val (eZ.injective (hh'.trans eZ.map_one.symm)))
    have hone : (eZ ⟨z,mem_zpowers z⟩).toAdd = 1 := by
      generalize (eZ ⟨z,mem_zpowers z⟩).toAdd = b at *
      fin_cases b <;> simp_all
    fin_cases a
    · simp
    · change eZ ⟨z^1,_⟩ = Multiplicative.ofAdd 1
      apply Multiplicative.toAdd.injective
      simpa only [pow_one,toAdd_ofAdd] using hone
  let c : X →* zpowers z := {
    toFun := fun x => ⟨⁅(x : G),d⁆,hd x⟩
    map_one' := Subtype.ext (by simp)
    map_mul' := by
      intro a b
      apply Subtype.ext
      change ⁅(a : G)*(b : G),d⁆ = ⁅(a : G),d⁆*⁅(b : G),d⁆
      rw [commutatorElement_mul_left_eq_conj_mul]
      have ha : (a : G) ∈ centralizer (zpowers z : Set G) := by
        simpa only [zpowers_eq_closure,centralizer_closure] using hXZ a.property
      rw [←ha _ (hd b),mul_inv_cancel_right]
      exact congrArg Subtype.val (mul_comm (⟨⁅(b : G),d⁆,hd b⟩ : zpowers z) ⟨⁅(a : G),d⁆,hd a⟩) }
  let cZ := eZ.toMonoidHom.comp c
  have hkc : qX.ker ≤ cZ.ker := by
    intro x hx
    have hxK : (x : G) ∈ K := hkerX.le hx
    change eZ (c x)=1
    have hc : c x=1 := Subtype.ext (commutatorElement_eq_one_iff_mul_comm.mpr (hKd x hxK))
    rw [hc,map_one]
  let f := qX.liftOfSurjective hqX ⟨cZ,hkc⟩
  let fa : Module.Dual (ZMod 2) M →+ ZMod 2 := {
    toFun := fun a => (f (Multiplicative.ofAdd a)).toAdd
    map_zero' := f.map_one
    map_add' := fun a b => f.map_mul _ _ }
  let ell := fa.toZModLinearMap 2
  obtain ⟨w,hw⟩ := hqW (Multiplicative.ofAdd ((Module.evalEquiv (ZMod 2) M).symm ell))
  have he (x : X) : ⁅(x : G),(w : G)⁆ = ⁅(x : G),d⁆ := by
    have hf : f (qX x) = cZ x := MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _
    have hval : (qX x).toAdd (qW w).toAdd = (cZ x).toAdd := by
      rw [hw]
      exact (Module.apply_evalEquiv_symm_apply (ZMod 2) M _ ell).trans (congrArg Multiplicative.toAdd hf)
    have hh : (⟨⁅(x : G),(w : G)⁆,by rw [hpair]; exact pow_mem (mem_zpowers z) _⟩ : zpowers z) = c x := by
      apply eZ.injective
      rw [show (⟨⁅(x : G),(w : G)⁆,_⟩ : zpowers z) =
        ⟨z^((qX x).toAdd (qW w).toAdd).val,pow_mem (mem_zpowers z) _⟩ from Subtype.ext (hpair x w),heZ]
      exact congrArg Multiplicative.ofAdd hval
    exact congrArg Subtype.val hh
  refine ⟨w,w.property,?_⟩
  intro x hx
  have hh := he ⟨x,hx⟩
  rw [commutatorElement_def,commutatorElement_def] at hh
  have hconj : x*d*x⁻¹ = (x*(w : G)*x⁻¹)*(w : G)⁻¹*d := by
    exact (mul_inv_eq_iff_eq_mul.mp hh.symm)
  apply mul_inv_eq_iff_eq_mul.mp
  calc
    x*((w : G)⁻¹*d)*x⁻¹ = (x*(w : G)*x⁻¹)⁻¹*(x*d*x⁻¹) := by group
    _ = (w : G)⁻¹*d := by rw [hconj]; group

/-- Perfectness propagates centralization from a normal actor whenever its
fixed subgroup in the displacement layer is central in the perfect group. -/
theorem centralizer_core_le_of_perfect
    (Q V R X Z : Subgroup G) [Group.IsPerfect R]
    (hRQ : R ≤ normalizer (Q : Set G)) (hRX : R ≤ normalizer (X : Set G))
    (hcomm : ⁅Q,R⁆ ≤ V) (hfix : V ⊓ centralizer (X : Set G) ≤ Z)
    (hZR : Z ≤ centralizer (R : Set G)) :
    Q ⊓ centralizer (X : Set G) ≤ centralizer (R : Set G) := by
  let A := Q ⊓ centralizer (X : Set G)
  have hRA : R ≤ normalizer (A : Set G) :=
    (le_inf hRQ (hRX.trans (normalizer_le_normalizer_centralizer X))).trans
      inf_normalizer_le_normalizer_inf
  have hc : ⁅A,R⁆ ≤ Z := (le_inf
    ((commutator_mono inf_le_left le_rfl).trans hcomm)
    ((le_normalizer_iff_commutator_le_left.mp hRA).trans inf_le_right)).trans hfix
  exact commutator_eq_bot_iff_le_centralizer.mp
    (commutator_eq_bot_of_iterated_eq_bot A R
      (commutator_eq_bot_iff_le_centralizer.mpr (hc.trans hZR)))

/-- Sylow averaging puts a point-residual fixed element in the original binary
layer when the full Sylow centralizer of the component is trivial. -/
theorem core_centralizer_le_of_sylow
    (L V Q R T : Subgroup G) [Finite L] [IsElementaryAbelian 2 V]
    (hLV : L ≤ normalizer (V : Set G)) (hVT : V ≤ T) (hQT : Q ≤ T)
    (hcomm : ⁅L,Q⁆ ≤ V) (hTC : T ⊓ centralizer (L : Set G) = ⊥)
    (S : Sylow 2 L) (hSR : (S : Subgroup L).map L.subtype ≤ R) :
    Q ⊓ centralizer (R : Set G) ≤ V := by
  intro d hd
  obtain ⟨v,hv,hvc⟩ := fixed_coset_of_sylow L V hLV
    (fun v hv => elemPow_eq_one_of_isElementaryAbelian (p := 2) v hv) S d
    (fun l hl => hcomm (commutator_mem_commutator hl hd.1))
    (fun l hl => hd.2 l (hSR (mem_map_of_mem L.subtype hl)))
  have he : v*d=1 := mem_bot.mp (hTC ▸ ⟨T.mul_mem (hVT hv) (hQT hd.1),hvc⟩)
  have he' : d=v⁻¹ := by simpa only [inv_mul_cancel_left,mul_one] using congrArg (fun x => v⁻¹*x) he
  exact he' ▸ V.inv_mem hv

end Theory.GroupTheory
