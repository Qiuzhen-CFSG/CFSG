module

public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Theory.ElementaryAbelian.Basic
public import Mathlib.Algebra.Field.ZMod
public import Theory.AtlasPort.LinearGroups.G2.Torus
public import Theory.AtlasPort.LinearGroups.G2.WeylMaps
public import Theory.GroupTheory.QuasithinBasic

/-!
# Two concrete local normalizers in G₂(3)

The longest Weyl element and the binary part of the split torus give an
embedded elementary abelian subgroup of order eight in the actual ternary
split-octonion automorphism group. The embedding uses three binary coordinates;
multiplication and injectivity are checked on the octonion basis by kernel
reduction. The first torus involution is nonidentity and has square one.

The two subgroups used for the small-model local calculation are the
normalizer of that involution line and the normalizer of the elementary eight.
Both are two-local, and the first is the involution centralizer. This module
does not assert that they cover all two-locals, compute their orders, or
identify their two-cores; those are separate local-structure assertions.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, Theorem
0.1.2(4), printed pp.3–4 and 481–482; the two local configurations are described
in §I.4, printed p.417. Root and torus conventions come from the licensed ATLAS
port; see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

@[expose] public section

namespace Atlas.G2.TernaryLocals
open Atlas.SplitOctonion
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

private theorem model_ext (g h : Model (ZMod 3))
    (he : ∀ i j, g.val (basisVector i) j = h.val (basisVector i) j) : g = h := by
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  exact linearMap_ext _ _ (fun i => funext (he i))

/-- The longest Weyl element in the actual octonion model. -/
def longest : Model (ZMod 3) := (weylR * weylS)^3
abbrev Parameters := Multiplicative (Fin 3 → ZMod 2)

def evaluate (a : Parameters) : Model (ZMod 3) :=
  torus ((-1 : (ZMod 3)ˣ)^(a.toAdd 0).val)
    ((-1 : (ZMod 3)ˣ)^(a.toAdd 1).val) * longest^(a.toAdd 2).val

def embedding : Parameters →* Model (ZMod 3) where
  toFun := evaluate
  map_one' := by
    apply model_ext
    exact (by decide +kernel : ∀ i j,
      (evaluate 1).val (basisVector i) j = (1 : Model (ZMod 3)).val (basisVector i) j)
  map_mul' a b := by
    apply model_ext
    exact (by decide +kernel : ∀ (a b : Parameters) i j,
      (evaluate (a*b)).val (basisVector i) j =
      (evaluate a * evaluate b).val (basisVector i) j) a b

theorem embedding_injective : Function.Injective embedding := by
  intro a b h
  have hc := congrArg (fun g : Model (ZMod 3) => g.val (basisVector 0)) h
  have hd := congrArg (fun g : Model (ZMod 3) => g.val (basisVector 3)) h
  have he := congrArg (fun g : Model (ZMod 3) => g.val (basisVector 1)) h
  change a.toAdd = b.toAdd
  apply funext
  exact (by decide +kernel : ∀ (a b : Parameters),
    (∀ j, (evaluate a).val (basisVector 0) j = (evaluate b).val (basisVector 0) j) →
    (∀ j, (evaluate a).val (basisVector 3) j = (evaluate b).val (basisVector 3) j) →
    (∀ j, (evaluate a).val (basisVector 1) j = (evaluate b).val (basisVector 1) j) →
    ∀ k, a.toAdd k = b.toAdd k) a b (congrFun hc) (congrFun hd) (congrFun he)

/-- The image of the three binary torus/Weyl parameters. -/
def elementary : Subgroup (Model (ZMod 3)) := embedding.range

noncomputable def elementaryEquiv : Parameters ≃* elementary :=
  MonoidHom.ofInjective embedding_injective

theorem card_elementary : Nat.card elementary = 8 := by
  rw [← Nat.card_congr elementaryEquiv.toEquiv]
  change Nat.card (Fin 3 → ZMod 2) = 8
  simp

instance elementary_isElementaryAbelian : IsElementaryAbelian 2 elementary where
  is_comm := ⟨by
    rintro ⟨_,a,rfl⟩ ⟨_,b,rfl⟩
    apply Subtype.ext
    change embedding a * embedding b = embedding b * embedding a
    rw [← map_mul, ← map_mul, mul_comm]⟩
  exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by
    rintro ⟨_,a,rfl⟩
    apply Subtype.ext
    change embedding a ^ 2 = 1
    rw [← map_pow]
    have h : a^2=1 := by
      rw [pow_two]
      change (fun i => a.toAdd i + a.toAdd i) = (fun _ => 0)
      exact funext (fun i => (by decide +kernel : ∀ x : ZMod 2, x+x=0) (a.toAdd i))
    rw [h, map_one])

def involution : Model (ZMod 3) := torus (-1) 1

theorem involution_sq : involution ^ 2 = 1 := by
  apply model_ext
  exact (by decide +kernel : ∀ i j,
    (involution ^ 2).val (basisVector i) j = (1 : Model (ZMod 3)).val (basisVector i) j)

theorem involution_ne_one : involution ≠ 1 := by
  intro h
  have he := congrArg (fun g : Model (ZMod 3) => g.val (basisVector 0) 0) h
  exact (by decide +kernel : involution.val (basisVector 0) 0 ≠
    (1 : Model (ZMod 3)).val (basisVector 0) 0) he

/-- The involution-line normalizer and elementary-eight normalizer. -/
def localSubgroup : Bool → Subgroup (Model (ZMod 3))
  | false => Subgroup.normalizer (Subgroup.zpowers involution : Set (Model (ZMod 3)))
  | true => Subgroup.normalizer (elementary : Set (Model (ZMod 3)))

/-- Both specified groups are actual normalizers of nonidentity two-groups. -/
theorem localSubgroup_isTwoLocal (i : Bool) : IsTwoLocal (localSubgroup i) := by
  cases i
  · have hP := IsElementaryAbelian.zpowers_of_pow_eq_one involution_sq
    let := hP
    exact ⟨Subgroup.zpowers involution,
      fun h => involution_ne_one (Subgroup.zpowers_eq_bot.mp h),
      IsElementaryAbelian.isPGroup 2 _, rfl⟩
  · have hE : elementary ≠ ⊥ := by
      intro h
      have he := card_elementary
      simp [h] at he
    exact ⟨elementary, hE, IsElementaryAbelian.isPGroup 2 _, rfl⟩

/-- In the order-two case the normalizer is the element centralizer. -/
theorem localSubgroup_false :
    localSubgroup false = Subgroup.centralizer ({involution} : Set (Model (ZMod 3))) :=
  Subgroup.normalizer_zpowers_eq_centralizer_of_order_two involution
    (orderOf_eq_prime involution_sq involution_ne_one)

end Atlas.G2.TernaryLocals
