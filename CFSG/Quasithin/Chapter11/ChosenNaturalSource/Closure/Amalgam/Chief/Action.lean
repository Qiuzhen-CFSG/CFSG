module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Centralization
public import Theory.Representation.BinaryOffender.EmbeddedFixedIndex
public import Theory.Representation.BinaryOffender.SectionLinear
public import Theory.Representation.BinaryOffender.CommutatorRank

/-!
# The actual odd-pair representation

The actor is (KT)^g and the module is Additive U^g, where U is the
KT-closure of V. The representation is literal left conjugation, and its
kernel is the relative ambient centralizer. OddPair.axis bounds the index
of the fixed subgroup by two, hence bounds every seed displacement by one.
OddPair.moves_closure gives nontrivial action on the whole module.

This does not assert that the motion survives on a chief factor.
Source: Aschbacher--Smith, 11.5.8, printed p.784. Left conjugation by g
corresponds to the source's right-conjugation exponent g inverse.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Chief
open Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V} (E : Closure.Geometry D) (g : G)

def actor : Subgroup G := (KT E).map (MulAut.conj g).toMonoidHom
def closure : Subgroup G := (localClosure E).map (MulAut.conj g).toMonoidHom

theorem closure_le_actor : closure E g ≤ actor E g :=
  map_mono (conjugateSpanBy_le_self (V_le_KT E))

theorem normalizes : actor E g ≤ normalizer (closure E g : Set G) :=
  (map_mono (le_normalizer_conjugateSpanBy V (KT E))).trans
    ((localClosure E).le_normalizer_map (MulAut.conj g).toMonoidHom)

theorem relative_normal : ((closure E g).subgroupOf (actor E g)).Normal :=
  (normal_subgroupOf_iff_le_normalizer (closure_le_actor E g)).mpr (normalizes E g)

instance closure_elementary [IsElementaryAbelian 2 (localClosure E)] :
    IsElementaryAbelian 2 (closure E g) := IsElementaryAbelian.map _

variable [IsElementaryAbelian 2 (localClosure E)]

def action : Representation (ZMod 2) (actor E g) (Additive (closure E g)) where
  toFun a := ((closure E g).normalizerMonoidHom
    (inclusion (normalizes E g) a)).toMonoidHom.toAdditive.toZModLinearMap 2
  map_one' := by
    apply LinearMap.ext
    intro v
    apply Additive.toMul.injective
    apply Subtype.ext
    change (1 : G) * v.toMul * 1⁻¹ = v.toMul
    simp
  map_mul' a b := by
    apply LinearMap.ext
    intro v
    apply Additive.toMul.injective
    apply Subtype.ext
    change (a : G) * b * v.toMul * ((a : G) * b)⁻¹ =
      a * (b * v.toMul * (b : G)⁻¹) * (a : G)⁻¹
    group

theorem action_apply (a : actor E g) (u : Additive (closure E g)) :
    ((action E g a u).toMul : G) = a * u.toMul * (a : G)⁻¹ := rfl

theorem action_kernel : (action E g).ker =
    (centralizer (closure E g : Set G)).subgroupOf (actor E g) := by
  ext a
  constructor
  · intro ha u hu
    have he := congrArg (fun v : Additive (closure E g) => (v.toMul : G))
      (LinearMap.congr_fun ha (Additive.ofMul (⟨u,hu⟩ : closure E g)))
    change (a : G) * u * (a : G)⁻¹ = u at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  · intro ha
    apply LinearMap.ext
    intro u
    apply Additive.toMul.injective
    apply Subtype.ext
    change (a : G) * u.toMul * (a : G)⁻¹ = u.toMul
    have hc : (u.toMul : G) * a = (a : G) * u.toMul := ha _ u.toMul.property
    rw [← hc, mul_inv_cancel_right]

def seed (p : OddPair E g) : V →* actor E g := inclusion p.seed_le_actor

theorem seed_moves (p : OddPair E g) : ¬ (seed E g p).range ≤ (action E g).ker := by
  intro hk
  apply p.moves_closure
  apply commutator_eq_bot_iff_le_centralizer.mpr
  intro v hv
  have hm := hk (show seed E g p ⟨v,hv⟩ ∈ (seed E g p).range from ⟨⟨v,hv⟩,rfl⟩)
  rw [action_kernel] at hm
  exact hm

theorem fixed_index (p : OddPair E g) :
    (centralizer (V : Set G)).relIndex (closure E g) =
      2 ^ fixedCodim (action E g) (seed E g p).range := by
  let j : Multiplicative (Additive (closure E g)) →* G :=
    { toFun := fun x => x.toAdd.toMul.val
      map_one' := rfl
      map_mul' _ _ := rfl }
  exact embedded_centralizer_index (action E g) (closure E g) V j
    (fun _ _ he => Subtype.ext he) (by ext x; simp [j]) (seed E g p)
      (fun _ _ => rfl)

theorem seed_fixedCodim_le_one (h : LocalInputs E) (hab : IsMulCommutative E.W)
    (hs : letI := D.elementary; ChapterE.globalS V = (E.input.field.degree : ℕ∞))
    (p : OddPair E g) : fixedCodim (action E g) (seed E g p).range ≤ 1 := by
  have ha := OddPair.axis E h hab hs p
  have hi : (centralizer (V : Set G)).relIndex (closure E g) ≤ 2 :=
    (relIndex_le_of_le_left ha.1 (by
      change ((U₀ E g).subgroupOf (closure E g)).index ≠ 0
      exact index_ne_zero_of_finite)).trans ha.2.1
  rw [fixed_index E g p] at hi
  have := (Nat.log_mono_right hi (b := 2)).trans (by decide : Nat.log 2 2 ≤ 1)
  simpa using this

theorem seed_displacement_le_one (h : LocalInputs E) (hab : IsMulCommutative E.W)
    (hs : letI := D.elementary; ChapterE.globalS V = (E.input.field.degree : ℕ∞))
    (p : OddPair E g) (v : V) :
    Module.finrank (ZMod 2) (LinearMap.range (action E g (seed E g p v) - 1)) ≤ 1 := by
  change Module.finrank (ZMod 2)
    (LinearMap.range (action E g (seed E g p v) - LinearMap.id)) ≤ 1
  rw [← fixedCodim_zpowers_eq_displacement_rank]
  have hle : fixedSpace (action E g) (seed E g p).range ≤
      fixedSpace (action E g) (zpowers (seed E g p v)) := by
    intro u hu a
    exact hu ⟨a, (zpowers_le.mpr (show seed E g p v ∈ (seed E g p).range from
      ⟨v, rfl⟩)) a.property⟩
  have hd := Submodule.finrank_mono hle
  have h₁ := fixedCodim_add_finrank (action E g) (seed E g p).range
  have h₂ := fixedCodim_add_finrank (action E g) (zpowers (seed E g p v))
  have hb := seed_fixedCodim_le_one E g h hab hs p
  omega

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Chief
