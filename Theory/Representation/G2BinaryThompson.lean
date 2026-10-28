module
public import Theory.Representation.G2BinaryModelOffenders
public import Theory.Representation.G2NaturalFaithfulness
public import Stellmacher.CentralizerQuotientRepresentation
public import Theory.Representation.BinaryOffender.EquivariantOffender

/-!
# Thompson centralization in the binary derived G₂ action

A maximum elementary subgroup moving a normal elementary module gives an
FF-offender in its faithful action image. The actual binary derived G₂
group has elementary rank at most two, while every natural offender has
rank three. Thus any subgroup whose image lies in G₂(2)′ has Thompson
subgroup centralizing the module. The action map need not be surjective.

Source: Aschbacher--Smith B.2.4, B.4.6(13) and C.1.37, pp.75,90,141.
The octonion model retains the attribution in LICENSES/ATLAS.txt.
-/

public section
open Subgroup Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace Atlas.G2.Natural.BinaryNormalizer
variable {G : Type*} [Group G] [Finite G]
variable (V : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
variable (q : G →* Full) (E : Additive V ≃ₗ[ZMod 2] Space (ZMod 2))
variable (hE : ∀ g v, E (Additive.ofMul (MulAut.conjNormal g v)) =
  action (ZMod 2) (q g) (E (Additive.ofMul v)))
include E hE

omit [Finite G] in
/-- Faithfulness identifies the kernel of the literal marked natural action. -/
theorem marked_kernel_eq_centralizer : q.ker = centralizer (V : Set G) := by
  ext g
  constructor
  · intro hg v hv
    have he := hE g ⟨v,hv⟩
    change q g = 1 at hg
    rw [hg,map_one,Module.End.one_apply] at he
    have hh : g * v * g⁻¹ = v :=
      congrArg (fun w : Additive V => (w.toMul : G)) (E.injective he)
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  · intro hg
    change q g = 1
    apply action_injective (ZMod 2)
    rw [map_one]
    apply LinearMap.ext
    intro w
    obtain ⟨v,rfl⟩ := E.surjective w
    have he := hE g v.toMul
    have hc : MulAut.conjNormal g v.toMul = v.toMul := by
      apply Subtype.ext
      change g * (v.toMul : G) * g⁻¹ = v.toMul
      rw [← hg v.toMul v.toMul.property,mul_inv_cancel_right]
    rw [hc] at he
    exact he.symm

/-- The derived-image branch has no moving maximum elementary subgroup. -/
theorem thompson_centralizes_of_image_le_derived (R : Subgroup G) (hVR : V ≤ R)
    (hRD : R.map q ≤ Derived) :
    elementaryAbelianMaxJ R ≤ centralizer (V : Set G) := by
  have hk := marked_kernel_eq_centralizer V q E hE
  let qr := q.rangeRestrict
  have hkr : qr.ker = centralizer (V : Set G) := q.ker_rangeRestrict.trans hk
  let ρ := NormalElementaryQuotient.representation V qr q.rangeRestrict_surjective hkr
  have he (g : q.range) (v : Additive V) :
      E (ρ g v) = action (ZMod 2) g.val (E v) := by
    obtain ⟨g,rfl⟩ := q.rangeRestrict_surjective g
    have hr := NormalElementaryQuotient.representation_apply V qr
      q.rangeRestrict_surjective hkr g v
    have hh : (ρ (qr g) v).toMul = MulAut.conjNormal g v.toMul := Subtype.ext hr
    change E (Additive.ofMul ((ρ (qr g) v).toMul)) = _
    rw [hh]
    exact hE g v.toMul
  apply sSup_le
  intro A hA
  by_contra hn
  have ho := NormalElementaryQuotient.maxElementary_isOffender V qr
    q.rangeRestrict_surjective hkr R A hVR hA (by rwa [hkr])
  have ht := ho.map_equivariant ρ (action (ZMod 2))
    q.range.subtype q.range.subtype_injective E he
  have hd : (A.map qr).map q.range.subtype ≤ Derived := by
    rw [Subgroup.map_map]
    exact (map_mono hA.1).trans hRD
  have hr := BinaryModelOffenders.rank_le_two _ hd ht.1
  have hc := BinaryModelOffenders.natural_small_rank_bound _ ht.1 (by omega)
  exact (not_lt_of_ge ht.2) hc
end Atlas.G2.Natural.BinaryNormalizer
