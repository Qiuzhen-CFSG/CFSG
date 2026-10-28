module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.BestReduction.Marked
public import Theory.SpecificGroups.BinaryLinear.Parabolics
public import Theory.Representation.BinaryPermutation.CubicFixedSpace.Five

/-!
# Cubic witnesses for the marked small alternatives

An explicit cubic in GL₃(2) fixes the line fixed by its elementary parabolic
radical. It fixes that radical's fixed vectors on either one or two identical
natural modules. The existing regular-four calculation gives the S₅ witness.
Sylow conjugacy and the actual central quotient transport these witnesses to
any marked subspace fixed by the specified Sylow subgroup. Central extensions
are retained: the cubic displacement argument requires no splitting.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
15.3.67, printed p.1154, and B.5.1, p.99. These are model calculations only;
lifting an actor through the original action kernel and proving that its lift
normalizes Z_S remain separate geometric obligations of source assembly.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.SmallModels
open BestReduction

namespace LinearThree
abbrev Space := Fin 3 → ZMod 2
abbrev Actor := BinaryLinear.GL Space

def natural : Representation (ZMod 2) Actor Space where
  toFun g := g.toLinearMap
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Identity on the first coordinate, a cubic on the last two coordinates. -/
def cycle : Actor where
  toFun v := ![v 0, v 2, v 1 + v 2]
  invFun v := ![v 0, v 1 + v 2, v 1]
  map_add' := by decide +kernel
  map_smul' := by decide +kernel
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem cycle_pow : cycle ^ 3 = 1 := by
  apply LinearEquiv.ext
  decide +kernel

theorem cycle_ne_one : cycle ≠ 1 := by
  intro h
  have he := congrArg (fun g : Actor => g ![0, 1, 0]) h
  exact zero_ne_one (congrFun he 1)

def line : Submodule (ZMod 2) Space := Submodule.span (ZMod 2) {Pi.single 0 1}

theorem line_ne_bot : line ≠ ⊥ := by
  apply mt Submodule.span_singleton_eq_bot.mp
  intro h
  have := congrFun h 0
  norm_num at this

private theorem fixes_line (v : Space) (hv : v ∈ line) : cycle v = v := by
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hv
  rw [map_smul]
  congr 1
  decide +kernel

theorem cycle_normalizes :
    cycle ∈ normalizer (BinaryLinear.radical line : Set Actor) := by
  apply BinaryLinear.parabolic_le_normalizer line
  intro v
  constructor
  · intro hv
    have he : cycle v = v := cycle.injective (fixes_line (cycle v) hv)
    rwa [he] at hv
  · intro hv
    simpa only [fixes_line v hv] using hv

theorem cycle_fixes_natural :
    ∀ v ∈ fixedSpace natural (BinaryLinear.radical line), natural cycle v = v := by
  intro v hv
  apply fixes_line
  exact (BinaryLinear.mem_iff_fixed_radical line_ne_bot v).mpr (fun g hg => hv ⟨g, hg⟩)

theorem cycle_fixes_double :
    ∀ v ∈ fixedSpace (natural.prod natural) (BinaryLinear.radical line),
      (natural.prod natural) cycle v = v := by
  intro v hv
  exact Prod.ext (cycle_fixes_natural v.1 (fun g => congrArg Prod.fst (hv g)))
    (cycle_fixes_natural v.2 (fun g => congrArg Prod.snd (hv g)))

/-- Both extension orientations are allowed, with a central kernel and a
trivial outer quotient. The section is specified by an intertwining map. -/
private theorem centralSection_cubic
    {D V X : Type*} [Group D] [Finite D] [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup X] [Module (ZMod 2) X]
    (ρ : Representation (ZMod 2) D V) (f : Actor →* D) (hf : Function.Injective f)
    (σ : Representation (ZMod 2) Actor X)
    (hσ : ∀ x ∈ fixedSpace σ (BinaryLinear.radical line), σ cycle x = x)
    (U : Subrepresentation (ρ.comp f)) (q : U.toSubmodule →ₗ[ZMod 2] X)
    (hq : ∀ g u, q (U.toRepresentation g u) = σ g (q u))
    (hker : ∀ g u, q u = 0 → U.toRepresentation g u = u)
    (hquot : ∀ g v, ρ (f g) v - v ∈ U) (S : Sylow 2 D) :
    ∃ c : D, orderOf c = 3 ∧ ∀ v ∈ fixedSpace ρ (S : Subgroup D), ρ c v = v := by
  obtain ⟨c, hc, hp, hv⟩ := sylow_fixedSpace_enlargement_of_embedded_cubic ρ f hf
    (BinaryLinear.radical line) (BinaryLinear.radical_two line) cycle cycle_pow cycle_ne_one
    (cubic_fixedSpace_of_central_section (ρ.comp f) σ _ _ cycle_pow cycle_normalizes
      U q hq hker hquot hσ) S
  exact ⟨c, orderOf_eq_prime hp (fun h => hc (h ▸ S.one_mem)), hv⟩

/-- A natural central section, with either nonsplit extension orientation,
supplies a genuine order-three witness fixing the entire Sylow fixed space. -/
theorem natural_centralSection_cubic
    {D V : Type*} [Group D] [Finite D] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (f : Actor →* D) (hf : Function.Injective f)
    (U : Subrepresentation (ρ.comp f)) (q : U.toSubmodule →ₗ[ZMod 2] Space)
    (hq : ∀ g u, q (U.toRepresentation g u) = natural g (q u))
    (hker : ∀ g u, q u = 0 → U.toRepresentation g u = u)
    (hquot : ∀ g v, ρ (f g) v - v ∈ U) (S : Sylow 2 D) :
    ∃ c : D, orderOf c = 3 ∧ ∀ v ∈ fixedSpace ρ (S : Subgroup D), ρ c v = v :=
  centralSection_cubic ρ f hf natural cycle_fixes_natural U q hq hker hquot S

/-- The doubled section has two isomorphic natural factors with the same
actor. Central kernels and trivial outer quotients are still permitted. -/
theorem double_centralSection_cubic
    {D V : Type*} [Group D] [Finite D] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (f : Actor →* D) (hf : Function.Injective f)
    (U : Subrepresentation (ρ.comp f)) (q : U.toSubmodule →ₗ[ZMod 2] (Space × Space))
    (hq : ∀ g u, q (U.toRepresentation g u) = (natural.prod natural) g (q u))
    (hker : ∀ g u, q u = 0 → U.toRepresentation g u = u)
    (hquot : ∀ g v, ρ (f g) v - v ∈ U) (S : Sylow 2 D) :
    ∃ c : D, orderOf c = 3 ∧ ∀ v ∈ fixedSpace ρ (S : Subgroup D), ρ c v = v :=
  centralSection_cubic ρ f hf (natural.prod natural) cycle_fixes_double U q hq hker hquot S

end LinearThree

variable {D L W X : Type*} [Group D] [Finite D] [Group L]
  [AddCommGroup W] [Module (ZMod 2) W] [AddCommGroup X] [Module (ZMod 2) X]

/-- Transport uses the literal central quotient and the same actor isomorphism
as the module coordinates; no split replacement of W is made. -/
theorem marked_cubic_of_model
    {ρ : Representation (ZMod 2) D W} {σ : Representation (ZMod 2) L X}
    {J : Subgroup D} (d : MarkedNormalizer ρ J) (c : CentralQuotientCoordinates ρ σ)
    (A : Subgroup L) (hA : IsPGroup 2 A) (t : L) (ht : t ^ 3 = 1) (hne : t ≠ 1)
    (hfix : ∀ x ∈ fixedSpace σ A, σ t x = x) :
    ∃ g : D, orderOf g = 3 ∧ ∀ v ∈ d.marker, ρ g v = v := by
  let q := c.coordinates.toLinearMap.comp ρ.invariants.mkQ
  have hq (g : L) (v : W) : q (ρ (c.actor.symm g) v) = σ g (q v) := by
    simpa only [q, LinearMap.comp_apply, LinearEquiv.coe_coe, MulEquiv.apply_symm_apply]
      using c.intertwines (c.actor.symm g) v
  have hk (v : W) (hv : v ∈ q.ker) : ρ (c.actor.symm t) v = v := by
    have hz : ρ.invariants.mkQ v = 0 := c.coordinates.injective
      (show c.coordinates (ρ.invariants.mkQ v) = c.coordinates 0 from
        hv.trans c.coordinates.map_zero.symm)
    exact ((Submodule.Quotient.mk_eq_zero _).mp hz) _
  obtain ⟨g, hg, hp, hf⟩ := sylow_fixedSpace_enlargement_of_embedded_cubic ρ
    c.actor.symm.toMonoidHom c.actor.symm.injective A hA t ht hne
    (cubic_fixedSpace_of_map (ρ.comp c.actor.symm.toMonoidHom) σ A t ht q hq hk hfix) d.sylow
  exact ⟨g, orderOf_eq_prime hp (fun h => hg (h ▸ d.sylow.one_mem)),
    fun v hv => hf v (d.sylow_fixes hv)⟩

/-- The S₅ natural module excludes the marked three-prime stabilizer. -/
theorem symmetricFive_marked_cubic
    {ρ : Representation (ZMod 2) D W} {J : Subgroup D}
    (d : MarkedNormalizer ρ J)
    (c : CentralQuotientCoordinates ρ (BinaryPermutation.naturalRepresentation (Fin 5))) :
    ∃ g : D, orderOf g = 3 ∧ ∀ v ∈ d.marker, ρ g v = v := by
  let f := (alternatingGroup (Fin 5)).subtype
  let A := BinaryPermutation.CubicFixedSpace.Five.klein
  let t := BinaryPermutation.CubicFixedSpace.Five.cycle
  apply marked_cubic_of_model d c (A.map f)
    (BinaryPermutation.CubicFixedSpace.Five.klein_isPGroup.map f) (f t)
    (by rw [← map_pow, BinaryPermutation.CubicFixedSpace.Five.cycle_pow, map_one])
    (fun h => BinaryPermutation.CubicFixedSpace.Five.cycle_ne_one (Subtype.ext h))
  intro v hv
  apply BinaryPermutation.CubicFixedSpace.Five.cycle_fixes_natural v
  intro a
  exact hv ⟨f a, ⟨a, a.property, rfl⟩⟩

theorem linearThree_marked_cubic
    {ρ : Representation (ZMod 2) D W} {J : Subgroup D}
    (d : MarkedNormalizer ρ J) (c : CentralQuotientCoordinates ρ LinearThree.natural) :
    ∃ g : D, orderOf g = 3 ∧ ∀ v ∈ d.marker, ρ g v = v :=
  marked_cubic_of_model d c _ (BinaryLinear.radical_two LinearThree.line) _
    LinearThree.cycle_pow LinearThree.cycle_ne_one LinearThree.cycle_fixes_natural

theorem doubleLinearThree_marked_cubic
    {ρ : Representation (ZMod 2) D W} {J : Subgroup D}
    (d : MarkedNormalizer ρ J)
    (c : CentralQuotientCoordinates ρ (LinearThree.natural.prod LinearThree.natural)) :
    ∃ g : D, orderOf g = 3 ∧ ∀ v ∈ d.marker, ρ g v = v :=
  marked_cubic_of_model d c _ (BinaryLinear.radical_two LinearThree.line) _
    LinearThree.cycle_pow LinearThree.cycle_ne_one LinearThree.cycle_fixes_double

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.SmallModels
