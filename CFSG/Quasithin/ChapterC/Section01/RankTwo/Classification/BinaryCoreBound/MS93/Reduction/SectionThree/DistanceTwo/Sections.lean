module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Setup.CommonFacts
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Setup.LocalStructure
public import Theory.ElementaryAbelian.AbelianNormalClosure
public import Theory.Frattini.PGroup

/-!
# Actual sections for the distance-two core argument

The moving group U lies centrally in the commutator core at positive
critical distance. Both are literal subgroups of the free amalgam; only
the containing vertex stabilizer is finite.

`NaturalCoreQuotient` specifies an actual surjection from the core to the
binary natural three-space with kernel U, equivariant for the given
SL3(2) quotient. Its marking is independent of the marking on U, so this
interface does not prematurely exclude the dual orientation.
`ExtensionEstimates` records the remaining local estimates used by the
central-extension argument. Neither structure has a source constructor
here. In particular, they assert neither abelianness nor trivial Frattini.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), the natural SL3 branch in the proof of (3.6), printed pp.870--871.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceTwo
variable {M : Type*} [Group M] {L R : Subgroup M}

theorem core_le_Q (a : Vertex R) : core R a ≤ Q R a :=
  le_normalizer_iff_commutator_le_left.mp
    ((map_subtype_le (pResidual 2 (stabilizer R a))).trans (Q_normalized R a))

theorem core_normalized (a : Vertex R) :
    stabilizer R a ≤ normalizer (core R a : Set (FreeAmalgam R)) := by
  intro g hg
  rw [mem_normalizer_iff_map_conj_eq]
  change (core R a).map (MulAut.conj g).toMonoidHom = core R a
  have h := core_act R g⁻¹ a
  have hga : act R g⁻¹ a = a := (stabilizer R a).inv_mem hg
  simpa only [hga, inv_inv] using h.symm

theorem U_le_core (geometry : Geometry R) (hb : 0 < geometry.b R)
    (a : Vertex R) (ha : color R a = false) : U R a ≤ core R a :=
  commutator_mono ((geometry.omega_bound a ha
    (by rw [geometry.distance_constant a ha]; exact hb)).trans (omegaCenter_le _)) le_rfl

theorem U_centralizes_core [Finite M] (a : Vertex R) (ha : color R a = false) :
    U R a ≤ centralizer (core R a : Set (FreeAmalgam R)) := by
  have hUZ : U R a ≤ Z R a := le_normalizer_iff_commutator_le_left.mp
    ((map_subtype_le (pResidual 2 (stabilizer R a))).trans (Z_normalized R a))
  exact hUZ.trans ((commutator_eq_bot_iff_le_centralizer.mp
    (Z_centralizes_Q R a ha)).trans (centralizer_le (core_le_Q a)))

theorem U_subgroupOf_core_le_center [Finite M] (a : Vertex R) (ha : color R a = false) :
    (U R a).subgroupOf (core R a) ≤ center (core R a) := by
  intro u hu
  rw [mem_center_iff]
  intro v
  exact Subtype.ext (U_centralizes_core a ha hu v v.property)

theorem U_subgroupOf_core_normal [Finite M] (a : Vertex R) (ha : color R a = false) :
    ((U R a).subgroupOf (core R a)).Normal := by
  constructor
  intro u hu v
  rw [mem_center_iff.mp (U_subgroupOf_core_le_center a ha hu) v,
    mul_inv_cancel_right]
  exact hu

theorem finite_core [Finite M] (a : Vertex R) : Finite (core R a) := by
  let := finite_stabilizer R a
  exact Finite.of_injective (inclusion ((core_le_Q a).trans (fun _ hx => hx.1)))
    (inclusion_injective _)

/-- The natural three-dimensional head of the actual core, allowing its
own graph twist until the source proves agreement with the marking on U. -/
structure NaturalCoreQuotient (source : LocalSource L R) where
  marking : SL ≃* SL
  projection : core R (alpha R) →* Multiplicative (Fin 3 → ZMod 2)
  surjective : Function.Surjective projection
  kernel : projection.ker = (U R (alpha R)).subgroupOf (core R (alpha R))
  action : ∀ (m : M) (x y : core R (alpha R)),
    (y : FreeAmalgam R) = embedM R m * (x : FreeAmalgam R) * (embedM R m)⁻¹ →
    Multiplicative.toAdd (projection y) =
      (marking (source.projection m)).val.mulVec (Multiplicative.toAdd (projection x))

/-- The actual local estimates still to be constructed in the large-core
branch of (3.6). Generation is by involutions, not an exponent assumption. -/
structure ExtensionEstimates (source : LocalSource L R) where
  quotient : NaturalCoreQuotient source
  small_centralizer : ∃ y : core R (alpha R), (y : FreeAmalgam R) ∉ U R (alpha R) ∧
    (centralizer ({y} : Set (core R (alpha R)))).index ≤ 2
  involution_generation :
    closure {x : core R (alpha R) | x ^ 2 = 1} = ⊤

/-- After commutativity is proved, the genuine involution-generation
estimate supplies the trivial-Frattini clause of (3.6). -/
theorem frattini_eq_bot_of_commutative_of_involution_generation
    [Finite M] [IsMulCommutative (core R (alpha R))]
    (hgen : closure {x : core R (alpha R) | x ^ 2 = 1} = ⊤) :
    frattini (core R (alpha R)) = ⊥ := by
  let K := core R (alpha R)
  let : Finite K := finite_core (alpha R)
  have hpow (x : K) : x ^ 2 = 1 := by
    have hx : x ∈ closure {x : K | x ^ 2 = 1} := hgen.symm ▸ mem_top x
    induction hx using closure_induction with
    | mem y hy => exact hy
    | one => simp
    | mul y z _ _ hy hz =>
      have hc : Commute y z := mul_comm y z
      rw [hc.mul_pow, hy, hz, one_mul]
    | inv y _ hy => rw [inv_pow, hy, inv_one]
  let : IsElementaryAbelian 2 K :=
    { exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hpow }
  let : Fact (IsPGroup 2 K) := ⟨IsElementaryAbelian.isPGroup 2 K⟩
  exact frattini_eq_bot_of_isElementaryAbelian (p := 2)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceTwo
