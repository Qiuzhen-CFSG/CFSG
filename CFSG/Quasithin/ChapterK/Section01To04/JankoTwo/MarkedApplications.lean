module

public import CFSG.Quasithin.ChapterK.Section01To04.JankoTwo.MarkedModule
public import CFSG.Quasithin.ChapterK.Section01To04.JankoTwo.FieldInvolution
public import CFSG.Quasithin.ChapterK.Section01To04.JankoTwo.CentralizerCenter

/-!
# Applying the K.4.5 reductions to the marked source module

The six-dimensional outer fixed space follows from the compatible field
action. The rank-two exclusion uses the literal embedding into G₂(4), its
actual root pointwise fixer, and the center of the J₂ involution centralizer.
Only the displayed earlier root calculation and group-center inputs remain
in that reduction. It does not prove the complete source ratio theorem.
Source: Aschbacher–Smith, K.4.5, printed p.460.
-/

public section
namespace CFSG.Quasithin.ChapterK.JankoTwo
open Subgroup Representation Representation.BinaryOffender

variable {K G V : Type*} [Field K] [CharP K 2] [Algebra (ZMod 2) K]
  [FiniteDimensional (ZMod 2) K] [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V}

namespace MarkedModule
variable (D : MarkedModule (K := K) ρ)
include D

omit [FiniteDimensional (ZMod 2) K] in
/-- Equivariance on the actual inner subgroup, with its supplied G₂ embedding. -/
theorem inner_equivariant (l : D.inner) (v : V) :
    D.equiv.toLinearEquiv (ρ l v) =
      naturalAction K (D.embedding l) (D.equiv.toLinearEquiv v) :=
  (Representation.IntertwiningMap.isIntertwining _ _ D.equiv.toIntertwiningMap l v).trans
    (D.inner_action l _)

omit [FiniteDimensional (ZMod 2) K] in
/-- Cyclic fixed codimension transports along the literal inner embedding. -/
theorem inner_fixedCodim (a : D.inner) :
    fixedCodim ρ (zpowers (a : G)) =
      fixedCodim (naturalAction K) (zpowers (D.embedding a)) := by
  have ht : fixedCodim ρ (zpowers (a : G)) = fixedCodim D.action (zpowers (a : G)) := by
    simpa only [Subgroup.map_id] using fixedCodim_map_equivariant ρ D.action
      (MonoidHom.id G) D.equiv.toLinearEquiv
      (Representation.IntertwiningMap.isIntertwining _ _ D.equiv.toIntertwiningMap)
      (zpowers (a : G))
  have hspace : fixedSpace D.action (zpowers (a : G)) =
      fixedSpace (naturalAction K) (zpowers (D.embedding a)) := by
    ext v
    rw [mem_fixedSpace_zpowers_iff, mem_fixedSpace_zpowers_iff, D.inner_action]
  rw [ht, fixedCodim, hspace]
  rfl

omit [FiniteDimensional (ZMod 2) K] in
/-- The outer involution has equal displacement and fixed space in the actual
natural quotient coordinates. -/
theorem outer_range_eq_fixed (i : G) (hi : i ∉ D.inner) (hi2 : orderOf i = 2) :
    LinearMap.range (D.action i - LinearMap.id) = fixedSpace D.action (zpowers i) :=
  field_involution_range_eq_fixed D.action i
    (by simpa only [hi2] using pow_orderOf_eq_one i)
    D.fieldGenerator D.generator_relation (D.outer_semilinear i hi hi2)

/-- The two binary dimensions in the first paragraph of K.4.5 are derived
from the marked semilinearity and transported to the literal source action. -/
theorem outer_dimensions [FiniteDimensional (ZMod 2) V]
    (i : G) (hi : i ∉ D.inner) (hi2 : orderOf i = 2) :
    fixedCodim ρ (zpowers i) = 6 ∧
      Module.finrank (ZMod 2) (fixedSpace ρ (zpowers i)) = 6 := by
  let : FiniteDimensional (ZMod 2) (Atlas.G2.Natural.Space K) :=
    Module.Finite.trans K _
  have hd := field_involution_dimensions D.action D.finrank_space i
    (by simpa only [hi2] using pow_orderOf_eq_one i)
    D.fieldGenerator D.generator_relation (D.outer_semilinear i hi hi2)
  have ht : fixedCodim ρ (zpowers i) = fixedCodim D.action (zpowers i) := by
    simpa only [Subgroup.map_id] using fixedCodim_map_equivariant ρ D.action
      (MonoidHom.id G) D.equiv.toLinearEquiv
      (Representation.IntertwiningMap.isIntertwining _ _ D.equiv.toIntertwiningMap)
      (zpowers i)
  have hr := fixedCodim_add_finrank ρ (zpowers i)
  have hv := D.finrank
  omega

/-- For an actor containing an outer involution and a nontrivial inner
involution, B.4.6's lower displacement bound forces codimension at least eight.
The fixed dimension four is proved by the semilinear injection, not assumed. -/
theorem outer_actor_codim
    (A : Subgroup G) (i : G) (hi : i ∉ D.inner) (hi2 : orderOf i = 2)
    (hiA : i ∈ A) (a : D.inner) (haA : (a : G) ∈ A)
    (ha : 4 ≤ fixedCodim (naturalAction K) (zpowers (D.embedding a))) :
    8 ≤ fixedCodim ρ A := by
  let : FiniteDimensional (ZMod 2) (Atlas.G2.Natural.Space K) :=
    Module.Finite.trans K _
  have ha' : 4 ≤ fixedCodim D.action (zpowers (a : G)) := by
    have hspace : fixedSpace D.action (zpowers (a : G)) =
        fixedSpace (naturalAction K) (zpowers (D.embedding a)) := by
      ext v
      rw [mem_fixedSpace_zpowers_iff, mem_fixedSpace_zpowers_iff, D.inner_action]
    unfold fixedCodim
    rw [hspace]
    exact ha
  have hlinear : ∀ (r : K) (v : Atlas.G2.Natural.Space K),
      D.action a (r • v) = r • D.action a v := by
    intro r v
    rw [D.inner_action, D.inner_action]
    exact (Atlas.G2.Natural.action K (D.embedding a)).map_smul r v
  have h := outer_actor_codim_bound D.action D.finrank_space A i hiA a haA ha'
    D.fieldGenerator D.generator_relation (D.outer_semilinear i hi hi2) hlinear
  have ht : fixedCodim ρ A = fixedCodim D.action A := by
    simpa only [Subgroup.map_id] using fixedCodim_map_equivariant ρ D.action
      (MonoidHom.id G) D.equiv.toLinearEquiv
      (Representation.IntertwiningMap.isIntertwining _ _ D.equiv.toIntertwiningMap) A
  rwa [ht]

/-- Once the group calculation bounds an outer actor's rank by three, its
codimension-eight lower bound contradicts the small-ratio inequality. -/
theorem outer_actor_exclusion
    (A : Subgroup G) (hA : rank A ≤ 3)
    (i : G) (hi : i ∉ D.inner) (hi2 : orderOf i = 2) (hiA : i ∈ A)
    (a : D.inner) (haA : (a : G) ∈ A)
    (ha : 4 ≤ fixedCodim (naturalAction K) (zpowers (D.embedding a))) :
    2 * rank A < fixedCodim ρ A := by
  have h := D.outer_actor_codim A i hi hi2 hiA a haA ha
  omega

/-- The universal G₂ involution lower bound and the proved outer calculation
supply the hypothesis used by Chapter K's noncyclic cubic-actor reduction. -/
theorem moduleM_ge_four [FiniteDimensional (ZMod 2) V]
    (hM : ∀ x : Atlas.G2.Model K, orderOf x = 2 →
      4 ≤ fixedCodim (naturalAction K) (zpowers x)) :
    4 ≤ ChapterE.moduleM ρ := by
  apply le_csInf ⟨_, Set.mem_insert (Module.finrank (ZMod 2) V) _⟩
  rintro n (rfl | ⟨i, hi, rfl⟩)
  · rw [D.finrank]
    decide
  · by_cases hm : i ∈ D.inner
    · let a : D.inner := ⟨i, hm⟩
      have hai : orderOf a = 2 :=
        (orderOf_injective D.inner.subtype D.inner.subtype_injective a).symm.trans hi
      have hae : orderOf (D.embedding a) = 2 :=
        (orderOf_injective D.embedding D.embedding_injective a).trans hai
      have h := hM (D.embedding a) hae
      rw [← D.inner_fixedCodim a] at h
      exact h
    · rw [(D.outer_dimensions i hm hi).1]
      decide

/-- The actual Chapter K reduction now uses only the earlier universal G₂
involution bound, besides the genuine marked module. -/
theorem exists_small_cubic_actor [Finite G] [FiniteDimensional (ZMod 2) V]
    (hM : ∀ x : Atlas.G2.Model K, orderOf x = 2 →
      4 ≤ fixedCodim (naturalAction K) (zpowers x))
    (hq : cubicRatio ρ ≤ 2) :
    ∃ A, IsElementaryTwo A ∧ 1 < rank A ∧ IsCubic ρ A ∧
      fixedCodim ρ A ≤ 2 * rank A := by
  have hm := D.moduleM_ge_four hM
  exact ChapterK.exists_noncyclic_cubic_of_ratio_le_two ρ (by omega) hq

omit [FiniteDimensional (ZMod 2) K] in
/-- Consumer of the root-intersection lemma on the genuine marked J₂ subgroup.
The displacement-four input concerns the actual ambient root involution. -/
theorem inner_rank_two_exclusion [Finite G] [FiniteDimensional (ZMod 2) V]
    (A : Subgroup D.inner) (hA : rank A = 2) (z : D.inner) (hzA : z ∈ A)
    (hz : orderOf z = 2)
    (hzdim : fixedCodim (naturalAction K) (zpowers (D.embedding z)) = 4)
    (R : Subgroup (Atlas.G2.Model K))
    (hroot : subspaceKernel (naturalAction K)
      (fixedSpace (naturalAction K) (zpowers (D.embedding z))) ⊤ = R)
    (hR : R ≤ centralizer (centralizer ({D.embedding z} : Set (Atlas.G2.Model K)) :
      Set (Atlas.G2.Model K)))
    (hcenter : (center (centralizer ({z} : Set D.inner))).map
      (centralizer ({z} : Set D.inner)).subtype ≤ zpowers z) :
    2 * rank A < fixedCodim (ρ.comp D.inner.subtype) A := by
  have hzdim' : fixedCodim (ρ.comp D.inner.subtype) (zpowers z) = 4 := by
    rw [fixedCodim_map_equivariant (ρ.comp D.inner.subtype) (naturalAction K)
      D.embedding D.equiv.toLinearEquiv D.inner_equivariant,
      MonoidHom.map_zpowers, hzdim]
  exact rank_two_exclusion (ρ.comp D.inner.subtype) (naturalAction K)
    D.embedding D.embedding_injective D.equiv.toLinearEquiv D.inner_equivariant
    A hA z hzA hz hzdim' R hroot hR hcenter

omit [FiniteDimensional (ZMod 2) K] in
/-- The rank-two obstruction on the fixed degree-100 carrier has its entire
J₂ centralizer-center premise discharged. Its remaining inputs are the
ambient root and fixed-space calculation at the actual embedded involution. -/
theorem carrier_rank_two_exclusion [FiniteDimensional (ZMod 2) V]
    (A : Subgroup Sporadic.LeechRelated.J2.Carrier) (hA : rank A = 2)
    (hzA : Sporadic.LeechRelated.J2.GeneratorPair.FirstFusion.t ∈ A)
    (R : Subgroup (Atlas.G2.Model K))
    (hzdim : fixedCodim (naturalAction K)
      (zpowers (D.embedding (D.carrierEquiv.symm
        Sporadic.LeechRelated.J2.GeneratorPair.FirstFusion.t))) = 4)
    (hroot : subspaceKernel (naturalAction K)
      (fixedSpace (naturalAction K) (zpowers (D.embedding (D.carrierEquiv.symm
        Sporadic.LeechRelated.J2.GeneratorPair.FirstFusion.t)))) ⊤ = R)
    (hR : R ≤ centralizer (centralizer
      ({D.embedding (D.carrierEquiv.symm Sporadic.LeechRelated.J2.GeneratorPair.FirstFusion.t)} :
        Set (Atlas.G2.Model K)) : Set (Atlas.G2.Model K))) :
    2 * rank A < fixedCodim
      (ρ.comp (D.inner.subtype.comp D.carrierEquiv.symm.toMonoidHom)) A := by
  let f := D.embedding.comp D.carrierEquiv.symm.toMonoidHom
  let τ := ρ.comp (D.inner.subtype.comp D.carrierEquiv.symm.toMonoidHom)
  have hE : ∀ g v, D.equiv.toLinearEquiv (τ g v) =
      naturalAction K (f g) (D.equiv.toLinearEquiv v) :=
    fun g v => D.inner_equivariant (D.carrierEquiv.symm g) v
  have hzdim' : fixedCodim τ
      (zpowers Sporadic.LeechRelated.J2.GeneratorPair.FirstFusion.t) = 4 := by
    rw [fixedCodim_map_equivariant τ (naturalAction K) f D.equiv.toLinearEquiv hE,
      MonoidHom.map_zpowers]
    exact hzdim
  exact rank_two_exclusion τ (naturalAction K) f
    (D.embedding_injective.comp D.carrierEquiv.symm.injective) D.equiv.toLinearEquiv hE
    A hA _ hzA
    Sporadic.LeechRelated.J2.ExceptionalParabolics.SecondParabolic.central_involution_order
    hzdim' R hroot hR centralizer_center.le

end MarkedModule
end CFSG.Quasithin.ChapterK.JankoTwo
