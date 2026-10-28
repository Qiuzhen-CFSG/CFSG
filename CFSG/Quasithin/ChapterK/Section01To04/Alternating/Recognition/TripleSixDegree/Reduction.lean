module

public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.Branches
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.AlternatingSixCover
public import Theory.Representation.BinaryOffender.CubicConjugateBound
public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.OddCentralizer
public import Theory.Representation.Quotient
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizing

/-!
# Reducing the triple-A₆ degree problem to two independent inputs

The actual even hexacode cover forces binary degree divisible by six. Its
central quotient bounds the ambient two-rank by three, so a cubic actor of
ratio at most two has fixed codimension at most six. An actor containing an
involution that inverts the cubic center gives degree at most twelve: that
involution moves exactly half the space. For the other actors, rank at most
two and generation over the component by three conjugates give the same bound.

Thus the remaining inputs are the inner/outer actor geometry and exclusion of
an irreducible twelve-space for the component. These inputs are stated
explicitly; the conditional reduction is not a proof of the degree assertion.
All operators, conjugates and fixed spaces remain in the original action.

Source: Aschbacher–Smith K.1 and K.1.3, printed pp.452–453 (PDF pp.463–464),
citing Guralnick–Malle (2002), Theorem 6.2 and Table 6.3. The divisibility and
automorphism-rank inputs are the checked G.9 triple-cover calculations.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory Atlas.Codes

namespace CFSG.Quasithin.ChapterK.Alternating.TripleSixReduction
open ChapterG.Section09.DefiningCharacteristic.AlternatingSixCover

universe u v
variable {G : Type u} [Group G] {V : Type v} [AddCommGroup V]
  [Module (ZMod 2) V] (ρ : Representation (ZMod 2) G V)
  {K : GroupClass.{u}} {L : Subgroup G}

/-- The marked cubic center element, inside the original ambient group. -/
noncomputable def centralElement (e : L ≃* HexEvenAutomorphisms) : G :=
  (e.symm hexEvenZ : G)

/-- The central mark retains its order under the actual component inclusion. -/
theorem centralElement_order (e : L ≃* HexEvenAutomorphisms) :
    orderOf (centralElement e) = 3 := by
  exact (orderOf_injective (L.subtype.comp e.symm.toMonoidHom)
    (L.subtype_injective.comp e.symm.injective) hexEvenZ).trans hexEvenZ_order

/-- Faithful irreducibility on L makes its central cubic fixed-point free. -/
theorem centralElement_fixed_free (h : Input ρ K L) (e : L ≃* HexEvenAutomorphisms) :
    ∀ v : V, ρ (centralElement e) v = v → v = 0 := by
  let τ := (ρ.comp L.subtype).comp e.symm.toMonoidHom
  let : IsIrreducible τ :=
    (irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective _).mpr h.irreducible
  have hn : (zpowers hexEvenZ).Normal := by
    rw [← hexEvenCoordinate_kernel, Hexacode.even_kernel_eq_center]
    infer_instance
  exact RankTwo.fixed_free_of_faithful_irreducible_normal_three τ
    ((h.faithful.comp L.subtype_injective).comp e.symm.injective)
    hexEvenZ hexEvenZ_order hn

variable [Finite G] [FiniteDimensional (ZMod 2) V]

omit [Finite G] in
/-- The existing coprime Sylow calculation applies to the literal component action. -/
theorem six_dvd_finrank (h : Input ρ K L) (e : L ≃* HexEvenAutomorphisms) :
    6 ∣ Module.finrank (ZMod 2) V := by
  let τ := (ρ.comp L.subtype).comp e.symm.toMonoidHom
  let : IsIrreducible τ :=
    (irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective _).mpr h.irreducible
  let := Hexacode.even_isQuasisimple
  exact six_dvd_dimension Hexacode.even_quotient_center_equiv
    Hexacode.even_center_card τ
    ((h.faithful.comp L.subtype_injective).comp e.symm.injective)

omit [FiniteDimensional (ZMod 2) V] in
/-- This bounds G itself, retaining all outer actors in the source input. -/
theorem ambient_two_rank_le_three (h : Input ρ K L) (e : L ≃* HexEvenAutomorphisms) :
    primeRank 2 G ≤ 3 := by
  let : L.Normal := by rw [h.fitting]; infer_instance
  let := h.irreducible
  have hr := BinaryIrreducibleCentralizer.primeRank_le_automorphisms ρ L h.faithful
  rw [primeRank_equiv 2 (MulAut.congr e)] at hr
  let := Hexacode.even_isQuasisimple
  exact hr.trans (cover_automorphism_two_rank Hexacode.even_quotient_center_equiv)

omit [Finite G] in
/-- An involution inverting the actual central cubic moves exactly half of V. -/
theorem finrank_eq_two_mul_fixedCodim_of_inverts (h : Input ρ K L)
    (e : L ≃* HexEvenAutomorphisms) (t : G) (ht : t ^ 2 = 1)
    (hinv : t * centralElement e * t⁻¹ = (centralElement e)⁻¹) :
    Module.finrank (ZMod 2) V = 2 * fixedCodim ρ (zpowers t) := by
  let z := centralElement e
  have hz : z ^ 3 = 1 := by rw [← centralElement_order e]; exact pow_orderOf_eq_one _
  have hzi : z⁻¹ = z ^ 2 := by
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_succ']
    exact hz
  have htz : t * z = z ^ 2 * t := by
    rw [← hzi]
    exact mul_inv_eq_iff_eq_mul.mp hinv
  have hd := RankTwo.finrank_range_inverting_cubic (ρ z) (ρ t)
    (by rw [← map_pow, hz, map_one]) (centralElement_fixed_free ρ h e)
    (by rw [← map_mul, ← pow_two, ht, map_one])
    (by rw [← map_pow, ← map_mul, ← map_mul, htz])
  rw [fixedCodim_zpowers_eq_displacement_rank]
  exact hd.symm

/-- The group geometry needed for one elementary actor. The first alternative
uses actual conjugates in G. The second uses inversion of the marked center. -/
def ActorGeometry (e : L ≃* HexEvenAutomorphisms) (A : Subgroup G) : Prop :=
  ∃ t : G, t ∈ A ∧ t ≠ 1 ∧
    ((rank A ≤ 2 ∧ ∃ g : Fin 3 → G,
      L ≤ closure (Set.range fun i => g i * t * (g i)⁻¹)) ∨
      t * centralElement e * t⁻¹ = (centralElement e)⁻¹)

/-- Once the actor geometry is supplied, the ambient cubic bound gives degree
at most twelve without any module catalogue or presumed action equivalence. -/
theorem finrank_le_twelve_of_actorGeometry (h : Input ρ K L)
    (e : L ≃* HexEvenAutomorphisms)
    (hgeom : ∀ A : Subgroup G, IsElementaryTwo A → ActorGeometry e A) :
    Module.finrank (ZMod 2) V ≤ 12 := by
  obtain ⟨A, hA, _, hsmall⟩ := (cubicRatio_le_nat_iff ρ 2).mp h.cubic_bound
  obtain ⟨t, htA, ht1, hinner | houter⟩ := hgeom A hA
  · obtain ⟨hr, g, hg⟩ := hinner
    have hcodim : fixedCodim ρ (zpowers t) ≤ 4 := by
      have hle : fixedSpace ρ A ≤ fixedSpace ρ (zpowers t) := by
        intro v hv a
        exact hv ⟨a, (zpowers_le.mpr htA) a.property⟩
      have hmono := Submodule.finrank_mono hle
      have hdimA := fixedCodim_add_finrank ρ A
      have hdimt := fixedCodim_add_finrank ρ (zpowers t)
      omega
    let : IsSimpleGroup (L ⧸ center L) := h.quasisimple.simple
    let : Nontrivial L := (QuotientGroup.mk'_surjective (center L)).nontrivial
    exact (finrank_le_mul_fixedCodim_of_conjugate_generation ρ L
      (fixedSpace_eq_bot_of_faithful_irreducible_on ρ L h.faithful h.irreducible)
      t g hg).trans (by omega)
  · obtain ⟨ht2, hcodim⟩ := involution_fixedCodim_le_of_mem_small_actor ρ hA
      (ambient_two_rank_le_three ρ h e) hsmall htA
    rw [finrank_eq_two_mul_fixedCodim_of_inverts ρ h e t ht2 houter]
    omega

/-- Divisibility and positivity leave precisely the two degrees six and twelve. -/
theorem finrank_six_or_twelve_of_actorGeometry (h : Input ρ K L)
    (e : L ≃* HexEvenAutomorphisms)
    (hgeom : ∀ A : Subgroup G, IsElementaryTwo A → ActorGeometry e A) :
    Module.finrank (ZMod 2) V = 6 ∨ Module.finrank (ZMod 2) V = 12 := by
  have hdiv := six_dvd_finrank ρ h e
  have hle := finrank_le_twelve_of_actorGeometry ρ h e hgeom
  let := h.irreducible
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial (ρ.comp L.subtype)
  have hpos := Module.finrank_pos (R := ZMod 2) (M := V)
  omega

end CFSG.Quasithin.ChapterK.Alternating.TripleSixReduction

namespace CFSG.Quasithin.ChapterK.Alternating
namespace TripleSixReduction
universe u v

/-- The required elementary-actor geometry on the actual ambient action.
No dimension, representation classification or action equivalence is assumed. -/
def CubicActorGeometry : Prop :=
  ∀ {G : Type u} {V : Type v} [Group G] [Finite G] [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (K : GroupClass.{u}) (L : Subgroup G),
    Input ρ K L → ∀ e : L ≃* HexEvenAutomorphisms,
      ∀ A : Subgroup G, IsElementaryTwo A → ActorGeometry e A

/-- Only the twelve-dimensional component representation needs to be
excluded; no full module catalogue is requested by this reduction. -/
def NoTwelve : Prop :=
  ∀ {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (τ : Representation (ZMod 2) HexEvenAutomorphisms V),
    Function.Injective τ → IsIrreducible τ → Module.finrank (ZMod 2) V ≠ 12

end TripleSixReduction

end CFSG.Quasithin.ChapterK.Alternating
