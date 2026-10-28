module

public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.Definitions
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.J2CentralClass
public import Theory.GroupTheory.DoubleCoverCentralizer.PerfectSquareOrbit
public import Theory.GroupTheory.Commutator.PerfectQuotient

/-!
# The literal J₂ centralizer restriction and its square orbit

The central quotient map, followed by an actual equivalence with the fixed
ATLAS carrier, defines the preimage of the marked centralizer. Its restricted
map has precisely the ambient center as kernel. The checked five-point action
therefore gives this preimage its actual A₅ quotient by the two-core.

When the preimage is perfect, the preimage of the quotient center is central.
Thus every lift of the marked involution has this exact centralizer, and the
two-residual is the whole preimage. The square-orbit theorem then constructs
an involution square and proves the literal `HasUniqueCoreSquareLift` clause.

Perfection of the quotient centralizer and its nonempty square-root orbit
remain explicit intrinsic inputs. The theorem `preimage_perfect_of_restriction`
reduces perfection upstairs to that quotient input and the earlier restriction
law (i). These are conditional reductions, not completion of I.2.2: the
concrete orbit and the projective-module/SL₂(5) recognition remain to be proved.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, I.2.2(5),
printed pp.411–412 / PDF pp.422–423. The centralizer/core action comes from
the checked Chapter 16 J₂ centralizer calculation and its literal ATLAS maps.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.J2Local
open Sporadic.LeechRelated.J2
open ExceptionalParabolics ExceptionalParabolics.Seed ExceptionalParabolics.FirstParabolic
open ExceptionalParabolics.FirstParabolic.QuotientActions
variable {K : Type*} [Group K]

def projection (e : (K ⧸ center K) ≃* Carrier) : K →* Carrier :=
  e.toMonoidHom.comp (QuotientGroup.mk' (center K))

def preimage (e : (K ⧸ center K) ≃* Carrier) : Subgroup K :=
  l₁.comap (projection e)

def restriction (e : (K ⧸ center K) ≃* Carrier) : preimage e →* l₁ :=
  ((projection e).comp (preimage e).subtype).codRestrict l₁ (fun x => x.property)

def marked : l₁ := ⟨z, mem_centralizer_singleton_iff.mpr rfl⟩

theorem marked_central : marked ∈ center l₁ := by
  apply mem_center_iff.mpr
  intro x
  apply Subtype.ext
  exact mem_centralizer_singleton_iff.mp x.property

theorem marked_order : orderOf marked = 2 := by
  exact (orderOf_injective l₁.subtype l₁.subtype_injective marked).symm.trans
    (orderOf_eq_prime GeneratorPair.FirstFusion.t_pow_two GeneratorPair.FirstFusion.t_ne_one)

theorem projection_surjective (e : (K ⧸ center K) ≃* Carrier) :
    Function.Surjective (projection e) :=
  e.surjective.comp (QuotientGroup.mk'_surjective (center K))

theorem projection_ker (e : (K ⧸ center K) ≃* Carrier) :
    (projection e).ker = center K := by
  ext x
  change e (QuotientGroup.mk' (center K) x) = 1 ↔ x ∈ center K
  rw [map_eq_one_iff _ e.injective]
  exact QuotientGroup.eq_one_iff x

theorem center_le_preimage (e : (K ⧸ center K) ≃* Carrier) :
    center K ≤ preimage e := by
  intro x hx
  have hk : x ∈ (projection e).ker := (projection_ker e).symm ▸ hx
  change projection e x ∈ l₁
  rw [MonoidHom.mem_ker.mp hk]
  exact l₁.one_mem

theorem restriction_surjective (e : (K ⧸ center K) ≃* Carrier) :
    Function.Surjective (restriction e) := by
  intro y
  obtain ⟨x, hx⟩ := projection_surjective e y.val
  exact ⟨⟨x, show projection e x ∈ l₁ from hx ▸ y.property⟩, Subtype.ext hx⟩

theorem restriction_ker (e : (K ⧸ center K) ≃* Carrier) :
    (restriction e).ker = (center K).subgroupOf (preimage e) := by
  ext x
  change restriction e x = 1 ↔ x.val ∈ center K
  rw [← projection_ker e]
  exact Subtype.ext_iff

theorem restriction_kernel_card (e : (K ⧸ center K) ≃* Carrier) :
    Nat.card (restriction e).ker = Nat.card (center K) := by
  rw [restriction_ker]
  exact Nat.card_congr (subgroupOfEquivOfLe (center_le_preimage e)).toEquiv

theorem restriction_ker_central (e : (K ⧸ center K) ≃* Carrier) :
    (restriction e).ker ≤ center (preimage e) := by
  intro x hx
  rw [restriction_ker] at hx
  apply mem_center_iff.mpr
  intro y
  exact Subtype.ext (mem_center_iff.mp hx y.val)

theorem preimage_perfect_of_restriction (e : (K ⧸ center K) ≃* Carrier)
    [Group.IsPerfect l₁] (hi : center K ≤ ⁅preimage e, preimage e⁆) :
    Group.IsPerfect (preimage e) := by
  have hk : (restriction e).ker ≤ commutator (preimage e) := by
    intro x hx
    rw [restriction_ker] at hx
    have h := hi hx
    rw [← map_subtype_commutator] at h
    obtain ⟨y, hy, he⟩ := h
    exact (Subtype.ext he : y = x) ▸ hy
  exact ⟨by
    have h := CentralExtension.ker_sup_commutator_eq_top_of_surjective
      (restriction e) (restriction_surjective e)
    rwa [sup_eq_right.mpr hk] at h⟩

def perfectRestriction (e : (K ⧸ center K) ≃* Carrier)
    [Group.IsPerfect (preimage e)] : PerfectCentralCovering.Cover (preimage e) l₁ where
  toMonoidHom := restriction e
  surjective := restriction_surjective e
  isPerfect := inferInstance
  ker_le_center := restriction_ker_central e

theorem centralizer_eq_preimage (e : (K ⧸ center K) ≃* Carrier)
    [Group.IsPerfect (preimage e)] (u : K) (hu : projection e u = z) :
    centralizer ({u} : Set K) = preimage e := by
  have huP : u ∈ preimage e := by
    change projection e u ∈ l₁
    rw [hu]
    exact marked.property
  have huc : (⟨u, huP⟩ : preimage e) ∈ center (preimage e) := by
    rw [← (perfectRestriction e).comap_center]
    change restriction e ⟨u, huP⟩ ∈ center l₁
    have hm : restriction e ⟨u, huP⟩ = marked := Subtype.ext hu
    rw [hm]
    exact marked_central
  ext x
  constructor
  · intro hx
    apply mem_centralizer_singleton_iff.mpr
    have h := congrArg (projection e) (mem_centralizer_singleton_iff.mp hx)
    simpa only [map_mul, hu] using h
  · intro hx
    apply mem_centralizer_singleton_iff.mpr
    exact congrArg Subtype.val (mem_center_iff.mp huc ⟨x, hx⟩)

theorem residual_eq_preimage [Finite K] (e : (K ⧸ center K) ≃* Carrier)
    [Group.IsPerfect (preimage e)] (u : K) (hu : projection e u = z) :
    centralizerTwoResidual u = preimage e := by
  have hp : pResidual 2 (preimage e) = ⊤ := by
    apply (pResidual_eq_top_iff _ _).mpr
    intro N hN hq
    let := hN
    have hsub : Subsingleton ((preimage e) ⧸ N) := by
      by_contra! hn
      exact Group.IsPerfect.not_isNilpotent _ hq.isNilpotent
    apply eq_top_iff.mpr
    intro g _
    exact (QuotientGroup.eq_one_iff g).mp (Subsingleton.elim _ _)
  rw [centralizerTwoResidual, centralizer_eq_preimage e u hu, hp]
  rw [← MonoidHom.range_eq_map, range_subtype]

theorem core_eq_preimage_core [Finite K] (e : (K ⧸ center K) ≃* Carrier)
    [Group.IsPerfect (preimage e)] (u : K) (hu : projection e u = z) :
    centralizerCore u = (pCore 2 (preimage e)).map (preimage e).subtype := by
  rw [centralizerCore, residual_eq_preimage e u hu]

theorem restriction_kernel_exponent_two [Finite K]
    (e : (K ⧸ center K) ≃* Carrier) (hZ : Nat.card (center K) = 2)
    (x : preimage e) (hx : x ∈ (restriction e).ker) : x ^ 2 = 1 := by
  rw [restriction_ker] at hx
  have h := pow_card_eq_one' (x := (⟨x.val, hx⟩ : center K))
  rw [hZ] at h
  exact Subtype.ext (congrArg (fun a : center K => (a : K)) h)

theorem restriction_kernel_two_group [Finite K]
    (e : (K ⧸ center K) ≃* Carrier) (hZ : Nat.card (center K) = 2) :
    IsPGroup 2 (restriction e).ker := by
  intro x
  exact ⟨1, Subtype.ext (restriction_kernel_exponent_two e hZ x.val x.property)⟩

theorem core_preimage [Finite K] (e : (K ⧸ center K) ≃* Carrier)
    (hZ : Nat.card (center K) = 2) :
    (pCore 2 l₁).comap (restriction e) = pCore 2 (preimage e) :=
  (restriction e).comap_pCore_of_ker_isPGroup (restriction_surjective e)
    (restriction_kernel_two_group e hZ)

noncomputable def a5Action (e : (K ⧸ center K) ≃* Carrier) :
    preimage e →* alternatingGroup (Fin 5) := innerAction.comp (restriction e)

theorem a5Action_surjective (e : (K ⧸ center K) ≃* Carrier) :
    Function.Surjective (a5Action e) := innerAction_surjective.comp (restriction_surjective e)

theorem a5Action_ker [Finite K] (e : (K ⧸ center K) ≃* Carrier)
    (hZ : Nat.card (center K) = 2) : (a5Action e).ker = pCore 2 (preimage e) := by
  have hk : innerAction.ker = pCore 2 l₁ := by
    rw [innerAction_ker card_radical,
      l₁_core_eq_of_radical_action card_radical innerAction innerAction_surjective
        (innerAction_ker card_radical)]
  rw [a5Action, ← MonoidHom.comap_ker, hk, core_preimage e hZ]

noncomputable def a5Quotient [Finite K] (e : (K ⧸ center K) ≃* Carrier)
    (hZ : Nat.card (center K) = 2) :
    preimage e ⧸ pCore 2 (preimage e) ≃* alternatingGroup (Fin 5) :=
  (QuotientGroup.quotientMulEquivOfEq (a5Action_ker e hZ).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (a5Action e) (a5Action_surjective e))

theorem a5Quotient_mk [Finite K] (e : (K ⧸ center K) ≃* Carrier)
    (hZ : Nat.card (center K) = 2) (x : preimage e) :
    a5Quotient e hZ (QuotientGroup.mk' (pCore 2 (preimage e)) x) = a5Action e x := rfl

theorem unique_core_square_of_quotient_orbit [Finite K]
    (e : (K ⧸ center K) ≃* Carrier) (hZ : Nat.card (center K) = 2)
    [Group.IsPerfect (preimage e)]
    (hex : ∃ r ∈ pCore 2 l₁, r ^ 2 = marked)
    (horbit : ∀ r ∈ pCore 2 l₁, ∀ s ∈ pCore 2 l₁,
      r ^ 2 = marked → s ^ 2 = marked → IsConj r s)
    (u : K) (hu : projection e u = z) : HasUniqueCoreSquareLift u := by
  obtain ⟨v, ⟨hv, x, hx, hx2⟩, huniq⟩ := (perfectRestriction e).unique_core_square
    (restriction_kernel_two_group e hZ) (restriction_kernel_exponent_two e hZ)
    marked marked_central hex horbit
  have hvproj : projection e v.val = z := congrArg Subtype.val hv
  refine ⟨v.val, ⟨?_, x.val, ?_, congrArg Subtype.val hx2⟩, ?_⟩
  · exact e.injective (hvproj.trans hu.symm)
  · rw [core_eq_preimage_core e u hu]
    exact ⟨x, hx, rfl⟩
  · rintro w ⟨hw, y, hy, hy2⟩
    rw [core_eq_preimage_core e u hu] at hy
    obtain ⟨yP, hyP, rfl⟩ := hy
    have hwP : w ∈ preimage e := hy2 ▸ (preimage e).pow_mem yP.property 2
    have hwproj : projection e w = z := (congrArg e hw).trans hu
    exact congrArg Subtype.val (huniq ⟨w, hwP⟩
      ⟨Subtype.ext hwproj, yP, hyP, Subtype.ext hy2⟩)

theorem involution_square_lift_of_quotient_orbit [Finite K]
    (e : (K ⧸ center K) ≃* Carrier) (hZ : Nat.card (center K) = 2)
    [Group.IsPerfect (preimage e)]
    (hex : ∃ r ∈ pCore 2 l₁, r ^ 2 = marked)
    (horbit : ∀ r ∈ pCore 2 l₁, ∀ s ∈ pCore 2 l₁,
      r ^ 2 = marked → s ^ 2 = marked → IsConj r s) :
    ∃ v : K, orderOf v = 2 ∧ projection e v = z ∧
      (∃ x ∈ centralizerCore v, x ^ 2 = v) ∧ HasUniqueCoreSquareLift v := by
  obtain ⟨v, hv2, hv, ⟨x, hx, hx2⟩, _⟩ := (perfectRestriction e).core_square_order_two
    (restriction_kernel_two_group e hZ) (restriction_kernel_exponent_two e hZ)
    marked marked_central marked_order hex horbit
  have hvproj : projection e v.val = z := congrArg Subtype.val hv
  refine ⟨v.val, ?_, hvproj, ⟨x.val, ?_, congrArg Subtype.val hx2⟩,
    unique_core_square_of_quotient_orbit e hZ hex horbit v.val hvproj⟩
  · exact (orderOf_injective (preimage e).subtype (preimage e).subtype_injective v).trans hv2
  · rw [core_eq_preimage_core e v.val hvproj]
    exact ⟨x, hx, rfl⟩

end CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.J2Local
