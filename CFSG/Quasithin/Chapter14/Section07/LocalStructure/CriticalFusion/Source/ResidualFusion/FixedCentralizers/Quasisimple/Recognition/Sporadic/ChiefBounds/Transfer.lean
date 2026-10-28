module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Quasisimple.Recognition.Sporadic.Setup
public import Theory.GroupTheory.NoncentralChiefRefinement.CentralQuotient
public import Theory.GroupAction.SylowFixedCentralQuotient

/-!
# Chief-factor transfer for the marked sporadic cover

The original quotient equivalence induces an actual two-central inner action
on the named carrier. Fixed-point lifting gives a central surjection between
the fixed residuals. The unchanged inclusion into G identifies the upstairs
residual with K; central-kernel chief accounting then transfers the native
carrier bound to every complete chief series of this original K.

The native J₂ and HS chief counts are separate obligations. No multiplier
order, covering-group recognition, or assumed bound upstairs is used here.
Source: Aschbacher–Smith 14.7.68(2), printed p.1071 / PDF p.1088,
and 1.1.5(3)(f), printed pp.502–503.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory NoncentralChiefRefinement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08 Chapter15.Section03.Candidates.ComponentStructure
open ClassificationModels
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]

namespace SporadicSieve

private theorem map_twoCentralInner {A B : Type*} [Group A] [Group B]
    [Finite A] [Group.IsPerfect A] (a : MulAut A) (b : MulAut B)
    (f : A →* B) (hf : Function.Surjective f) (hc : f.ker ≤ center A)
    (heq : ∀ x, f (a x) = b (f x)) (ha : TwoCentralInner a) : TwoCentralInner b := by
  have ha2 : a ^ 2 = 1 := by rw [← ha.2.1, pow_orderOf_eq_one]
  have hb2 : b ^ 2 = 1 := by
    ext y
    obtain ⟨x, rfl⟩ := hf y
    change b (b (f x)) = f x
    rw [← heq, ← heq]
    have hx := congrArg (fun c : MulAut A => c x) ha2
    change a (a x) = x at hx
    rw [hx]
  have hbne : b ≠ 1 := by
    intro hb
    have hane : a ≠ 1 := by
      intro h
      have ho := ha.2.1
      rw [h, orderOf_one] at ho
      omega
    apply hane
    apply MulAut.eq_one_of_central_displacement
    intro x
    apply hc
    rw [MonoidHom.mem_ker, map_mul, map_inv, heq, hb, MulAut.one_apply, inv_mul_cancel]
  refine ⟨?_, orderOf_eq_prime hb2 hbne, ?_⟩
  · obtain ⟨x, hx⟩ := ha.1
    refine ⟨f x, ?_⟩
    ext y
    obtain ⟨y, rfl⟩ := hf y
    rw [← heq, ← hx]
    simp only [MulAut.conj_apply, map_mul, map_inv]
  · obtain ⟨P, hP⟩ := ha.2.2
    refine ⟨P.mapSurjective hf, ?_⟩
    rintro ⟨y, hy⟩
    change y ∈ (P : Subgroup A).map f at hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [← heq, hP ⟨x, hx⟩]

end SporadicSieve

namespace Data
variable (d : Data T L V F W) (u : F.U) {Lu : Subgroup G}
  (α : MulAut (Lu.subgroupOf (d.fixedCentralizer u))) {name : SporadicName}
  (e : ((Lu.subgroupOf (d.fixedCentralizer u)) ⧸
    pCore 2 (Lu.subgroupOf (d.fixedCentralizer u))) ≃* name.Carrier)

/-- The action on the given model of the literal two-core quotient. -/
def fixedSporadicAction : MulAut name.Carrier :=
  MulAut.congr e ((pCore 2 (Lu.subgroupOf (d.fixedCentralizer u))).quotientAut α)

/-- Equivariance retains the actual quotient map. -/
theorem fixedSporadicAction_compatible
    (h : SporadicSieve.Case d u Lu α name) (x : Lu.subgroupOf (d.fixedCentralizer u)) :
    (d.fixedSporadicCover u h.le_centralizer h.quasisimple e).toMonoidHom (α x) =
      d.fixedSporadicAction u α e
        ((d.fixedSporadicCover u h.le_centralizer h.quasisimple e).toMonoidHom x) := by
  change e (QuotientGroup.mk' (pCore 2 _) (α x)) =
    e ((pCore 2 _).quotientAut α (e.symm (e (QuotientGroup.mk' (pCore 2 _) x))))
  rw [e.symm_apply_apply, quotientAut_apply_mk]

/-- Innerness, involutory order and fixation of an actual Sylow subgroup all descend. -/
theorem fixedSporadicAction_twoCentral (h : SporadicSieve.Case d u Lu α name) :
    TwoCentralInner (d.fixedSporadicAction u α e) := by
  let f := d.fixedSporadicCover u h.le_centralizer h.quasisimple e
  let := f.isPerfect
  exact SporadicSieve.map_twoCentralInner α (d.fixedSporadicAction u α e)
    f.toMonoidHom f.surjective f.ker_le_center
    (d.fixedSporadicAction_compatible u α e h) h.twoCentral

/-- The intrinsic fixed residual is the original K by its ambient inclusion. -/
def fixedIntrinsicResidualEquiv (h : SporadicSieve.Case d u Lu α name) :
    pResidual 2 α.fixedSubgroup ≃* K F :=
  ((pResidual 2 α.fixedSubgroup).equivMapOfInjective α.fixedSubgroup.subtype
    α.fixedSubgroup.subtype_injective).trans
      (d.fixedComponentResidualEquiv u h.le_centralizer h.contains.le α h.conjugation)

@[simp] theorem fixedIntrinsicResidualEquiv_apply (h : SporadicSieve.Case d u Lu α name)
    (x : pResidual 2 α.fixedSubgroup) :
    (d.fixedIntrinsicResidualEquiv u α h x : G) =
      d.fixedComponentInclusion u Lu (x : α.fixedSubgroup) := rfl

/-- The actual quotient homomorphism restricted to the two fixed residuals. -/
def fixedSporadicResidualMap (h : SporadicSieve.Case d u Lu α name) :
    pResidual 2 α.fixedSubgroup →*
      pResidual 2 (d.fixedSporadicAction u α e).fixedSubgroup :=
  MulAut.fixedResidualMap 2 α (d.fixedSporadicAction u α e)
    (d.fixedSporadicCover u h.le_centralizer h.quasisimple e).toMonoidHom
    (d.fixedSporadicAction_compatible u α e h)

/-- On every representative the residual projection is the original marked map. -/
@[simp] theorem fixedSporadicResidualMap_apply (h : SporadicSieve.Case d u Lu α name)
    (x : pResidual 2 α.fixedSubgroup) :
    (((d.fixedSporadicResidualMap u α e h x :
        pResidual 2 (d.fixedSporadicAction u α e).fixedSubgroup) :
        (d.fixedSporadicAction u α e).fixedSubgroup) : name.Carrier) =
      e (QuotientGroup.mk' (pCore 2 _) (x : α.fixedSubgroup)) := rfl

/-- Sylow-fixed lifting gives a surjection on full fixed subgroups. -/
theorem fixedSporadic_fixedMap_surjective (h : SporadicSieve.Case d u Lu α name) :
    Function.Surjective (MulAut.fixedSubgroupMap α (d.fixedSporadicAction u α e)
      (d.fixedSporadicCover u h.le_centralizer h.quasisimple e).toMonoidHom
      (d.fixedSporadicAction_compatible u α e h)) := by
  let f := d.fixedSporadicCover u h.le_centralizer h.quasisimple e
  obtain ⟨P, hP⟩ := h.twoCentral.2.2
  apply MulAut.fixedSubgroupMap_surjective_of_sylow_fixed α _ f.toMonoidHom
    f.surjective f.ker_le_center (d.fixedSporadicAction_compatible u α e h)
    (by rw [← h.twoCentral.2.1, pow_orderOf_eq_one]) P
  intro x hx
  exact hP ⟨x, hx⟩

/-- The literal fixed-residual map is onto. -/
theorem fixedSporadicResidualMap_surjective (h : SporadicSieve.Case d u Lu α name) :
    Function.Surjective (d.fixedSporadicResidualMap u α e h) := by
  let f := MulAut.fixedSubgroupMap α (d.fixedSporadicAction u α e)
    (d.fixedSporadicCover u h.le_centralizer h.quasisimple e).toMonoidHom
    (d.fixedSporadicAction_compatible u α e h)
  have hm := map_pResidual_of_surjective 2 f
    (d.fixedSporadic_fixedMap_surjective u α e h)
  intro y
  obtain ⟨x, hx, hxy⟩ := hm.ge y.property
  exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

/-- The fixed-residual kernel remains central. -/
theorem fixedSporadicResidualMap_ker_le_center (h : SporadicSieve.Case d u Lu α name) :
    (d.fixedSporadicResidualMap u α e h).ker ≤ center (pResidual 2 α.fixedSubgroup) :=
  MulAut.fixedResidualMap_ker_le_center 2 α (d.fixedSporadicAction u α e) _ _
    (d.fixedSporadicCover u h.le_centralizer h.quasisimple e).ker_le_center

/-- Actual source application: an upstairs K-series and a downstairs model
series have equal counts. Their normal intervals and actions use the original maps. -/
theorem fixedSporadic_noncentralTwoCount_eq (h : SporadicSieve.Case d u Lu α name)
    (s : ChiefSeries (K F))
    (t : ChiefSeries (pResidual 2 (d.fixedSporadicAction u α e).fixedSubgroup))
    (hs0 : s.head = ⊥) (hs1 : s.last = ⊤)
    (ht0 : t.head = ⊥) (ht1 : t.last = ⊤) :
    s.noncentralTwoCount = t.noncentralTwoCount := by
  let E := d.fixedIntrinsicResidualEquiv u α h
  obtain ⟨hr0, hr1⟩ := s.mapActor_complete E.symm hs0 hs1
  have he := ChiefSeries.noncentralTwoCount_eq_of_central_surjective
    (d.fixedSporadicResidualMap u α e h) (d.fixedSporadicResidualMap_surjective u α e h)
    (d.fixedSporadicResidualMap_ker_le_center u α e h)
    (s.mapActor E.symm) t hr0 hr1 ht0 ht1
  simpa only [ChiefSeries.mapActor_noncentralTwoCount] using he

include e in
/-- Transfer a native model theorem to the actual original K. This conditional
reduction is discharged separately for the J₂ and HS native centralizers. -/
theorem fixedSporadic_noncentralTwoCount_le_of_native
    (h : SporadicSieve.Case d u Lu α name) (n : ℕ)
    (hnative : ∀ (β : MulAut name.Carrier), TwoCentralInner β →
      ∀ t : ChiefSeries (pResidual 2 β.fixedSubgroup),
        t.head = ⊥ → t.last = ⊤ → t.noncentralTwoCount ≤ n)
    (s : ChiefSeries (K F)) (hs0 : s.head = ⊥) (hs1 : s.last = ⊤) :
    s.noncentralTwoCount ≤ n := by
  let : Finite name.Carrier := Finite.of_surjective
    (d.fixedSporadicCover u h.le_centralizer h.quasisimple e).toMonoidHom
    (d.fixedSporadicCover u h.le_centralizer h.quasisimple e).surjective
  obtain ⟨t, ht0, ht1⟩ := exists_chiefSeries
    (⊥ : NormalNode (pResidual 2 (d.fixedSporadicAction u α e).fixedSubgroup)) ⊤ bot_le
  rw [d.fixedSporadic_noncentralTwoCount_eq u α e h s t hs0 hs1 ht0 ht1]
  exact hnative _ (d.fixedSporadicAction_twoCentral u α e h) t ht0 ht1

end Data
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
