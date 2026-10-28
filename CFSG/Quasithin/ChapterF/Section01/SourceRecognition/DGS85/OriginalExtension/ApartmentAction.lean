module
public import Theory.GroupTheory.Amalgam.CompletionAction
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.MarkedQuotient
public import Theory.GroupAction.RankTwoCosetGeometry.ExtensionGeometry

/-!
# Original actions on the reduced apartment quotient

A compatible automorphism of the reduced amalgam induces an automorphism of
its universal completion and of its literal typed coset tree. Sending the
chosen apartment into one reduced translate preserves all apartment paths,
the generated equivalence relation, and the kernel on its classes. The
universal lift then supplies precisely the kernel-preservation premise used
by original endpoint restoration.

The criterion is applied to the actual `ApartmentExchange.quotientCompletion`;
its universal lift is proved to be the same quotient map. A second criterion
uses conjugacy of a Cartan subgroup when the apartment is its full fixed-point
set. That equality is an explicit geometric hypothesis, not an inference from
a Cartan label: the small-field obstructions in the source still require work.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
(15.2), printed p.227, and the apartment relation of (3.6), pp.77--78.
This proves the descent step, not the source assertion that all original
actors preserve the apartment family or act through permissible Aut⁰(X).
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
namespace CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension
namespace ApartmentAction
universe u
variable {L B R : Type u} [Group L] [Group B] [Group R]
  {X K : Type*} [Group X] [Group K]
  {α : RankTwoAmalgam L B R}
  (a : K →* Iso α α) (c : FaithfulCompletion α (G := X))

private theorem universal_lift_id :
    Universal.lift α (Universal.completion α c) = MonoidHom.id α.Universal := by
  apply Monoid.PushoutI.hom_ext_nonempty
  intro i
  cases i <;> ext x
  · exact Universal.lift_left α (Universal.completion α c) x
  · exact Universal.lift_right α (Universal.completion α c) x

private theorem universal_preserves :
    CompletionAction.PreservesCompletionKernel a (Universal.completion α c) := by
  intro b x hx
  rw [universal_lift_id] at hx
  change x = 1 at hx
  subst x
  exact map_one _

def universalAction : K →* MulAut α.Universal :=
  CompletionAction.completionAction a (Universal.completion α c) (universal_preserves a c)

@[simp] theorem universalAction_left (b : K) (x : L) :
    universalAction a c b (Universal.left α x) = Universal.left α ((a b).left x) :=
  CompletionAction.completionAction_left a (Universal.completion α c) _ b x

@[simp] theorem universalAction_right (b : K) (x : R) :
    universalAction a c b (Universal.right α x) = Universal.right α ((a b).right x) :=
  CompletionAction.completionAction_right a (Universal.completion α c) _ b x

private theorem endpoint_preimage (b : K) (i : Bool) :
    (Universal.cosetFamily α i).comap (universalAction a c b).toMonoidHom =
      Universal.cosetFamily α i := by
  ext x
  cases i
  · change (∃ y, Universal.left α y = universalAction a c b x) ↔
      ∃ y, Universal.left α y = x
    constructor
    · rintro ⟨y,hy⟩
      refine ⟨(a b).left.symm y, (universalAction a c b).injective ?_⟩
      rw [universalAction_left, MulEquiv.apply_symm_apply, hy]
    · rintro ⟨y,rfl⟩
      exact ⟨(a b).left y, (universalAction_left a c b y).symm⟩
  · change (∃ y, Universal.right α y = universalAction a c b x) ↔
      ∃ y, Universal.right α y = x
    constructor
    · rintro ⟨y,hy⟩
      refine ⟨(a b).right.symm y, (universalAction a c b).injective ?_⟩
      rw [universalAction_right, MulEquiv.apply_symm_apply, hy]
    · rintro ⟨y,rfl⟩
      exact ⟨(a b).right y, (universalAction_right a c b y).symm⟩

open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open Subgroup.CosetGeometry.RankTwo

/-- The canonical action on the literal universal coset tree. -/
def treeAutomorphism (b : K) : sourceGraph α ≃g sourceGraph α :=
  ExtensionGeometry.graphIso (Universal.cosetFamily α) (Universal.cosetFamily α)
    (universalAction a c b).toMonoidHom (endpoint_preimage a c b)
    (fun x => ⟨(universalAction a c b).symm x, by
      change (universalAction a c b ((universalAction a c b).symm x))⁻¹ * x ∈ _
      rw [MulEquiv.apply_symm_apply, inv_mul_cancel]
      exact one_mem _⟩)

@[simp] theorem treeAutomorphism_base (b : K) (i : Bool) :
    treeAutomorphism a c b (Subgroup.CosetGeometry.base (Universal.cosetFamily α) i) =
      Subgroup.CosetGeometry.base (Universal.cosetFamily α) i :=
  ExtensionGeometry.vertex_base _ _ _ _ i

@[simp] theorem treeAutomorphism_smul (b : K) (g : α.Universal) (v : SourceVertex α) :
    treeAutomorphism a c b (g • v) =
      universalAction a c b g • treeAutomorphism a c b v :=
  ExtensionGeometry.vertex_smul _ _ _ _ g v

open Theory.GroupTheory.WeakBNPair.RegularTree

section Geometry
variable {Y V : Type*} [Group Y] [MulAction Y V]
  {Γ : SimpleGraph V} {T : Set V} {n : ℕ}
  (e : MulAut Y) (f : Γ ≃g Γ)
  (heq : ∀ g v, f (g • v) = e g • f v)
  (hT : ∃ t : Y, ∀ v ∈ T, ∃ w ∈ T, f v = t • w)

include e f heq hT

/-- Sending the chosen apartment into one translate sends every apartment
path to an apartment path of the same length. -/
theorem apartmentStep_map {v w : V} (h : ApartmentStep (X := Y) Γ T n v w) :
    ApartmentStep (X := Y) Γ T n (f v) (f w) := by
  obtain ⟨p,hp,hlen,g,hg⟩ := h
  obtain ⟨t,ht⟩ := hT
  refine ⟨p.map f.toHom, hp.map f.injective, ?_, e g * t, ?_⟩
  · simpa only [SimpleGraph.Walk.length_map] using hlen
  · intro z hz
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hz
    obtain ⟨v,hv,rfl⟩ := hz
    obtain ⟨w,hw,rfl⟩ := hg v hv
    obtain ⟨z,hz,hfz⟩ := ht w hw
    exact ⟨z,hz,by rw [mul_smul, ← hfz, ← heq]; rfl⟩

/-- The equivalence closure is preserved, not merely its elementary paths. -/
theorem apartmentSetoid_map {v w : V}
    (h : apartmentSetoid (X := Y) Γ T n v w) :
    apartmentSetoid (X := Y) Γ T n (f v) (f w) := by
  induction h with
  | rel v w h => exact Relation.EqvGen.rel _ _ (apartmentStep_map e f heq hT h)
  | refl v => exact Relation.EqvGen.refl _
  | symm v w _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans v w z _ _ hvw hwz => exact Relation.EqvGen.trans _ _ _ hvw hwz

/-- Semilinearity transfers the kernel on apartment classes. Surjectivity on
vertices is used here; no faithfulness or finiteness assumption is needed. -/
theorem quotientKernel_map
    (hact : ∀ (g : Y) {v w : V}, Γ.Adj v w → Γ.Adj (g • v) (g • w)) :
    (quotientKernel (apartmentSetoid (X := Y) Γ T n)
      (apartmentSetoid_invariant hact)).map e.toMonoidHom ≤
    quotientKernel (apartmentSetoid (X := Y) Γ T n) (apartmentSetoid_invariant hact) := by
  rintro _ ⟨g,hg,rfl⟩
  apply (mem_quotientKernel _ _ _).mpr
  intro v
  obtain ⟨w,rfl⟩ := f.surjective v
  change apartmentSetoid (X := Y) Γ T n (e g • f w) (f w)
  rw [← heq]
  exact apartmentSetoid_map e f heq hT ((mem_quotientKernel _ _ _).mp hg w)
omit hT in
/-- When the chosen apartment is the full fixed-point set of a Cartan
subgroup, conjugacy of its image already gives apartment preservation.
The fixed-set equality is essential in the exceptional small-field cases. -/
theorem apartment_image_of_cartan (C : Subgroup Y)
    (hfixed : ∀ v, v ∈ T ↔ ∀ k ∈ C, k • v = v)
    (t : Y) (hC : C.map e.toMonoidHom = C.map (MulAut.conj t).toMonoidHom) :
    ∀ v ∈ T, ∃ w ∈ T, f v = t • w := by
  intro v hv
  refine ⟨t⁻¹ • f v, (hfixed _).mpr ?_, by simp only [smul_inv_smul]⟩
  intro k hk
  have hm : t*k*t⁻¹ ∈ C.map e.toMonoidHom := by
    rw [hC]
    exact ⟨k,hk,rfl⟩
  obtain ⟨x,hx,he⟩ := hm
  change e x = t*k*t⁻¹ at he
  have ha : (t*k*t⁻¹) • f v = f v := by
    rw [← he, ← heq, (hfixed v).mp hv x hx]
  calc
    k • (t⁻¹ • f v) = t⁻¹ • ((t*k*t⁻¹) • f v) := by
      simp only [← mul_smul]
      congr 1
      simp only [mul_assoc, inv_mul_cancel_left]
    _ = t⁻¹ • f v := congrArg (fun z => t⁻¹ • z) ha
end Geometry

/-- The universal lift of the changed marking is the old lift after the
canonical automorphism of the universal completion. -/
theorem lift_twisted (b : K) :
    Universal.lift α (c.comapIso (a b)) =
      (Universal.lift α c).comp (universalAction a c b).toMonoidHom := by
  apply Monoid.PushoutI.hom_ext_nonempty
  intro i
  cases i <;> ext x
  · change L at x
    change Universal.lift α (c.comapIso (a b)) (Universal.left α x) =
      Universal.lift α c (universalAction a c b (Universal.left α x))
    rw [universalAction_left, Universal.lift_left, Universal.lift_left]
    rfl
  · change R at x
    change Universal.lift α (c.comapIso (a b)) (Universal.right α x) =
      Universal.lift α c (universalAction a c b (Universal.right α x))
    rw [universalAction_right, Universal.lift_right, Universal.lift_right]
    rfl

/-- A geometric criterion for the completion-kernel premise: use the actual
apartment relation and its kernel, and require only that each actor sends
the chosen apartment into a reduced translate. -/
theorem preservesCompletionKernel_of_apartments
    (T : Set (SourceVertex α)) (n : ℕ)
    (hker : (Universal.lift α c).ker = kernel α T n)
    (hap : ∀ b : K, ∃ t : α.Universal, ∀ v ∈ T, ∃ w ∈ T,
      treeAutomorphism a c b v = t • w) :
    CompletionAction.PreservesCompletionKernel a c := by
  intro b x hx
  have hxD : x ∈ kernel α T n := hker ▸ hx
  have hu : universalAction a c b x ∈ kernel α T n :=
    quotientKernel_map (universalAction a c b) (treeAutomorphism a c b)
      (treeAutomorphism_smul a c b) (hap b) (source_action α) ⟨x,hxD,rfl⟩
  rw [← hker] at hu
  change Universal.lift α (c.comapIso (a b)) x = 1
  rw [lift_twisted]
  exact hu

/-- Cartan conjugacy can discharge the geometric premise, provided the
apartment has actually been identified with the Cartan fixed-point set. -/
theorem preservesCompletionKernel_of_cartan
    (T : Set (SourceVertex α)) (n : ℕ)
    (hker : (Universal.lift α c).ker = kernel α T n)
    (C : Subgroup α.Universal)
    (hfixed : ∀ v, v ∈ T ↔ ∀ k ∈ C, k • v = v)
    (hC : ∀ b : K, ∃ t : α.Universal,
      C.map (universalAction a c b).toMonoidHom = C.map (MulAut.conj t).toMonoidHom) :
    CompletionAction.PreservesCompletionKernel a c := by
  apply preservesCompletionKernel_of_apartments a c T n hker
  intro b
  obtain ⟨t,ht⟩ := hC b
  exact ⟨t, apartment_image_of_cartan (universalAction a c b)
    (treeAutomorphism a c b) (treeAutomorphism_smul a c b) C hfixed t ht⟩

variable (T : Set (SourceVertex α)) (n : ℕ)
  (hL : Function.Injective α.left) (hR : Function.Injective α.right)
  (hsep : Separated (sourceRelation α T n) (sourceGraph α) (2*n)) (hn : 1 < n)
  (hcore : ((Universal.left α).range ⊓ (Universal.right α).range).normalCore = ⊥)

/-- The universal lift of the geometric completion is literally its quotient
map, so no kernel-identification premise is needed for this completion. -/
theorem geometric_lift :
    Universal.lift α (quotientCompletion α T n hL hR hsep hn hcore) =
      quotientMap α T n := by
  apply Monoid.PushoutI.hom_ext_nonempty
  intro i
  cases i <;> ext x
  · exact Universal.lift_left α (quotientCompletion α T n hL hR hsep hn hcore) x
  · exact Universal.lift_right α (quotientCompletion α T n hL hR hsep hn hcore) x

theorem geometric_lift_ker :
    (Universal.lift α (quotientCompletion α T n hL hR hsep hn hcore)).ker =
      kernel α T n := by
  rw [geometric_lift]
  exact QuotientGroup.ker_mk' _

/-- Literal application to the quotient constructed by the apartment-exchange
owner. The algebraic kernel-preservation input is now discharged. -/
theorem preserves_geometricCompletion
    (hap : ∀ b : K, ∃ t : α.Universal, ∀ v ∈ T, ∃ w ∈ T,
      treeAutomorphism a (quotientCompletion α T n hL hR hsep hn hcore) b v = t • w) :
    CompletionAction.PreservesCompletionKernel a
      (quotientCompletion α T n hL hR hsep hn hcore) :=
  preservesCompletionKernel_of_apartments a _ T n
    (geometric_lift_ker T n hL hR hsep hn hcore) hap

end ApartmentAction
end CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension
