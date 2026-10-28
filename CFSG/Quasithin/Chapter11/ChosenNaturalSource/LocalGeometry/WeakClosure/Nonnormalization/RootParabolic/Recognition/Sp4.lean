module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Nonnormalization.RootParabolic.Recognition.Sp4.Action
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Nonnormalization.RootParabolic.Assembly

/-!
# The reciprocal root on the original conjugate cover

The two small-action coranks transport backwards along the original g to
indices on V and on W^(g⁻¹). The resulting actual symplectic homomorphism
has the whole transvection root as image. Its full-module action equation
supplies I.2.3's original cover calculation. Conjugating forward identifies
the ambient commutator with the complete field-line preimage in Vᵍ,
including its central kernel. The direction of the root conjugator is kept
explicit through the derived symplectic subgroup.

Source: Aschbacher--Smith, 11.2.4, printed p.769, and I.2.3(1b), p.413.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open Subgroup Representation Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
open Theory.SpecificGroups.SymplecticFour
open SymplecticConjugatePair.Ambient SymplecticConjugatePair.Ambient.Normalizer
open CFSG.Quasithin.ChapterE
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Nonnormalization.RootParabolic.Recognition
open NormalizedPlane.TransvectionFree

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))

/-- A literal full-root image saturates the original nonsplit field-line preimage. -/
theorem commutator_field_line_of_small_indices {A : Subgroup G}
    [IsElementaryAbelian 2 A]
    (hA : A ≤ normalizer (V : Set G)) (hsq : ∀ a : A, a^2=1)
    (hindex : (centralizer (A : Set G)).relIndex V ≤ Nat.card S.field.Carrier)
    (hcorank : subgroupCorank A (A ⊓ centralizer (V : Set G)) = S.field.degree) :
    ∃ U : Submodule S.field.Carrier (Coordinates.sp4 m).Space,
      Module.finrank S.field.Carrier U = 1 ∧ ⁅A,V⁆ = (Coordinates.sp4 m).preimage U := by
  let α := smallHom m hA hsq hindex
  obtain ⟨h,hh⟩ := smallHom_conjugate_root m hA hsq hindex hcorank
  letI := S.source.quasisimple
  letI : Group.IsPerfect (Sp S.field.Carrier) :=
    Group.IsPerfect.ofSurjective (f := m.groupEquiv.toMonoidHom) m.groupEquiv.surjective
  let z : SymplecticFourOrthogonalCover.L (K := S.field.Carrier) :=
    ⟨h⁻¹,Group.IsPerfect.mem_commutator⟩
  let β : A →* SymplecticFourOrthogonalCover.L (K := S.field.Carrier) :=
    α.codRestrict (commutator _) (fun _ => Group.IsPerfect.mem_commutator)
  have hβ (a : A) : β a ∈ SymplecticFourOrthogonalCover.Roots.conjugateGroup z := by
    have hr : h * α a * h⁻¹ ∈ RootSubgroup.group 0 := by
      rw [←hh]
      exact mem_map_of_mem _ (show α a ∈ α.range from ⟨a,rfl⟩)
    let r : SymplecticFourOrthogonalCover.L (K := S.field.Carrier) :=
      ⟨h * α a * h⁻¹,Group.IsPerfect.mem_commutator⟩
    refine ⟨r,hr,?_⟩
    apply Subtype.ext
    change h⁻¹ * (h * α a * h⁻¹) * (h⁻¹)⁻¹ = α a
    group
  let γ : A →* SymplecticFourOrthogonalCover.Roots.conjugateGroup z :=
    β.codRestrict _ hβ
  have hγ : Function.Surjective γ := by
    rintro ⟨r,⟨s,hs,he⟩⟩
    have hs' : s.val ∈ α.range.map (MulAut.conj h).toMonoidHom := by
      rw [hh]
      exact hs
    obtain ⟨b,⟨a,ha⟩,hb⟩ := hs'
    refine ⟨a,?_⟩
    apply Subtype.ext
    apply Subtype.ext
    have hh' := congrArg (fun t : Sp S.field.Carrier => h⁻¹*t*h) hb
    rw [←ha] at hh'
    have he' := congrArg Subtype.val he
    change h⁻¹*s.val*(h⁻¹)⁻¹ = r.val at he'
    change h⁻¹*(h*α a*h⁻¹)*h = h⁻¹*s.val*h at hh'
    have hcancel : h⁻¹*(h*α a*h⁻¹)*h = α a := by group
    rw [hcancel] at hh'
    exact hh'.trans (by simpa only [inv_inv] using he')
  have hc := commutator_preimage_of_sp4_root_action D S m 1 A z γ hγ (by
    intro a v
    change (1:G) * (D.spaceEquiv (Multiplicative.ofAdd
      (Preliminary.markedAction D m (α a) v)) : G) * 1⁻¹ =
      (a:G) * (1 * (D.spaceEquiv (Multiplicative.ofAdd v) : G) * 1⁻¹) * (a:G)⁻¹
    simpa only [one_mul,inv_one,mul_one] using
      smallHom_action m hA hsq hindex a v)
  have h1 : (MulAut.conj (1:G)).toMonoidHom = MonoidHom.id G := by ext; simp
  rw [h1,map_id,map_id] at hc
  exact ⟨_,sp4_root_line_finrank D S z,hc⟩

omit [Finite G] in
private theorem conjugate_cancel (B : Subgroup G) (g : G) :
    (B.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = B := by
  rw [offender_map_conj_map,inv_mul_cancel]
  have he : (MulAut.conj (1:G)).toMonoidHom = MonoidHom.id G := by ext; simp
  rw [he,map_id]

/-- Small reciprocal Sp₄ actions give the complete original field-line preimage. -/
theorem sp4_smallRootRecognition (f : InvariantFlag (Coordinates.sp4 m)) :
    SmallRootRecognition f := by
  intro g _ _ W hs hn
  let A := V.map (MulAut.conj g).toMonoidHom
  let B := W.map (MulAut.conj g⁻¹).toMonoidHom
  have hcomm : ⁅B,V⁆ = (⁅W,A⁆).map (MulAut.conj g⁻¹).toMonoidHom := by
    rw [map_commutator,conjugate_cancel]
  have hBV : B ≤ normalizer (V : Set G) := by
    apply le_normalizer_iff_commutator_le_right.mpr
    rw [hcomm]
    have h := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom)
      (le_normalizer_iff_commutator_le_right.mp hn)
    rwa [conjugate_cancel] at h
  letI := D.elementary
  letI : IsElementaryAbelian 2 W := IsElementaryAbelian.of_le hs.le_seed
  letI : IsElementaryAbelian 2 B := IsElementaryAbelian.map (MulAut.conj g⁻¹).toMonoidHom
  letI : IsElementaryAbelian 2 A := IsElementaryAbelian.map (MulAut.conj g).toMonoidHom
  have hC : (A ⊓ centralizer (W : Set G)).map (MulAut.conj g⁻¹).toMonoidHom =
      V ⊓ centralizer (B : Set G) := by
    rw [map_inf _ _ _ (MulAut.conj g⁻¹).injective,conjugate_cancel,
      Theory.GroupTheory.map_centralizer_equiv]
    rfl
  have hC' : (W ⊓ centralizer (A : Set G)).map (MulAut.conj g⁻¹).toMonoidHom =
      B ⊓ centralizer (V : Set G) := by
    rw [map_inf _ _ _ (MulAut.conj g⁻¹).injective,
      Theory.GroupTheory.map_centralizer_equiv]
    change B ⊓ centralizer (A.map (MulAut.conj g⁻¹).toMonoidHom : Set G) = _
    rw [conjugate_cancel]
  have hi : (centralizer (B : Set G)).relIndex V = Nat.card S.field.Carrier := by
    rw [←inf_relIndex_left V,←hC]
    have hc : V = A.map (MulAut.conj g⁻¹).toMonoidHom := (conjugate_cancel V g).symm
    conv_lhs => arg 2; rw [hc]
    rw [relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective,
      relIndex_eq_two_pow_quotient_finrank,←subgroupCorank_eq_quotient_finrank,
      hs.actor_corank,S.field.card_eq]
  have hr : subgroupCorank B (B ⊓ centralizer (V : Set G)) = S.field.degree := by
    rw [←hC',subgroupCorank,relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective]
    exact hs.vector_corank
  have hsq : ∀ b : B, b^2=1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 B)
  obtain ⟨U,hU,hUeq⟩ := commutator_field_line_of_small_indices m hBV hsq hi.le hr
  refine ⟨U,hU,?_⟩
  have hh := congrArg (map (MulAut.conj g).toMonoidHom) hUeq
  rw [hcomm] at hh
  have hc : ((⁅W,A⁆).map (MulAut.conj g⁻¹).toMonoidHom).map
      (MulAut.conj g).toMonoidHom = ⁅W,A⁆ := by
    simpa only [inv_inv] using conjugate_cancel ⁅W,A⁆ g⁻¹
  rwa [hc] at hh

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Nonnormalization.RootParabolic.Recognition
