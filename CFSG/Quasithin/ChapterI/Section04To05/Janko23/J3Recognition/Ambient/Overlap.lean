module
public import Theory.SpecificGroups.Janko3.SourceRecognition.PlaneCoordinates
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J3Recognition.LocalSixteen.PlaneNatural
import Mathlib.Tactic.FinCases

/-!
# Compatible coordinates on the original common four-group

The actual root group acts nontrivially on each sixteen-plane and fixes
its center E. In natural GL₂(4) coordinates, a nonidentity actor fixing a
nonzero vector fixes just its field line. Thus E is a field line in each
marking. Normalize z to (1,0), then adjust one marking by coefficient
Frobenius to match the second generator u. The two markings now agree
on every element of E, with both full conjugation actions retained.

We also identify the whole ambient overlap N_G(A₁) ∩ N_G(A₂) with the
plane stabilizer inside N_G(R), and prove its order is 576. These results
do not align the two complements on this whole overlap or construct an
opposite-root/Weyl system.

Source: Aschbacher, *Sporadic Groups* (1994), 46.14(1–5a), pp.257–258;
Aschbacher–Smith I.4.7(2), p.418.
-/

public noncomputable section
open Subgroup
open Representation.CentralCubicNaturalFour
open Sporadic.Janko3.SourceRecognition.PlaneCoordinates
namespace CFSG.Quasithin.Janko23.J3Recognition.Ambient
open LocalSixteen
variable {G : Type*} [Group G] [Finite G] {D : Seed G}

private theorem z_ne_one : D.z ≠ 1 := by
  intro h
  have hh := D.localType.involution
  simp [h] at hh

/-- Normalize the distinguished involution and identify the whole common center
as a field line, using a nontrivial actor from the actual root group. -/
theorem plane_marking_at_center (P : ReturningPair D) (hclass : OneInvolutionClass G)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hA : Nat.card A = 16)
    (hAR : A ≤ P.R) (hEA : P.E ≤ A) :
    ∃ (f : A.normalizerMonoidHom.range ≃* LinearGroup) (a : A ≃* Plane),
      (∀ n x, a (n • x) = naturalAction (f n) (a x)) ∧
      a ⟨D.z,hEA P.z_mem_E⟩ = axis (Multiplicative.ofAdd 1) ∧
      ∀ x : P.E, (a (inclusion hEA x)).toAdd 1 = 0 := by
  obtain ⟨f,a,ha⟩ := P.plane_automizer_natural hclass A hA hAR
  have hz : a ⟨D.z,hEA P.z_mem_E⟩ ≠ 1 := by
    intro h
    exact z_ne_one (congrArg Subtype.val (a.injective (h.trans a.map_one.symm)))
  obtain ⟨t,ht⟩ := normalize_nonidentity _ hz
  let f' := f.trans (MulAut.conj t)
  let a' := a.trans (naturalAction t)
  have ha' (n : A.normalizerMonoidHom.range) (x : A) :
      a' (n • x) = naturalAction (f' n) (a' x) := by
    change naturalAction t (a (n • x)) = _
    rw [ha]
    exact (linear_change_action t (f n) (a x)).symm
  refine ⟨f',a',ha',ht,?_⟩
  have hnot : ¬ P.R ≤ A := by
    intro h
    have hh := card_le_of_le h
    rw [P.R_card,hA] at hh
    omega
  obtain ⟨n,hnR,hnA⟩ := SetLike.not_le_iff_exists.mp hnot
  let nN : normalizer (A : Set G) := ⟨n,P.R_le_plane_normalizer A hA hAR hnR⟩
  let b := A.normalizerMonoidHom.rangeRestrict nN
  have hb : f' b ≠ 1 := by
    intro h
    have hb1 : b = 1 := f'.injective (h.trans f'.map_one.symm)
    have hk : nN ∈ A.normalizerMonoidHom.ker := congrArg Subtype.val hb1
    rw [P.plane_normalizer_action_kernel A hA hAR] at hk
    exact hnA hk
  have hfix (x : P.E) : b • inclusion hEA x = inclusion hEA x := by
    apply Subtype.ext
    change n * (x : G) * n⁻¹ = (x : G)
    exact mul_inv_eq_iff_eq_mul.mpr (P.R_le_centralizer_E hnR x x.property).symm
  have hbz : naturalAction (f' b) (axis (Multiplicative.ofAdd 1)) =
      axis (Multiplicative.ofAdd 1) := by
    rw [← ht]
    change naturalAction (f' b) (a' (inclusion hEA ⟨D.z,P.z_mem_E⟩)) =
      a' (inclusion hEA ⟨D.z,P.z_mem_E⟩)
    rw [← ha',hfix]
  intro x
  apply fixed_axis (f' b) hb hbz
  rw [← ha',hfix]


private theorem E_hom_ext (P : ReturningPair D) (f g : P.E →* Plane)
    (hz : f ⟨D.z,P.z_mem_E⟩ = g ⟨D.z,P.z_mem_E⟩)
    (hu : f ⟨P.u,P.u_mem_E⟩ = g ⟨P.u,P.u_mem_E⟩) : f = g := by
  let L := f.eqLocus g
  have h : P.E ≤ L.map P.E.subtype :=
    sup_le (zpowers_le.mpr ⟨⟨D.z,P.z_mem_E⟩,hz,rfl⟩)
      (zpowers_le.mpr ⟨⟨P.u,P.u_mem_E⟩,hu,rfl⟩)
  apply MonoidHom.ext
  intro x
  obtain ⟨y,hy,he⟩ := h x.property
  have hyx : y = x := Subtype.ext he
  subst y
  exact hy

private theorem axis_of_second_zero (v : Plane) (hv : v.toAdd 1 = 0) :
    v = axis (Multiplicative.ofAdd (v.toAdd 0)) := by
  change v.toAdd = ![v.toAdd 0,0]
  funext i
  fin_cases i
  · rfl
  · exact hv

private theorem second_generator_parameter (P : ReturningPair D)
    (A : Subgroup G) (hEA : P.E ≤ A) (a : A ≃* Plane)
    (hz : a ⟨D.z,hEA P.z_mem_E⟩ = axis (Multiplicative.ofAdd 1))
    (hu : (a ⟨P.u,hEA P.u_mem_E⟩).toAdd 1 = 0) :
    (a ⟨P.u,hEA P.u_mem_E⟩).toAdd 0 ≠ 0 ∧
      (a ⟨P.u,hEA P.u_mem_E⟩).toAdd 0 ≠ 1 := by
  have ha := axis_of_second_zero _ hu
  constructor
  · intro h
    rw [h] at ha
    have hu1 : P.u = 1 := congrArg Subtype.val (a.injective
      (ha.trans ((axis.map_one).trans a.map_one.symm)))
    have hh := P.u_order
    simp [hu1] at hh
  · intro h
    rw [h,← hz] at ha
    exact P.ne (congrArg Subtype.val (a.injective ha))

/-- The two natural markings agree on every original element of the common
four-group. Their automizer markings still describe literal conjugation. -/
theorem compatible_automizer_markings (P : ReturningPair D) (hclass : OneInvolutionClass G)
    (eR : P.R ≃* Matrix.PSL3Four.RootNormalizerModel.Root) :
    ∃ (f₁ : (P.A₁ eR).normalizerMonoidHom.range ≃* LinearGroup)
      (a₁ : P.A₁ eR ≃* Plane)
      (f₂ : (P.A₂ eR).normalizerMonoidHom.range ≃* LinearGroup)
      (a₂ : P.A₂ eR ≃* Plane),
      (∀ n x, a₁ (n • x) = naturalAction (f₁ n) (a₁ x)) ∧
      (∀ n x, a₂ (n • x) = naturalAction (f₂ n) (a₂ x)) ∧
      (∀ (x : G) (hx₁ : x ∈ P.A₁ eR) (hx₂ : x ∈ P.A₂ eR),
        a₁ ⟨x,hx₁⟩ = a₂ ⟨x,hx₂⟩) ∧
      a₁ ⟨D.z,((P.planes_inf eR).ge.trans inf_le_left) P.z_mem_E⟩ = axis (Multiplicative.ofAdd 1) ∧
      ∀ x : P.E, (a₁ ⟨x,((P.planes_inf eR).ge.trans inf_le_left) x.property⟩).toAdd 1 = 0 := by
  have hE₁ : P.E ≤ P.A₁ eR := by
    rw [← P.planes_inf eR]; exact inf_le_left
  have hE₂ : P.E ≤ P.A₂ eR := by
    rw [← P.planes_inf eR]; exact inf_le_right
  obtain ⟨f₁,a₁,ha₁,hz₁,hl₁⟩ :=
    plane_marking_at_center P hclass _ (P.A₁_card eR) (P.A₁_le_R eR) hE₁
  obtain ⟨f₂,a₂,ha₂,hz₂,hl₂⟩ :=
    plane_marking_at_center P hclass _ (P.A₂_card eR) (P.A₂_le_R eR) hE₂
  have hc₁ := second_generator_parameter P _ hE₁ a₁ hz₁ (hl₁ ⟨P.u,P.u_mem_E⟩)
  have hc₂ := second_generator_parameter P _ hE₂ a₂ hz₂ (hl₂ ⟨P.u,P.u_mem_E⟩)
  obtain ⟨σ,hσ⟩ := align_nonbinary _ _ hc₂.1 hc₂.2 hc₁.1 hc₁.2
  let f₂' := f₂.trans (Matrix.GeneralLinearGroup.coefficientEquiv σ)
  let a₂' := a₂.trans (coefficientPlane σ)
  have hz₂' : a₂' ⟨D.z,hE₂ P.z_mem_E⟩ = axis (Multiplicative.ofAdd 1) := by
    change coefficientPlane σ (a₂ _) = _
    rw [hz₂,coefficientPlane_axis]
    change axis (Multiplicative.ofAdd (σ 1)) = axis (Multiplicative.ofAdd 1)
    rw [σ.map_one]
  have hu' : a₁ ⟨P.u,hE₁ P.u_mem_E⟩ = a₂' ⟨P.u,hE₂ P.u_mem_E⟩ := by
    change _ = coefficientPlane σ (a₂ _)
    have hu₂ : (a₂ ⟨P.u,hE₂ P.u_mem_E⟩).toAdd 1 = 0 := hl₂ ⟨P.u,P.u_mem_E⟩
    rw [axis_of_second_zero _ hu₂,coefficientPlane_axis]
    change _ = axis (Multiplicative.ofAdd (σ ((a₂ ⟨P.u,hE₂ P.u_mem_E⟩).toAdd 0)))
    rw [hσ]
    exact axis_of_second_zero _ (hl₁ ⟨P.u,P.u_mem_E⟩)
  have hh := E_hom_ext P (a₁.toMonoidHom.comp (inclusion hE₁))
    (a₂'.toMonoidHom.comp (inclusion hE₂)) (hz₁.trans hz₂'.symm) hu'
  refine ⟨f₁,a₁,f₂',a₂',ha₁,?_,?_,hz₁,hl₁⟩
  · intro n x
    change coefficientPlane σ (a₂ (n • x)) = _
    rw [ha₂]
    exact (coefficient_change_action σ (f₂ n) (a₂ x)).symm
  · intro x hx₁ hx₂
    have hx : x ∈ P.E := P.planes_inf eR ▸ (show x ∈ P.A₁ eR ⊓ P.A₂ eR from ⟨hx₁,hx₂⟩)
    exact congrArg (fun f : P.E →* Plane => f ⟨x,hx⟩) hh


/-- The full common plane normalizer is the stabilizer of either plane inside
N_G(R); the second plane cannot be lost when the first is fixed. -/
theorem overlap_eq_root_stabilizer (P : ReturningPair D)
    (eR : P.R ≃* Matrix.PSL3Four.RootNormalizerModel.Root) :
    normalizer (P.A₁ eR : Set G) ⊓ normalizer (P.A₂ eR : Set G) =
      normalizer (P.A₁ eR : Set G) ⊓ normalizer (P.R : Set G) := by
  apply le_antisymm
  · apply le_inf inf_le_left
    rw [← P.planes_sup eR]
    exact normalizer_inf_normalizer_le_normalizer_sup _ _
  · intro n hn
    refine ⟨hn.1,mem_normalizer_iff_map_conj_eq.mpr ?_⟩
    let b := MulAut.conj n
    let A := (P.A₂ eR).map b.toMonoidHom
    let : IsElementaryAbelian 2 A := IsElementaryAbelian.map _
    have hAR : A ≤ P.R := by
      have hh := map_mono (f := b.toMonoidHom) (P.A₂_le_R eR)
      have hr := mem_normalizer_iff_map_conj_eq.mp hn.2
      exact hh.trans hr.le
    have hAc : Nat.card A = 16 :=
      (card_map_of_injective b.injective).trans (P.A₂_card eR)
    rcases (P.elementary_sixteen_iff eR A hAR).mp ⟨inferInstance,hAc⟩ with h | h
    · have h₁ : (P.A₁ eR).map b.toMonoidHom = P.A₁ eR :=
        mem_normalizer_iff_map_conj_eq.mp hn.1
      exact False.elim (P.planes_ne eR (map_injective b.injective (h₁.trans h.symm)))
    · exact h

/-- The actual common subgroup has order 576, not the order of the full root normalizer. -/
theorem overlap_card (P : ReturningPair D)
    (eR : P.R ≃* Matrix.PSL3Four.RootNormalizerModel.Root) :
    Nat.card (normalizer (P.A₁ eR : Set G) ⊓ normalizer (P.A₂ eR : Set G) : Subgroup G) = 576 := by
  rw [overlap_eq_root_stabilizer P eR]
  exact P.plane_root_stabilizer_card _ (P.A₁_card eR) (P.A₁_le_R eR)

end CFSG.Quasithin.Janko23.J3Recognition.Ambient
