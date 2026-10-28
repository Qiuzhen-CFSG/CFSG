module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.NativeSourceRankOne.Models
public import Theory.SpecificGroups.PSL2.SylowPointwiseInner
public import Theory.SpecificGroups.Suzuki.BorelPointwiseRigidity
public import Theory.SpecificGroups.SU3.SylowPointwiseInner.Full
public import Theory.GroupAction.SylowPointwiseInnerTransport

/-!
# Sylow pointwise automorphisms of the Section 16 circle

The concrete linear, Suzuki and unitary calculations identify every pointwise
Sylow fixer with conjugation by an element of that same Sylow subgroup.
Faithfulness of the central quotient action lifts the result to the actual
perfect circle, including its possible central cover. This is the precise
model input for the central Omega step of 16.4(b) and the order-two
centralizer Sylow calculation in 16.6(b).

Source: GLS IV, Chapter 2, Lemma 16.4(b) and Corollary 16.6(b), using
Chapter 4, Lemma 3.6(a).
-/

noncomputable section
namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII PFchapter1section1 Subgroup
open _root_.BenderSuzuki.MatrixGroups
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

/-- The actual simple Bender models have Sylow pointwise fixer equal to
inner conjugation by the same Sylow. No automorphism-order premise is used. -/
public theorem simpleBender_fixing_sylow_inner
    (hG : IsSimpleBenderGroup G) (P : Sylow 2 G) (a : MulAut G)
    (hfix : ∀ x ∈ P, a x = x) : ∃ x ∈ P, a = MulAut.conj x := by
  obtain ⟨n,hn,hm⟩ := hG.exists_exponent
  rcases hm with hl | hs | hu
  · obtain ⟨e⟩ := hl
    exact MulAut.fixing_sylow_inner_of_equiv e
      Theory.PSL2.aut_fixing_sylow_inner P a hfix
  · obtain ⟨m,hnm,⟨e⟩⟩ := hs
    exact suzuki_aut_fixing_sylow_inner (by omega) e P a hfix
  · obtain ⟨E,hE,hEf,J,hJ,hcard,hfixed,⟨e⟩⟩ := hu
    let : Field E := hE
    let : Finite E := hEf
    let : IsSimpleGroup G := hG.isSimple
    let : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J) := e.isSimpleGroup_congr.mp inferInstance
    exact MulAut.fixing_sylow_inner_of_equiv e
      (HermitianForm.SylowPointwiseInner.fixing_sylow_eq_mem_conj J hn hcard
        (External.huppert_II_10_4_conj_eq_frobenius J (2 ^ n) hcard hfixed)) P a hfix

/-- The source pointwise-Sylow automorphism theorem on the original
perfect centralizer circle, retaining its literal Sylow subgroup. -/
public theorem source16_circle_fixing_sylow_inner
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) {u : G} (hu : PFAppendixIII.IsInvolution u)
    (huM : u ∈ M) (hBM : ¬ centralizer ({u} : Set G) ≤ M)
    (hns : ¬ Group.IsSolvable (localCircle Z (centralizer ({u} : Set G))))
    (P : Sylow 2 (localCircle Z (centralizer ({u} : Set G))))
    (a : MulAut (localCircle Z (centralizer ({u} : Set G))))
    (hfix : ∀ x ∈ P, a x = x) : ∃ x ∈ P, a = MulAut.conj x := by
  let B := centralizer ({u} : Set G)
  let C := localCircle Z B
  obtain ⟨z,hz,hzM,hzu⟩ := exists_distinguished_commuting_in_M h.disconnected r hu huM
  obtain ⟨_,hperfect,hmodel,_⟩ := localCircle_nonsolvable_structure h r ha B
    (r.involution_centralizer_ne_top h.disconnected hu) hBM
    ⟨z,hz,mem_centralizer_singleton_iff.mpr hzu.eq,hzM⟩ hns
  let : Group.IsPerfect C := ⟨hperfect⟩
  exact MulAut.fixing_sylow_inner_of_centralQuotient (MulEquiv.refl _)
    (simpleBender_fixing_sylow_inner hmodel) P a hfix

/-- The actual ambient pointwise Sylow centralizer is contained in the
product of the mapped Sylow center and the circle centralizer. This is the
literal `C_{T₁}(P) ≤ Q C_{T₁}(B°)` model step used in 16.6(b). -/
public theorem source16_circle_sylow_centralizer_le
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) {u : G} (hu : PFAppendixIII.IsInvolution u)
    (huM : u ∈ M) (hBM : ¬ centralizer ({u} : Set G) ≤ M)
    (hns : ¬ Group.IsSolvable (localCircle Z (centralizer ({u} : Set G))))
    (P : Sylow 2 (localCircle Z (centralizer ({u} : Set G)))) :
    let B := centralizer ({u} : Set G)
    let C := localCircle Z B
    let f := localCircleHom Z B
    let Q := (omegaOneAmbient (P : Subgroup C)).map f
    B ⊓ centralizer ((P : Subgroup C).map f : Set G) ≤
      Q ⊔ (B ⊓ centralizer (localCircleIn Z B : Set G)) := by
  let B := centralizer ({u} : Set G)
  let C := localCircle Z B
  let f := localCircleHom Z B
  let Q := (omegaOneAmbient (P : Subgroup C)).map f
  obtain ⟨z,hz,hzM,hzu⟩ := exists_distinguished_commuting_in_M h.disconnected r hu huM
  have hne : ∃ z ∈ Z, z ∈ B ∧ z ∈ M :=
    ⟨z,hz,mem_centralizer_singleton_iff.mpr hzu.eq,hzM⟩
  let : C.Normal := localCircle_normal h.disconnected B hBM hne
  obtain ⟨n,hn,_,hgeom⟩ := involutionCentralizer_circle_models h r ha hu huM hBM hns
  have hOmega := (hgeom P).1
  change B ⊓ centralizer ((P : Subgroup C).map f : Set G) ≤
    Q ⊔ (B ⊓ centralizer (localCircleIn Z B : Set G))
  intro v hv
  let n : normalizer (C : Set B) := ⟨⟨v,hv.1⟩, by rw [normalizer_eq_top]; trivial⟩
  let a : MulAut C := C.normalizerMonoidHom n
  have hfix : ∀ x ∈ P, a x = x := by
    intro x hx
    apply (localCircleHom_injective Z B)
    change v * f x * v⁻¹ = f x
    rw [← hv.2 (f x) (mem_map_of_mem f hx), mul_inv_cancel_right]
  obtain ⟨c,hcP,hc⟩ := source16_circle_fixing_sylow_inner h r ha hu huM hBM hns P a hfix
  have hcZ : (⟨c,hcP⟩ : (P : Subgroup C)) ∈ center (P : Subgroup C) := by
    rw [mem_center_iff]
    intro x
    apply Subtype.ext
    have hh := DFunLike.congr_fun hc (x : C)
    rw [hfix x x.property] at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh.symm).symm
  have hcQ : f c ∈ Q := by
    apply mem_map_of_mem
    rw [hOmega]
    exact mem_map_of_mem (P : Subgroup C).subtype hcZ
  let w := (f c)⁻¹ * v
  have hwB : w ∈ B := B.mul_mem (B.inv_mem c.val.property) hv.1
  have hwC : w ∈ centralizer (localCircleIn Z B : Set G) := by
    rintro x ⟨xB,hxC,rfl⟩
    let xC : C := ⟨xB,hxC⟩
    have he := congrArg f (DFunLike.congr_fun hc xC)
    change v * f xC * v⁻¹ = f c * f xC * (f c)⁻¹ at he
    change f xC * w = w * f xC
    symm
    calc
      w * f xC = (f c)⁻¹ * (v * f xC * v⁻¹) * v := by dsimp only [w]; group
      _ = (f c)⁻¹ * (f c * f xC * (f c)⁻¹) * v := by rw [he]
      _ = f xC * w := by dsimp only [w]; group
  have hvprod : f c * w = v := by dsimp only [w]; group
  rw [← hvprod]
  exact mul_mem_sup hcQ ⟨hwB,hwC⟩

end BenderSuzuki.ZD
