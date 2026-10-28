module
public import Theory.Representation.G2NaturalOffenders.Long
public import Theory.AtlasPort.LinearGroups.G2.EvenInvolutionGeometry.PureLong
public import Theory.Representation.BinaryOffender.RatioFromStrong

/-!
# Offenders on the natural even G₂ module

Every offender is conjugate to the concrete elementary subgroup generated
by the A, B and C root curves. Pure-long elementary groups lie in a common
long-root plane, which cannot offend. An offender containing a short root
is identified with the A–B–C subgroup by the sharp two-rank and fixed-space
calculation. Thus every offender has binary rank and fixed codimension
three times the field degree, there are no strong offenders, and the
quadratic ratio is one. In particular one common conjugator places the
specified long and short root elements in every offender.

This proves the inner-group natural-module geometry used in
Aschbacher–Smith B.4.6(13), printed pp.88–90, and in the B.5.1 trace
argument. All groups and representations here are the actual octonion
model and its six-dimensional natural quotient.
-/

@[expose] public noncomputable section
namespace Atlas.G2.NaturalOffenders
open Representation Representation.BinaryOffender Subgroup
variable {F : Type*} [Field F] [CharP F 2] [Algebra (ZMod 2) F] [Finite F]

private theorem offender_conj (A : Subgroup (Model F))
    (hA : IsOffender (binaryAction (F:=F)) A) (g : Model F) :
    IsOffender (binaryAction (F:=F)) (A.map (MulAut.conj g).toMonoidHom) := by
  refine ⟨hA.1.map_conj g, ?_⟩
  rw [fixedCodim_map_conj, rank_map_conj]
  exact hA.2

theorem offender_conjugate_elementary {n : ℕ} (hc : Nat.card F = 2^n) (hn : 0<n)
    (A : Subgroup (Model F)) (hA : IsOffender (binaryAction (F:=F)) A) :
    ∃ g : Model F, A = (EvenTwoRank.elementary F).map (MulAut.conj g).toMonoidHom := by
  let : IsElementaryAbelian 2 A := hA.1.2
  by_cases hs : ∃ b ∈ A, ShortRootProducts.IsShortRootElement b
  · obtain ⟨b,hb,a,ha,g,rfl⟩ := hs
    have hm : rootC a ∈ A.map (MulAut.conj g⁻¹).toMonoidHom := by
      refine ⟨MulAut.conj g (rootC a), hb, ?_⟩
      simp [MulAut.conj_apply,mul_assoc]
    have he := offender_eq_elementary_of_shortRoot hc _ (offender_conj A hA g⁻¹) a ha hm
    refine ⟨g, le_antisymm ?_ ?_⟩
    · intro x hx
      refine ⟨MulAut.conj g⁻¹ x, ?_, ?_⟩
      · rw [← he]
        exact mem_map_of_mem _ hx
      · simp [MulAut.conj_apply,mul_assoc]
    · rintro x ⟨y,hy,rfl⟩
      rw [← he] at hy
      obtain ⟨z,hz,rfl⟩ := hy
      simpa [MulAut.conj_apply,mul_assoc] using hz
  · have hp : ∀ b ∈ A, b ≠ 1 → ShortRootProducts.IsLongRootElement b := by
      intro b hb hb1
      have hh := EvenInvolutionGeometry.involution_isRoot
        (elemPow_eq_one_of_isElementaryAbelian b hb) hb1
      rcases hh with ⟨g,a,ha,hx⟩ | ⟨g,a,ha,hx⟩
      · exact ⟨a,ha,g,hx⟩
      · exact (hs ⟨b,hb,a,ha,g,hx⟩).elim
    obtain ⟨g,hg⟩ := EvenInvolutionGeometry.PureLong.exists_map_le_longRootLocal A hA.1.2 hp
    exact (not_offender_of_le_longRootLocal hc hn _ hg (offender_conj A hA g)).elim

theorem natural_offender_conjugate_elementary {n : ℕ} (hc : Nat.card F = 2^n) (hn : 0<n)
    (A : Subgroup (Model F)) (hA : IsOffender (binaryNatural (F:=F)) A) :
    ∃ g : Model F, A = (EvenTwoRank.elementary F).map (MulAut.conj g).toMonoidHom :=
  offender_conjugate_elementary hc hn A ((natural_offender_iff A).mp hA)

theorem natural_offender_rank {n : ℕ} (hc : Nat.card F = 2^n) (hn : 0<n)
    (A : Subgroup (Model F)) (hA : IsOffender (binaryNatural (F:=F)) A) : rank A = 3*n := by
  obtain ⟨g,rfl⟩ := natural_offender_conjugate_elementary hc hn A hA
  rw [rank_map_conj, elementary_rank hc]

theorem natural_offender_fixedCodim {n : ℕ} (hc : Nat.card F = 2^n) (hn : 0<n)
    (A : Subgroup (Model F)) (hA : IsOffender (binaryNatural (F:=F)) A) :
    fixedCodim (binaryNatural (F:=F)) A = 3*n := by
  obtain ⟨g,rfl⟩ := natural_offender_conjugate_elementary hc hn A hA
  rw [natural_fixedCodim_eq,fixedCodim_map_conj,fixedCodim_elementary hc]

theorem natural_offender_rootPair {n : ℕ} (hc : Nat.card F = 2^n) (hn : 0<n)
    (A : Subgroup (Model F)) (hA : IsOffender (binaryNatural (F:=F)) A) :
    ∃ g : Model F, g * rootA 1 * g⁻¹ ∈ A ∧ g * rootC 1 * g⁻¹ ∈ A := by
  obtain ⟨g,rfl⟩ := natural_offender_conjugate_elementary hc hn A hA
  exact ⟨g, mem_map_of_mem (MulAut.conj g).toMonoidHom (rootA_mem_elementary 1),
    mem_map_of_mem (MulAut.conj g).toMonoidHom (rootC_mem_elementary 1)⟩

theorem natural_no_strong {n : ℕ} (hc : Nat.card F = 2^n) (hn : 0<n) :
    ¬ IsStrongFFModule (binaryNatural (F:=F)) := by
  rintro ⟨A,hA⟩
  have ho : IsOffender (binaryNatural (F:=F)) A := ⟨hA.1,hA.2.le⟩
  have hr := natural_offender_rank hc hn A ho
  have hd := natural_offender_fixedCodim hc hn A ho
  have hl := hA.2
  omega

theorem natural_elementary_offender {n : ℕ} (hc : Nat.card F = 2^n) (hn : 0<n) :
    IsOffender (binaryNatural (F:=F)) (EvenTwoRank.elementary F) := by
  refine ⟨⟨?_,inferInstance⟩, ?_⟩
  · intro h
    have hr := elementary_rank hc
    rw [h,Representation.BinaryOffender.rank_bot] at hr
    omega
  · rw [natural_fixedCodim_eq,fixedCodim_elementary hc,elementary_rank hc]

theorem natural_bestOffender_iff_conjugate {n : ℕ} (hc : Nat.card F = 2^n) (hn : 0<n)
    (A : Subgroup (Model F)) :
    IsBestOffender (binaryNatural (F:=F)) A ↔
      ∃ g : Model F, A = (EvenTwoRank.elementary F).map (MulAut.conj g).toMonoidHom := by
  constructor
  · intro hA
    exact natural_offender_conjugate_elementary hc hn A (hA.isOffender _)
  · rintro ⟨g,rfl⟩
    apply (isBestOffender_iff_of_not_strong _ (natural_no_strong hc hn) _).mpr
    refine ⟨(natural_elementary_offender hc hn).1.map_conj g, ?_⟩
    rw [natural_fixedCodim_eq,fixedCodim_map_conj,rank_map_conj,
      fixedCodim_elementary hc,elementary_rank hc]

theorem natural_quadraticRatio {n : ℕ} (hc : Nat.card F = 2^n) (hn : 0<n) :
    quadraticRatio (binaryNatural (F:=F)) = 1 := by
  apply quadraticRatio_eq_one_of_no_strong
    _ ⟨EvenTwoRank.elementary F,natural_elementary_offender hc hn⟩
  intro A hA
  exact natural_no_strong hc hn ⟨A,hA⟩

end Atlas.G2.NaturalOffenders
