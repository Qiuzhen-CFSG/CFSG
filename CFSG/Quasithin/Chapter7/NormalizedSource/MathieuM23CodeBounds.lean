module
public import CFSG.Quasithin.ChapterE.Section03.Parameters.Module
public import CFSG.Quasithin.ChapterE.Section03.Offenders.Calculus
public import CFSG.Quasithin.Chapter7.Section01To05.M23Span
public import Theory.Mathieu.M23.Properties.TwoRank
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Octad.SourceInvolutions
public import Theory.Representation.MathieuCodeRestriction.QuadraticActors.NoFF
public import Theory.Representation.MathieuCodeRestriction.OddFixedSpaces.Spectrum
public import Theory.Representation.BinaryOffender.QuadraticRatioTransport
public import Theory.Representation.BinaryOffender.UniformFixedSpace

/-!
# The M₂₃ code estimates for the escaping-space argument

Every elementary sixteen contains the marked common four, whose code fixed
space has dimension four. An (F-1)-offender would consequently have rank
three and displacement four. All its nonidentity elements would have the
same fixed space, giving a quadratic eight, contrary to the proved quadratic
actor bound. Thus the actual code has a strict higher-Thompson gap.

The native odd-prime spectrum gives displacement at least six; cyclic duality
transfers this bound from cocode to code. Both estimates are transported
through actual group and linear markings. NonFFSourceMathieuM23Code uses
them in E.6.27 and completes the literal M₂₃-code application of 7.5.4.
Source: Aschbacher--Smith H.14.4,H.16.8 and7.4.1--7.5.4,
printed pp.397--398,405,700.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter7.NormalizedSource
open ChapterE ChapterH.Section13To16 Sporadic.Mathieu MathieuCode
open Sporadic.Mathieu.M24LocalGeometry

private theorem m23Code_moduleM : 4 ≤ moduleM m23CodeRepresentation := by
  apply le_csInf ⟨_, Set.mem_insert _ _⟩
  rintro d (rfl | ⟨t,ht,rfl⟩)
  · rw [finrank_code]; decide
  · rw [m23_code_cocode_fixedCodim_zpowers,
      CocodeOctad.Involutions.m23_involution_fixedCodim t ht]

private theorem m23Code_common_codim :
    fixedCodim m23CodeRepresentation m23CommonKernel = 7 := by
  have hK : m23CommonKernel.map pointEmbedding ≤ octadPointwiseKernel standardOctad := by
    rw [← octad_core_map_eq_pointwise]
    rintro _ ⟨x,hx,rfl⟩
    exact hx.1
  have hcard : Nat.card (m23CommonKernel.map pointEmbedding) = 4 := by
    rw [Subgroup.card_map_of_injective pointEmbedding_injective]
    exact m23CommonKernel_card
  have hdim : Module.finrank (ZMod 2) (fixedSpace m23CodeRepresentation m23CommonKernel) = 4 := by
    rw [m23CodeRepresentation, fixedSpace_comp_map]
    exact octad_kernel_four_fixed_finrank standardOctad _ hK hcard
  have hd := fixedCodim_add_finrank m23CodeRepresentation m23CommonKernel
  rw [hdim,finrank_code] at hd
  omega

/-- The actual M23 code has no (F-1)-offender. Rank four is excluded by
its common-four fixed space; rank three would force a quadratic eight. -/
theorem m23Code_fixedCodim_gap (A : Subgroup M23) (hA : IsElementaryTwo A) :
    rank A + 1 < fixedCodim m23CodeRepresentation A := by
  let := hA.2
  have hmin := m23Code_moduleM.trans (moduleM_le_fixedCodim m23CodeRepresentation hA)
  have hr := (offender_rank_le_primeRank A).trans m23_twoRank_le_four
  by_contra hgap
  have hcod : fixedCodim m23CodeRepresentation A ≤ rank A + 1 := by omega
  have hfour : rank A ≠ 4 := by
    intro he
    have hc : Nat.card A = 16 := by
      obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_card_eq
      have hn4 : n = 4 := by simpa only [rank,hn,Nat.log_pow Nat.one_lt_two] using he
      rw [hn,hn4]
      rfl
    obtain ⟨g,hg⟩ := standardM23_card16_contains_common_conjugate A hA.2 hc
    have hlo := fixedCodim_mono m23CodeRepresentation hg
    rw [fixedCodim_map_conj,m23Code_common_codim] at hlo
    omega
  have hr3 : rank A = 3 := by omega
  have hc4 : fixedCodim m23CodeRepresentation A = 4 := by omega
  have hsame : ∀ a ∈ A, a ≠ 1 →
      fixedSpace m23CodeRepresentation A = fixedSpace m23CodeRepresentation (zpowers a) := by
    intro a ha hane
    have hao : orderOf a = 2 :=
      orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian a ha) hane
    have hlow := m23Code_moduleM.trans (moduleM_le_involution m23CodeRepresentation hao)
    have hhigh := fixedCodim_mono m23CodeRepresentation (zpowers_le.mpr ha)
    exact fixedSpace_eq_of_fixedCodim_eq m23CodeRepresentation (zpowers_le.mpr ha) (by omega)
  have hquad := isQuadratic_of_common_fixedSpace m23CodeRepresentation hsame
  let B := A.map pointEmbedding
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map pointEmbedding
  have hBq : IsQuadratic codeRepresentation B :=
    quadratic_map_equivariant m23CodeRepresentation codeRepresentation pointEmbedding
      (LinearEquiv.refl _ _) (fun _ _ => rfl) hquad
  have hcard := QuadraticActors.m24_code_card_le_four B hBq
  rw [show Nat.card B = Nat.card A from card_map_of_injective pointEmbedding_injective] at hcard
  have hlog : rank A ≤ 2 := (Nat.log_mono_right hcard).trans (by decide : Nat.log 2 4 ≤ 2)
  omega

/-- Group and linear markings transport the strict code displacement gap. -/
theorem m23Code_marked_fixedCodim_gap
    {X W : Type*} [Group X] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) X W) (hc : IsM23Code ρ)
    (A : Subgroup X) (hA : IsElementaryTwo A) :
    rank A + 1 < fixedCodim ρ A := by
  obtain ⟨e,E,he⟩ := hc
  let := hA.2
  have hAm : IsElementaryTwo (A.map e.toMonoidHom) :=
    ⟨fun hb => hA.1 ((A.map_eq_bot_iff_of_injective e.injective).mp hb),
      IsElementaryAbelian.map e.toMonoidHom⟩
  have hh := m23Code_fixedCodim_gap _ hAm
  rw [rank_map_injective e.toMonoidHom e.injective,
    ←fixedCodim_map_equivariant ρ m23CodeRepresentation e.toMonoidHom E he] at hh
  exact hh

/-- Every odd prime actor of a marked M23 code moves at least six dimensions.
The duality used here is for a cyclic subgroup, not a common fixed space. -/
theorem m23Code_marked_odd_fixedCodim
    {X W : Type*} [Group X] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) X W) (hc : IsM23Code ρ)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (a : X) (ha : orderOf a = p) :
    6 ≤ fixedCodim ρ (zpowers a) := by
  obtain ⟨e,E,he⟩ := hc
  rw [fixedCodim_map_equivariant ρ m23CodeRepresentation e.toMonoidHom E he,
    MonoidHom.map_zpowers,m23_code_cocode_fixedCodim_zpowers]
  exact m23_cocode_fixedCodim_ge_six _ hp ho
    ((Nat.card_zpowers (e a)).trans ((e.orderOf_eq a).trans ha))
end CFSG.Quasithin.Chapter7.NormalizedSource
