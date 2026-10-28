module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Modules.SeedAnalysis.NaturalSuzukiPair
public import Theory.Representation.Suzuki.ComponentPairDegree

/-!
# The degree cost of the literal natural-kernel Suzuki pair

The previously extracted Suzuki component and its conjugate both move the
whole original moved module. Clifford restriction and the component-pair
kernel argument therefore make every nonzero pair submodule faithful.
The commuting perfect factor forces two nonzero Suzuki summands, giving
binary degree at least `8*(2*r+1)` on each such submodule.

The original natural SL₂ centralizer acts on two identical invariant
summands. Restrict one of those literal kernel summands to the same Suzuki
pair and apply that bound; the original moved module consequently has
degree at least `16*(2*r+1)`. The source application constructs the actual
Suzuki marking from the original Hall context. Both seed orientations are
retained, and no invariant pair constituent is assumed to be fixed by the
exchanger.

This proves a degree obstruction inside the remaining full-movement branch.
The actor fixed-codimension comparison, tensor exclusion, original seed
separation and constituent construction, and final `SeedAnalysisAt` and
`SourceNonnormalCentralHallAt` assembly remain with
qt-d-10-nona5-central-hall-orders.
Source: Aschbacher--Smith D.3.7, D.3.9 and D.3.21,
printed pp.197--201,204--207; application 10.1.1, p.741.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
open Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance naturalTensorElementary : IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D
local instance naturalTensorFiniteDimensional :
    FiniteDimensional (ZMod 2) (Additive (⁅D.fullModule,L⁆ : Subgroup G)) := Module.Finite.of_finite
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
local instance naturalTensorAlgebra : Algebra (ZMod 2) F := ZMod.algebra _ 2

/-- The literal natural centralizer double amplifies the exchanged Suzuki-pair
bound to sixteen times the Suzuki field degree on the original moved module. -/
theorem natural_suzuki_pair_degree_bound
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (I : Subrepresentation ((movedStabilizerAction D).comp (movedStabilizerComponent D).subtype))
    (hI : I.toRepresentation.IsIrreducible)
    (E : (Fin 2 → F) ≃ₗ[ZMod 2] I.toSubmodule)
    (hE : ∀ (l : movedStabilizerComponent D) v,
      E (naturalComponent e ⟨l.val.val,l.property⟩ v) = I.toRepresentation l (E v))
    (J : Subgroup (actionImage (movedStabilizerAction D)))
    (hJ : IsComponent _ J) (hJK : J ≤ (movedNaturalImageQuotientAction D e I E hE).ker)
    (hindex : (normalizer (J : Set (actionImage (movedStabilizerAction D)))).index = 2)
    (a : actionImage (movedStabilizerAction D))
    (han : a ∉ normalizer (J : Set (actionImage (movedStabilizerAction D))))
    (hm : subspaceCommutator (imageRepresentation (movedStabilizerAction D)) ⊤ J = ⊤)
    (r : ℕ) (hr : 0 < r) (eJ : J ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup r) :
    16 * (2*r+1) ≤ Module.finrank (ZMod 2) (Additive (⁅D.fullModule,L⁆ : Subgroup G)) := by
  let ρ := movedStabilizerAction D
  let σ := imageRepresentation ρ
  let α := movedNaturalImageQuotientAction D e I E hE
  let K := J.map (MulAut.conj a).toMonoidHom
  let X := J ⊔ K
  have hi : σ.IsIrreducible :=
    (irreducible_comp_surjective_iff (actionHom ρ) ρ.asGroupHom.rangeRestrict_surjective σ).mp
      (movedStabilizerAction_irreducible D c ht htn hsep)
  let : σ.IsIrreducible := hi
  let := Subrepresentation.irreducible_module_nontrivial σ
  obtain ⟨U,⟨eU⟩⟩ := naturalImageQuotientAction_kernel_double D c ht htn hsep e I hI E hE
  have hdim : Module.finrank (ZMod 2) (Additive (⁅D.fullModule,L⁆ : Subgroup G)) =
      Module.finrank (ZMod 2) U.toSubmodule + Module.finrank (ZMod 2) U.toSubmodule := by
    simpa only [Module.finrank_prod] using eU.toLinearEquiv.finrank_eq
  have hUb : U ≠ ⊥ := by
    intro he
    have hz : Module.finrank (ZMod 2) U.toSubmodule = 0 := by
      rw [he]
      exact finrank_bot (ZMod 2) _
    have hp := Module.finrank_pos (R := ZMod 2)
      (M := Additive (⁅D.fullModule,L⁆ : Subgroup G))
    omega
  have hXK : X ≤ α.ker := by
    apply sup_le hJK
    rintro x ⟨j,hj,rfl⟩
    exact (inferInstance : α.ker.Normal).conj_mem j (hJK hj) a
  let P : Subrepresentation (σ.comp X.subtype) := {
    toSubmodule := U.toSubmodule
    apply_mem_toSubmodule x v hv := U.apply_mem_toSubmodule ⟨x.val,hXK x.property⟩ hv }
  have hPb : P ≠ ⊥ := by
    intro he
    have he' : P.toSubmodule = ⊥ :=
      congrArg (fun S : Subrepresentation (σ.comp X.subtype) => S.toSubmodule) he
    exact hUb (Subrepresentation.toSubmodule_injective he')
  have hb := Representation.Suzuki.exchanged_pair_subrepresentation_finrank_ge
    σ hi J hJ hindex a han hm r hr eJ P hPb
  change 8 * (2*r+1) ≤ Module.finrank (ZMod 2) U.toSubmodule at hb
  omega

local instance naturalTensorGaloisAlgebra (n : ℕ) : Algebra (ZMod 2) (GaloisField 2 n) :=
  ZMod.algebra _ 2

omit [Field F] [Finite F] [CharP F 2] in
/-- Apply the pair degree estimate to the actual Suzuki factor extracted from
 the original natural Hall context, preserving its marking and quotient kernel. -/
theorem source_natural_suzuki_pair_degree_bound
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))
    (n : ℕ) (hn : 1 < n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n))
    (I : Subrepresentation ((movedStabilizerAction D).comp (movedStabilizerComponent D).subtype))
    (hI : I.toRepresentation.IsIrreducible)
    (E : (Fin 2 → GaloisField 2 n) ≃ₗ[ZMod 2] I.toSubmodule)
    (hE : ∀ (l : movedStabilizerComponent D) v,
      E (naturalComponent e ⟨l.val.val,l.property⟩ v) = I.toRepresentation l (E v)) :
    ∃ (J : Subgroup (actionImage (movedStabilizerAction D))) (r : ℕ),
      IsComponent _ J ∧ J ≤ (movedNaturalImageQuotientAction D e I E hE).ker ∧
      0 < r ∧ Nonempty (J ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup r) ∧
      16 * (2*r+1) ≤ Module.finrank (ZMod 2) (Additive (⁅D.fullModule,L⁆ : Subgroup G)) := by
  obtain ⟨_,A,J,_,_,_,_,hJ,hJK,⟨r,hr,⟨eJ⟩⟩,_,_,hindex,a,_,han,_,hm,_⟩ :=
    source_natural_starred_actor_suzuki_full_movement D c ht htn hsep n hn e I hI E hE
  exact ⟨J,r,hJ,hJK,hr,⟨eJ⟩,
    natural_suzuki_pair_degree_bound D c ht htn hsep e I hI E hE J hJ hJK hindex a han hm r hr eJ⟩
end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
