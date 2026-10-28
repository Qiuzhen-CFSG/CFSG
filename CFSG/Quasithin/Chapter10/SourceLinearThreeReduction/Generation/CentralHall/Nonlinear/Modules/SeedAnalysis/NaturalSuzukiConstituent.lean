module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Modules.SeedAnalysis.NaturalSuzukiDisplacement
public import Theory.Representation.Suzuki.ExchangedFixedSpace
public import Theory.Representation.BinaryOffender.ConstituentSchur

/-!
# A stable Schur-linear constituent for the original Suzuki pair

Start with the genuine starred actor and exchanged Suzuki pair constructed
from either original seed orientation. In the pair-centralizer fixed space,
the displacement bound forces every irreducible pair constituent to be
actor-invariant. Select one, prove the pair faithful on it, and identify its
actor kernel with the literal pair centralizer. The restricted actor retains
the fixed-space rank bound and a ratio strictly below the original cubic ratio.

The constituent degree is at least `8*(2*r+1)`. The resulting strict
half-dimension displacement bound forces all actors to commute with every
Schur endomorphism. Invariance under the exchanger and Schur linearity are
conclusions, not hypotheses. All actions remain on subspaces of the original
moved module, with the same natural quotient marking and source actor.

The tensor-exchange exclusion and the remaining original seed separation
and constituent analysis are still needed for SeedAnalysisAt and
SourceNonnormalCentralHallAt, owned by qt-d-10-nona5-central-hall-orders.
Source: Aschbacher--Smith D.3.7--9 and D.3.21, printed pp.197--201,204--207;
application 10.1.1, printed p.741.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
open Chapter3.Section02
/-- An actual invariant pair constituent, with its literal actor kernels,
rank, ratio, degree and Schur action. -/
@[expose] def InvariantSuzukiPairConstituent
    {Γ V : Type*} [Group Γ] [AddCommGroup V] [Module (ZMod 2) V]
    (σ : Representation (ZMod 2) Γ V) (A J : Subgroup Γ) (a : Γ) (r : ℕ) : Prop :=
    let X := J ⊔ J.map (MulAut.conj a).toMonoidHom
    let C := A ⊓ centralizer (X : Set Γ)
    ∃ U : Subrepresentation (σ.comp X.subtype),
       U.toRepresentation.IsIrreducible ∧ Function.Injective U.toRepresentation ∧
       U.toSubmodule ≤ fixedSpace σ C ∧ A ≤ subspaceStabilizer σ U.toSubmodule ∧
       subspaceKernel σ U.toSubmodule A = C ∧
       subspaceKernel σ (fixedSpace σ C) A = C ∧
       rank (restrictedSubgroup σ U.toSubmodule A) ≤ 2*r+2 ∧
       restrictedSubgroup σ U.toSubmodule A ∈ ChapterD.Qhat (subspaceImageRepresentation σ U.toSubmodule) ∧
       actionRatio (subspaceImageRepresentation σ U.toSubmodule)
         (restrictedSubgroup σ U.toSubmodule A) < cubicRatio σ ∧
       8 * (2*r+1) ≤ Module.finrank (ZMod 2) U.toSubmodule ∧
       ∀ b : subspaceStabilizer σ U.toSubmodule, (b : Γ) ∈ A →
         ∀ (f : IntertwiningMap U.toRepresentation U.toRepresentation) (v : U.toSubmodule),
           stabilizerRepresentation σ U.toSubmodule b (f v) =
             f (stabilizerRepresentation σ U.toSubmodule b v)

private theorem reduced_suzuki_constituent
    {Γ V : Type*} [Group Γ] [Finite Γ] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) Γ V) (hirr : σ.IsIrreducible)
    (A J : Subgroup Γ) (hA : A ∈ ChapterD.QhatStar σ) (hJ : IsComponent Γ J)
    (hi : (normalizer (J : Set Γ)).index = 2)
    (a : Γ) (ha : a ∈ A) (han : a ∉ normalizer (J : Set Γ))
    (hmJ : subspaceCommutator σ ⊤ J = ⊤)
    (r : ℕ) (hr : 0 < r) (eJ : J ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup r)
    (hXA : ⁅J ⊔ J.map (MulAut.conj a).toMonoidHom,A⁆ = J ⊔ J.map (MulAut.conj a).toMonoidHom)
    (hfixed :
      let C := A ⊓ centralizer ((J ⊔ J.map (MulAut.conj a).toMonoidHom : Subgroup Γ) : Set Γ)
      let W := fixedSpace σ C
      rank (restrictedSubgroup σ W A) ≤ 2*r+2 ∧
      restrictedSubgroup σ W A ∈ ChapterD.Qhat (subspaceImageRepresentation σ W) ∧
      actionRatio (subspaceImageRepresentation σ W) (restrictedSubgroup σ W A) < cubicRatio σ) :
    orderOf a = 2 ∧
    InvariantSuzukiPairConstituent σ A J a r := by
  let X := J ⊔ J.map (MulAut.conj a).toMonoidHom
  let C := A ⊓ centralizer (X : Set Γ)
  let W := fixedSpace σ C
  let : X.Normal := sup_conjugate_normal_of_normalizer_index_two J hi a han
  let : IsElementaryAbelian 2 A := hA.1.2.1.2
  obtain ⟨hsmall,hq,hdrop⟩ := hfixed
  change rank (restrictedSubgroup σ W A) ≤ 2*r+2 at hsmall
  change restrictedSubgroup σ W A ∈ ChapterD.Qhat (subspaceImageRepresentation σ W) at hq
  change actionRatio (subspaceImageRepresentation σ W) (restrictedSubgroup σ W A) < cubicRatio σ at hdrop
  have hc := (actionRatio_le_nat_iff _ hq.1 2).mp hq.2.2
  obtain ⟨U,hU,hUW,hUA,hf,hKU,hKW,hRU,hRatio,hdeg⟩ :=
    Representation.Suzuki.exchanged_fixedSpace_constituent σ hirr J hJ hi a han hmJ
      r hr eJ A hA.1.2.1 hXA (by
        change fixedCodim (subspaceImageRepresentation σ W)
          (restrictedSubgroup σ W A) ≤ 2 * (2*r+2)
        omega)
  have hnU : ¬ U.toSubmodule ≤ fixedSpace σ A := by
    intro hz
    have haK : a ∈ subspaceKernel σ U.toSubmodule A := ⟨ha, fun v hv => hz hv ⟨a,ha⟩⟩
    have haC : a ∈ C := by
      change subspaceKernel σ U.toSubmodule A = C at hKU
      rwa [←hKU]
    exact han ((Subgroup.centralizer_le_normalizer _) ((centralizer_le
      (show (J : Set Γ) ⊆ (X : Set Γ) from fun _ hx => (show J ≤ X from le_sup_left) hx)) haC.2))
  have ha2 : orderOf a = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian (p := 2) a ha)
    (fun he => han (he ▸ (normalizer (J : Set Γ)).one_mem))
  refine ⟨ha2,U,hU,hf,hUW,hUA,hKU,hKW,hRU.trans_le hsmall,?_,hRatio.trans_lt hdrop,hdeg,?_⟩
  · exact ⟨hA.1.2.1.restrictedSubgroup σ U.toSubmodule hUA hnU,
      ChapterD.isCubic_restrictedSubgroup σ U.toSubmodule hA.1.2.2.1,
      hRatio.trans hq.2.2⟩
  · apply constituent_schurLinear_of_small_restricted_codim σ X U hU A
    have hQ := hA.1.2.1.restrictedSubgroup σ U.toSubmodule hUA hnU
    have hCU := (actionRatio_le_nat_iff _ hQ 2).mp (hRatio.trans hq.2.2)
    have hrank := hRU.trans_le hsmall
    omega

universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance : IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D
local instance : FiniteDimensional (ZMod 2) (Additive (⁅D.fullModule,L⁆ : Subgroup G)) :=
  Module.Finite.of_finite
local instance (n : ℕ) : Algebra (ZMod 2) (GaloisField 2 n) := ZMod.algebra _ 2

-- The source declaration combines dependent action and quotient transports.
-- Keep its additional elaboration allowance local to this theorem.
set_option maxHeartbeats 400000 in
/-- The original natural Hall branch supplies an actual faithful irreducible
Suzuki-pair constituent preserved by the whole starred actor. Its exact actor
kernel, reduced rank and ratio, and Schur linearity are all proved. -/
theorem source_natural_suzuki_invariant_constituent
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
    let Γ := actionImage (movedStabilizerAction D)
    let σ := imageRepresentation (movedStabilizerAction D)
    Odd n ∧ ∃ (A J : Subgroup (Γ)) (r : ℕ),
      A ∈ ChapterD.QhatStar (σ) ∧
      IsComponent _ J ∧ J ≤ (movedNaturalImageQuotientAction D e I E hE).ker ∧
      0 < r ∧ Nonempty (J ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup r) ∧
      (normalizer (J : Set (Γ))).index = 2 ∧
      ∃ a : Γ, a ∈ A ∧ orderOf a = 2 ∧
        a ∉ normalizer (J : Set (Γ)) ∧
        componentOrbit J A = J ⊔ J.map (MulAut.conj a).toMonoidHom ∧
        subspaceCommutator (σ) ⊤ J = ⊤ ∧
        InvariantSuzukiPairConstituent σ A J a r := by
  intro Γ σ
  have hex := source_natural_starred_actor_suzuki_displacement (G := G) (T := T) (L := L) D
    (H := H) (B := B) c (t := t) ht htn hsep n hn e I hI E hE
  rcases hex with ⟨ho,A,J,r,h⟩
  have hA := h.1
  have hJ := h.2.2.2.1
  have hJK := h.2.2.2.2.1
  have hr := h.2.2.2.2.2.1
  obtain ⟨eJ⟩ := h.2.2.2.2.2.2.1
  have hm := h.2.2.2.2.2.2.2.1
  have hi := h.2.2.2.2.2.2.2.2.2.1
  have hfixed := h.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨a,hswap⟩ := h.2.2.2.2.2.2.2.2.2.2.2.2.2
  have ha := hswap.1
  have han := hswap.2.1
  have horbit := hswap.2.2.1
  have hmJ := hswap.2.2.2.1
  let X := J ⊔ J.map (MulAut.conj a).toMonoidHom
  let : X.Normal := sup_conjugate_normal_of_normalizer_index_two J hi a han
  have hirr : σ.IsIrreducible :=
    (irreducible_comp_surjective_iff (actionHom (movedStabilizerAction D))
      (movedStabilizerAction D).asGroupHom.rangeRestrict_surjective σ).mp
      (movedStabilizerAction_irreducible D c ht htn hsep)
  have hXA : ⁅X,A⁆ = X := by
    apply le_antisymm (commutator_le_left X A)
    calc
      X = ⁅X,A ⊓ (movedNaturalImageQuotientAction D e I E hE).ker⁆ := by
        simpa only [horbit] using hm.symm
      _ ≤ ⁅X,A⁆ := commutator_mono le_rfl inf_le_left
  dsimp only at hfixed
  rw [horbit] at hfixed
  have hred := reduced_suzuki_constituent σ hirr A J hA hJ hi a ha han hmJ r hr eJ hXA hfixed
  exact ⟨ho,A,J,r,hA,hJ,hJK,hr,⟨eJ⟩,hi,a,ha,hred.1,han,horbit,hmJ,hred.2⟩

end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
