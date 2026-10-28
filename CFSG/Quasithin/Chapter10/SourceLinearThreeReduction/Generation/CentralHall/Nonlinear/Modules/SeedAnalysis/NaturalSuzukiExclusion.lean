module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Modules.SeedAnalysis.NaturalSuzukiConstituent
public import Theory.Representation.Suzuki.ExchangedTensor

/-!
# Excluding the genuine exchanged Suzuki pair in the natural Hall branch

The invariant pair constituent constructed from the source starred actor has
binary degree at least `8*(2*r+1)`. Its actual exchanger is Schur-linear and
therefore moves at least three-eighths of that dimension. This exceeds the
whole reduced actor's displacement budget `2*(2*r+2)` for every `r > 0`.

Apply this contradiction to both original seed orientations. No natural
constituent can occur in the literal moved module once seed separation is
proved; the quotient marking, original actor and original module are retained.
Original seed separation and the remaining constituent rows still belong to
qt-d-10-nona5-central-hall-orders, which retains final SeedAnalysisAt and
SourceNonnormalCentralHallAt assembly.
Source: Aschbacher--Smith D.3.7--9, D.3.21 and10.1.1,
printed pp.197--201,204--207 and741.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender

/-- The reduced source actor cannot exchange a faithful irreducible Suzuki
pair constituent: three-eighths of its degree exceeds the entire actor budget. -/
theorem not_invariantSuzukiPairConstituent
    {Γ V : Type*} [Group Γ] [Finite Γ] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) Γ V) (A J : Subgroup Γ) (hJ : IsComponent Γ J)
    (a : Γ) (ha : a ∈ A) (ha2 : orderOf a = 2)
    (han : a ∉ normalizer (J : Set Γ))
    (r : ℕ) (hr : 0 < r) (eJ : J ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup r) :
    ¬ InvariantSuzukiPairConstituent σ A J a r := by
  rintro ⟨U,hU,hf,_,hUA,_,_,hrank,hq,_,hdeg,hschur⟩
  let b : subspaceStabilizer σ U.toSubmodule := ⟨a,hUA ha⟩
  let T := stabilizerRepresentation σ U.toSubmodule b
  have h2 : a*a=1 := by simpa only [ha2,pow_two] using pow_orderOf_eq_one a
  have hb2 : b*b=1 := Subtype.ext h2
  have hT2 : T*T=1 := by
    change stabilizerRepresentation σ U.toSubmodule b * stabilizerRepresentation σ U.toSubmodule b = 1
    rw [←map_mul,hb2,map_one]
  have hd := Representation.Suzuki.exchanged_component_displacement J hJ a h2 han r hr eJ
    U.toRepresentation hU hf T hT2 (by
      intro x y hxy v
      apply Subtype.ext
      change σ a (σ (x : Γ) (v : V)) = σ (y : Γ) (σ a (v : V))
      rw [←hxy]
      simp only [←Module.End.mul_apply,←map_mul,mul_assoc,inv_mul_cancel,mul_one])
    (hschur b ha)
  let τ := subspaceImageRepresentation σ U.toSubmodule
  let B := restrictedSubgroup σ U.toSubmodule A
  let b' := subspaceActionHom σ U.toSubmodule b
  have hb' : b' ∈ B := ⟨b,ha,rfl⟩
  have hc := NaturalTensor.operatorFixedCodim_le_fixedCodim τ B hb'
  have he : NaturalTensor.operatorFixedCodim (τ b') =
      Module.finrank (ZMod 2) (T-1).range :=
    rfl
  rw [he] at hc
  have hbound := (actionRatio_le_nat_iff _ hq.1 2).mp hq.2.2
  change fixedCodim τ B ≤ 2 * rank B at hbound
  change rank B ≤ 2*r+2 at hrank
  omega

open Chapter3.Section02
open scoped MatrixGroups IsMulCommutative
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance : IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D
local instance : FiniteDimensional (ZMod 2) (Additive (⁅D.fullModule,L⁆ : Subgroup G)) :=
  Module.Finite.of_finite
local instance (n : ℕ) : Algebra (ZMod 2) (GaloisField 2 n) := ZMod.algebra _ 2

/-- In either original separated seed orientation, a natural constituent of
the literal full moved module is impossible. All exchanged Suzuki-pair and
Schur-linearity premises are constructed from the original Hall context. -/
theorem no_natural_constituent_of_seed_separated
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
      E (naturalComponent e ⟨l.val.val,l.property⟩ v) = I.toRepresentation l (E v)) : False := by
  obtain ⟨_,A,J,r,_,hJ,_,hr,⟨eJ⟩,_,a,ha,ha2,han,_,_,hU⟩ :=
    source_natural_suzuki_invariant_constituent D c ht htn hsep n hn e I hI E hE
  exact not_invariantSuzukiPairConstituent _ A J hJ a ha ha2 han r hr eJ hU
end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
