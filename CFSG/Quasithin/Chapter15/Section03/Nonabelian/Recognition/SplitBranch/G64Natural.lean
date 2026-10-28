module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.Action
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.Statements
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.SplitBranch.Models
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.SplitBranch.G64Natural.Images
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.SplitBranch.G64Natural.Assembly

/-!
# Natural-model recognition in the split branch of 15.3.58

Apply the exact universal G.6.4 to both constituents of the literal U/Z action.
Semisimple centralizer transport and the actual displacement-plane stabilizer
restriction exclude all models except GL₃(2). Perfectness supplies surjective
natural coordinates for K; the invariant nondegenerate quadratic form then
eliminates both kernels. The resulting `SplitPair.HasNaturalModels` retains
actual group and linear equivalences and their intertwining identities.

The exact earlier G.6.4 and the genuine earlier source inputs remain explicit.
No recognized-group or faithful-constituent conclusion is assumed.
Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed p.1149.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition.Component.RecognitionStep
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.SplitBranch.G64Natural
universe u w

/-- A centralizing element stabilizes the actual displacement plane. Hence the
source prime-to-three condition excludes centralizing elements of order three. -/
theorem no_cubic_centralizer_of_plane
    {A W : Type*} [Group A] [Finite A] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) A W) (v : A)
    (hplane : Nat.Coprime 3 (Nat.card (subspaceStabilizer ρ
      (LinearMap.range (ρ v - LinearMap.id))))) :
    ∀ c : A, orderOf c = 3 → ¬ Commute c v := by
  intro c ho hc
  have hle : centralizer ({v} : Set A) ≤
      subspaceStabilizer ρ (LinearMap.range (ρ v - LinearMap.id)) := by
    apply le_subspaceStabilizer
    intro a ha w hw
    obtain ⟨x, rfl⟩ := hw
    refine ⟨ρ a x, ?_⟩
    change ρ v (ρ a x) - ρ a x = ρ a (ρ v x - x)
    rw [map_sub]
    have he := congrArg (fun b => ρ b x) (mem_centralizer_singleton_iff.mp ha)
    simpa only [map_mul, Module.End.mul_apply] using
      congrArg (fun y => y - ρ a x) he.symm
  have hm := hle (mem_centralizer_singleton_iff.mpr hc)
  have hd := (subspaceStabilizer ρ (LinearMap.range (ρ v - LinearMap.id))).orderOf_dvd_natCard hm
  rw [ho] at hd
  exact Nat.prime_three.coprime_iff_not_dvd.mp hplane hd

variable {G : Type u} [Group G] [Finite G] (Z ZS : Subgroup G)
  [(Z.subgroupOf (closureU Z ZS)).Normal]
  [IsElementaryAbelian 2 (VectorQuotient Z ZS)]
  (hkernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z))

/-- G.6.4(4) on both literal constituents, with all application hypotheses
proved from the branch input, the actual Sylow marking and an SQTK cover.
This recognizes the faithful images, not yet the original group K. -/
theorem central_image_alternatives
    {κ : GroupClass.{u}} (hG64 : G64SourceTheorem κ)
    (K : Subgroup (ActorQuotient Z)) [K.Normal] (v : ActorQuotient Z) (s : ℕ)
    (p : SplitPair (actorRepresentation Z ZS hkernel) K v s)
    (T : Sylow 2 (ActorQuotient Z))
    (ht : v ∈ (center T).map (T : Subgroup (ActorQuotient Z)).subtype)
    {Cover : Type u} [Group Cover] [Finite Cover]
    (q : Cover →* ActorQuotient Z) (hq : Function.Surjective q)
    (hcover : IsSQTK κ Cover) :
    G64CentralAlternative (imageRepresentation (constituentAction p.first p.first_invariant)) ∧
    G64CentralAlternative (imageRepresentation (constituentAction p.second p.second_invariant)) := by
  exact ⟨(constituent_g64 hG64 (actorRepresentation Z ZS hkernel) K v T ht
    p.first p.first_invariant p.first_irreducible p.first_displacement q hq hcover).2,
    (constituent_g64 hG64 (actorRepresentation Z ZS hkernel) K v T ht
      p.second p.second_invariant p.second_irreducible p.second_displacement q hq hcover).2⟩

/-- Both chosen literal constituents have natural PSL₃(2) coordinates. All G.6.4
application hypotheses, model exclusions and kernel eliminations are proved.
The quadratic form is the genuine 15.3.56(1) form; the local order restriction
is on the actual setwise stabilizer of the marked displacement plane. -/
theorem hasNaturalModels
    {κ : GroupClass.{u}} (hG64 : G64SourceTheorem κ)
    {S : Type w} [Group S] [IsSimpleGroup S] {n : ℕ}
    (hna : ¬ IsMulCommutative S)
    (K : Subgroup (ActorQuotient Z)) [K.Normal] (e : K ≃* (Fin n → S))
    (v : ActorQuotient Z) (s : ℕ) (hs : 0 < s)
    (p : SplitPair (actorRepresentation Z ZS hkernel) K v s)
    (Q : QuadraticForm (ZMod 2) (Space Z ZS))
    (hQ : ∀ a x, Q (actorRepresentation Z ZS hkernel a x) = Q x)
    (hnd : Q.polarBilin.Nondegenerate)
    (T : Sylow 2 (ActorQuotient Z))
    (ht : v ∈ (center T).map (T : Subgroup (ActorQuotient Z)).subtype)
    (hplane : Nat.Coprime 3 (Nat.card (subspaceStabilizer
      (actorRepresentation Z ZS hkernel)
      (LinearMap.range (actorRepresentation Z ZS hkernel v - LinearMap.id)))))
    {Cover : Type u} [Group Cover] [Finite Cover]
    (q : Cover →* ActorQuotient Z) (hq : Function.Surjective q)
    (hcover : IsSQTK κ Cover) : p.HasNaturalModels :=
  natural_models_of_source_data hG64 hna K e (actorRepresentation Z ZS hkernel)
    (actorRepresentation_injective Z ZS hkernel) v s hs p Q hQ hnd T ht
    hplane q hq hcover

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.SplitBranch.G64Natural
