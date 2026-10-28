module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.SplitBranch.G64Natural.KernelLift
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.SplitBranch.G64Natural.LinearSieve
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.SplitBranch.G64Natural.PermutationSieve

/-!
# The unique surviving G.6.4 model on each constituent image

The extension K⟨v⟩ has cyclic quotient modulo K, so its image's derived subgroup
lies in the image of K. Semisimple centralizer lifting transfers the actual
prime-to-three displacement-plane stabilizer bound to that image. The cubic
centralizer obstructions then exclude all symmetric models and all binary
linear dimensions above three; the source lower dimension bound excludes two.

This recognizes only the faithful image. The original constituent kernel is
eliminated separately using the source orthogonal form.
Source: Aschbacher–Smith, combined manuscript (1 March 2004), 15.3.58, p.1149,
using the exact universal G.6.4, printed pp.345–346.
-/

public section

open Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition.Component.RecognitionStep
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.SplitBranch.G64Natural
universe u w
variable {A E : Type u} [Group A] [AddCommGroup E] [Module (ZMod 2) E]

/-- The cyclic supplement forces the derived subgroup into K. -/
theorem extension_commutator_le (K : Subgroup A) [K.Normal] (v : A) :
    commutator (extensionActor K v) ≤ K.subgroupOf (extensionActor K v) := by
  apply Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top
    (codisjoint_subgroupOf_sup K (zpowers v)).eq_top
  let e := subgroupOfEquivOfLe (le_sup_right : zpowers v ≤ extensionActor K v)
  exact ⟨⟨fun x y => e.injective (by simp [mul_comm])⟩⟩

/-- The same containment survives every surjective image of the extension. -/
theorem image_commutator_le (K : Subgroup A) [K.Normal] (v : A)
    {B : Type*} [Group B] (f : extensionActor K v →* B) (hf : Function.Surjective f) :
    commutator B ≤ (K.subgroupOf (extensionActor K v)).map f := by
  have hh := map_mono (f := f) (extension_commutator_le K v)
  rwa [map_commutator_eq, f.range_eq_top_of_surjective hf] at hh

/-- Commutation with the marking preserves its actual displacement subspace. -/
theorem centralizer_le_displacement_stabilizer (ρ : Representation (ZMod 2) A E) (v : A) :
    centralizer ({v} : Set A) ≤
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

/-- The plane stabilizer restriction forbids commuting cubics in the derived image. -/
theorem image_no_cubic [Finite A]
    {S : Type w} [Group S] [IsSimpleGroup S] {n : ℕ}
    (hna : ¬ IsMulCommutative S) {K : Subgroup A} [K.Normal]
    (e : K ≃* (Fin n → S)) (ρ : Representation (ZMod 2) A E) (v : A)
    (J : Subrepresentation (ρ.comp K.subtype))
    (hv : J.toSubmodule.map (ρ v) = J.toSubmodule)
    (hplane : Nat.Coprime 3 (Nat.card (subspaceStabilizer ρ
      (LinearMap.range (ρ v - LinearMap.id))))) :
    ∀ c ∈ commutator (actionImage (constituentAction J hv)), orderOf c = 3 →
      ¬ Commute c (actionHom (constituentAction J hv) (extensionMark K v)) := by
  have hc := hplane.of_dvd_right
    (card_dvd_of_le ((inf_le_right : K ⊓ centralizer ({v} : Set A) ≤ _).trans
      (centralizer_le_displacement_stabilizer ρ v)))
  have hi := constituent_centralizer_image_primeToThree hna e J hv hc
  intro c hc ho hcomm
  have hm := image_commutator_le K v (actionHom (constituentAction J hv))
    (constituentAction J hv).asGroupHom.rangeRestrict_surjective hc
  have hd := ((K.subgroupOf (extensionActor K v)).map
    (actionHom (constituentAction J hv)) ⊓ centralizer
      ({actionHom (constituentAction J hv) (extensionMark K v)} :
        Set (actionImage (constituentAction J hv)))).orderOf_dvd_natCard
          ⟨hm, mem_centralizer_singleton_iff.mpr hcomm⟩
  rw [ho] at hd
  exact Nat.prime_three.coprime_iff_not_dvd.mp hi hd

/-- G.6.4 and the actual local restriction recognize the image as the natural GL₃(2) action. -/
theorem constituent_linear_three [Finite A] [Finite E] {κ : GroupClass.{u}}
    (hG64 : G64SourceTheorem κ)
    {S : Type w} [Group S] [IsSimpleGroup S] {n : ℕ}
    (hna : ¬ IsMulCommutative S) (K : Subgroup A) [K.Normal]
    (e : K ≃* (Fin n → S)) (ρ : Representation (ZMod 2) A E) (v : A)
    (T : Sylow 2 A) (ht : v ∈ (center T).map (T : Subgroup A).subtype)
    (J : Subrepresentation (ρ.comp K.subtype))
    (hv : J.toSubmodule.map (ρ v) = J.toSubmodule)
    (hJ : J.toRepresentation.IsIrreducible)
    (hr : Module.finrank (ZMod 2)
      (LinearMap.range ((ρ v - LinearMap.id).comp J.toSubmodule.subtype)) = 1)
    (hdim : 3 ≤ Module.finrank (ZMod 2) J.toSubmodule)
    (hplane : Nat.Coprime 3 (Nat.card (subspaceStabilizer ρ
      (LinearMap.range (ρ v - LinearMap.id)))))
    {Cover : Type u} [Group Cover] [Finite Cover]
    (q : Cover →* A) (hq : Function.Surjective q) (hcover : IsSQTK κ Cover) :
    HasActionModel (imageRepresentation (constituentAction J hv)) (linearRepresentation 3) := by
  have halt := (constituent_g64 hG64 ρ K v T ht J hv hJ hr q hq hcover).2
  have hr' : Module.finrank (ZMod 2) (LinearMap.range
      (imageRepresentation (constituentAction J hv)
        (actionHom (constituentAction J hv) (extensionMark K v)) - LinearMap.id)) = 1 :=
    (constituentAction_rank J hv).trans hr
  have hno := image_no_cubic hna e ρ v J hv hplane
  obtain ⟨m, hm₂, hm₅, hm⟩ := PermutationSieve.linear_of_central_alternative _
    (imageRepresentation_injective _) _ (transvection_of_rank_one _ _ hr') hno halt
  exact (LinearSieve.linear_model_eq_three _ _ hr' hdim hno hm₂ hm₅ hm).2

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.SplitBranch.G64Natural
