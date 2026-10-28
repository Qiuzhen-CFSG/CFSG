module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.NaturalRecognition.AlternatingSeed.Support.Normalizer
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Odd
public import Theory.Representation.BinaryOffender.Restriction
public import Theory.Representation.BinaryOffender.InvariantAction

/-!
# Supported transpositions from moving minimal offenders

The single-copy A₅ normalizer embeds the full action image in S₅. Its natural
module has no strong offenders, so restriction of a moving minimal best
offender is faithful and spans the original module with its fixed space.
The fixed complement is therefore fixed pointwise. The complete natural S₅
offender classification supplies a transposition in the original coordinates.
Conjugating its involution into any Sylow subgroup preserves both properties.

Source: Aschbacher–Smith B.1.5, B.3.2, B.4.2(5), and13.6.15,
printed pp.69–70,83–84,86,930.
-/

public section
noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.NaturalRecognition.AlternatingSeed.Support
open ChapterB.QuasisimpleSource
variable {D V : Type*} [Group D] [Finite D] [AddCommGroup V] [Module (ZMod 2) V]
  [Module.Finite (ZMod 2) V] {ρ : Representation (ZMod 2) D V} {C : Subgroup D}

omit [Finite D] [Module.Finite (ZMod 2) V] in
private theorem faithful_image_action (U : Subrepresentation ρ)
    (e : ActionEquiv (U.toRepresentation.comp C.subtype) (alternatingNatural 5))
    (r : D →* Equiv.Perm (Fin 5))
    (hr : ∀ g w, e.linearEquiv (U.toRepresentation g w) =
      BinaryPermutation.naturalRepresentation (Fin 5) (r g) (e.linearEquiv w)) :
    ∃ f : subspaceActionImage ρ U.toSubmodule →* Equiv.Perm (Fin 5),
      Function.Injective f ∧
      (∀ g, f (invariantActionHom ρ U.toSubmodule
        (le_subspaceStabilizer ρ _ (fun g _ _ hv => U.apply_mem_toSubmodule g hv)) g) = r g) ∧
      ∀ g w, e.linearEquiv (subspaceImageRepresentation ρ U.toSubmodule g w) =
        BinaryPermutation.naturalRepresentation (Fin 5) (f g) (e.linearEquiv w) := by
  let hU : (⊤ : Subgroup D) ≤ subspaceStabilizer ρ U.toSubmodule :=
    le_subspaceStabilizer ρ _ (fun g _ _ hv => U.apply_mem_toSubmodule g hv)
  let q := invariantActionHom ρ U.toSubmodule hU
  have hq := invariantActionHom_surjective ρ U.toSubmodule hU
  have hk : q.ker ≤ r.ker := by
    intro g hg
    apply BinaryPermutation.naturalRepresentation_injective (Fin 5) (by decide)
    apply LinearMap.ext
    intro w
    obtain ⟨v, rfl⟩ := e.linearEquiv.surjective w
    rw [← hr]
    have he := LinearMap.congr_fun
      (congrArg (subspaceImageRepresentation ρ U.toSubmodule) hg) v
    change U.toRepresentation g v = v at he
    simp only [he, map_one, Module.End.one_apply]
  let f := q.liftOfSurjective hq ⟨r, hk⟩
  have hfq (g : D) : f (q g) = r g :=
    q.liftOfRightInverse_comp_apply (Function.surjInv hq) (Function.rightInverse_surjInv hq) ⟨r, hk⟩ g
  have hf (g : subspaceActionImage ρ U.toSubmodule) (w : U.toSubmodule) :
      e.linearEquiv (subspaceImageRepresentation ρ U.toSubmodule g w) =
        BinaryPermutation.naturalRepresentation (Fin 5) (f g) (e.linearEquiv w) := by
    obtain ⟨g, rfl⟩ := hq g
    rw [hfq]
    exact hr g w
  refine ⟨f, ?_, hfq, hf⟩
  intro g h hgh
  apply subspaceImageRepresentation_injective ρ U.toSubmodule
  apply LinearMap.ext
  intro w
  apply e.linearEquiv.injective
  rw [hf, hf, hgh]

private theorem not_strong_of_permutation_injection
    {E W : Type*} [Group E] [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) E W) (f : E →* Equiv.Perm (Fin 5))
    (hf : Function.Injective f) (e : W ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 5))
    (he : ∀ g w, e (σ g w) = BinaryPermutation.naturalRepresentation (Fin 5) (f g) (e w)) :
    ¬ IsStrongFFModule σ := by
  rintro ⟨A, hA, hlt⟩
  have ho := (show IsOffender σ A from ⟨hA, hlt.le⟩).map_equivariant σ _ f hf e he
  apply ChapterB.Offenders.Odd.not_isStrongOffender_natural (Or.inl rfl) (A.map f)
  refine ⟨ho.1, ?_⟩
  rw [← fixedCodim_map_equivariant σ _ f e he, rank_map_injective f hf]
  exact hlt

private theorem family_contains_swap {A : Subgroup (Equiv.Perm (Fin 5))}
    (h : ChapterB.Offenders.CaseAFamily 5 A) : ∃ a ∈ A, a.IsSwap := by
  obtain ⟨m, hm, _, g, rfl⟩ := h
  let t := ChapterB.Offenders.pairSwap 5 (0 : Fin (5 / 2))
  refine ⟨(MulAut.conj g) t, mem_map_of_mem _ ?_, ?_⟩
  · exact ChapterB.Offenders.pairSwap_mem (0 : Fin (5 / 2)) (by change 0 < m; omega)
  · refine ⟨g 0, g 1, g.injective.ne (by decide), ?_⟩
    exact Equiv.symm_trans_swap_trans (0 : Fin 5) 1 g

/-- A moving minimal best offender fixes the component's whole fixed
complement and contains a transposition in the original marking. -/
theorem minimal_supported_transposition [C.Normal]
    (U : Subrepresentation ρ)
    (e : ActionEquiv (U.toRepresentation.comp C.subtype) (alternatingNatural 5))
    (hc : IsCompl U.toSubmodule (fixedSpace ρ C))
    (r : D →* Equiv.Perm (Fin 5))
    (hr : ∀ g w, e.linearEquiv (U.toRepresentation g w) =
      BinaryPermutation.naturalRepresentation (Fin 5) (r g) (e.linearEquiv w))
    {A : Subgroup D} (hA : IsMinimalBestOffender ρ A)
    (hn : ¬ U.toSubmodule ≤ fixedSpace ρ A) :
    ∃ a ∈ A, (r a).IsSwap ∧ a ^ 2 = 1 ∧
      ∀ w ∈ fixedSpace ρ C, ρ a w = w := by
  let hU : (⊤ : Subgroup D) ≤ subspaceStabilizer ρ U.toSubmodule :=
    le_subspaceStabilizer ρ _ (fun g _ _ hv => U.apply_mem_toSubmodule g hv)
  obtain ⟨f, hf, hfq, hfe⟩ := faithful_image_action U e r hr
  let σ := subspaceImageRepresentation ρ U.toSubmodule
  have hns := not_strong_of_permutation_injection σ f hf e.linearEquiv hfe
  have hs := (hA.faithful_span_of_not_strong ρ U.toSubmodule
    (le_top.trans hU) hn (fun h => hns ⟨_, h⟩)).2
  have hfixed : fixedSpace ρ C ≤ fixedSpace ρ A := by
    intro w hw a
    have hu : ρ a w - w ∈ U.toSubmodule := by
      have hw' : w ∈ U.toSubmodule ⊔ fixedSpace ρ A := hs ▸ Submodule.mem_top
      obtain ⟨u, hu, z, hz, rfl⟩ := Submodule.mem_sup.mp hw'
      have he : ρ a (u + z) - (u + z) = ρ a u - u := by
        rw [map_add, show ρ a z = z from hz a]
        abel
      rw [he]
      exact U.toSubmodule.sub_mem (U.apply_mem_toSubmodule a hu) hu
    have hc' : ρ a w - w ∈ fixedSpace ρ C := (fixedSpace ρ C).sub_mem
      ((fixedSpace_stable_of_normal ρ C (mem_top a) w).2 hw) hw
    have hz : ρ a w - w ∈ U.toSubmodule ⊓ fixedSpace ρ C := ⟨hu, hc'⟩
    rw [hc.inf_eq_bot] at hz
    exact sub_eq_zero.mp hz
  have ho := (hA.1.restricted ρ U.toSubmodule (le_top.trans hU) hn).isOffender σ
  have hom := ho.map_equivariant σ _ f hf e.linearEquiv hfe
  have hbest := hom.isBest_of_not_strong _ (fun h =>
    ChapterB.Offenders.Odd.not_isStrongOffender_natural (Or.inl rfl) h.choose h.choose_spec)
  have hfamily := (ChapterB.Offenders.Odd.isBestOffender_natural_iff_caseAFamily
    (Or.inl rfl) _).mp hbest
  obtain ⟨t, ⟨b, hb, hbt⟩, ht⟩ := family_contains_swap hfamily
  rw [← invariantActionHom_map ρ U.toSubmodule hU] at hb
  obtain ⟨a, ha, rfl⟩ := hb
  have hat : r a = t := (hfq a).symm.trans hbt
  let : IsElementaryAbelian 2 A := hA.1.1.2
  refine ⟨a, ha, hat ▸ ht, ?_, fun w hw => hfixed hw ⟨a, ha⟩⟩
  exact congrArg Subtype.val (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
    (IsElementaryAbelian.exponent_dvd_p 2 A) (⟨a, ha⟩ : A))


omit [Module.Finite (ZMod 2) V] in
/-- Conjugation places a supported transposition in any specified Sylow
subgroup and preserves its support, because C is normal. -/
theorem supported_transposition_in_sylow [C.Normal]
    (r : D →* Equiv.Perm (Fin 5)) (a : D) (ha : (r a).IsSwap) (h2 : a ^ 2 = 1)
    (hf : ∀ w ∈ fixedSpace ρ C, ρ a w = w) (P : Sylow 2 D) :
    ∃ b ∈ P, (r b).IsSwap ∧ b ^ 2 = 1 ∧
      ∀ w ∈ fixedSpace ρ C, ρ b w = w := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : IsElementaryAbelian 2 (zpowers a) := IsElementaryAbelian.zpowers_of_pow_eq_one h2
  obtain ⟨Q, hQ⟩ := (IsElementaryAbelian.isPGroup 2 (zpowers a)).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq D Q P
  let b := g * a * g⁻¹
  have hb : b ∈ P := by
    rw [← hg]
    change b ∈ ((g • Q : Sylow 2 D) : Set D)
    rw [Sylow.coe_smul]
    exact ⟨a, hQ (mem_zpowers a), rfl⟩
  refine ⟨b, hb, ?_, ?_, ?_⟩
  · obtain ⟨i,j,hij,he⟩ := ha
    refine ⟨r g i, r g j, (r g).injective.ne hij, ?_⟩
    change r (g * a * g⁻¹) = _
    rw [map_mul,map_mul,map_inv,he]
    exact Equiv.symm_trans_swap_trans i j (r g)
  · have he := congrArg (MulAut.conj g) h2
    simpa only [map_pow,map_one,MulAut.conj_apply] using he
  · intro w hw
    have hi : ρ g⁻¹ w ∈ fixedSpace ρ C :=
      (fixedSpace_stable_of_normal ρ C (mem_top g⁻¹) w).2 hw
    change ρ (g * a * g⁻¹) w = w
    simp only [map_mul,Module.End.mul_apply]
    rw [hf _ hi]
    simp

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.NaturalRecognition.AlternatingSeed.Support
