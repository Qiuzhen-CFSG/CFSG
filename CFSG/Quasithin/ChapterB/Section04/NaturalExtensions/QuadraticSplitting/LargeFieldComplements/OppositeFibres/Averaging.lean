module
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.QuadraticSplitting.LargeFieldComplements.Fibre
public import Theory.Representation.BinaryOffender.FixedQuotientKernel
public import Theory.Representation.BinaryOffender.MovedSpaceTransport

/-!
# An odd-order equivariant section through the Levi fixed space

Average the conjugates of a binary linear section over a finite odd-order
group. Its order is one in F₂, so the average is still a section, and its
image is invariant. Applied to the actual quotient map restricted to the
Levi fixed space, this gives the complement needed in the opposite branch
of Aschbacher–Smith B.4.9(1), printed p.93 (1 March 2004 manuscript).
The construction does not assume that the orbit of one lift is a complement.
-/

@[expose] public section
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.NaturalExtensions.QuadraticSplitting
variable {A V L : Type*} [Group A] [Finite A]
  [AddCommGroup V] [Module (ZMod 2) V]
  [AddCommGroup L] [Module (ZMod 2) L]

/-- Averaging preserves a section and makes it equivariant. -/
theorem opposite_averaged_section
    (ρ : Representation (ZMod 2) A V) (σ : Representation (ZMod 2) A L)
    (p : V →ₗ[ZMod 2] L) (hp : ∀ a v, p (ρ a v) = σ a (p v))
    (S : Submodule (ZMod 2) V)
    (hS : ∀ a v, v ∈ S → ρ a v ∈ S)
    (hsurj : ∀ z : L, ∃ v ∈ S, p v = z)
    (hodd : Odd (Nat.card A)) :
    ∃ t : L →ₗ[ZMod 2] V,
      (∀ z, p (t z) = z) ∧ (∀ z, t z ∈ S) ∧
      (∀ a z, t (σ a z) = ρ a (t z)) := by
  classical
  let := Fintype.ofFinite A
  let pS : S →ₗ[ZMod 2] L := p.comp S.subtype
  have hpS : Function.Surjective pS := by
    intro z
    obtain ⟨v,hv,he⟩ := hsurj z
    exact ⟨⟨v,hv⟩,he⟩
  obtain ⟨s,hs⟩ := pS.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hpS)
  let t₀ : L →ₗ[ZMod 2] V := S.subtype.comp s
  have ht₀ (z : L) : p (t₀ z) = z := LinearMap.congr_fun hs z
  let t : L →ₗ[ZMod 2] V := ∑ a : A, (ρ a⁻¹).comp (t₀.comp (σ a))
  have ht (z : L) : t z = ∑ a : A, ρ a⁻¹ (t₀ (σ a z)) := by
    simp only [t, LinearMap.sum_apply, LinearMap.comp_apply]
  refine ⟨t, ?_, ?_, ?_⟩
  · intro z
    rw [ht, map_sum]
    simp only [hp, ht₀, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel,
      map_one, Module.End.one_apply, Finset.sum_const, Finset.card_univ]
    rw [← Nat.cast_smul_eq_nsmul (ZMod 2), ← Nat.card_eq_fintype_card,
      hodd.natCast_zmod_two, one_smul]
  · intro z
    rw [ht]
    exact S.sum_mem (fun a _ => hS a⁻¹ _ (s (σ a z)).property)
  · intro a z
    rw [ht, ht, map_sum]
    refine Fintype.sum_bijective (· * a) (Group.mulRight_bijective a) _ _ (fun b => ?_)
    simp only [mul_inv_rev, map_mul, Module.End.mul_apply]
    simp only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]


section FixedSection
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (K H : Subgroup G) [Finite H]

/-- Average a section of the actual quotient line through the K-fixed space.
This uses no scalar structure on the original module beyond F₂. -/
theorem opposite_fixed_section (N : Subrepresentation ρ)
    (L : Submodule (ZMod 2) (V ⧸ N.toSubmodule))
    (hL : H ≤ subspaceStabilizer N.quotientRepresentation L)
    (hK : H ≤ Subgroup.normalizer K)
    (hf : L ≤ (fixedSpace ρ K).map N.toSubmodule.mkQ)
    (hodd : Odd (Nat.card H)) :
    ∃ t : L →ₗ[ZMod 2] V,
      (∀ z : L, N.toSubmodule.mkQ (t z) = z) ∧
      (∀ z : L, t z ∈ fixedSpace ρ K) ∧
      H ≤ subspaceStabilizer ρ (LinearMap.range t) := by
  let E := fixedSpace ρ K ⊓ L.comap N.toSubmodule.mkQ
  have hfix : H ≤ subspaceStabilizer ρ (fixedSpace ρ K) :=
    hK.trans (normalizer_le_stabilizer_fixedSpace ρ K)
  have hE : H ≤ subspaceStabilizer ρ E := by
    apply le_subspaceStabilizer
    intro h hh v hv
    refine ⟨(hfix hh v).mpr hv.1, ?_⟩
    exact (hL hh (N.toSubmodule.mkQ v)).mpr hv.2
  let τ := (invariantSubspace ρ H E hE).toRepresentation
  let σ := (invariantSubspace N.quotientRepresentation H L hL).toRepresentation
  let p : E →ₗ[ZMod 2] L :=
    (N.toSubmodule.mkQ.comp E.subtype).codRestrict L (fun z => z.property.2)
  have hp : ∀ h v, p (τ h v) = σ h (p v) := by
    intro h v
    apply Subtype.ext
    rfl
  have hsurj : ∀ z : L, ∃ v ∈ (⊤ : Submodule (ZMod 2) E), p v = z := by
    intro z
    obtain ⟨v,hv,he⟩ := hf z.property
    refine ⟨⟨v,hv,?_⟩, Submodule.mem_top, Subtype.ext he⟩
    change N.toSubmodule.mkQ v ∈ L
    rw [he]
    exact z.property
  obtain ⟨s,hs,_,heq⟩ := opposite_averaged_section τ σ p hp ⊤
    (fun _ _ _ => Submodule.mem_top) hsurj hodd
  let t : L →ₗ[ZMod 2] V := E.subtype.comp s
  refine ⟨t, fun z => congrArg Subtype.val (hs z), fun z => (s z).property.1, ?_⟩
  apply le_subspaceStabilizer
  rintro h hh _ ⟨z,rfl⟩
  refine ⟨σ ⟨h,hh⟩ z, ?_⟩
  exact congrArg (fun e : E => (e : V)) (heq ⟨h,hh⟩ z)

/-- The binary averaged section supplies an odd-group-invariant complement
through the prescribed displacement fibre. -/
theorem opposite_odd_complement (Q : Subgroup G) (N : Subrepresentation ρ)
    (W : Submodule (ZMod 2) V)
    (I L : Submodule (ZMod 2) (V ⧸ N.toSubmodule))
    (hIL : IsCompl I L) (hWdis : Disjoint N.toSubmodule W)
    (hWI : W.map N.toSubmodule.mkQ = I)
    (hWK : K ≤ subspaceStabilizer ρ W) (hWQ : W ≤ fixedSpace ρ Q)
    (hWH : H ≤ subspaceStabilizer ρ W)
    (hL : H ≤ subspaceStabilizer N.quotientRepresentation L)
    (hK : H ≤ Subgroup.normalizer K)
    (hf : L ≤ (fixedSpace ρ K).map N.toSubmodule.mkQ)
    (hfibre : fixedSpace ρ K ≤ displacementFibre ρ K Q W)
    (hodd : Odd (Nat.card H)) :
    ∃ C : Submodule (ZMod 2) V, IsCompl N.toSubmodule C ∧
      (K ⊔ Q) ⊔ H ≤ subspaceStabilizer ρ C := by
  obtain ⟨t,ht,htK,htH⟩ := opposite_fixed_section ρ K H N L hL hK hf hodd
  have hc := fibreSection_complement ρ K Q N W I L hIL hWdis hWI hWK hWQ
    t ht (fun z => hfibre (htK z))
  exact ⟨W ⊔ LinearMap.range t, hc.1, sup_le hc.2 (subspaceStabilizer_sup ρ hWH htH)⟩
end FixedSection
end CFSG.Quasithin.ChapterB.NaturalExtensions.QuadraticSplitting
