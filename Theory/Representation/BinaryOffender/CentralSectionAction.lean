module

public import Theory.Representation.BinaryOffender.IrreducibleTransport
public import Theory.GroupTheory.PerfectCentralizerLift

/-!
# The normalizer action on a central section

A subgroup stabilizing I and normalizing L acts on the literal quotient
I / C_I(L). Its kernel is characterized by the action differences lying in
C_I(L). Normalization of L is relative to this acting subgroup; no ambient
normality is imposed. These actions are used when lifting the section chosen
in Aschbacher–Smith, *The Classification of Quasithin Groups*, B.1.11,
printed pp. 72–73.
-/

@[expose] public section

namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

theorem fixedSpace_stable_of_normalizes {L H : Subgroup G}
    (hHL : H ≤ (Subgroup.normalizer (L : Set G))) : H ≤ subspaceStabilizer ρ (fixedSpace ρ L) := by
  apply le_subspaceStabilizer
  intro g hg v hv l
  have hl : g⁻¹ * l * g ∈ L := by
    simpa only [inv_inv] using (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (L : Set G)).inv_mem (hHL hg)) l).1 l.property
  have hh := hv ⟨g⁻¹ * l * g, hl⟩
  change ρ l (ρ g v) = ρ g v
  calc
    _ = ρ g (ρ (g⁻¹ * l * g) v) := by
      simp only [map_mul, Module.End.mul_apply]
      simp
    _ = ρ g v := congrArg (ρ g) hh

noncomputable def centralSectionFixedSubspace (L H : Subgroup G) (I : Submodule (ZMod 2) V)
    (hHI : H ≤ subspaceStabilizer ρ I) (hHL : H ≤ (Subgroup.normalizer (L : Set G))) :
    Subrepresentation (invariantSubspace ρ H I hHI).toRepresentation where
  toSubmodule := (fixedSpace ρ L).comap I.subtype
  apply_mem_toSubmodule h v hv := (fixedSpace_stable_of_normalizes ρ hHL h.property v).2 hv

noncomputable def centralSectionRepresentation (L H : Subgroup G) (I : Submodule (ZMod 2) V)
    (hHI : H ≤ subspaceStabilizer ρ I) (hHL : H ≤ (Subgroup.normalizer (L : Set G))) :
    Representation (ZMod 2) H (centralQuotient ρ L I) :=
  (centralSectionFixedSubspace ρ L H I hHI hHL).quotientRepresentation

theorem centralSectionRepresentation_ker_iff (L H : Subgroup G) (I : Submodule (ZMod 2) V)
    (hHI : H ≤ subspaceStabilizer ρ I) (hHL : H ≤ (Subgroup.normalizer (L : Set G))) (h : H) :
    h ∈ (centralSectionRepresentation ρ L H I hHI hHL).ker ↔
      ∀ v ∈ I, ρ h v - v ∈ fixedSpace ρ L := by
  constructor
  · intro hk v hv
    have hh := congrArg (fun t : Module.End (ZMod 2) (centralQuotient ρ L I) =>
      t (Submodule.Quotient.mk (⟨v, hv⟩ : I))) hk
    change Submodule.Quotient.mk _ = Submodule.Quotient.mk _ at hh
    have hx := (Submodule.Quotient.eq ((fixedSpace ρ L).comap I.subtype)).mp hh
    exact hx
  · intro hk
    apply LinearMap.ext
    intro v
    induction v using Submodule.Quotient.induction_on with | _ v =>
    change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
    apply (Submodule.Quotient.eq _).mpr
    exact hk v v.property
end Representation.BinaryOffender


namespace Representation.BinaryOffender
variable {G D V W : Type*} [Group G] [Group D]
  [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]
  (ρ : Representation (ZMod 2) G V) (σ : Representation (ZMod 2) D W)
  (f : G →* D) (e : W →ₗ[ZMod 2] V) (he : Function.Injective e)
  (hact : ∀ g w, ρ g (e w) = e (σ (f g) w))

def preimageSubgroupHom (D₀ : Subgroup D) : D₀.comap f →* D₀ where
  toFun h := ⟨f h, h.property⟩
  map_one' := Subtype.ext f.map_one
  map_mul' h k := Subtype.ext (f.map_mul h k)

theorem preimageSubgroupHom_surjective (hf : Function.Surjective f) (D₀ : Subgroup D) :
    Function.Surjective (preimageSubgroupHom f D₀) := by
  intro d
  obtain ⟨g, hg⟩ := hf d
  refine ⟨⟨g, ?_⟩, Subtype.ext hg⟩
  change f g ∈ D₀
  rw [hg]
  exact d.property

include hact in
theorem preimage_stabilizes_embedding (D₀ : Subgroup D) (I : Submodule (ZMod 2) W)
    (hI : D₀ ≤ subspaceStabilizer σ I) :
    D₀.comap f ≤ subspaceStabilizer ρ (I.map e) :=
  map_subspace_invariant ρ σ f e hact _ I ((Subgroup.map_comap_le _ _).trans hI)

theorem embeddedSection_intertwines (L : Subgroup G) (D₀ : Subgroup D)
    (I : Submodule (ZMod 2) W) (hI : D₀ ≤ subspaceStabilizer σ I)
    (hN : D₀ ≤ Subgroup.normalizer (L.map f : Set D))
    (hN' : D₀.comap f ≤ Subgroup.normalizer (L : Set G))
    (h : D₀.comap f) (v : centralQuotient σ (L.map f) I) :
    embeddedCentralQuotientEquiv ρ σ f e he hact L I
      (centralSectionRepresentation σ (L.map f) D₀ I hI hN (preimageSubgroupHom f D₀ h) v) =
    centralSectionRepresentation ρ L (D₀.comap f) (I.map e)
      (preimage_stabilizes_embedding ρ σ f e hact D₀ I hI) hN' h
      (embeddedCentralQuotientEquiv ρ σ f e he hact L I v) := by
  induction v using Submodule.Quotient.induction_on with | _ v =>
  change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
  congr 1
  apply Subtype.ext
  exact (hact h v).symm

include he in
theorem section_centralizer_lifts (L : Subgroup G) [Group.IsPerfect L]
    (D₀ : Subgroup D) (I : Submodule (ZMod 2) W)
    (hI : D₀ ≤ subspaceStabilizer σ I)
    (hN : D₀ ≤ Subgroup.normalizer (L.map f : Set D))
    (hN' : D₀.comap f ≤ Subgroup.normalizer (L : Set G))
    (hker : f.ker ≤ Subgroup.centralizer (L : Set G))
    (hcent : (centralSectionRepresentation σ (L.map f) D₀ I hI hN).ker.map D₀.subtype ≤
      D₀ ⊓ Subgroup.centralizer (L.map f : Set D)) :
    (centralSectionRepresentation ρ L (D₀.comap f) (I.map e)
      (preimage_stabilizes_embedding ρ σ f e hact D₀ I hI) hN').ker.map
        (D₀.comap f).subtype ≤ (D₀.comap f) ⊓ Subgroup.centralizer (L : Set G) := by
  rintro x ⟨h, hh, rfl⟩
  have hd : preimageSubgroupHom f D₀ h ∈
      (centralSectionRepresentation σ (L.map f) D₀ I hI hN).ker := by
    apply LinearMap.ext
    intro v
    apply (embeddedCentralQuotientEquiv ρ σ f e he hact L I).injective
    rw [embeddedSection_intertwines ρ σ f e he hact L D₀ I hI hN hN']
    rw [show centralSectionRepresentation ρ L (D₀.comap f) (I.map e)
      (preimage_stabilizes_embedding ρ σ f e hact D₀ I hI) hN' h = 1 from hh]
    rfl
  have hc : f h ∈ Subgroup.centralizer (L.map f : Set D) :=
    (hcent ⟨preimageSubgroupHom f D₀ h, hd, rfl⟩).2
  refine ⟨h.property, ?_⟩
  rw [← Subgroup.comap_centralizer_map_eq_of_perfect f L hker]
  exact hc

noncomputable def embeddedSectionImageEquiv (hf : Function.Surjective f)
    (L : Subgroup G) (D₀ : Subgroup D) (I : Submodule (ZMod 2) W)
    (hI : D₀ ≤ subspaceStabilizer σ I)
    (hN : D₀ ≤ Subgroup.normalizer (L.map f : Set D))
    (hN' : D₀.comap f ≤ Subgroup.normalizer (L : Set G)) :
    (centralSectionRepresentation σ (L.map f) D₀ I hI hN).asGroupHom.range ≃*
      (centralSectionRepresentation ρ L (D₀.comap f) (I.map e)
        (preimage_stabilizes_embedding ρ σ f e hact D₀ I hI) hN').asGroupHom.range :=
  equivariantActionImageEquiv _ _ (preimageSubgroupHom f D₀)
    (embeddedCentralQuotientEquiv ρ σ f e he hact L I)
    (preimageSubgroupHom_surjective f hf D₀)
    (fun h v => (embeddedSection_intertwines ρ σ f e he hact L D₀ I hI hN hN' h v).symm)

theorem le_preimage_of_map_le (L : Subgroup G) (D₀ : Subgroup D)
    (hL : L.map f ≤ D₀) : L ≤ D₀.comap f :=
  fun _ hl => hL (Subgroup.mem_map_of_mem f hl)
end Representation.BinaryOffender
