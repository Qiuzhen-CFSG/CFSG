module

public import Theory.AtlasPort.LinearGroups.G2.SylowParabolicInvariance.Normalizers
public import Theory.AtlasPort.LinearGroups.G2.SylowParabolicInvariance.Binary
public import Theory.AtlasPort.LinearGroups.G2.DerivedParabolicGeneration

/-!
# Sylow-stabilizer invariance of the two derived G₂ parabolics

Let D = G₂(F)′ and R = U ∩ D, for a finite field of characteristic two.
The highest-root subgroup is the set of central involutions of R, including
identity; the two-long-root subgroup is the set of involutions in its second
center. These descriptions are invariant under every automorphism preserving R.
Their normalizers in D are exactly the two standard restricted parabolics.

Above order two, perfectness identifies D with the full model. At order two,
coefficientwise field transport applies the separate calculation for the
proper subgroup G₂(2)′. No classification of automorphisms or additional local
structure hypotheses enter the argument.

Source: the invariant-parabolic argument of Aschbacher–Smith 2.3.9(7), printed
p.526, applied to the G₂ models in 1.1.5(3), pp.501–502. The coordinate and
field-transport APIs come from the licensed ATLAS port; see LICENSES/ATLAS.txt
and LICENSES/ATLAS-CITATION.cff.
-/

@[expose] public section

open Atlas.G2.LieParabolicSetup
open Subgroup
namespace Atlas.G2.SylowParabolicInvariance
variable {F K : Type*} [Field F] [Field K]

private theorem field_map_unipotent (e : F ≃+* K) :
    (unipotent (K := F)).map (fieldEquiv e).toMonoidHom = unipotent := by
  ext g
  simp only [mem_map, unipotent_eq_range]
  constructor
  · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
    exact ⟨e ∘ t, (long_field_unipotentProduct e t).symm⟩
  · rintro ⟨t, rfl⟩
    refine ⟨unipotentProduct (e.symm ∘ t), ⟨_, rfl⟩, ?_⟩
    change fieldEquiv e (unipotentProduct (e.symm ∘ t)) = _
    rw [long_field_unipotentProduct]
    congr 1
    funext i
    exact e.apply_symm_apply _

private theorem field_map_highestRoot (e : F ≃+* K) :
    (highestRoot (F := F)).map (fieldEquiv e).toMonoidHom = highestRoot := by
  ext g
  constructor
  · rintro ⟨_, ⟨a,rfl⟩, rfl⟩
    refine ⟨Multiplicative.ofAdd (e a.toAdd), ?_⟩
    exact (fieldEquiv_rootA e a.toAdd).symm
  · rintro ⟨a,rfl⟩
    refine ⟨rootA (e.symm a.toAdd), ⟨Multiplicative.ofAdd _,rfl⟩, ?_⟩
    change fieldEquiv e (rootA _) = rootA _
    rw [fieldEquiv_rootA, e.apply_symm_apply]

private theorem field_map_longRoot (e : F ≃+* K) :
    (longRootLocal (F := F)).map (fieldEquiv e).toMonoidHom = longRootLocal := by
  apply SetLike.coe_injective
  exact fieldEquiv_longRootLocal_image e

private theorem field_map_derivedSylow (e : F ≃+* K) :
    (unipotent ⊓ commutator (Model F)).map (fieldEquiv e).toMonoidHom =
      unipotent ⊓ commutator (Model K) := by
  rw [map_inf _ _ _ (fieldEquiv e).injective, field_map_unipotent, map_commutator_eq,
    MonoidHom.range_eq_top.mpr (fieldEquiv e).surjective]
  rfl

variable [Finite F] [CharP F 2]

private theorem derivedSylow_characterizations :
    (∀ g : Model F, g ∈ highestRoot ↔
      CentralInvolution (unipotent ⊓ commutator (Model F)) g) ∧
    (∀ g : Model F, g ∈ longRootLocal ↔
      SecondCentralInvolution (unipotent ⊓ commutator (Model F)) g) := by
  by_cases hq : Nat.card F = 2
  · let e := fieldEquiv (binaryFieldEquiv hq)
    have hR : (unipotent ⊓ commutator (Model F)).map e.toMonoidHom =
        BinaryParabolicPair.derivedSylowAmbient := field_map_derivedSylow _
    have hA : (highestRoot (F := F)).map e.toMonoidHom = highestRoot :=
      field_map_highestRoot _
    have hB : (longRootLocal (F := F)).map e.toMonoidHom = longRootLocal :=
      field_map_longRoot _
    constructor
    · intro g
      calc
        g ∈ highestRoot ↔ e g ∈ highestRoot := by
          rw [← hA]
          exact (mem_map_iff_mem e.injective).symm
        _ ↔ CentralInvolution BinaryParabolicPair.derivedSylowAmbient (e g) :=
          binary_highestRoot_iff _
        _ ↔ CentralInvolution (unipotent ⊓ commutator (Model F)) g := by
          rw [← hR]
          exact centralInvolution_map_iff e.toMonoidHom e.injective _ _
    · intro g
      calc
        g ∈ longRootLocal ↔ e g ∈ longRootLocal := by
          rw [← hB]
          exact (mem_map_iff_mem e.injective).symm
        _ ↔ SecondCentralInvolution BinaryParabolicPair.derivedSylowAmbient (e g) :=
          binary_longRootLocal_iff _
        _ ↔ SecondCentralInvolution (unipotent ⊓ commutator (Model F)) g := by
          rw [← hR]
          exact secondCentralInvolution_map_iff e.toMonoidHom e.injective _ _
  · have : Group.IsPerfect (Model F) := isPerfect (by
      have := Finite.one_lt_card (α := F)
      omega)
    rw [Group.IsPerfect.commutator_eq_top, inf_top_eq]
    exact ⟨highestRoot_iff_centralInvolution, longRootLocal_iff_secondCentralInvolution⟩

/-- Every automorphism of the actual derived G₂ model preserving its standard
Sylow subgroup fixes both standard restricted parabolics, including over F₂. -/
theorem restricted_parabolics_invariant
    (b : MulAut (commutator (Model F)))
    (hb : (unipotent.subgroupOf (commutator (Model F))).map b.toMonoidHom =
      unipotent.subgroupOf (commutator (Model F))) :
    (parabolic₁.subgroupOf (commutator (Model F))).map b.toMonoidHom =
        parabolic₁.subgroupOf (commutator (Model F)) ∧
    (parabolic₂.subgroupOf (commutator (Model F))).map b.toMonoidHom =
        parabolic₂.subgroupOf (commutator (Model F)) := by
  let D := commutator (Model F)
  obtain ⟨hA,hB⟩ := derivedSylow_characterizations (F := F)
  have hAD : highestRoot (F := F) ≤ D := fun g hg => ((hA g).mp hg).1.2
  have hBD : longRootLocal (F := F) ≤ D := fun g hg => ((hB g).mp hg).1.2
  have hAI : ∀ g : D, g ∈ highestRoot.subgroupOf D ↔
      CentralInvolution (unipotent.subgroupOf D) g := by
    intro g
    change g.val ∈ highestRoot ↔ _
    rw [hA]
    have h := centralInvolution_map_iff D.subtype D.subtype_injective
      (unipotent.subgroupOf D) g
    rw [subgroupOf_map_subtype] at h
    exact h
  have hBI : ∀ g : D, g ∈ longRootLocal.subgroupOf D ↔
      SecondCentralInvolution (unipotent.subgroupOf D) g := by
    intro g
    change g.val ∈ longRootLocal ↔ _
    rw [hB]
    have h := secondCentralInvolution_map_iff D.subtype D.subtype_injective
      (unipotent.subgroupOf D) g
    rw [subgroupOf_map_subtype] at h
    exact h
  have ha := map_eq_of_centralInvolutions _ _ hAI b hb
  have hb' := map_eq_of_secondCentralInvolutions _ _ hBI b hb
  constructor
  · rw [← normalizer_highestRoot, subgroupOf_normalizer_eq hAD,
      map_equiv_normalizer_eq, ha]
  · rw [← normalizer_longRootLocal, subgroupOf_normalizer_eq hBD,
      map_equiv_normalizer_eq, hb']

end Atlas.G2.SylowParabolicInvariance

end
