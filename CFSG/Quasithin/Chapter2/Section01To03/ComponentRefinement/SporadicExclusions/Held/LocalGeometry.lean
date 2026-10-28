module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SporadicExclusions.Held.LocalGeometry.OrbitCore
public import Theory.SpecificGroups.Held.AutomorphismLocalPair
public import Theory.GroupTheory.PCoreSurjective.OddExtension

/-!
# The actual Held local generating family

Source: Aschbacher–Smith 2.3.9(7), printed p.526, and GLS3 Table 5.3p,
printed p.277 (including the convention for classes fused by automorphisms).

For the image T of the supplied component Sylow subgroup in the degree-2058
Held carrier, use C_He(Z(T)) and N_He(E(T)), where E(T) joins all normal
elementary subgroups of order 64 in T. The second definition retains both
classes exchanged by outer automorphisms. The checked model pair generates
Held and has self-centralizing two-cores; both members are invariant under
every automorphism preserving T.

Pull these two subgroups back through the specified quotient of L and adjoin
the entire supplied S. The relative component-orbit theorem proves local
characteristic two without assuming that S normalizes L. The central
two-kernel is retained in both preimages. Quotient generation gives the
required generation of L with C_G(z).

The explicit definitions, membership descriptions, component projections and
normal orbit quotients below expose the actual groups for subsequent block
analysis. This module constructs the geometry, not the block obstruction.
-/

@[expose] public section

noncomputable section
namespace CFSG.Quasithin.Chapter2.ComponentRefinement.HeldCase

open Subgroup Theory.GroupTheory
open scoped Pointwise

variable {G : Type*} [Group G] {H L M : Subgroup G} {S : Sylow 2 H} {z : G}

/-- The two canonical model locals: false is the center centralizer, true the
normalizer of the characteristic join of normal elementary order-64 subgroups. -/
def heldModelLocal (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .he) : Bool → Subgroup Held.He
  | false => Held.AutomorphismLocalPair.centerLocal (modelSylow h d)
  | true => Held.AutomorphismLocalPair.largeLocal (modelSylow h d)

theorem mem_heldModelLocal (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .he) (i : Bool) (x : Held.He) :
    x ∈ heldModelLocal h d i ↔ match i with
      | false => ∀ y ∈ Held.AutomorphismLocalPair.centerSeed (modelSylow h d),
          y * x = x * y
      | true => ∀ y : Held.He,
          y ∈ Held.AutomorphismLocalPair.largeSeed (modelSylow h d) ↔
            x * y * x⁻¹ ∈ Held.AutomorphismLocalPair.largeSeed (modelSylow h d) := by
  cases i
  · exact Held.AutomorphismLocalPair.mem_centerLocal _ _
  · exact Held.AutomorphismLocalPair.mem_largeLocal _ _

theorem modelSylow_le_heldModelLocal (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .he) (i : Bool) :
    (modelSylow h d : Subgroup Held.He) ≤ heldModelLocal h d i := by
  cases i
  · exact Held.AutomorphismLocalPair.le_centerLocal _
  · exact Held.AutomorphismLocalPair.le_largeLocal _

theorem heldModelLocal_selfCentralizingCore (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .he) (i : Bool) :
    centralizer (pCore 2 (heldModelLocal h d i) : Set (heldModelLocal h d i)) ≤
      pCore 2 (heldModelLocal h d i) := by
  cases i
  · exact Held.AutomorphismLocalPair.centerLocal_selfCentralizingCore _
  · exact Held.AutomorphismLocalPair.largeLocal_selfCentralizingCore_of_sylow _

/-- The actual normalizer actors may be outer. Setwise preservation of the
specified Sylow subgroup suffices for invariance of each canonical local. -/
theorem heldModelLocal_invariant (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .he) (i : Bool) (a : MulAut Held.He)
    (ha : a ∈ modelActors d ((S : Subgroup H).map H.subtype)) :
    (heldModelLocal h d i).map a.toMonoidHom = heldModelLocal h d i := by
  have hi := Held.AutomorphismLocalPair.locals_invariant (modelSylow h d) a
    (modelActors_preserve_sylow h d a ha)
  cases i
  · exact hi.1
  · exact hi.2

theorem heldModelLocal_generate (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .he) :
    heldModelLocal h d false ⊔ heldModelLocal h d true = ⊤ :=
  Held.AutomorphismLocalPair.locals_generate _

/-- A literal quotient preimage inside the chosen component, embedded in G. -/
def heldComponentLocal (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .he) (i : Bool) : Subgroup G :=
  componentPreimage d (heldModelLocal h d i)

/-- Adjoin all of S, including elements permuting components. -/
def heldLocal (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .he) (i : Bool) : Subgroup G :=
  localOvergroup d ((S : Subgroup H).map H.subtype) (heldModelLocal h d i)

theorem mem_heldComponentLocal (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .he) (i : Bool) (x : G) :
    x ∈ heldComponentLocal h d i ↔
      ∃ hx : x ∈ L, modelMap d ⟨x, hx⟩ ∈ heldModelLocal h d i :=
  mem_componentPreimage d _ x

theorem heldComponentLocal_le (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .he) (i : Bool) : heldComponentLocal h d i ≤ L :=
  componentPreimage_le d _

theorem heldComponentLocal_normalized (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .he) (i : Bool) :
    (S : Subgroup H).map H.subtype ⊓ normalizer (L : Set G) ≤
      normalizer (heldComponentLocal h d i : Set G) :=
  componentPreimage_normalized d _ _ (heldModelLocal_invariant h d i)

/-- Neither local preimage removes the central two-kernel. -/
theorem twoCore_le_heldComponentLocal (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .he) (i : Bool) :
    L.pCoreIn 2 ≤ heldComponentLocal h d i :=
  twoCore_le_componentPreimage d _

/-- The projection of the ambient component preimage onto the actual model local. -/
def heldComponentMap (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .he) (i : Bool) :
    heldComponentLocal h d i →* heldModelLocal h d i where
  toFun x := ⟨modelMap d ⟨x, heldComponentLocal_le h d i x.property⟩,
    ((mem_heldComponentLocal h d i x).mp x.property).2⟩
  map_one' := by apply Subtype.ext; exact map_one (modelMap d)
  map_mul' x y := by
    apply Subtype.ext
    exact map_mul (modelMap d) ⟨x, heldComponentLocal_le h d i x.property⟩
      ⟨y, heldComponentLocal_le h d i y.property⟩

theorem heldComponentMap_apply (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .he) (i : Bool) (x : heldComponentLocal h d i) :
    (heldComponentMap h d i x : Held.He) =
      modelMap d ⟨x, heldComponentLocal_le h d i x.property⟩ := rfl

theorem heldComponentMap_surjective (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .he) (i : Bool) :
    Function.Surjective (heldComponentMap h d i) := by
  intro y
  obtain ⟨x, hx⟩ := modelMap_surjective d y
  refine ⟨⟨x, (mem_heldComponentLocal h d i x).mpr ⟨x.property, ?_⟩⟩, ?_⟩
  · exact hx.symm ▸ y.property
  · exact Subtype.ext hx

/-- The kernel is exactly the embedded component two-core, not a discarded center. -/
theorem heldComponentMap_ker (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .he) (i : Bool) :
    (heldComponentMap h d i).ker =
      (L.pCoreIn 2).subgroupOf (heldComponentLocal h d i) := by
  ext x
  change (heldComponentMap h d i x : heldModelLocal h d i) = 1 ↔
    (x : G) ∈ (pCore 2 L).map L.subtype
  rw [Subtype.ext_iff, heldComponentMap_apply]
  change modelMap d ⟨x, heldComponentLocal_le h d i x.property⟩ = 1 ↔ _
  rw [← MonoidHom.mem_ker, modelMap_ker d]
  exact (mem_map_iff_mem L.subtype_injective).symm

theorem heldComponentMap_ker_isPGroup (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .he) (i : Bool) :
    IsPGroup 2 (heldComponentMap h d i).ker := by
  rw [heldComponentMap_ker]
  exact (isPGroup_pCoreIn 2 L).comap_subtype

theorem heldComponentMap_pCore (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .he) (i : Bool) :
    (pCore 2 (heldModelLocal h d i)).comap (heldComponentMap h d i) =
      pCore 2 (heldComponentLocal h d i) := by
  let := h.finite
  exact (heldComponentMap h d i).comap_pCore_of_ker_isPGroup
    (heldComponentMap_surjective h d i) (heldComponentMap_ker_isPGroup h d i)

/-- The actual quotient by the intrinsic core is identified with the model
local's core quotient through the specified projection. -/
def heldComponentCoreEquiv (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .he) (i : Bool) :
    (heldComponentLocal h d i ⧸ pCore 2 (heldComponentLocal h d i)) ≃*
      (heldModelLocal h d i ⧸ pCore 2 (heldModelLocal h d i)) := by
  let := h.finite
  exact (heldComponentMap h d i).quotientPCoreEquivOfSurjective
    (heldComponentMap_surjective h d i) (heldComponentMap_ker_isPGroup h d i)

theorem heldComponentCoreEquiv_mk (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .he) (i : Bool) (x : heldComponentLocal h d i) :
    heldComponentCoreEquiv h d i (QuotientGroup.mk' (pCore 2 (heldComponentLocal h d i)) x) =
      QuotientGroup.mk' (pCore 2 (heldModelLocal h d i)) (heldComponentMap h d i x) := by
  let := h.finite
  exact MonoidHom.quotientPCoreEquivOfSurjective_mk _ _ _ x

theorem sylow_le_heldLocal (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .he) (i : Bool) :
    (S : Subgroup H).map H.subtype ≤ heldLocal h d i := le_sup_right

theorem heldLocal_le (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .he) (i : Bool) :
    heldLocal h d i ≤ L ⊔ (S : Subgroup H).map H.subtype :=
  localOvergroup_le d _ _

/-- The two concrete locals in fact generate all of L joined with S. -/
theorem heldLocal_sup (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .he) :
    heldLocal h d false ⊔ heldLocal h d true = L ⊔ (S : Subgroup H).map H.subtype := by
  change (componentPreimage d (heldModelLocal h d false) ⊔ _) ⊔
    (componentPreimage d (heldModelLocal h d true) ⊔ _) = _
  rw [sup_sup_sup_comm, sup_idem, ← componentPreimage_sup,
    heldModelLocal_generate h d, componentPreimage_top]

theorem heldLocal_mem_He (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .he) (i : Bool) :
    heldLocal h d i ∈ Chapter1.He G :=
  localOvergroup_mem_He h d _ (modelSylow_le_heldModelLocal h d i)
    (heldModelLocal_selfCentralizingCore h d i) (heldModelLocal_invariant h d i)

theorem heldLocal_mem_HeOver (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .he) (i : Bool) :
    heldLocal h d i ∈ Chapter1.HeOver G ((S : Subgroup H).map H.subtype : Set G) :=
  localOvergroup_mem_HeOver h d _ (heldLocal_mem_He h d i)

theorem heldLocal_core_ne_bot (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .he) (i : Bool) :
    (heldLocal h d i).pCoreIn 2 ≠ ⊥ := (heldLocal_mem_HeOver h d i).2.1

theorem heldLocal_selfCentralizingCore (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .he) (i : Bool) :
    centralizer (pCore 2 (heldLocal h d i) : Set (heldLocal h d i)) ≤
      pCore 2 (heldLocal h d i) :=
  (inf_centralizer_pCoreIn_le_iff 2 _).mp (heldLocal_mem_He h d i)

/-- The normal subgroup generated by the actual S-conjugates of the local preimage. -/
def heldLocalOrbit (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .he) (i : Bool) : Subgroup (heldLocal h d i) :=
  (componentOrbit (heldComponentLocal h d i)
    ((S : Subgroup H).map H.subtype)).subgroupOf (heldLocal h d i)

instance heldLocalOrbit_normal (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .he) (i : Bool) : (heldLocalOrbit h d i).Normal :=
  componentOrbit_normal_subgroupOf_sup _ _

theorem heldLocalOrbit_map (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .he) (i : Bool) :
    (heldLocalOrbit h d i).map (heldLocal h d i).subtype =
      componentOrbit (heldComponentLocal h d i) ((S : Subgroup H).map H.subtype) :=
  map_subgroupOf_eq_of_le (componentOrbit_le_sup _ _)

/-- The literal quotient map by the normal orbit, used to localize blocks. -/
def heldLocalOrbitProjection (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .he) (i : Bool) :
    heldLocal h d i →* heldLocal h d i ⧸ heldLocalOrbit h d i :=
  QuotientGroup.mk' (heldLocalOrbit h d i)

theorem heldLocalOrbitProjection_ker (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .he) (i : Bool) :
    (heldLocalOrbitProjection h d i).ker = heldLocalOrbit h d i := QuotientGroup.ker_mk' _

theorem heldLocalOrbitProjection_surjective (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .he) (i : Bool) :
    Function.Surjective (heldLocalOrbitProjection h d i) := QuotientGroup.mk'_surjective _

/-- Every element is an orbit element times an element of the supplied S.
The orbit is essential: S is not presumed to normalize the chosen component. -/
theorem mem_heldLocal (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .he) (i : Bool) (x : G) :
    x ∈ heldLocal h d i ↔
      ∃ y ∈ componentOrbit (heldComponentLocal h d i) ((S : Subgroup H).map H.subtype),
        ∃ s ∈ (S : Subgroup H).map H.subtype, y * s = x := by
  change x ∈ localOvergroup d _ _ ↔ _
  rw [← localOvergroup_orbit]
  change x ∈ (↑(componentOrbit (heldComponentLocal h d i)
    ((S : Subgroup H).map H.subtype) ⊔ (S : Subgroup H).map H.subtype) : Set G) ↔ _
  rw [coe_mul_of_right_le_normalizer_left _ _ (le_normalizer_componentOrbit _ _)]
  rfl

/-- The quotient by the full local orbit is a two-group. -/
theorem heldLocalOrbit_quotient_isPGroup (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .he) (i : Bool) :
    IsPGroup 2 (heldLocal h d i ⧸ heldLocalOrbit h d i) :=
  local_orbit_quotient_isPGroup _ _ (S.isPGroup'.map H.subtype)

/-- A two-perfect block subgroup lies in the actual normal local orbit. -/
theorem heldLocal_pPerfect_le_orbit (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .he) (i : Bool)
    (B : Subgroup (heldLocal h d i)) (hB : IsPPerfect 2 B) :
    B ≤ heldLocalOrbit h d i :=
  le_local_orbit_of_isPPerfect _ _ (S.isPGroup'.map H.subtype) B hB

/-- The Held geometry from the source setup, with every model and orbit premise
discharged. Its two locals are the explicit indexed overgroups above. -/
def heldLocalGeometry (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .he) :
    LocalGeometry L ((S : Subgroup H).map H.subtype) z :=
  localGeometryOfPair h d (heldModelLocal h d false) (heldModelLocal h d true)
    (by rw [heldModelLocal_generate h d, sup_top_eq])
    (heldLocal_mem_He h d false) (heldLocal_mem_He h d true)

theorem heldLocalGeometry_locals (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .he) :
    (heldLocalGeometry h d).locals = {heldLocal h d false, heldLocal h d true} := rfl

theorem mem_heldLocalGeometry_locals (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .he) (K : Subgroup G) :
    K ∈ (heldLocalGeometry h d).locals ↔ ∃ i : Bool, K = heldLocal h d i := by
  rw [heldLocalGeometry_locals]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Bool.exists_bool]

end CFSG.Quasithin.Chapter2.ComponentRefinement.HeldCase

end
