module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Binary.Geometry
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Binary.Projection
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Binary.ParabolicPairs.FlagCores
public import CFSG.Quasithin.Chapter1.Section01
public import Theory.GroupTheory.ComponentLocalOrbitCore

/-!
# Binary flag overgroups in the relative component setup

An N_S(L)-invariant flag stabilizer gives a member of HeOver(S) after
adjoining all of S, provided it contains the component Sylow intersection.
We work inside H, where L is a component. Distinct conjugate flag
stabilizers commute, and their two-cores generate a normal two-subgroup
of the overgroup. The commuting-product centralizer calculation and the
two-group quotient give a self-centralizing ambient two-core. The source
projection t belongs to this core, proving that it is nontrivial.

The supplied flag is the conditional input needed in the binary cases of
Aschbacher–Smith 2.3.9(7), printed pp.525–526. The argument applies in every
dimension admitting such a flag, hence in particular to L₄(2) and L₅(2).
Only N_S(L)-invariance is used; S may permute the components of H.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Binary
open Subgroup Theory.GroupTheory

variable {G : Type*} [Group G] {H L M : Subgroup G} {S : Sylow 2 H} {z : G}
  {n : ℕ} [NeZero n]

private theorem flagOvergroup_core_properties (h : LocalSetup H L M S z)
    (e : L ≃* PSL n) (F : Flag n)
    (hinv : FlagInvariant e ((S : Subgroup H).map H.subtype) F) :
    flagOvergroup e F ((S : Subgroup H).map H.subtype) ∈ Chapter1.He G ∧
      (ambientFlagStabilizer e F).pCoreIn 2 ≤
        (flagOvergroup e F ((S : Subgroup H).map H.subtype)).pCoreIn 2 := by
  let := h.finite
  let P := ambientFlagStabilizer e F
  let K := P.subgroupOf H
  have hPH : P ≤ H := (ambientFlagStabilizer_le e F).trans h.component_le
  have hKL : K ≤ L.subgroupOf H := fun _ hx => ambientFlagStabilizer_le e F hx
  have hmK : K.map H.subtype = P := map_subgroupOf_eq_of_le hPH
  have hinvH : (S : Subgroup H) ⊓ normalizer (L.subgroupOf H : Set H) ≤
      normalizer (K : Set H) := by
    rw [← subgroupOf_normalizer_eq h.component_le]
    change (S : Subgroup H) ⊓ (normalizer (L : Set G)).subgroupOf H ≤
      normalizer (P.subgroupOf H : Set H)
    rw [← subgroupOf_normalizer_eq hPH]
    intro x hx
    exact hinv ⟨mem_map_of_mem H.subtype hx.1, hx.2⟩
  have hselfP : P ⊓ centralizer (P.pCoreIn 2 : Set G) ≤ P.pCoreIn 2 := by
    change (flagStabilizer e F).map L.subtype ⊓
      centralizer (((flagStabilizer e F).map L.subtype).pCoreIn 2 : Set G) ≤
        ((flagStabilizer e F).map L.subtype).pCoreIn 2
    rw [← map_pCoreIn_of_injective 2 (flagStabilizer e F) L.subtype L.subtype_injective]
    exact (inf_centralizer_map_le_iff (flagStabilizer e F)
      ((flagStabilizer e F).pCoreIn 2) L.subtype L.subtype_injective).mpr
        ((inf_centralizer_pCoreIn_le_iff 2 (flagStabilizer e F)).mpr
          (flagStabilizer_selfCentralizingCore e F))
  have hselfK : K ⊓ centralizer (K.pCoreIn 2 : Set H) ≤ K.pCoreIn 2 := by
    apply (inf_centralizer_map_le_iff K (K.pCoreIn 2) H.subtype H.subtype_injective).mp
    rw [map_pCoreIn_of_injective 2 K H.subtype H.subtype_injective, hmK]
    exact hselfP
  have hcent := h.component.local_adjoin_centralizer hKL S.isPGroup' hinvH hselfK
  have hcore : K.pCoreIn 2 ≤ (K ⊔ (S : Subgroup H)).pCoreIn 2 :=
    (le_componentOrbit _ (S : Subgroup H)).trans
      (h.component.local_core_orbit_le hKL hinvH)
  have hmX : (K ⊔ (S : Subgroup H)).map H.subtype =
      flagOvergroup e F ((S : Subgroup H).map H.subtype) := by
    rw [Subgroup.map_sup, hmK]
    rfl
  have hmc : ((K ⊔ (S : Subgroup H)).pCoreIn 2).map H.subtype =
      (flagOvergroup e F ((S : Subgroup H).map H.subtype)).pCoreIn 2 := by
    rw [map_pCoreIn_of_injective 2 _ H.subtype H.subtype_injective, hmX]
  have hcentG := (inf_centralizer_map_le_iff (K ⊔ (S : Subgroup H))
    ((K ⊔ (S : Subgroup H)).pCoreIn 2) H.subtype H.subtype_injective).mpr hcent
  rw [hmX, hmc] at hcentG
  have hcoreG := map_mono (f := H.subtype) hcore
  rw [map_pCoreIn_of_injective 2 K H.subtype H.subtype_injective, hmK, hmc] at hcoreG
  exact ⟨hcentG, hcoreG⟩

/-- Adjoining the whole Sylow subgroup preserves characteristic two for
an invariant binary flag stabilizer. -/
theorem flagOvergroup_selfCentralizingCore (h : LocalSetup H L M S z)
    (e : L ≃* PSL n) (F : Flag n)
    (hinv : FlagInvariant e ((S : Subgroup H).map H.subtype) F) :
    centralizer (pCore 2 (flagOvergroup e F ((S : Subgroup H).map H.subtype)) :
      Set (flagOvergroup e F ((S : Subgroup H).map H.subtype))) ≤
      pCore 2 (flagOvergroup e F ((S : Subgroup H).map H.subtype)) :=
  Chapter1.mem_He_iff.mp (flagOvergroup_core_properties h e F hinv).1

/-- The component projection lies in the actual ambient overgroup's two-core. -/
theorem projection_mem_flagOvergroup_core (h : LocalSetup H L M S z)
    (e : L ≃* PSL n) {t : L} (ht : IsConjugationProjection L z t)
    (ht2 : orderOf t = 2) (F : Flag n)
    (hinv : FlagInvariant e ((S : Subgroup H).map H.subtype) F)
    (hF : ((S : Subgroup H).map H.subtype).subgroupOf L ≤ flagStabilizer e F) :
    (t : G) ∈ (flagOvergroup e F ((S : Subgroup H).map H.subtype)).pCoreIn 2 := by
  apply (flagOvergroup_core_properties h e F hinv).2
  rw [ambientFlagStabilizer, ← map_pCoreIn_of_injective 2 (flagStabilizer e F)
    L.subtype L.subtype_injective]
  exact mem_map_of_mem L.subtype (projection_mem_flagStabilizer_core h e ht ht2 F hF)

/-- The projection involution certifies nontriviality of the ambient two-core. -/
theorem flagOvergroup_core_ne_bot (h : LocalSetup H L M S z)
    (e : L ≃* PSL n) {t : L} (ht : IsConjugationProjection L z t)
    (ht2 : orderOf t = 2) (F : Flag n)
    (hinv : FlagInvariant e ((S : Subgroup H).map H.subtype) F)
    (hF : ((S : Subgroup H).map H.subtype).subgroupOf L ≤ flagStabilizer e F) :
    (flagOvergroup e F ((S : Subgroup H).map H.subtype)).pCoreIn 2 ≠ ⊥ := by
  intro he
  have htmem := projection_mem_flagOvergroup_core h e ht ht2 F hinv hF
  rw [he, mem_bot] at htmem
  have htone : t = 1 := Subtype.ext htmem
  have hord : orderOf t = 1 := by rw [htone, orderOf_one]
  omega

/-- An explicit invariant flag containing S ∩ L supplies the HeOver(S)
overgroup used for the binary parabolic pair in source 2.3.9(7). -/
theorem flagOvergroup_mem_HeOver (h : LocalSetup H L M S z)
    (e : L ≃* PSL n) {t : L} (ht : IsConjugationProjection L z t)
    (ht2 : orderOf t = 2) (F : Flag n)
    (hinv : FlagInvariant e ((S : Subgroup H).map H.subtype) F)
    (hF : ((S : Subgroup H).map H.subtype).subgroupOf L ≤ flagStabilizer e F) :
    flagOvergroup e F ((S : Subgroup H).map H.subtype) ∈
      Chapter1.HeOver G (((S : Subgroup H).map H.subtype : Subgroup G) : Set G) := by
  exact ⟨(flagOvergroup_core_properties h e F hinv).1,
    flagOvergroup_core_ne_bot h e ht ht2 F hinv hF, le_flagOvergroup e F _⟩

end CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Binary

end
