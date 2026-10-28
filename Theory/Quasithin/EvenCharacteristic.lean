module

public import Theory.Quasithin
public import Theory.PGroupCore
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Even characteristic and conjugacy of local subgroups

The even-characteristic condition tests `C_M(O₂(M)) ≤ O₂(M)` only for maximal
2-local subgroups `M` containing a fixed Sylow 2-subgroup. Characteristic 2-type
tests the same condition for every maximal 2-local subgroup. The latter therefore
implies the former, and Sylow conjugacy makes the former independent of the
chosen Sylow subgroup.

The proof transports normalizers and the subgroup inclusion order under group
isomorphisms, then transports the intrinsic centralizer of the p-core using
`pCore_map_iso`. Sylow conjugacy supplies the final change of Sylow subgroup.
The conditions are stated explicitly so source-level definitions can use this
API without a dependency from `Theory` to a classification module.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, §0.1, printed pp. 3–4.
-/

namespace Theory.Quasithin

open Subgroup

variable {G H : Type*} [Group G] [Group H]

/-- An isomorphism sends a 2-local subgroup to a 2-local subgroup. -/
public theorem isTwoLocal_map (e : G ≃* H) {M : Subgroup G} (hM : IsTwoLocal M) :
    IsTwoLocal (M.map e.toMonoidHom) := by
  obtain ⟨Q, hQ, hp, rfl⟩ := hM
  exact ⟨Q.map e.toMonoidHom, fun h => hQ ((map_eq_bot_iff_of_injective Q e.injective).mp h),
    hp.map _, map_equiv_normalizer_eq Q e⟩

/-- Being 2-local is invariant under group isomorphisms. -/
public theorem isTwoLocal_map_iff (e : G ≃* H) (M : Subgroup G) :
    IsTwoLocal (M.map e.toMonoidHom) ↔ IsTwoLocal M := by
  refine ⟨fun h => ?_, isTwoLocal_map e⟩
  have h' := isTwoLocal_map e.symm h
  simpa [map_map] using h'

/-- An isomorphism preserves maximality among the 2-local subgroups. -/
public theorem isMaximalTwoLocal_map (e : G ≃* H) {M : Subgroup G}
    (hM : IsMaximalTwoLocal M) : IsMaximalTwoLocal (M.map e.toMonoidHom) := by
  refine ⟨isTwoLocal_map e hM.1, ?_⟩
  intro N hN hle
  have hMN : M ≤ N.map e.symm.toMonoidHom := by
    simpa [map_map] using map_mono (f := e.symm.toMonoidHom) hle
  have hNM := hM.2 (isTwoLocal_map e.symm hN) hMN
  simpa [map_map] using map_mono (f := e.toMonoidHom) hNM

/-- Being maximal 2-local is invariant under group isomorphisms. -/
public theorem isMaximalTwoLocal_map_iff (e : G ≃* H) (M : Subgroup G) :
    IsMaximalTwoLocal (M.map e.toMonoidHom) ↔ IsMaximalTwoLocal M := by
  refine ⟨fun h => ?_, isMaximalTwoLocal_map e⟩
  simpa [map_map] using isMaximalTwoLocal_map e.symm h

/-- An isomorphism transports maximal 2-local overgroups of a specified subgroup. -/
public theorem maximalTwoLocal_overgroup_map_iff (e : G ≃* H) (T M : Subgroup G) :
    (IsMaximalTwoLocal (M.map e.toMonoidHom) ∧
      T.map e.toMonoidHom ≤ M.map e.toMonoidHom) ↔
    (IsMaximalTwoLocal M ∧ T ≤ M) := by
  rw [isMaximalTwoLocal_map_iff, map_le_map_iff_of_injective e.injective]

/-- Conjugation transports maximal 2-local overgroups of a fixed Sylow 2-subgroup. -/
public theorem maximalTwoLocal_overgroup_conj_iff (g : G) (T : Sylow 2 G) (M : Subgroup G) :
    (IsMaximalTwoLocal (M.map (MulAut.conj g).toMonoidHom) ∧
      ((g • T : Sylow 2 G) : Subgroup G) ≤ M.map (MulAut.conj g).toMonoidHom) ↔
    (IsMaximalTwoLocal M ∧ (T : Subgroup G) ≤ M) :=
  maximalTwoLocal_overgroup_map_iff (MulAut.conj g) T M

/-- An isomorphism carries the centralizer of a subgroup to the centralizer of its image. -/
public theorem map_centralizer (e : G ≃* H) (Q : Subgroup G) :
    (centralizer (Q : Set G)).map e.toMonoidHom =
      centralizer (Q.map e.toMonoidHom : Set H) := by
  apply le_antisymm
  · exact map_centralizer_le_centralizer_image _ _
  · intro x hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    intro y hy
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using hx (e y) (mem_map_of_mem _ hy)

/-- Having a self-centralizing p-core is invariant under group isomorphisms. -/
public theorem centralizer_pCore_le_iff (p : ℕ) (e : G ≃* H) :
    centralizer (pCore p G : Set G) ≤ pCore p G ↔
      centralizer (pCore p H : Set H) ≤ pCore p H := by
  rw [← map_le_map_iff_of_injective (f := e.toMonoidHom) e.injective, map_centralizer, pCore_map_iso]

/-- The intrinsic p-core of a subgroup is self-centralizing exactly when that of its image is. -/
public theorem centralizer_pCore_map_le_iff (p : ℕ) (e : G ≃* H) (M : Subgroup G) :
    centralizer (pCore p (M.map e.toMonoidHom) : Set (M.map e.toMonoidHom)) ≤
        pCore p (M.map e.toMonoidHom) ↔
      centralizer (pCore p M : Set M) ≤ pCore p M :=
  (centralizer_pCore_le_iff p (e.subgroupMap M)).symm

/-- The even-characteristic centralizer condition over a specified subgroup transports under
isomorphisms. No Sylow or finiteness assumption is needed for this transport. -/
public theorem evenCharacteristicAt_map_iff (e : G ≃* H) (T : Subgroup G) :
    (∀ M : Subgroup G, IsMaximalTwoLocal M → T ≤ M →
      centralizer (pCore 2 M : Set M) ≤ pCore 2 M) ↔
    (∀ N : Subgroup H, IsMaximalTwoLocal N → T.map e.toMonoidHom ≤ N →
      centralizer (pCore 2 N : Set N) ≤ pCore 2 N) := by
  constructor
  · intro h N hN hTN
    have hT : T ≤ N.map e.symm.toMonoidHom := by
      simpa [map_map] using map_mono (f := e.symm.toMonoidHom) hTN
    exact (centralizer_pCore_map_le_iff 2 e.symm N).mp
      (h _ (isMaximalTwoLocal_map e.symm hN) hT)
  · intro h M hM hTM
    exact (centralizer_pCore_map_le_iff 2 e M).mp
      (h _ (isMaximalTwoLocal_map e hM) (map_mono hTM))

/-- The even-characteristic condition holds over a Sylow 2-subgroup if and only if it holds
over any of its conjugates. -/
public theorem evenCharacteristicAt_conj_iff (g : G) (T : Sylow 2 G) :
    (∀ M : Subgroup G, IsMaximalTwoLocal M → (T : Subgroup G) ≤ M →
      centralizer (pCore 2 M : Set M) ≤ pCore 2 M) ↔
    (∀ M : Subgroup G, IsMaximalTwoLocal M → ((g • T : Sylow 2 G) : Subgroup G) ≤ M →
      centralizer (pCore 2 M : Set M) ≤ pCore 2 M) :=
  evenCharacteristicAt_map_iff (MulAut.conj g) T

/-- For a finite group, the even-characteristic condition is independent of the chosen
Sylow 2-subgroup. -/
public theorem evenCharacteristicAt_sylow_iff [Finite G] (T U : Sylow 2 G) :
    (∀ M : Subgroup G, IsMaximalTwoLocal M → (T : Subgroup G) ≤ M →
      centralizer (pCore 2 M : Set M) ≤ pCore 2 M) ↔
    (∀ M : Subgroup G, IsMaximalTwoLocal M → (U : Subgroup G) ≤ M →
      centralizer (pCore 2 M : Set M) ≤ pCore 2 M) := by
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G T U
  exact evenCharacteristicAt_conj_iff g T

/-- The existential formulation of even characteristic is equivalent to the source condition
for any fixed Sylow 2-subgroup. -/
public theorem evenCharacteristic_exists_iff_at [Finite G] (T : Sylow 2 G) :
    (∃ U : Sylow 2 G, ∀ M : Subgroup G, IsMaximalTwoLocal M → (U : Subgroup G) ≤ M →
      centralizer (pCore 2 M : Set M) ≤ pCore 2 M) ↔
    (∀ M : Subgroup G, IsMaximalTwoLocal M → (T : Subgroup G) ≤ M →
      centralizer (pCore 2 M : Set M) ≤ pCore 2 M) := by
  constructor
  · rintro ⟨U, hU⟩
    exact (evenCharacteristicAt_sylow_iff U T).mp hU
  · exact fun hT => ⟨T, hT⟩

/-- Testing even characteristic at some Sylow 2-subgroup is equivalent to testing it at every
Sylow 2-subgroup. -/
public theorem evenCharacteristic_exists_iff_forall [Finite G] :
    (∃ T : Sylow 2 G, ∀ M : Subgroup G, IsMaximalTwoLocal M → (T : Subgroup G) ≤ M →
      centralizer (pCore 2 M : Set M) ≤ pCore 2 M) ↔
    (∀ T : Sylow 2 G, ∀ M : Subgroup G, IsMaximalTwoLocal M → (T : Subgroup G) ≤ M →
      centralizer (pCore 2 M : Set M) ≤ pCore 2 M) := by
  constructor
  · rintro ⟨T, hT⟩ U
    exact (evenCharacteristicAt_sylow_iff T U).mp hT
  · intro h
    exact ⟨default, h default⟩

/-- Characteristic 2-type implies the even-characteristic condition for each chosen Sylow
2-subgroup. The premise tests all maximal 2-locals, with no Sylow-containment restriction. -/
public theorem evenCharacteristicAt_of_characteristicTwoType
    (h : ∀ M : Subgroup G, IsMaximalTwoLocal M →
      centralizer (pCore 2 M : Set M) ≤ pCore 2 M) (T : Sylow 2 G) :
    ∀ M : Subgroup G, IsMaximalTwoLocal M → (T : Subgroup G) ≤ M →
      centralizer (pCore 2 M : Set M) ≤ pCore 2 M := by
  intro M hM _
  exact h M hM

/-- Characteristic 2-type implies the existential even-characteristic condition. -/
public theorem evenCharacteristic_of_characteristicTwoType
    (h : ∀ M : Subgroup G, IsMaximalTwoLocal M →
      centralizer (pCore 2 M : Set M) ≤ pCore 2 M) :
    ∃ T : Sylow 2 G, ∀ M : Subgroup G, IsMaximalTwoLocal M → (T : Subgroup G) ≤ M →
      centralizer (pCore 2 M : Set M) ≤ pCore 2 M :=
  ⟨default, evenCharacteristicAt_of_characteristicTwoType h default⟩

end Theory.Quasithin
