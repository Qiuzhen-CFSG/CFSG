module

public import CFSG.Quasithin.Chapter15.Section03.Constructions
public import CFSG.Quasithin.Chapter4.Section01.Maximality
public import Theory.GroupTheory.QuasithinBasic
public import Theory.GroupTheory.TwoLocalUniquenessControl

/-!
# Assembling the uniqueness conclusions of Section 15.3

The component exclusions have two outputs: 15.3.35 forces the actual
quotient `Y₊S/O₂(Y₊S)` to be `S₃`, and 15.3.43 excludes that quotient.
It suffices to establish both for minimal outside overgroups. Finiteness
and the maximal-two-local definition then give 15.3.44.

The deduction of 15.3.45 uses 15.3.44 twice, first for `Y`, then for
`O²(C_Y(V₁))`. Enlarge this residual to `C_Y(V₁)` and conjugate by the
element interchanging the two definite planes. Their normalizers, and
the centralizers of their nontrivial fixed subgroups, lie in `M` by
two-local maximality.

The component exclusions remain explicit inputs here, pending their
proofs; this module does not assert that 15.3.35 or 15.3.43 has been
established. Source: Aschbacher--Smith, combined manuscript (1 March
2004), printed pp.1135 and 1139--1140.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section03

open Subgroup

variable {G : Type*} [Group G]

/-- The actual quotient in 15.3.35 and 15.3.43, including its two-core.
This is an isomorphism condition, not an order or family label. -/
def SymmetricThreeShadow (Yplus S : Subgroup G) : Prop :=
  Nonempty (((Yplus ⊔ S : Subgroup G) ⧸ pCore 2 (Yplus ⊔ S : Subgroup G)) ≃*
    Equiv.Perm (Fin 3))

/-- The finite minimal-counterexample step in 15.3.44. Both component
exclusions must be supplied by their proofs before using this for the
source theorem. -/
theorem unique_of_component_exclusions [Finite G]
    {Yplus S M : Subgroup G}
    (hM : IsMaximalTwoLocal M) (hYM : Yplus ≤ M) (hSM : S ≤ M)
    (h35 : ∀ I ∈ minimalOutsideFamily Yplus S M, SymmetricThreeShadow Yplus S)
    (h43 : ∀ I ∈ minimalOutsideFamily Yplus S M, ¬ SymmetricThreeShadow Yplus S) :
    Chapter4.UniqueMaximalOvergroup (Yplus ⊔ S) M := by
  apply Chapter4.uniqueMaximalOvergroup_of_no_outside hM (sup_le hYM hSM)
  intro h
  obtain ⟨I, hI⟩ := (Set.toFinite (outsideFamily Yplus S M)).exists_minimal h
  exact h43 I hI (h35 I hI)

private theorem unique_mono {A B M : Subgroup G}
    (h : Chapter4.UniqueMaximalOvergroup A M) (hAB : A ≤ B) (hBM : B ≤ M) :
    Chapter4.UniqueMaximalOvergroup B M :=
  ⟨h.1, hBM, fun N hN hBN => h.2.2 N hN (hAB.trans hBN)⟩

private theorem unique_map {A M : Subgroup G}
    (h : Chapter4.UniqueMaximalOvergroup A M) (e : G ≃* G) :
    Chapter4.UniqueMaximalOvergroup (A.map e.toMonoidHom) (M.map e.toMonoidHom) := by
  refine ⟨Theory.GroupTheory.isMaximalTwoLocal_map e h.1, map_mono h.2.1, ?_⟩
  intro N hN hAN
  have hh : A ≤ N.map e.symm.toMonoidHom := by
    simpa [map_map] using map_mono (f := e.symm.toMonoidHom) hAN
  have he := h.2.2 _ (Theory.GroupTheory.isMaximalTwoLocal_map e.symm hN) hh
  simpa [map_map] using congrArg (fun B : Subgroup G => B.map e.toMonoidHom) he

private theorem centralizer_join_map_le
    (Y S V₁ V₂ : Subgroup G) (e : G ≃* G)
    (hY : Y.map e.toMonoidHom = Y) (hS : S.map e.toMonoidHom = S)
    (hV : V₁.map e.toMonoidHom = V₂) :
    ((Y ⊓ centralizer (V₁ : Set G)) ⊔ S).map e.toMonoidHom ≤
      (Y ⊓ centralizer (V₂ : Set G)) ⊔ S := by
  rw [Subgroup.map_sup]
  apply sup_le
  · apply le_trans _ le_sup_left
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨hY ▸ mem_map.mpr ⟨x, hx.1, rfl⟩, ?_⟩
    intro v hv
    obtain ⟨w, hw, rfl⟩ := mem_map.mp (hV.symm ▸ hv)
    simpa only [map_mul] using congrArg e.toMonoidHom (hx.2 w hw)
  · exact hS.le.trans le_sup_right

private theorem plane_control [Finite G]
    {Y S M V : Subgroup G}
    (hunique : Chapter4.UniqueMaximalOvergroup ((Y ⊓ centralizer (V : Set G)) ⊔ S) M)
    (hV : IsPGroup 2 V) (hne : V ≠ ⊥)
    (hnorm : Y ⊔ S ≤ normalizer (V : Set G))
    (hfix : fixedPlane V S ≠ ⊥) :
    normalizer (V : Set G) ≤ M ∧ centralizer (fixedPlane V S : Set G) ≤ M := by
  have hJ : (Y ⊓ centralizer (V : Set G)) ⊔ S ≤ Y ⊔ S :=
    sup_le_sup inf_le_left le_rfl
  refine ⟨normalizer_le_of_unique_maximalTwoLocal hunique.2.2 hV hne
    (hJ.trans hnorm), ?_⟩
  have hcentral : (Y ⊓ centralizer (V : Set G)) ⊔ S ≤
      centralizer (fixedPlane V S : Set G) := by
    apply sup_le
    · exact inf_le_right.trans (centralizer_le inf_le_left)
    · apply le_centralizer_iff.mpr
      exact inf_le_right
  exact (Subgroup.centralizer_le_normalizer _).trans
    (normalizer_le_of_unique_maximalTwoLocal hunique.2.2
      (hV.to_le inf_le_left) hfix (hcentral.trans (Subgroup.centralizer_le_normalizer _)))

/-- The complete deduction of 15.3.45 from 15.3.44 and the local plane
data. The quantifier gives all three clauses for **both** definite planes.
The residual in Hypothesis 15.3.10 is enlarged to the full centralizer;
the second plane is obtained by actual conjugation inside `M`.

`h44` is still a theorem input: the component-exclusion owner must prove
it before this becomes a proof of 15.3.45 in the standing source setup. -/
theorem lemma_15_3_45_of_uniqueness [Finite G]
    {M Y S V₁ V₂ : Subgroup G}
    (hYM : Y ≤ M) (hSM : S ≤ M)
    (h44 : ∀ Yplus : Subgroup G, Hypothesis15310 M Y S V₁ Yplus →
      Chapter4.UniqueMaximalOvergroup (Yplus ⊔ S) M)
    (t : G) (htM : t ∈ M)
    (htY : t ∈ normalizer (Y : Set G)) (htS : t ∈ normalizer (S : Set G))
    (htV : V₁.map (MulAut.conj t).toMonoidHom = V₂)
    (hplanes : ∀ V ∈ ({V₁, V₂} : Set (Subgroup G)),
      IsPGroup 2 V ∧ V ≠ ⊥ ∧ Y ⊔ S ≤ normalizer (V : Set G) ∧ fixedPlane V S ≠ ⊥) :
    ∀ V ∈ ({V₁, V₂} : Set (Subgroup G)),
      Chapter4.UniqueMaximalOvergroup ((Y ⊓ centralizer (V : Set G)) ⊔ S) M ∧
      normalizer (V : Set G) ≤ M ∧ centralizer (fixedPlane V S : Set G) ≤ M := by
  have hYunique := h44 Y (Or.inl rfl)
  have hres := h44 (Stellmacher.twoResidualAmbient (Y ⊓ centralizer (V₁ : Set G)))
    (Or.inr ⟨hYunique, rfl⟩)
  have h₁ : Chapter4.UniqueMaximalOvergroup ((Y ⊓ centralizer (V₁ : Set G)) ⊔ S) M :=
    unique_mono hres (sup_le_sup (map_subtype_le _) le_rfl)
      (sup_le (inf_le_left.trans hYM) hSM)
  have hconj := unique_map h₁ (MulAut.conj t)
  have hMmap : M.map (MulAut.conj t).toMonoidHom = M :=
    mem_normalizer_iff_map_conj_eq.mp (M.le_normalizer htM)
  rw [hMmap] at hconj
  have h₂ : Chapter4.UniqueMaximalOvergroup ((Y ⊓ centralizer (V₂ : Set G)) ⊔ S) M :=
    unique_mono hconj
      (centralizer_join_map_le Y S V₁ V₂ (MulAut.conj t)
        (mem_normalizer_iff_map_conj_eq.mp htY)
        (mem_normalizer_iff_map_conj_eq.mp htS) htV)
      (sup_le (inf_le_left.trans hYM) hSM)
  intro V hV
  obtain ⟨hp, hne, hnorm, hfix⟩ := hplanes V hV
  have hu : Chapter4.UniqueMaximalOvergroup ((Y ⊓ centralizer (V : Set G)) ⊔ S) M := by
    rcases Set.mem_insert_iff.mp hV with rfl | hV
    · exact h₁
    · exact Set.mem_singleton_iff.mp hV ▸ h₂
  exact ⟨hu, plane_control hu hp hne hnorm hfix⟩

end CFSG.Quasithin.Chapter15.Section03
