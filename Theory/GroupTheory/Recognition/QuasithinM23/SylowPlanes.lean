module
public import Theory.SpecificGroups.PSL3Even.UnipotentGeometry.Transport
public import Theory.SpecificGroups.PSL3Even.UnipotentGeometry.CommutatorRows
public import Theory.GroupTheory.SubgroupConjugation

/-!
# The two full elementary planes in a marked unitriangular group

The characteristic-two coordinate calculation puts every elementary subgroup
in one of two root planes. Two distinct planes of the full order must therefore
be those two subgroups. Their join, central intersection and normalizers are
transported through the same actual equivalence to the original Sylow group.

Source application: Aschbacher–Smith 5.2.11(2), printed pp.653–654
(`refs/quasithin.pdf`). The Chapter6 consumer uses this to recover the literal
intersection of the two original maximal locals.
-/

public noncomputable section
open Subgroup
open Matrix.PSL3Even.UnipotentGeometry
namespace Theory.GroupTheory.QuasithinM23
variable {G : Type*} [Group G] [Finite G]
variable (F : Type*) [Field F] [CharP F 2]

private theorem marked_plane_pair (S : Subgroup G) (e : U F ≃* S)
    (V W : Subgroup G) [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 W]
    (hV : V ≤ S) (hW : W ≤ S)
    (hcV : Nat.card V = Nat.card F ^ 2) (hcW : Nat.card W = Nat.card F ^ 2)
    (hne : V ≠ W) :
    (V = (V₁ F).map (markedHom F S e) ∧ W = (V₂ F).map (markedHom F S e)) ∨
    (V = (V₂ F).map (markedHom F S e) ∧ W = (V₁ F).map (markedHom F S e)) := by
  have choose (A : Subgroup G) [IsElementaryAbelian 2 A] (hAS : A ≤ S)
      (hc : Nat.card A = Nat.card F ^ 2) :
      A = (V₁ F).map (markedHom F S e) ∨ A = (V₂ F).map (markedHom F S e) := by
    rcases marked_elementary_le_plane F S e A hAS with h | h
    · exact Or.inl (eq_of_le_of_card_ge h (by rw [marked_card_plane₁,hc]))
    · exact Or.inr (eq_of_le_of_card_ge h (by rw [marked_card_plane₂,hc]))
  rcases choose V hV hcV with hV | hV <;> rcases choose W hW hcW with hW | hW
  · exact (hne (hV.trans hW.symm)).elim
  · exact Or.inl ⟨hV,hW⟩
  · exact Or.inr ⟨hV,hW⟩
  · exact (hne (hV.trans hW.symm)).elim

/-- Two distinct full elementary planes recover the whole unitriangular subgroup,
its central intersection, and every full elementary subgroup. -/
theorem unitriangular_two_planes (S : Subgroup G) (e : U F ≃* S)
    (V W : Subgroup G) [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 W]
    (hV : V ≤ S) (hW : W ≤ S)
    (hcV : Nat.card V = Nat.card F ^ 2) (hcW : Nat.card W = Nat.card F ^ 2)
    (hne : V ≠ W) :
    V ⊔ W = S ∧ V ⊓ W = (center S).map S.subtype ∧
      Nat.card (V ⊓ W : Subgroup G) = Nat.card F ∧
      ∀ A : Subgroup G, IsElementaryAbelian 2 A → A ≤ S →
        Nat.card A = Nat.card F ^ 2 → A = V ∨ A = W := by
  have hp := marked_plane_pair F S e V W hV hW hcV hcW hne
  have hsup : (V₁ F).map (markedHom F S e) ⊔ (V₂ F).map (markedHom F S e) = S := by
    rw [←Subgroup.map_sup,planes_generate,←MonoidHom.range_eq_map,range_markedHom]
  have hinf : (V₁ F).map (markedHom F S e) ⊓ (V₂ F).map (markedHom F S e) =
      (Z F).map (markedHom F S e) := by
    rw [←map_inf _ _ _ (markedHom_injective F S e),root_planes_inter]
  have hcenter : V ⊓ W = (center S).map S.subtype := by
    rw [marked_center F S e]
    rcases hp with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact hinf
    · exact (inf_comm _ _).trans hinf
  refine ⟨?_,hcenter,?_,?_⟩
  · rcases hp with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact hsup
    · exact (sup_comm _ _).trans hsup
  · rw [hcenter,marked_center F S e,marked_card_center]
  · intro A hA hAS hcard
    let := hA
    have hA' : A = (V₁ F).map (markedHom F S e) ∨
        A = (V₂ F).map (markedHom F S e) := by
      rcases marked_elementary_le_plane F S e A hAS with h | h
      · exact Or.inl (eq_of_le_of_card_ge h (by rw [marked_card_plane₁,hcard]))
      · exact Or.inr (eq_of_le_of_card_ge h (by rw [marked_card_plane₂,hcard]))
    rcases hp with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact hA'
    · exact hA'.symm

/-- A normalizer preserving one of the two full elementary planes preserves
the other. This is relative to the given original subgroup S. -/
theorem unitriangular_plane_normalizers (S : Subgroup G) (e : U F ≃* S)
    (V W : Subgroup G) [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 W]
    (hV : V ≤ S) (hW : W ≤ S)
    (hcV : Nat.card V = Nat.card F ^ 2) (hcW : Nat.card W = Nat.card F ^ 2)
    (hne : V ≠ W) :
    normalizer (S : Set G) ⊓ normalizer (W : Set G) =
      normalizer (V : Set G) ⊓ normalizer (W : Set G) := by
  obtain ⟨hgen,_,_,hplanes⟩ := unitriangular_two_planes F S e V W hV hW hcV hcW hne
  apply le_antisymm
  · rintro g ⟨hgS,hgW⟩
    have hS := mem_normalizer_iff_map_conj_eq.mp hgS
    have hW' := mem_normalizer_iff_map_conj_eq.mp hgW
    let A := V.map (MulAut.conj g).toMonoidHom
    let : IsElementaryAbelian 2 A := IsElementaryAbelian.map _
    have hAS : A ≤ S := (map_mono hV).trans_eq hS
    have hcA : Nat.card A = Nat.card F ^ 2 := by
      rw [card_map_of_injective (MulAut.conj g).injective,hcV]
    rcases hplanes A inferInstance hAS hcA with hA | hA
    · exact ⟨mem_normalizer_iff_map_conj_eq.mpr hA,hgW⟩
    · exact (hne (map_injective (MulAut.conj g).injective (hA.trans hW'.symm))).elim
  · intro g hg
    refine ⟨?_,hg.2⟩
    rw [←hgen]
    exact normalizer_inf_normalizer_le_normalizer_sup V W hg

end Theory.GroupTheory.QuasithinM23
