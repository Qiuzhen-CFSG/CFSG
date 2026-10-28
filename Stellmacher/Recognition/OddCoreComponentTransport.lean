module
public import Stellmacher.Recognition.OddCoreComponentNormalizer

/-!+# Transporters of completed odd-core components

If two conjugate elementary subgroups lie in the same commuting component,
their transporter normalizes that component's actual odd-core closure. Thus
the normalizer of a subgroup Q normalizes the closure whenever Q contains a
vertex and all its vertices lie in this component. This is the normalizer
step in GLS2 Section 22 (the argument of Proposition 22.4(ii)).

In a nonsolvable simple N2 group, a rank-three elementary subgroup containing
an involution with nontrivial centralizer odd core consequently has a conjugate
outside its component. Completion and simplicity make the closure normalizer
proper, so an element outside that normalizer gives the required conjugate.
This exposes a genuine obstruction; it does not assume global connectivity,
put every involution in rank three, or dispose of the rank-two PSL2 models.

Source: `refs/KGroup/GLS2/ChapterF.tex`, Sections 21--22, especially Lemma 22.2
and Proposition 22.4. The binary fusion needed to establish the global
connectivity hypotheses remains separate.
-/

namespace Stellmacher.Recognition

/-- A transporter between vertices of one component normalizes its odd core. -/
public theorem mem_normalizer_oddCoreClosure_of_connected_conjugate
    {G : Type*} [Group G] [Finite G] (hN : IsNTwoGroup G)
    {A B : Subgroup G} (g : G)
    (hAB : Subgroup.ElementaryCommutingConnected 2 A B)
    (hBg : Subgroup.ElementaryCommutingConnected 2 A
      (B.map (MulAut.conj g).toMonoidHom)) :
    g ∈ Subgroup.normalizer (involutionOddCoreClosure A : Set G) := by
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  change (involutionOddCoreClosure A).map (MulAut.conj g).toMonoidHom = _
  calc
    (involutionOddCoreClosure A).map (MulAut.conj g).toMonoidHom =
        (involutionOddCoreClosure B).map (MulAut.conj g).toMonoidHom :=
      congrArg (fun R : Subgroup G => R.map (MulAut.conj g).toMonoidHom)
        (oddCoreClosure_eq_of_connected hN hAB)
    _ = involutionOddCoreClosure (B.map (MulAut.conj g).toMonoidHom) :=
      involutionOddCoreClosure_map (MulAut.conj g) B
    _ = involutionOddCoreClosure A := (oddCoreClosure_eq_of_connected hN hBg).symm

/-- If all elementary rank-two vertices in Q lie in one component, N(Q)
normalizes that component's odd-core closure. Q need not be elementary. -/
public theorem normalizer_le_oddCoreClosure_normalizer_of_connected_vertices
    {G : Type*} [Group G] [Finite G] (hN : IsNTwoGroup G)
    (A Q : Subgroup G)
    (hvertex : ∃ B : Subgroup G, B ≤ Q ∧ IsElementaryAbelian 2 B ∧ 4 ≤ Nat.card B)
    (hconn : ∀ B : Subgroup G, B ≤ Q → IsElementaryAbelian 2 B →
      4 ≤ Nat.card B → Subgroup.ElementaryCommutingConnected 2 A B) :
    Subgroup.normalizer (Q : Set G) ≤
      Subgroup.normalizer (involutionOddCoreClosure A : Set G) := by
  obtain ⟨B, hBQ, hB, hcard⟩ := hvertex
  have hAB := hconn B hBQ hB hcard
  intro g hg
  apply mem_normalizer_oddCoreClosure_of_connected_conjugate hN g hAB
  have hmap := (hAB.map (MulAut.conj g)).right
  apply hconn _ _ hmap.1 hmap.2
  exact (Subgroup.map_mono hBQ).trans_eq
    (Subgroup.mem_normalizer_iff_map_conj_eq.mp hg)

/-- A bad-core involution in A makes the actual closure of A nontrivial. -/
public theorem involutionOddCoreClosure_ne_bot_of_bad_involution
    {G : Type*} [Group G] (A : Subgroup G) {t : G}
    (htA : t ∈ A) (ht : orderOf t = 2)
    (hbad : pPrimeCore 2 (Subgroup.centralizer ({t} : Set G)) ≠ ⊥) :
    involutionOddCoreClosure A ≠ ⊥ := by
  have htne : (⟨t, htA⟩ : A) ≠ 1 := by
    intro h
    have htone : t = 1 := congrArg Subtype.val h
    simp [htone] at ht
  have hle : involutionOddCore t ≤ involutionOddCoreClosure A :=
    le_iSup_of_le (⟨t, htA⟩ : A) (le_iSup_of_le htne le_rfl)
  intro hbot
  have hcore : involutionOddCore t = ⊥ := le_bot_iff.mp (hbot ▸ hle)
  exact hbad ((Subgroup.map_eq_bot_iff_of_injective _ Subtype.coe_injective).mp hcore)

/-- A rank-three component supporting a bad involution odd core is moved by
some ambient conjugation in a nonsolvable simple N2 group. -/
public theorem exists_conjugate_not_connected_of_bad_involution
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hA : 8 ≤ Nat.card A)
    {t : G} (htA : t ∈ A) (ht : orderOf t = 2)
    (hbad : pPrimeCore 2 (Subgroup.centralizer ({t} : Set G)) ≠ ⊥) :
    ∃ g : G, ¬ Subgroup.ElementaryCommutingConnected 2 A
      (A.map (MulAut.conj g).toMonoidHom) := by
  classical
  obtain ⟨hproper, _, htransport⟩ := oddCore_component_normalizer hns hN A hA
    (involutionOddCoreClosure_ne_bot_of_bad_involution A htA ht hbad)
  by_contra h
  push Not at h
  apply ne_of_lt hproper
  exact top_unique (fun g _ => htransport g (h g))

end Stellmacher.Recognition
