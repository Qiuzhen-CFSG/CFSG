module
public import Theory.GroupTheory.ElementaryFourExtension
public import Theory.GroupTheory.ElementaryCommutingTwoGroup

/-!
# Moving four-groups and their centralizers into a Sylow subgroup

An ambient elementary extension of a four-group need not lie in a specified
Sylow subgroup. Nevertheless, one can conjugate the four-group into that Sylow
so that it has an elementary extension there, while simultaneously carrying
its original Sylow centralizer into the same Sylow subgroup.

Choose a Sylow subgroup of the ambient centralizer containing the original
Sylow centralizer. It has elementary rank at least three, and contains the
four-group centrally. Join the four-group to an elementary subgroup of rank
three, then conjugate the whole centralizer Sylow into the specified Sylow.
In a finite simple group the ambient extension is supplied by the four-group
extension theorem. The resulting conjugate belongs to the rank-three
commuting component, without asserting that the conjugating element stabilizes
that component.

This is the Sylow-centralizer transport underlying GLS, volume 4, Chapter 2,
Lemma 18.1 (`refs/KGroup/GLS4/Chapter2.tex`), and is useful in the binary fusion
analysis following GLS, volume 2, Proposition 22.4.
-/

namespace Subgroup

private theorem rank_three_in_sylow
    {G : Type*} [Group G] [Finite G]
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hA : 8 ≤ Nat.card A)
    (S : Sylow 2 G) :
    ∃ B : Subgroup S, IsElementaryAbelian 2 B ∧ 8 ≤ Nat.card B := by
  obtain ⟨T, hAT⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_le_sylow
  let AT := A.subgroupOf (T : Subgroup G)
  let : IsElementaryAbelian 2 AT := IsElementaryAbelian.subgroupOf hAT
  let f := (T.equiv S).toMonoidHom
  refine ⟨AT.map f, IsElementaryAbelian.map f, ?_⟩
  rw [card_map_of_injective (T.equiv S).injective]
  change 8 ≤ Nat.card (A.subgroupOf (T : Subgroup G))
  rwa [Nat.card_congr (subgroupOfEquivOfLe hAT).toEquiv]

/-- An ambient elementary extension gives a conjugate extension in a chosen
Sylow, with the entire original Sylow centralizer transported into that Sylow. -/
public theorem exists_conj_elementary_extension_with_sylow_centralizer
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (E D : Subgroup G)
    [IsElementaryAbelian 2 E] [IsElementaryAbelian 2 D]
    (hES : E ≤ S) (hED : E ≤ D) (hD : 8 ≤ Nat.card D) :
    ∃ (g : G) (B : Subgroup G), IsElementaryAbelian 2 B ∧
      8 ≤ Nat.card B ∧ B ≤ S ∧ E.map (MulAut.conj g).toMonoidHom ≤ B ∧
      ((S : Subgroup G) ⊓ centralizer (E : Set G)).map
        (MulAut.conj g).toMonoidHom ≤ S := by
  let C := centralizer (E : Set G)
  let K := (S : Subgroup G) ⊓ C
  have hDC : D ≤ C := by
    intro d hd e he
    exact congrArg Subtype.val (mul_comm' (⟨e, hED he⟩ : D) ⟨d, hd⟩)
  have hEK : E ≤ K := le_inf hES E.le_centralizer
  have hKC : K ≤ C := inf_le_right
  have hK : IsPGroup 2 K := S.isPGroup'.of_injective
    (inclusion (show K ≤ (S : Subgroup G) from inf_le_left)) (inclusion_injective _)
  have hKCp : IsPGroup 2 (K.subgroupOf C) :=
    hK.of_injective (subgroupOfEquivOfLe hKC).toMonoidHom
      (subgroupOfEquivOfLe hKC).injective
  obtain ⟨T, hKT⟩ := hKCp.exists_le_sylow
  let R : Subgroup G := (T : Subgroup C).map C.subtype
  have hKR : K ≤ R := by
    intro k hk
    exact mem_map.mpr ⟨⟨k, hKC hk⟩, hKT hk, rfl⟩
  have hER : E ≤ R := hEK.trans hKR
  have hRC : R ≤ C := map_subtype_le _
  have hR : IsPGroup 2 R := T.isPGroup'.map C.subtype
  let : IsElementaryAbelian 2 (D.subgroupOf C) := IsElementaryAbelian.subgroupOf hDC
  obtain ⟨F, hFe, hF⟩ := rank_three_in_sylow (D.subgroupOf C)
    (by rwa [Nat.card_congr (subgroupOfEquivOfLe hDC).toEquiv]) T
  let : IsElementaryAbelian 2 F := hFe
  let f : T →* G := C.subtype.comp (T : Subgroup C).subtype
  have hf : Function.Injective f := C.subtype_injective.comp Subtype.coe_injective
  let L := F.map f
  let : IsElementaryAbelian 2 L := IsElementaryAbelian.map f
  have hLR : L ≤ R := by
    rintro x ⟨t, ht, rfl⟩
    exact mem_map.mpr ⟨t, t.property, rfl⟩
  have hL : 8 ≤ Nat.card L := by
    rwa [card_map_of_injective hf]
  let B₀ := E ⊔ L
  let : IsElementaryAbelian 2 B₀ :=
    IsElementaryAbelian.sup_of_le_centralizer (hLR.trans hRC)
  have hB₀R : B₀ ≤ R := sup_le hER hLR
  have hB₀ : 8 ≤ Nat.card B₀ := hL.trans (card_le_of_le le_sup_right)
  obtain ⟨U, hRU⟩ := hR.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G U S
  let c := MulAut.conj g
  have hRS : R.map c.toMonoidHom ≤ (S : Subgroup G) := by
    rw [← hg]
    exact map_mono hRU
  refine ⟨g, B₀.map c.toMonoidHom, IsElementaryAbelian.map _, ?_,
    (map_mono hB₀R).trans hRS, map_mono le_sup_left, (map_mono hKR).trans hRS⟩
  rwa [card_map_of_injective c.injective]

/-- In a finite simple group of elementary binary rank at least three, a
four-group has a conjugate in the rank-three Sylow commuting component, and
its original Sylow centralizer is carried into the same Sylow subgroup. -/
public theorem exists_conj_four_connected_with_sylow_centralizer_of_simple
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (A E : Subgroup G)
    [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 E]
    (hA : 8 ≤ Nat.card A) (hE : Nat.card E = 4)
    (hAS : A ≤ S) (hES : E ≤ S) :
    ∃ g : G, ElementaryCommutingConnected 2 A (E.map (MulAut.conj g).toMonoidHom) ∧
      ((S : Subgroup G) ⊓ centralizer (E : Set G)).map
        (MulAut.conj g).toMonoidHom ≤ S := by
  obtain ⟨D, hDe, hD, hED⟩ := exists_elementary_eight_above_four_of_simple A E hA hE
  let : IsElementaryAbelian 2 D := hDe
  obtain ⟨g, B, hBe, hB, hBS, hEB, hCS⟩ :=
    exists_conj_elementary_extension_with_sylow_centralizer S E D hES hED hD
  let : IsElementaryAbelian 2 B := hBe
  let E' := E.map (MulAut.conj g).toMonoidHom
  let : IsElementaryAbelian 2 E' := IsElementaryAbelian.map _
  have hE' : Nat.card E' = 4 := by
    rw [card_map_of_injective (MulAut.conj g).injective, hE]
  have hBE : B ≤ centralizer (E' : Set G) := by
    intro b hb e he
    exact congrArg Subtype.val (mul_comm' (⟨e, hEB he⟩ : B) ⟨b, hb⟩)
  exact ⟨g, (elementaryCommutingConnected_of_le_twoGroup (S : Subgroup G) A B
    S.isPGroup' hA hB hAS hBS).trans
      (ElementaryCommutingAdjacent.connected
        ⟨inferInstance, by omega, inferInstance,
          (show 2 ^ 2 ≤ Nat.card E' by omega), hBE⟩), hCS⟩

end Subgroup
