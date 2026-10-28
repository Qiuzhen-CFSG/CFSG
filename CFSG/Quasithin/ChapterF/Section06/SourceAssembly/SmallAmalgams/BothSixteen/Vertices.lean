module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.BothSixteen.Cores
public import Theory.GroupTheory.ElementaryEightSymmetricThreeSplit

/-!
# The original vertices at overlap order sixteen

Both cores are elementary eights and are distinct by faithfulness. Thus each
opposite core supplies an involution outside the local kernel. The elementary
S₃ splitting theorem identifies each original vertex with C₂×S₄ and Sylow
normalization marks the whole common group as C₂×D₈. The last two theorems
apply this to the actual residual F.6.18 Sylow and to the original G/O₂(G)
images. No vertex model, splitting, or core identity is assumed.

Source: Aschbacher–Smith F.1.12(I)(2) and F.6.5, printed pp.262,305.
Compatible recognition of the pair as the Sp₄(2) flag amalgam is separate.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.SourceAssembly.BothSixteen
variable {G : Type*} [Group G] [Finite G] {A B : Subgroup G}

private theorem opposite_core_not_le (h : IsGoldschmidtTriple A B)
    (hcore : pCore 2 G=⊥) (hT : Nat.card (A⊓B : Subgroup G)=16) :
    ¬ (pCore 2 B).map B.subtype≤(pCore 2 A).map A.subtype := by
  let Q := (pCore 2 A).map A.subtype
  let R := (pCore 2 B).map B.subtype
  have hn (H : Subgroup G) : H≤normalizer ((pCore 2 H).map H.subtype : Set G) := by
    intro x hx
    apply (pCore 2 H).le_normalizer_map H.subtype
    exact ⟨⟨x,hx⟩,by rw [(pCore 2 H).normalizer_eq_top];trivial,rfl⟩
  have hcQ : Nat.card Q=8 := (card_map_of_injective A.subtype_injective).trans (core_card h hT)
  have hcR : Nat.card R=8 := (card_map_of_injective B.subtype_injective).trans
    (core_card h.symm (by simpa only [inf_comm B A] using hT))
  intro hRQ
  have he : R=Q := eq_of_le_of_card_ge hRQ (by rw [hcQ,hcR])
  have hnA : (Q.subgroupOf A).Normal :=
    (normal_subgroupOf_iff_le_normalizer (map_subtype_le _)).mpr (hn A)
  have hnB : (Q.subgroupOf B).Normal := by
    rw [←he]
    exact (normal_subgroupOf_iff_le_normalizer (map_subtype_le _)).mpr (hn B)
  have hb := h.common_normal_eq_bot hcore Q h.local_twoCore_le_intersection hnA hnB
  rw [hb,card_bot] at hcQ
  omega

/-- Both original good vertices at overlap order sixteen are C₂×S₄. The
involutory lift is selected from the distinct opposite elementary core. -/
theorem left_vertex (h : IsGoldschmidtTriple A B) (hcore : pCore 2 G=⊥)
    (hA : generalizedFitting A=pCore 2 A) (hB : generalizedFitting B=pCore 2 B)
    (hT : Nat.card (A⊓B : Subgroup G)=16) :
    Nonempty (A≃*Multiplicative (ZMod 2)×Equiv.Perm (Fin 4)) := by
  let e := h.quotient_left.some
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 A))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker=pCore 2 A := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have hEl := left_core_elementary h hcore hA hB hT
  have hEr := left_core_elementary h.symm hcore hB hA (by simpa only [inf_comm B A] using hT)
  let : IsElementaryAbelian 2 (pCore 2 B) := hEr
  let : IsElementaryAbelian 2 ((pCore 2 B).map B.subtype) := IsElementaryAbelian.map_subtype
  obtain ⟨w,hwR,hwQ⟩ := Set.not_subset.mp (opposite_core_not_le h hcore hT)
  have hwA : w∈A := (h.symm.local_twoCore_le_intersection hwR).2
  let wA : A := ⟨w,hwA⟩
  have hw2 : wA^2=1 := Subtype.ext (elemPow_eq_one_of_isElementaryAbelian w hwR)
  have hwn : f wA≠1 := by
    intro he
    have hw : wA∈pCore 2 A := hk ▸ (show wA∈f.ker from he)
    exact hwQ (mem_map_of_mem A.subtype hw)
  apply c2_symmetric_four_of_elementary_eight_s3_involution f hf
    (hk ▸ hEl) (hk ▸ core_card h hT) ?_ wA hw2 hwn
  rw [hk]
  exact h.local_core_selfCentralizing hA


/-- Mark the entire original common group inside the split Sylow model. -/
theorem common_sylow_split (h : IsGoldschmidtTriple A B) (hcore : pCore 2 G=⊥)
    (hA : generalizedFitting A=pCore 2 A) (hB : generalizedFitting B=pCore 2 B)
    (hT : Nat.card (A⊓B : Subgroup G)=16) :
    Nonempty ((A⊓B : Subgroup G)≃*Multiplicative (ZMod 2)×DihedralGroup 4) := by
  obtain ⟨eA⟩ := left_vertex h hcore hA hB hT
  let eZ : Multiplicative (ZMod 2)≃*ℤˣ := mulEquivOfPrimeCardEq (p := 2)
    (by simp [Nat.card_eq_fintype_card]) (by rw [Nat.card_eq_fintype_card];decide)
  let e := eA.trans (MulEquiv.prodCongr eZ (MulEquiv.refl _))
  obtain ⟨S,hS⟩ := h.intersection_sylow
  have hSA : (S : Subgroup G)≤A := hS.symm.le.trans inf_le_left
  let P := S.subtype hSA
  have hP : (P : Subgroup A)=(inclusion (show A⊓B≤A from inf_le_left)).range := by
    ext x
    change (x : G)∈(S : Subgroup G) ↔ _
    rw [←hS]
    exact ⟨fun hx => ⟨⟨x,hx⟩,rfl⟩,fun ⟨y,hy⟩ => hy ▸ y.property⟩
  obtain ⟨_,u,_⟩ := RankTwoAmalgam.exists_normalized_endpoint (inclusion inf_le_left)
    RankTwoAmalgam.MixedSixteen.left (inclusion_injective inf_le_left)
    RankTwoAmalgam.MixedSixteen.left_injective P hP
    RankTwoAmalgam.MixedSixteen.leftSylow rfl e
  exact ⟨u.trans (MulEquiv.prodCongr eZ.symm (MulEquiv.refl _))⟩

/-- The literal ambient Sylow in the residual F.6.18 source branch cannot
have order sixteen once the split-sixteen alternative has been excluded. -/
theorem common_sylow_card_ne_sixteen (h : IsGoldschmidtTriple A B) (hcore : pCore 2 G=⊥)
    (hA : generalizedFitting A=pCore 2 A) (hB : generalizedFitting B=pCore 2 B)
    (S : Sylow 2 G) (hS : A⊓B=(S : Subgroup G))
    (hns : ¬ Nonempty (S≃*Multiplicative (ZMod 2)×DihedralGroup 4)) : Nat.card S≠16 := by
  intro h16
  have hT : Nat.card (A⊓B : Subgroup G)=16 := hS ▸ h16
  obtain ⟨e⟩ := common_sylow_split h hcore hA hB hT
  exact hns ⟨(MulEquiv.subgroupCongr hS.symm).trans e⟩

/-- Original images in G/O₂(G), retaining the original common subgroup image. -/
theorem quotient_common_sylow_split (h : IsGoldschmidtTriple A B)
    (hA : generalizedFitting (A.map (QuotientGroup.mk' (pCore 2 G)))=
      pCore 2 (A.map (QuotientGroup.mk' (pCore 2 G))))
    (hB : generalizedFitting (B.map (QuotientGroup.mk' (pCore 2 G)))=
      pCore 2 (B.map (QuotientGroup.mk' (pCore 2 G))))
    (hT : Nat.card ((A⊓B).map (QuotientGroup.mk' (pCore 2 G)))=16) :
    Nonempty (((A⊓B).map (QuotientGroup.mk' (pCore 2 G)))≃*
      Multiplicative (ZMod 2)×DihedralGroup 4) := by
  have hT' : Nat.card (A.map (QuotientGroup.mk' (pCore 2 G))⊓
      B.map (QuotientGroup.mk' (pCore 2 G)) : Subgroup (G⧸pCore 2 G))=16 := by
    rw [←h.quotient_twoCore_intersection];exact hT
  obtain ⟨e⟩ := common_sylow_split h.quotient_twoCore h.quotient_twoCore_eq_bot hA hB hT'
  exact ⟨(MulEquiv.subgroupCongr h.quotient_twoCore_intersection).trans e⟩

end CFSG.Quasithin.ChapterF.SourceAssembly.BothSixteen
