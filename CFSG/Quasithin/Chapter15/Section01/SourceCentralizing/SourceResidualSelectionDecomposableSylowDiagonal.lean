module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableSylow

/-!
# The diagonal central seed of the original prime-three decomposable action

The two original Thompson four-groups are exchanged by the nontrivial
Sylow coset. Its fixed group is diagonal, has order four, and complements
each original marking in the whole sixteen-element fixed subgroup.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01.DecomposableMarker
open ChapterD ChapterD.UniqueFactor ChapterD.RatioDecomposition
open Stellmacher Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

private theorem fixed_diagonal
    (T E A B : Subgroup G) [IsElementaryAbelian 2 E]
    (hAE : A ≤ E) (hBE : B ≤ E) (hgen : A ⊔ B = E) (hdis : Disjoint A B)
    (hA : Nat.card A = 4) (hE : Nat.card E = 16)
    (hn : T ≤ normalizer (E : Set G))
    (hi : (T ⊓ centralizer (E : Set G)).relIndex T = 2)
    (t : G) (ht : t ∈ T) (htout : t ∉ centralizer (E : Set G))
    (hab : A.map (MulAut.conj t).toMonoidHom = B) :
    Nat.card (E ⊓ centralizer (T : Set G) : Subgroup G) = 4 ∧
      Disjoint A (E ⊓ centralizer (T : Set G)) ∧
      A ⊔ (E ⊓ centralizer (T : Set G)) = E := by
  let S := T ⊓ centralizer (E : Set G)
  let F := E ⊓ centralizer (T : Set G)
  let α : MulAut E := E.normalizerMonoidHom ⟨t,hn ht⟩
  let A' := A.subgroupOf E
  let B' := B.subgroupOf E
  let : IsElementaryAbelian 2 A' := IsElementaryAbelian.of_injective
    A'.subtype A'.subtype_injective
  have h2 : t^2 ∈ S := (S.subgroupOf T).sq_mem_of_index_two hi ⟨t,ht⟩
  have hα : ∀ x : E, α (α x) = x := by
    intro x
    apply Subtype.ext
    change t * (t * (x : G) * t⁻¹) * t⁻¹ = (x : G)
    calc
      _ = t^2 * (x : G) * (t^2)⁻¹ := by simp only [pow_two,mul_inv_rev,mul_assoc]
      _ = (x : G) := by rw [←h2.2 x x.property,mul_inv_cancel_right]
  have hAB : A'.map α.toMonoidHom = B' := by
    ext x
    constructor
    · rintro ⟨a,ha,rfl⟩
      change t * (a : G) * t⁻¹ ∈ B
      exact hab ▸ mem_map_of_mem (MulAut.conj t).toMonoidHom ha
    · intro hx
      change (x : G) ∈ B at hx
      obtain ⟨a,ha,he⟩ := (hab.symm ▸ hx : (x : G) ∈ A.map (MulAut.conj t).toMonoidHom)
      refine ⟨⟨a,hAE ha⟩,ha,?_⟩
      apply Subtype.ext
      exact he
  have hABtop : A' ⊔ B' = ⊤ := by
    apply map_injective E.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hAE,map_subgroupOf_eq_of_le hBE,hgen,
      ←MonoidHom.range_eq_map,E.range_subtype]
  have hdis' : Disjoint A' B' := by
    apply disjoint_iff.mpr
    ext x
    constructor
    · intro hx
      apply mem_bot.mpr
      apply Subtype.ext
      exact mem_bot.mp (disjoint_iff.mp hdis ▸ (show (x : G) ∈ A ⊓ B from hx))
    · exact fun hx => hx ▸ one_mem _
  have hcomm : A' ≤ centralizer (B' : Set E) := by
    intro a _ b _
    exact mul_comm _ _
  have hfixed : (A' ⊔ B') ⊓ α.toMonoidHom.eqLocus (MonoidHom.id E) =
      F.subgroupOf E := by
    rw [hABtop,top_inf_eq]
    ext x
    change α x = x ↔ (x : G) ∈ F
    constructor
    · intro hx
      have htx : t * (x : G) = (x : G) * t :=
        mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val hx)
      refine ⟨x.property,?_⟩
      intro y hy
      by_cases hyS : y ∈ S
      · exact (hyS.2 x x.property).symm
      · have hyt : y*t⁻¹ ∈ S := by
          apply ((S.subgroupOf T).mul_mem_iff_of_index_two hi
            (a := (⟨y,hy⟩ : T)) (b := (⟨t,ht⟩ : T)⁻¹)).mpr
          change y ∈ S ↔ t⁻¹ ∈ S
          simp only [S.inv_mem_iff]
          exact iff_of_false hyS (fun hh => htout hh.2)
        have hh := hyt.2 x x.property
        have hc := (show Commute (x : G) (y*t⁻¹) from hh).mul_right
          (show Commute (x : G) t from htx.symm)
        simpa only [inv_mul_cancel_right] using hc.eq.symm
    · intro hx
      apply Subtype.ext
      change t * (x : G) * t⁻¹ = (x : G)
      rw [hx.2 t ht,mul_inv_cancel_right]
  have hc := (elementary_swapped_pair_fixed A' B' hdis' hcomm α hα hAB).1
  rw [hfixed] at hc
  have hFc : Nat.card F = 4 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (show F ≤ E from inf_le_left)).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe hAE).toEquiv,hA] at hc
    exact hc
  have hAF : Disjoint A F := by
    apply disjoint_iff.mpr
    apply bot_unique
    intro a ha
    have hat : t * a * t⁻¹ = a := by rw [ha.2.2 t ht,mul_inv_cancel_right]
    have haB : a ∈ B := by
      rw [←hat]
      exact hab ▸ mem_map_of_mem (MulAut.conj t).toMonoidHom ha.1
    exact (disjoint_iff.mp hdis).le ⟨ha.1,haB⟩
  refine ⟨hFc,hAF,?_⟩
  have hFA : F ≤ centralizer (A : Set G) := by
    intro f hf a ha
    exact congrArg Subtype.val (mul_comm (⟨a,hAE ha⟩ : E) ⟨f,hf.1⟩)
  apply eq_of_le_of_card_ge (sup_le hAE inf_le_left)
  rw [card_sup_eq_mul_of_normalizes_of_disjoint _ _
    (hFA.trans (Subgroup.centralizer_le_normalizer _)) hAF,hA,hFc,hE]

/-- The literal Sylow fixed group is the diagonal complement of each marked
four-group. The support hypothesis is supplied by the prime-three source row. -/
theorem ThompsonPair.fixed_diagonal_of_support_four_not_dvd
    {T : Sylow 2 G} {M V : Subgroup G} [IsElementaryAbelian 2 V]
    (hTM : (T : Subgroup G) ≤ M) (hn : M ≤ normalizer (V : Set G))
    {U : Submodule (ZMod 2) (Additive V)}
    (c : FactorData (imageRepresentation M V hn) (Jhat (imageRepresentation M V hn)) U)
    (d : Decomposition c.representation) (s : ThompsonPair (T := T) hn c d)
    (hfour : ¬ 4 ∣ Nat.card (subspaceActionImage (imageRepresentation M V hn)
      (c.ambientFactor d s.first).space)) :
    let E := thompsonFixed T V
    let Z := E ⊓ centralizer (T : Set G)
    let A := thompsonPlane T V (c.ambientFactor d s.first).space
    let B := thompsonPlane T V (c.ambientFactor d s.second).space
    Nat.card Z = 4 ∧ Disjoint A Z ∧ A ⊔ Z = E ∧ Disjoint B Z ∧ B ⊔ Z = E := by
  let E := thompsonFixed T V
  let A := thompsonPlane T V (c.ambientFactor d s.first).space
  let B := thompsonPlane T V (c.ambientFactor d s.second).space
  let S := (T : Subgroup G) ⊓ centralizer (E : Set G)
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.of_injective
    (inclusion (show E ≤ V from inf_le_left)) (inclusion_injective _)
  have hET : (T : Subgroup G) ≤ normalizer (E : Set G) :=
    le_normalizer_inf (hTM.trans hn) ((ChapterB.le_normalizer_thompsonJ _ _).trans
      (normalizer_le_normalizer_centralizer _))
  obtain ⟨hk,hi⟩ := s.fixed_sylow_kernel_of_support_four_not_dvd hTM hn c d hfour
  have hST : S ≤ (T : Subgroup G) := inf_le_left
  have hSne : S ≠ (T : Subgroup G) := by
    intro hh
    change S.relIndex (T : Subgroup G) = 2 at hi
    rw [hh,relIndex_self] at hi
    omega
  obtain ⟨t,ht,htS⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hST hSne)
  have htout : t ∉ centralizer (E : Set G) := fun hh => htS ⟨ht,hh⟩
  have htA : t ∉ normalizer (plane V (c.ambientFactor d s.first).space : Set G) := by
    intro hh
    apply htS
    change t ∈ (T : Subgroup G) ⊓ centralizer (thompsonFixed T V : Set G)
    rw [hk,(s.sylow_geometry_of_support_four_not_dvd hTM hn c d hfour).1]
    exact ⟨ht,hh⟩
  obtain ⟨hab,hba⟩ := s.thompson_exchanges t ht htA
  have h1 := fixed_diagonal (T : Subgroup G) E A B inf_le_right inf_le_right
    s.thompson_split.symm (disjoint_iff.mpr s.thompson_disjoint)
    (s.thompson_card s.first) s.fixed_card hET hi t ht htout hab
  have h2 := fixed_diagonal (T : Subgroup G) E B A inf_le_right inf_le_right
    ((sup_comm _ _).trans s.thompson_split.symm) (disjoint_iff.mpr s.thompson_disjoint).symm
    (s.thompson_card s.second) s.fixed_card hET hi t ht htout hba
  exact ⟨h1.1,h1.2.1,h1.2.2,h2.2.1,h2.2.2⟩

end CFSG.Quasithin.Chapter15.Section01.DecomposableMarker
