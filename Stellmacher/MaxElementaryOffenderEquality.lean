module
public import Stellmacher.MaxElementaryOffender
public import Stellmacher.ElementaryAbelianMaxJFixedCenter
public import Theory.ElementaryAbelian.AbelianNormalClosure

/-!
# Sharp maximum-elementary offender bounds

For an elementary abelian subgroup A whose order is a factor 2^j below the
maximum in S, compare A with V C_A(V). Relative-index counting gives the
sharp cardinal bound and shows that equality makes this replacement a member
of the maximum family. A maximum subgroup in C_S(V) transfers that family
into A(S), and yields both Omega-center containments.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, B.2.4, printed pp.75–76. This extends the cardinal
argument in `Stellmacher.MaxElementaryOffender` without changing its API.
-/

open scoped IsMulCommutative
namespace Stellmacher
variable {G H : Type*} [Group G] [Group H] [Finite G]

/-- A member of the maximum family realizes the maximum order. -/
public theorem maxOrder_eq_card_of_mem (S A : Subgroup G)
    (hA : A ∈ elementaryAbelianMaxSubgroups S) :
    elementaryAbelianMaxOrder S = Nat.card A := by
  exact (card_eq_elementaryAbelianMaxOrder S A hA).symm

/-- Every elementary subgroup has order at most the maximum order. -/
public theorem elementary_card_le_maxOrder (S A : Subgroup G) (hAS : A ≤ S)
    (hAe : IsElementaryAbelian 2 A) : Nat.card A ≤ elementaryAbelianMaxOrder S := by
  obtain ⟨B, hB⟩ := elementaryAbelianMaxSubgroups_nonempty S
  rw [maxOrder_eq_card_of_mem S B hB]
  exact hB.2.2 A hAS hAe

omit [Finite G] in
private theorem card_inf_mul_relIndex (K L : Subgroup G) :
    Nat.card ↥(K ⊓ L) * K.relIndex L = Nat.card L := by
  simpa only [Subgroup.relIndex_bot_left, Subgroup.inf_relIndex_right] using
    Subgroup.relIndex_mul_relIndex (⊥ : Subgroup G) (K ⊓ L) L bot_le inf_le_right

/-- The cardinal form of the rank-deficit bound, including its equality case. -/
public theorem maxElementary_card_bound_and_eq
    (S V A : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    [IsElementaryAbelian 2 A] (hVS : V ≤ S) (hAS : A ≤ S)
    (j : ℕ) (hAj : Nat.card A * 2 ^ j = elementaryAbelianMaxOrder S)
    (q : G →* H) (hker : q.ker = Subgroup.centralizer (V : Set G)) :
    Nat.card V ≤ Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) *
        Nat.card (A.map q) * 2 ^ j ∧
      (Nat.card V = Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) *
        Nat.card (A.map q) * 2 ^ j →
        V ⊔ (A ⊓ Subgroup.centralizer (V : Set G)) ∈ elementaryAbelianMaxSubgroups S) := by
  let C := A ⊓ Subgroup.centralizer (V : Set G)
  let I := V ⊓ C
  let F := V ⊓ Subgroup.centralizer (A : Set G)
  let _ : IsElementaryAbelian 2 C := IsElementaryAbelian.of_le inf_le_left
  have he : IsElementaryAbelian 2 ↥(V ⊔ C) :=
    IsElementaryAbelian.sup_of_le_centralizer inf_le_right
  have hBS : V ⊔ C ≤ S := sup_le hVS (inf_le_left.trans hAS)
  have hmax : Nat.card ↥(V ⊔ C) ≤ Nat.card A * 2 ^ j := by
    rw [hAj]
    exact elementary_card_le_maxOrder S _ hBS he
  have hprod : Nat.card V * V.relIndex C = Nat.card ↥(V ⊔ C) := by
    simpa only [inf_sup_self, Subgroup.relIndex_sup_left] using
      card_inf_mul_relIndex V (V ⊔ C)
  have hCcard : Nat.card I * V.relIndex C = Nat.card C :=
    card_inf_mul_relIndex V C
  have hAcard : Nat.card C * Nat.card (A.map q) = Nat.card A := by
    have ht := card_inf_mul_relIndex q.ker A
    rw [Subgroup.relIndex_ker] at ht
    simpa only [hker, inf_comm, C] using ht
  have hpos : 0 < V.relIndex C := by
    have hCpos : 0 < Nat.card C := Nat.card_pos
    nlinarith [hCcard]
  have hIle : I ≤ F := by
    refine le_inf inf_le_left ?_
    have hAA : A ≤ Subgroup.centralizer (A : Set G) :=
      Subgroup.le_centralizer_iff_isMulCommutative.mpr inferInstance
    exact (inf_le_right.trans inf_le_left).trans hAA
  have hIcard : Nat.card I ≤ Nat.card F :=
    Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective hIle)
  constructor
  · have hb : Nat.card V ≤ Nat.card I * Nat.card (A.map q) * 2 ^ j := by
      have hm : Nat.card V * V.relIndex C ≤
          (Nat.card I * Nat.card (A.map q) * 2 ^ j) * V.relIndex C := calc
        _ = Nat.card ↥(V ⊔ C) := hprod
        _ ≤ Nat.card A * 2 ^ j := hmax
        _ = _ := by rw [← hAcard, ← hCcard]; ac_rfl
      nlinarith
    exact hb.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hIcard))
  · intro heq
    refine ⟨hBS, he, fun E hES hEe => (elementary_card_le_maxOrder S E hES hEe).trans ?_⟩
    calc
      elementaryAbelianMaxOrder S =
          (Nat.card I * Nat.card (A.map q) * 2 ^ j) * V.relIndex C := by
        rw [← hAj, ← hAcard, ← hCcard]; ac_rfl
      _ ≤ (Nat.card F * Nat.card (A.map q) * 2 ^ j) * V.relIndex C := by
        gcongr
      _ = Nat.card V * V.relIndex C := by rw [heq]
      _ = Nat.card ↥(V ⊔ C) := hprod


/-- A maximum elementary subgroup contains every elementary subgroup of S centralizing it. -/
public theorem maxElementary_contains_elementary_centralizer (S A E : Subgroup G)
    (hA : A ∈ elementaryAbelianMaxSubgroups S) [IsElementaryAbelian 2 E]
    (hES : E ≤ S) (hEA : E ≤ Subgroup.centralizer (A : Set G)) : E ≤ A := by
  let _ : IsElementaryAbelian 2 A := hA.2.1
  have he : IsElementaryAbelian 2 ↥(A ⊔ E) :=
    IsElementaryAbelian.sup_of_le_centralizer hEA
  have hh : A = A ⊔ E :=
    Subgroup.eq_of_le_of_card_ge le_sup_left (hA.2.2 _ (sup_le hA.1 hES) he)
  exact (show E ≤ A ⊔ E from le_sup_right).trans_eq hh.symm

/-- A maximum elementary subgroup in the centralizer gives equality of maximum orders,
family inclusion, and the two Omega-center containments. -/
public theorem maxElementary_centralizer_maxOrder_and_omegaCenter (S V B : Subgroup G) [IsElementaryAbelian 2 V]
    (hVS : V ≤ S) (hB : B ∈ elementaryAbelianMaxSubgroups S)
    (hBC : B ≤ S ⊓ Subgroup.centralizer (V : Set G)) :
    elementaryAbelianMaxOrder (S ⊓ Subgroup.centralizer (V : Set G)) =
        elementaryAbelianMaxOrder S ∧
      elementaryAbelianMaxSubgroups (S ⊓ Subgroup.centralizer (V : Set G)) ⊆
        elementaryAbelianMaxSubgroups S ∧
      V ≤ omegaOneCenterAmbient
        (elementaryAbelianMaxJ (S ⊓ Subgroup.centralizer (V : Set G))) ∧
      omegaOneCenterAmbient (elementaryAbelianMaxJ S) ≤
        omegaOneCenterAmbient
          (elementaryAbelianMaxJ (S ⊓ Subgroup.centralizer (V : Set G))) := by
  let C := S ⊓ Subgroup.centralizer (V : Set G)
  have hBsmall : B ∈ elementaryAbelianMaxSubgroups C :=
    ⟨hBC, hB.2.1, fun E hEC hEe => hB.2.2 E (hEC.trans inf_le_left) hEe⟩
  have hord : elementaryAbelianMaxOrder C = elementaryAbelianMaxOrder S := by
    rw [maxOrder_eq_card_of_mem C B hBsmall, maxOrder_eq_card_of_mem S B hB]
  have hfam : elementaryAbelianMaxSubgroups C ⊆ elementaryAbelianMaxSubgroups S := by
    intro E hE
    refine ⟨hE.1.trans inf_le_left, hE.2.1, ?_⟩
    intro D hDS hDe
    calc
      Nat.card D ≤ elementaryAbelianMaxOrder S := elementary_card_le_maxOrder S D hDS hDe
      _ = elementaryAbelianMaxOrder C := hord.symm
      _ = Nat.card E := maxOrder_eq_card_of_mem C E hE
  have hJ : elementaryAbelianMaxJ C ≤ elementaryAbelianMaxJ S :=
    sSup_le fun E hE => le_sSup (hfam hE)
  have hJC : elementaryAbelianMaxJ C ≤ C := sSup_le fun E hE => hE.1
  have hJS : elementaryAbelianMaxJ S ≤ S := sSup_le fun E hE => hE.1
  have hVC : V ≤ C := le_inf hVS
    (Subgroup.le_centralizer_iff_isMulCommutative.mpr inferInstance)
  have hVJ : V ≤ Subgroup.centralizer (elementaryAbelianMaxJ C : Set G) :=
    Subgroup.le_centralizer_iff.mpr (hJC.trans inf_le_right)
  refine ⟨hord, hfam, elementary_centralizer_maxJ_le_omegaCenter C V hVC hVJ, ?_⟩
  let F := omegaOneCenterAmbient (elementaryAbelianMaxJ S)
  let _ : IsElementaryAbelian 2 F := omegaOneCenterAmbient_elementaryAbelian _
  have hFJ : F ≤ Subgroup.centralizer (elementaryAbelianMaxJ S : Set G) := by
    intro x hx
    exact Subgroup.mem_centralizer_iff.mpr ((mem_omegaOneCenterAmbient_iff _ _).mp hx).2.2
  have hFS : F ≤ S := by
    intro x hx
    exact hJS ((mem_omegaOneCenterAmbient_iff _ _).mp hx).1
  have hFB : F ≤ B := maxElementary_contains_elementary_centralizer S B F hB hFS
    (hFJ.trans (Subgroup.centralizer_le (show B ≤ elementaryAbelianMaxJ S from le_sSup hB)))
  exact elementary_centralizer_maxJ_le_omegaCenter C F (hFB.trans hBC)
    (hFJ.trans (Subgroup.centralizer_le hJ))

end Stellmacher
