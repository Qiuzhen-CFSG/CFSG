module
public import Stellmacher.ElementaryAbelianMaxJ
public import Theory.ElementaryAbelian.Join

/-!
# The maximal elementary subgroup offender bound

Let V be a normal elementary abelian subgroup of a finite group, lying in S,
and let A have maximal order among elementary abelian subgroups of S.
For any homomorphism q with kernel the centralizer of V, we prove
|V| ≤ |C_V(A)| |q(A)|. This is the cardinal inequality in the first paragraph
of Stellmacher (2.2), Journal of Algebra 190 (1997), p.20, as transcribed in
`refs/latex/stellmacher-n-group.tex`.

The elementary abelian subgroup V C_A(V) lies in S, so its order is at most
|A|. Relative-index counting computes its order and that of C_A(V) using
the same positive index. Kernel/image counting for q on A cancels this
index. Finally V ∩ C_A(V) lies in C_V(A). The inequality is independent of
the quotient action instance; Section 2 transports it to the offender
family using its named faithful conjugation action.
-/

namespace Stellmacher

private theorem card_inf_mul_relIndex {G : Type*} [Group G] (H K : Subgroup G) :
    Nat.card ↥(H ⊓ K) * H.relIndex K = Nat.card K := by
  simpa only [Subgroup.relIndex_bot_left, Subgroup.inf_relIndex_right] using
    Subgroup.relIndex_mul_relIndex (⊥ : Subgroup G) (H ⊓ K) K bot_le inf_le_right

private theorem elementary_of_le {G : Type*} [Group G]
    (H K : Subgroup G) [IsElementaryAbelian 2 K] (hHK : H ≤ K) :
    IsElementaryAbelian 2 H := by
  refine {
    toIsMulCommutative := ⟨⟨fun x y => Subtype.ext (congrArg (fun k : K => (k : G))
      ((IsMulCommutative.is_comm (M := K)).comm
        (⟨x, hHK x.property⟩ : K) (⟨y, hHK y.property⟩ : K)))⟩⟩
    exponent_dvd_p := ?_ }
  rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
  intro x
  exact Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (p := 2)
    (A := K) (x : G) (hHK x.property))

public theorem maxElementary_card_le_fixed_mul_image
    {G H : Type*} [Group G] [Group H] [Finite G]
    (S V A : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    (hVS : V ≤ S) (hA : A ∈ elementaryAbelianMaxSubgroups S)
    (q : G →* H) (hker : q.ker = Subgroup.centralizer (V : Set G)) :
    Nat.card V ≤ Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) *
      Nat.card (A.map q) := by
  let C := A ⊓ Subgroup.centralizer (V : Set G)
  let I := V ⊓ C
  let _ : IsElementaryAbelian 2 A := hA.2.1
  let _ : IsElementaryAbelian 2 C := elementary_of_le C A inf_le_left
  have hsupElem : IsElementaryAbelian 2 ↥(V ⊔ C) :=
    IsElementaryAbelian.sup_of_le_centralizer inf_le_right
  have hmax : Nat.card ↥(V ⊔ C) ≤ Nat.card A :=
    hA.2.2 (V ⊔ C) (sup_le hVS (inf_le_left.trans hA.1)) hsupElem
  have hprod : Nat.card V * V.relIndex C = Nat.card ↥(V ⊔ C) := by
    have ht := card_inf_mul_relIndex V (V ⊔ C)
    simpa only [inf_sup_self, Subgroup.relIndex_sup_left] using ht
  have hCcard : Nat.card I * V.relIndex C = Nat.card C :=
    card_inf_mul_relIndex V C
  have hAcard : Nat.card C * Nat.card (A.map q) = Nat.card A := by
    have ht := card_inf_mul_relIndex q.ker A
    rw [Subgroup.relIndex_ker] at ht
    simpa only [hker, inf_comm, C] using ht
  have hpos : 0 < V.relIndex C := by
    have hCpos : 0 < Nat.card C := Nat.card_pos
    nlinarith [hCcard]
  have hIle : I ≤ V ⊓ Subgroup.centralizer (A : Set G) := by
    refine le_inf inf_le_left ?_
    have hAA : A ≤ Subgroup.centralizer (A : Set G) :=
      Subgroup.le_centralizer_iff_isMulCommutative.mpr inferInstance
    exact (inf_le_right.trans inf_le_left).trans hAA
  have hIcard : Nat.card I ≤ Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) :=
    Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective hIle)
  have hbound : Nat.card V ≤ Nat.card I * Nat.card (A.map q) := by
    have hm : Nat.card V * V.relIndex C ≤
        (Nat.card I * Nat.card (A.map q)) * V.relIndex C := calc
      Nat.card V * V.relIndex C = Nat.card ↥(V ⊔ C) := hprod
      _ ≤ Nat.card A := hmax
      _ = (Nat.card I * Nat.card (A.map q)) * V.relIndex C := by
        rw [← hAcard, ← hCcard]
        ac_rfl
    nlinarith
  exact hbound.trans (Nat.mul_le_mul_right _ hIcard)

end Stellmacher
