module
public import Theory.GroupTheory.NormalAbelianSylowCentralizer
public import Theory.GroupTheory.PGroup.FrattiniAutomorphismKernel
public import Theory.GroupTheory.SylowDetectsKernel
public import Theory.GroupTheory.SpecificGroups.KleinFourAut
public import Theory.GroupTheory.PGroup.TrivialImage

/-!
# Index three after normality of an abelian Sylow subgroup

Let S be a normal abelian Sylow two-subgroup of a finite group G with trivial
odd core and no normal subgroup of index two. If the Frattini quotient of S
is a Klein four group, then S has index three. This supplies the index part
of the homocyclic conclusion cited in ABG II.3 Proposition 4, article page 28;
normality itself is a separate necessary hypothesis, not a conclusion here.

The normal abelian Sylow centralizer theorem makes conjugation faithful on
G/S. The kernel of the full automorphism action on the Frattini quotient is
a two-group. Since the abelian Sylow subgroup acts trivially by conjugation,
Sylow kernel detection makes the automizer's Frattini action faithful. Its
order, which is the index of S, therefore divides the order six of the
Klein four automorphism group. A Sylow index is odd, leaving one or three.
Index one would make G a two-group with no normal subgroup of index two,
so the trivial-image theorem would make G trivial, contradicting the
Klein four Frattini quotient.
-/

open Subgroup
open scoped IsMulCommutative

namespace Sylow

public theorem index_eq_three_of_normal_of_kleinFour_frattini
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    [(S : Subgroup G).Normal] [IsMulCommutative S]
    [IsKleinFour (S ⧸ frattini S)]
    (hcore : pPrimeCore 2 G = ⊥)
    (hno : ∀ N : Subgroup G, N.Normal → N.index ≠ 2) :
    (S : Subgroup G).index = 3 := by
  let U : Subgroup G := S
  let N := normalizer (U : Set G)
  let i : G →* N :=
    { toFun g := ⟨g, by change g ∈ normalizer (U : Set G); rw [U.normalizer_eq_top]; trivial⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
  let f : G →* MulAut S := U.normalizerMonoidHom.comp i
  let q := quotientAut (frattini S)
  have hfaith : Function.Injective (q.comp f.range.subtype) :=
    S.injective_on_range_of_isPGroup_kernel f q
      (isPGroup_quotientAut_frattini_kernel S.isPGroup') (by
        intro s _
        apply MulEquiv.ext
        intro t
        apply Subtype.ext
        change (s : G) * (t : G) * (s : G)⁻¹ = (t : G)
        have hc := congrArg Subtype.val (mul_comm s t)
        change (s : G) * (t : G) = (t : G) * (s : G) at hc
        rw [hc, mul_assoc, mul_inv_cancel, mul_one])
  have hfker : f.ker = U := by
    calc
      f.ker = centralizer (S : Set G) := by
        ext g
        change U.normalizerMonoidHom (i g) = 1 ↔ g ∈ centralizer (S : Set G)
        rw [← MonoidHom.mem_ker, normalizerMonoidHom_ker]
        rfl
      _ = U := S.centralizer_eq_self_of_normal_of_pPrimeCore_eq_bot hcore
  have hdvd : U.index ∣ 6 := by
    rw [← hfker, index_ker, ← IsKleinFour.card_mulAut (S ⧸ frattini S)]
    exact card_dvd_of_injective _ hfaith
  have hnotone : U.index ≠ 1 := by
    intro h
    have htop : U = ⊤ := index_eq_one.mp h
    have hGp : IsPGroup 2 G := by
      have hp := S.isPGroup'
      change IsPGroup 2 U at hp
      rw [htop] at hp
      exact hp.of_equiv (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G)
    have hone (g : G) : g = 1 :=
      MonoidHom.eq_one_of_no_normal_index_prime hno hGp (MonoidHom.id G) g
    let : Subsingleton G := ⟨fun x y => (hone x).trans (hone y).symm⟩
    let : Subsingleton (S ⧸ frattini S) := ⟨fun a b => by
      obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (frattini S) a
      obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (frattini S) b
      exact congrArg _ (show a = b from Subtype.ext (Subsingleton.elim _ _))⟩
    have hcard : Nat.card (S ⧸ frattini S) = 1 := Nat.card_unique
    have hfour := IsKleinFour.card_four (G := S ⧸ frattini S)
    omega
  have hodd := S.not_dvd_index
  have hle := Nat.le_of_dvd (by decide : 0 < 6) hdvd
  interval_cases h : U.index <;> simp_all

end Sylow
