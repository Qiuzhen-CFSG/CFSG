module

public import Theory.GroupTheory.PResidual.PrimeToAction
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupTheory.InvolutionCentralizerControl
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# The fixed line complementary to a natural binary plane

An abelian group of order eight acted on through a coprime conjugation
image splits as its moving subgroup and its fixed subgroup. If the moving
subgroup is a plane of order four, the fixed subgroup has order two. Any
group normalizing both the actor and the abelian group preserves this
fixed line, and therefore centralizes it.

The same conclusion needs only a fixed-free plane containing all
commutators: coprime splitting and subgroup orders force that plane to be
the whole moving subgroup. A cubic quotient modulo the actor's two-core
supplies the required odd image whenever that core centralizes the module.

This is the elementary fixed-complement argument used in the normal
rank-one branch of Aschbacher–Smith, Chapter 14, proof of (14.2.20),
combined manuscript of 1 March 2004. The statements keep the actual
ambient centralizer and normalizer action; no amalgam classification is
assumed.
-/

open scoped IsMulCommutative
namespace Subgroup

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem normalizes_of_le_abelian (A B C : Subgroup G) [IsMulCommutative A]
    (hBA : B ≤ A) (hCA : C ≤ A) : C ≤ normalizer (B : Set G) :=
  (hCA.trans ((le_centralizer_iff_isMulCommutative.mpr inferInstance).trans
    (centralizer_le hBA))).trans (centralizer_le_normalizer _)

/-- The centralizer of an actor moving exactly a four-plane in an abelian
eight is a complementary subgroup of order two. -/
public theorem card_fixed_complement_of_coprime_image
    (A V L : Subgroup G) [IsMulCommutative A]
    (hA : Nat.card A = 8) (hV : Nat.card V = 4)
    (hLA : L ≤ normalizer (A : Set G))
    (hcop : Nat.Coprime
      (Nat.card (A.normalizerMonoidHom.comp (inclusion hLA)).range) (Nat.card A))
    (hcomm : ⁅A,L⁆ = V) :
    Nat.card (A ⊓ centralizer (L : Set G) : Subgroup G) = 2 ∧
      V ⊔ (A ⊓ centralizer (L : Set G)) = A ∧
      Disjoint V (A ⊓ centralizer (L : Set G)) := by
  have hs := commutator_centralizer_decomposition_of_coprime_image A L hLA hcop
  rw [hcomm] at hs
  have hVA : V ≤ A := by
    rw [← hcomm]
    exact le_normalizer_iff_commutator_le_left.mp hLA
  have hd : Disjoint V (A ⊓ centralizer (L : Set G)) := disjoint_iff.mpr hs.2
  have hp := card_sup_eq_mul_of_normalizes_of_disjoint V
    (A ⊓ centralizer (L : Set G))
    (normalizes_of_le_abelian A _ _ hVA inf_le_left) hd
  rw [hs.1, hA, hV] at hp
  exact ⟨by omega, hs.1, hd⟩

/-- A fixed-free four-plane containing all displacements is the complete
moving subgroup of an abelian eight under a coprime image. -/
public theorem commutator_eq_plane_of_coprime_image
    (A V L : Subgroup G) [IsMulCommutative A]
    (hVA : V ≤ A) (hA : Nat.card A = 8) (hV : Nat.card V = 4)
    (hLA : L ≤ normalizer (A : Set G))
    (hcop : Nat.Coprime
      (Nat.card (A.normalizerMonoidHom.comp (inclusion hLA)).range) (Nat.card A))
    (hmove : ⁅A,L⁆ ≤ V) (hfixed : V ⊓ centralizer (L : Set G) = ⊥) :
    ⁅A,L⁆ = V := by
  let D := ⁅A,L⁆
  let E := A ⊓ centralizer (L : Set G)
  have hs := commutator_centralizer_decomposition_of_coprime_image A L hLA hcop
  have hDA : D ≤ A := hmove.trans hVA
  have hd : Disjoint D E := disjoint_iff.mpr hs.2
  have hp : 8 = Nat.card D * Nat.card E := by
    have hp := card_sup_eq_mul_of_normalizes_of_disjoint D E
      (normalizes_of_le_abelian A D E hDA inf_le_left) hd
    simpa only [D,E,hs.1,hA] using hp
  have hVE : Disjoint V E := by
    apply disjoint_iff.mpr
    apply bot_unique
    intro x hx
    have hm : x ∈ V ⊓ centralizer (L : Set G) := ⟨hx.1,hx.2.2⟩
    simpa only [hfixed,mem_bot] using hm
  have hcardVE := card_sup_eq_mul_of_normalizes_of_disjoint V E
    (normalizes_of_le_abelian A V E hVA inf_le_left) hVE
  have hbound : Nat.card (V ⊔ E : Subgroup G) ≤ 8 := by
    simpa only [hA] using card_le_of_le (sup_le hVA (show E ≤ A from inf_le_left))
  rw [hcardVE,hV] at hbound
  have hE : Nat.card E ≤ 2 := by omega
  have hD : Nat.card D ≤ 4 := by simpa only [hV] using card_le_of_le hmove
  have hD4 : Nat.card D = 4 := by nlinarith
  exact eq_of_le_of_card_ge hmove (by rw [hD4,hV])

/-- Every group preserving the module and actor centralizes their fixed
complement of order two. -/
public theorem fixed_complement_centralized_of_coprime_image
    (A V L I : Subgroup G) [IsMulCommutative A]
    (hA : Nat.card A = 8) (hV : Nat.card V = 4)
    (hLA : L ≤ normalizer (A : Set G))
    (hcop : Nat.Coprime
      (Nat.card (A.normalizerMonoidHom.comp (inclusion hLA)).range) (Nat.card A))
    (hcomm : ⁅A,L⁆ = V)
    (hIA : I ≤ normalizer (A : Set G)) (hIL : I ≤ normalizer (L : Set G)) :
    Nat.card (A ⊓ centralizer (L : Set G) : Subgroup G) = 2 ∧
      V ⊔ (A ⊓ centralizer (L : Set G)) = A ∧
      Disjoint V (A ⊓ centralizer (L : Set G)) ∧
      I ≤ centralizer (A ⊓ centralizer (L : Set G) : Set G) := by
  obtain ⟨hcard,hsup,hdis⟩ := card_fixed_complement_of_coprime_image A V L hA hV hLA hcop hcomm
  refine ⟨hcard,hsup,hdis,?_⟩
  exact ((le_inf hIA (hIL.trans (normalizer_le_normalizer_centralizer L))).trans
    inf_normalizer_le_normalizer_inf).trans
      (normalizer_le_centralizer_of_card_two _ hcard)

/-- An odd conjugation image with a fixed-free moving plane gives an actual
fixed line centralized by every common normalizer. -/
public theorem fixed_line_of_odd_image_and_fixed_free_plane
    (A V L I : Subgroup G) [IsMulCommutative A]
    (hVA : V ≤ A) (hA : Nat.card A = 8) (hV : Nat.card V = 4)
    (hLA : L ≤ normalizer (A : Set G))
    (hodd : Odd (Nat.card (A.normalizerMonoidHom.comp (inclusion hLA)).range))
    (hmove : ⁅A,L⁆ ≤ V) (hfixed : V ⊓ centralizer (L : Set G) = ⊥)
    (hIA : I ≤ normalizer (A : Set G)) (hIL : I ≤ normalizer (L : Set G)) :
    Nat.card (A ⊓ centralizer (L : Set G) : Subgroup G) = 2 ∧
      V ⊔ (A ⊓ centralizer (L : Set G)) = A ∧
      Disjoint V (A ⊓ centralizer (L : Set G)) ∧
      I ≤ centralizer (A ⊓ centralizer (L : Set G) : Set G) := by
  have hcop : Nat.Coprime
      (Nat.card (A.normalizerMonoidHom.comp (inclusion hLA)).range) (Nat.card A) := by
    rw [hA]
    exact hodd.coprime_two_right.pow_right 3
  exact fixed_complement_centralized_of_coprime_image A V L I hA hV hLA hcop
    (commutator_eq_plane_of_coprime_image A V L hVA hA hV hLA hcop hmove hfixed) hIA hIL

omit [Finite G] in
/-- An actor with cubic two-core quotient acts through an odd image if its
two-core centralizes the module. -/
public theorem odd_conjugation_image_of_cubic_two_core_quotient
    (A L : Subgroup G) (hLA : L ≤ normalizer (A : Set G))
    (hquot : Nat.card (L ⧸ pCore 2 L) = 3)
    (hcentral : L.pCoreIn 2 ≤ centralizer (A : Set G)) :
    Odd (Nat.card (A.normalizerMonoidHom.comp (inclusion hLA)).range) := by
  let f := A.normalizerMonoidHom.comp (inclusion hLA)
  have hker : pCore 2 L ≤ f.ker := by
    intro l hl
    change A.normalizerMonoidHom ⟨(l : G),hLA l.property⟩ = 1
    rw [← MonoidHom.mem_ker,A.normalizerMonoidHom_ker]
    exact hcentral (mem_map_of_mem L.subtype hl)
  have hdiv : Nat.card f.range ∣ 3 := by
    rw [← index_ker]
    simpa only [index_eq_card,hquot] using index_dvd_of_le hker
  exact (by decide : Odd 3).of_dvd_nat hdiv

end Subgroup
