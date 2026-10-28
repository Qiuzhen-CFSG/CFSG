module

public import Theory.GroupTheory.CentralizerCutFromFixedLifting
public import Theory.Representation.SymplecticFourOrthogonalCover.FixedLifting
public import Theory.ElementaryAbelian.VectorSpace

/-!
# The symplectic centralizer cut with its actual conjugation action

Universal odd-orthogonal fixed lifting turns a central displacement into
commutation in the original elementary subgroup. The final paragraph of
MS93 (3.4) therefore gives the actual cut once the preceding graph bounds
Zstar <= U D and [Zstar,Qtilde] <= D are supplied. The action formula uses
the original subgroup elements and a surjection from the original actor;
no complement to the central fixed layer is required.

Source: Meierfrankenfeld–Stellmacher (1993), (1.5)(ii) and (3.4), p.869.
-/

public section
open Subgroup Representation Representation.OneCohomology
open scoped IsMulCommutative commutatorElement

namespace CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
variable {G K : Type*} [Group G] [Field K] [Finite K] [CharP K 2]
  [Algebra (ZMod 2) K]
open Representation.SymplecticFourOrthogonalCover

theorem commute_of_central_displacement
    (U D A : Subgroup G) [Finite U] [IsElementaryAbelian 2 U]
    (π : A →* L (K := K)) (hπ : Function.Surjective π)
    (σ : Representation (ZMod 2) (L (K := K)) (Additive U))
    (hact : ∀ a : A, ∀ u : U,
      ((σ (π a) (Additive.ofMul u)).toMul : G) = (a:G)*u*(a:G)⁻¹)
    (p : σ.IntertwiningMap (binaryNatural (K := K))) (hp : IsCover p)
    (hDA : D ≤ centralizer (A : Set G))
    (u : G) (hu : u ∈ U) (a : G) (ha : a ∈ A) (hc : ⁅a,u⁆ ∈ D) :
    Commute a u := by
  let v : Additive U := Additive.ofMul ⟨u,hu⟩
  let g : L (K := K) := π ⟨a,ha⟩
  have hval : ((σ g v - v).toMul : G) = ⁅a,u⁆ := by
    rw [toMul_sub, div_eq_mul_inv]
    change ((σ (π ⟨a,ha⟩) (Additive.ofMul ⟨u,hu⟩)).toMul : G) * u⁻¹ = _
    rw [hact]
    rfl
  have hfixed : σ g v - v ∈ fixed σ := by
    intro b
    obtain ⟨b,rfl⟩ := hπ b
    apply Additive.toMul.injective
    apply Subtype.ext
    have hbact := hact b (σ g v - v).toMul
    simp only [ofMul_toMul] at hbact
    rw [hbact]
    have hb : (b:G) * ((σ g v - v).toMul:G) = ((σ g v - v).toMul:G) * b := by
      exact hDA (hval.symm ▸ hc) b b.property
    rw [hb, mul_inv_cancel_right]
  have he := cover_displacement_fixed p hp g v hfixed
  have hc1 : ⁅a,u⁆ = 1 := by
    rw [← hval, he, sub_self]
    rfl
  exact commutatorElement_eq_one_iff_commute.mp hc1

theorem centralizer_cut_of_symplectic_cover
    (A T Q U D Z : Subgroup G) [Finite U] [IsElementaryAbelian 2 U]
    (π : A →* L (K := K)) (hπ : Function.Surjective π)
    (σ : Representation (ZMod 2) (L (K := K)) (Additive U))
    (hact : ∀ a : A, ∀ u : U,
      ((σ (π a) (Additive.ofMul u)).toMul : G) = (a:G)*u*(a:G)⁻¹)
    (p : σ.IntertwiningMap (binaryNatural (K := K))) (hp : IsCover p)
    (hTA : T ≤ normalizer (A : Set G)) (hQT : Q ≤ T)
    (hDU : D ≤ normalizer (U : Set G))
    (hDA : D ≤ centralizer (A : Set G)) (hZ : Z ≤ U ⊔ D)
    (hcomm : ⁅Z, (A ⊔ (T ⊓ centralizer (Z : Set G))) ⊓ Q⁆ ≤ D) :
    (A ⊔ (T ⊓ centralizer (Z : Set G))) ⊓ Q ≤ T ⊓ centralizer (Z : Set G) :=
  centralizer_cut_of_fixed_lifting A T Q U D Z hTA hQT hDU hDA hZ hcomm
    (commute_of_central_displacement U D A π hπ σ hact p hp hDA)

end CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
