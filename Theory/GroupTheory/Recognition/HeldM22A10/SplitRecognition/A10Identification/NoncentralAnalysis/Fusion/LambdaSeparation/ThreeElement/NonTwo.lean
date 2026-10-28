module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.LambdaSeparation.ThreeElement.Overgroups

/-!
# The lambda-core normalizer is not a two-group

The action of N_G(W) on E=Z(W) has kernel W, of order 32. If this normalizer
were a two-group, the ambient Sylow order 128 would bound its action image
by four, making that image abelian. But xi sends lambda to mu*lambda.
An order-64 extension in C_G(lambda) fixes lambda and pi*mu. Commutation
with xi on E would therefore force this whole extension to fix mu and pi,
putting it in C_G(pi,lambda)=W, a contradiction.

Source: D. Held, Illinois J. Math. 13 (1969), 224–240,
DOI 10.1215/ijm/1256053756, Lemma 2.4, printed p.226. This action argument
replaces the source's comparison of order-64 subgroups inside a Sylow group.
-/

open Subgroup Equiv
open scoped IsMulCommutative
namespace Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.Fusion.LambdaSeparation
open Coordinates

private theorem commutative_of_card_le_four
    {K : Type*} [Group K] [Finite K] (h : Nat.card K ≤ 4) : IsMulCommutative K := by
  have hp : 0 < Nat.card K := Nat.card_pos
  have hh : Nat.card K = 1 ∨ Nat.card K = 2 ∨ Nat.card K = 3 ∨ Nat.card K = 4 := by omega
  rcases hh with h1 | h2 | h3 | h4
  · let : Subsingleton K := (Nat.card_eq_one_iff_unique.mp h1).1
    exact ⟨⟨fun _ _ => Subsingleton.elim _ _⟩⟩
  · let : IsCyclic K := isCyclic_of_prime_card h2
    infer_instance
  · let : IsCyclic K := isCyclic_of_prime_card h3
    infer_instance
  · exact IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) h4

universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)

/-- Lambda fusion forces an odd prime into the normalizer of W. -/
public theorem lambdaCore_normalizer_not_two
    (h : IsConj D.z (D.a10ModelEmbedding e lam)) :
    ¬ IsPGroup 2 (normalizer (lambdaCore D e : Set G)) := by
  rw [← lambdaCenter_normalizer_eq]
  intro htwo
  let E := lambdaCenter D e
  let N := normalizer (E : Set G)
  let r := E.normalizerMonoidHom
  have hEN : lambdaCore D e ≤ N := by
    rw [← lambdaCenter_centralizer D e]
    exact centralizer_le_normalizer _
  have hker : Nat.card r.ker = 32 := by
    rw [normalizerMonoidHom_ker, lambdaCenter_centralizer,
      Nat.card_congr (subgroupOfEquivOfLe hEN).toEquiv, lambdaCore_card]
  have hratio : 32 * Nat.card r.range = Nat.card N := by
    have hh := r.ker.card_mul_index
    rw [index_ker, hker] at hh
    exact hh
  have hbound : Nat.card N ≤ 128 := by
    obtain ⟨T, hNT⟩ := htwo.exists_le_sylow
    have hT : Nat.card T = 128 := by
      rw [T.card_eq_multiplicity, ← D.sylow.card_eq_multiplicity, D.sylow_card]
    exact (card_le_of_le hNT).trans hT.le
  have hsmall : Nat.card r.range ≤ 4 := by omega
  let := commutative_of_card_le_four hsmall
  have hrcomm (a b : N) : r a * r b = r b * r a :=
    setLike_mul_comm (show r a ∈ r.range from ⟨a, rfl⟩)
      (show r b ∈ r.range from ⟨b, rfl⟩)
  obtain ⟨P, hP, hWP, hPC⟩ := exists_lambda_core_overgroup D e h
  have hPN : P ≤ N := by
    change P ≤ normalizer (lambdaCenter D e : Set G)
    rw [lambdaCenter_normalizer_eq]
    exact lambda_core_overgroup_le_normalizer D e P hP hWP
  let f := D.a10ModelEmbedding e
  let piE : E := ⟨f pi, lambdaCenter_pi D e⟩
  let muE : E := ⟨f mu, lambdaCenter_mu D e⟩
  let lamE : E := ⟨f lam, lambdaCenter_lam D e⟩
  let xiN : N := ⟨f xi, by
    change f xi ∈ normalizer (lambdaCenter D e : Set G)
    rw [lambdaCenter_normalizer_eq]
    exact xi_mem_lambdaCore_normalizer D e⟩
  have hxi : r xiN lamE = muE * lamE := by
    apply Subtype.ext
    change f xi * f lam * (f xi)⁻¹ = f mu * f lam
    rw [← map_inv, ← map_mul, ← map_mul, ← map_mul]
    exact congrArg f (show xi * lam * xi⁻¹ = mu * lam by decide +kernel)
  have hPH : P ≤ D.centralizer := by
    intro g hg
    let gN : N := ⟨g, hPN hg⟩
    let b := r gN
    have hbl : b lamE = lamE := by
      apply Subtype.ext
      exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp (hPC hg))
    have hbc : b (piE * muE) = piE * muE := by
      apply Subtype.ext
      change g * (f pi * f mu) * g⁻¹ = f pi * f mu
      rw [← map_mul]
      exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp
        (lambdaCore_normalizer_le_centralizer D e
          (lambda_core_overgroup_le_normalizer D e P hP hWP hg)))
    have hbm : b muE = muE := by
      apply mul_right_cancel (b := lamE)
      calc
        b muE * lamE = b (muE * lamE) := by rw [map_mul, hbl]
        _ = b (r xiN lamE) := by rw [hxi]
        _ = r xiN (b lamE) := by
          exact (congrArg (fun a : MulAut E => a lamE) (hrcomm xiN gN)).symm
        _ = muE * lamE := by rw [hbl, hxi]
    have hbp : b piE = piE := by
      rw [map_mul, hbm] at hbc
      exact mul_right_cancel hbc
    have hgpi := congrArg Subtype.val hbp
    change g * f pi * g⁻¹ = f pi at hgpi
    rw [D.a10ModelEmbedding_central e] at hgpi
    exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hgpi)
  have hPW : P ≤ lambdaCore D e := by
    rw [lambdaCore_eq_inf_centralizer_lam]
    exact le_inf hPH hPC
  have hd := card_dvd_of_le hPW
  rw [hP, lambdaCore_card] at hd
  norm_num at hd

end Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.Fusion.LambdaSeparation
