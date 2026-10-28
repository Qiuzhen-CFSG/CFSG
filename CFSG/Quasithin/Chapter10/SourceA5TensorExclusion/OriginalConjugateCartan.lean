module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.OriginalLinearCartan

/-!
# The literal conjugate Cartan factor in the linear exclusion

Take the original factor A ∩ Lᵗ, where t belongs to the Sylow subgroup and
moves L. The source C-component calculation supplies its section centralization
of L. Elementary abelianness supplies exponent three. The checked linear
terminal theorem then gives the contradiction with the original Cartan orbit
and its order-three subgroup inside K. No tensor-coordinate or independent
section-centralizer premise remains.

The actual Cartan construction, its normalization of K, normalizer-orbit
identity, and the original linear action map remain source inputs.
Source: Aschbacher–Smith 9.3.8, printed p.734.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 Chapter4 ChapterA.Section03
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]
  {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

include m in
/-- The same original Cartan orbit excludes SL₃(4), for both the single
and repeated natural-module rows. No section-centralization premise remains. -/
theorem false_of_linear_conjugate_cartan
    (hF : Nat.card F = 4)
    (I K A N B : Subgroup G) [IsElementaryAbelian 3 A]
    (hLI : L ≤ I) (hKI : K ≤ I) {t : G}
    (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hEI : A ⊓ L.map (MulAut.conj t).toMonoidHom ≤ I)
    (f : I →* SL(3,F)) (S : Sylow 2 SL(3,F))
    (hL : (L.subgroupOf I).map f ∈ localCComponents S)
    (hproper : (L.subgroupOf I).map f ≠ ⊤)
    (hkL : IsPGroup 2 (f.subgroupMap (L.subgroupOf I)).ker)
    (hAK : A ≤ normalizer (K : Set G))
    (hkK : IsPGroup 2 (f.subgroupMap (K.subgroupOf I)).ker)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (hNK : N ≤ normalizer (K : Set G)) (hgen : componentOrbit (A ⊓ L.map (MulAut.conj t).toMonoidHom) N = A)
    (hBA : B ≤ A) (hBK : B ≤ K) (hB : Nat.card B = 3) : False := by
  have hBne : B ≠ ⊥ := by
    intro he
    rw [he,Subgroup.card_bot] at hB
    omega
  obtain ⟨b,hb⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hBne
  have hb3 : orderOf b = 3 := by
    exact ((Nat.dvd_prime (by decide : Nat.Prime 3)).mp
      (hB ▸ orderOf_dvd_natCard b)).resolve_left (fun h => hb (orderOf_eq_one_iff.mp h))
  let E := A ⊓ L.map (MulAut.conj t).toMonoidHom
  have hEC : E ≤ sectionCentralizer L :=
    inf_le_right.trans (m.conjugate_factor_le_sectionCentralizer ht htn)
  have h3 (x : G) (hx : x ∈ E) : x ^ 3 = 1 :=
    elemPow_eq_one_of_isElementaryAbelian x hx.1
  exact source_tensor_torus_cubic_contradiction K A E N eK hNK
    (source_tensor_linear_original_chosen_factor hF I L K E hLI hKI hEI
      f S hL hproper e hkL hEC (inf_le_left.trans hAK) hkK h3)
    hgen b (hBA b.property) (hBK b.property)
    ((Subgroup.orderOf_coe b).trans hb3)


end CFSG.Quasithin.Chapter10.SourceA5TensorModel
