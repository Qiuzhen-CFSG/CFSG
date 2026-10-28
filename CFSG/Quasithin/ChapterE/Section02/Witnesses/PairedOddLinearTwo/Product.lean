module
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.PairedBender.Dihedral
public import Theory.GroupTheory.TwoConjugateProduct.Projection
public import Theory.ElementaryAbelian.Injective

/-!
# Dihedral pairs from cyclic elementary coordinate images

A nontrivial elementary subgroup of a direct product has a nontrivial
coordinate image. If both images have order at most two, one has order
exactly two. The odd-rotation construction then retains all of the original
subgroup, including its other coordinate and its actual ambient Sylow.

Source: Aschbacher–Smith E.2.7, printed p.219, paired odd-linear case.
-/

@[expose] public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterE.Witnesses.PairedOddLinearTwo
variable {H : Type*} [Group H] [Finite H]

structure DihedralWitness (T : Sylow 2 H) (M V : Subgroup H)
    extends QuotientLift.Pair T M V where
  prime : ℕ
  prime_prime : prime.Prime
  prime_odd : prime ≠ 2
  degree : ℕ
  degree_pos : 0 < degree
  model : subgroup ⧸ (M.subgroupOf subgroup).normalCore ≃* DihedralGroup (prime ^ degree)

theorem exists_dihedral_of_projection_cards
    {G A : Type*} [Group G] [Finite G] [Group A] [Finite A]
    (W : Subgroup (G × A)) [IsElementaryAbelian 2 W] (hW : W ≠ ⊥)
    (hfirst : Nat.card (W.map (MonoidHom.fst G A)) ≤ 2)
    (hsecond : Nat.card (W.map (MonoidHom.snd G A)) ≤ 2)
    (hG : pCore 2 G = ⊥) (hA : pCore 2 A = ⊥)
    (T : Sylow 2 H) (M : Subgroup H) (f : G × A →* H) (hf : Function.Injective f)
    (hVT : W.map f ≤ T) (hVM : W.map f ≤ M.pCoreIn 2) :
    Nonempty (DihedralWitness T M (W.map f)) := by
  have hc (B : Subgroup (G × A)) [IsElementaryAbelian 2 B]
      (hB : B.map (MonoidHom.fst G A) ≠ ⊥)
      (hcard : Nat.card (B.map (MonoidHom.fst G A)) ≤ 2) :
      Nat.card (B.map (MonoidHom.fst G A)) = 2 := by
    let : IsElementaryAbelian 2 (B.map (MonoidHom.fst G A)) := IsElementaryAbelian.map _
    obtain h | h := two_or_four_of_elementary_ne_bot _ hB
    · exact h
    · omega
  rcases fst_ne_bot_or_snd_ne_bot W hW with h | h
  · obtain ⟨p,hp,hp2,w,a,ha,⟨e⟩⟩ :=
      PairedBender.exists_dihedral_product W (hc W h hfirst) hG T M f hf hVT hVM
    exact ⟨⟨w,p,hp,hp2,a,ha,e⟩⟩
  · let z : A × G ≃* G × A := MulEquiv.prodComm
    let W' := W.comap z.toMonoidHom
    let f' := f.comp z.toMonoidHom
    have hz : W'.map z.toMonoidHom = W := map_comap_eq_self_of_surjective z.surjective W
    let : IsElementaryAbelian 2 W' := IsElementaryAbelian.of_injective
      ((z.toMonoidHom.comp W'.subtype).codRestrict W (fun x => x.property))
      (by intro x y he; apply Subtype.ext; exact z.injective (congrArg Subtype.val he))
    have hproj : W'.map (MonoidHom.fst A G) = W.map (MonoidHom.snd G A) := by
      rw [← hz,map_map]
      rfl
    have hcard : Nat.card (W'.map (MonoidHom.fst A G)) = 2 := by
      rw [hproj]
      let : IsElementaryAbelian 2 (W.map (MonoidHom.snd G A)) := IsElementaryAbelian.map _
      obtain hh | hh := two_or_four_of_elementary_ne_bot _ h
      · exact hh
      · omega
    have hi : W'.map f' = W.map f := by rw [← map_map,hz]
    obtain ⟨p,hp,hp2,w,a,ha,⟨e⟩⟩ := PairedBender.exists_dihedral_product W' hcard hA
      T M f' (hf.comp z.injective) (by rwa [hi]) (by rwa [hi])
    have hw : Nonempty (DihedralWitness T M (W'.map f')) := ⟨⟨w,p,hp,hp2,a,ha,e⟩⟩
    rwa [hi] at hw

end CFSG.Quasithin.ChapterE.Witnesses.PairedOddLinearTwo
