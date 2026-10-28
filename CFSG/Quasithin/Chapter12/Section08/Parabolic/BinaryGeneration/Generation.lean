module

public import CFSG.Quasithin.Chapter12.Section08.Parabolic.BinaryGeneration.UAction
public import CFSG.Quasithin.Chapter12.Section08.Parabolic.BinaryModule.IntersectionCommutator
public import Theory.GroupTheory.SymmetricThreeGeneration
public import Theory.GroupTheory.LocalNormalizerUniqueness

/-!
# Generation by the two original U-conjugates

The nontrivial U-image has order two. Its original g-conjugate has a
 distinct fixed point, so the two images generate S₃. The plane kernel
 lies in H and normalizes both U and Uᵍ. Their join is consequently
 P-normal and equals the defining span I₂. No replacement of g inside I₂
 is required, and equality after adjoining T is never cancelled.

Source: Aschbacher–Smith, Lemma 12.8.9(1), printed pp.852–853.
-/

public section

open Subgroup
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter12.Section08.InvariantFlag
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {V : Subgroup G} {n : ℕ}

private theorem commuting_involutions_three : ∀ a b : Equiv.Perm (Fin 3),
    a ≠ 1 → a ^ 2 = 1 → b ^ 2 = 1 → a*b=b*a → b=1 ∨ b=a := by decide +kernel

private theorem two_subgroups_generate_three (A B : Subgroup (Equiv.Perm (Fin 3)))
    (hA : Nat.card A = 2) (hB : Nat.card B = 2) (hne : A ≠ B) : A ⊔ B = ⊤ := by
  apply sup_eq_top_of_symmetricThree_commutator_ne_bot
  intro hh
  have hAb : A ≠ ⊥ := by intro he; simp [he] at hA
  obtain ⟨a, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hAb
  have ha := a.property
  have ha1' : (a : Equiv.Perm (Fin 3)) ≠ 1 := fun h => ha1 (Subtype.ext h)
  have hcent := commutator_eq_bot_iff_le_centralizer.mp hh
  have hBA : B ≤ A := by
    intro b hb
    have hap : (a : Equiv.Perm (Fin 3)) ^ 2 = 1 := by
      simpa only [map_pow, map_one, hA, Subgroup.subtype_apply] using congrArg A.subtype (pow_card_eq_one' (x := a))
    have hbp : b ^ 2 = 1 := by
      simpa only [map_pow, map_one, hB, Subgroup.subtype_apply] using congrArg B.subtype (pow_card_eq_one' (x := (⟨b,hb⟩ : B)))
    rcases commuting_involutions_three a b ha1' hap hbp ((hcent ha) b hb).symm with rfl | rfl
    · exact A.one_mem
    · exact ha
  exact hne (eq_of_le_of_card_ge hBA (by rw [hA,hB])).symm


omit [Finite G] in
private theorem map_binary_conjugate {D : Type*} [Group D] (f : G →* D)
    (A : Subgroup G) (g : G) :
    (conjugate A g).map f = conjugate (A.map f) (f g) := by
  unfold conjugate
  rw [map_map, map_map]
  congr 1
  ext x
  simp

/-- The original displaced U and its conjugate generate I₂ and cover P
modulo its two-core. -/
theorem binary_two_conjugate_generation (F : InvariantFlag T V n)
    [IsElementaryAbelian 2 V] (hn : 2 ≤ n) (L : Subgroup G)
    (hL : L ≤ normalizer (V : Set G))
    (hfull : Function.Surjective (F.binarySeedAction L hL))
    (hcore : (L ⊔ (T : Subgroup G)) ⊓ centralizer (V : Set G) =
      (L ⊔ (T : Subgroup G)).pCoreIn 2)
    (hsquare : ∀ u ∈ F.U, u ^ 2 ∈ F.Vi 1)
    (hspan : F.U = conjugateSpanBy (F.Vi 2) F.H) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    F.U ⊔ conjugate F.U g = F.I₂ L ∧ F.P L = (F.P L).pCoreIn 2 ⊔ F.I₂ L := by
  let P := F.P L
  let K := P.pCoreIn 2
  let J := F.U ⊔ conjugate F.U g
  let f := F.binaryPermutationAction hn L hL
  let A := F.U.subgroupOf P
  let gp : P := ⟨g,hgP⟩
  let B := conjugate A gp
  have hUP : F.U ≤ P := F.binary_U_le_P (by omega) L hsquare
  have hAmap : A.map P.subtype = F.U := map_subgroupOf_eq_of_le hUP
  have hBmap : B.map P.subtype = conjugate F.U g := by
    change (conjugate A gp).map P.subtype = _
    rw [map_binary_conjugate, hAmap]; rfl
  have hk : f.ker = pCore 2 P := (F.binaryPermutationAction_ker hn L hL).trans
    (F.binaryPlaneAction_ker_eq_twoCore hn L hL hfull hcore)
  have hkmap : f.ker.map P.subtype = K := by rw [hk]; rfl
  obtain ⟨hKC,hKH⟩ := F.binary_parabolic_core hn L hL hfull hcore
  have hUW : F.U ⊓ K = F.W := by
    rw [show K = P ⊓ centralizer (F.Vi 2 : Set G) from hKC.symm,
      ← inf_assoc, inf_eq_left.mpr hUP]
    rfl
  have hcardA : Nat.card (A.map f) = 2 := by
    rw [← relIndex_ker]
    have he := relIndex_map_map_of_injective f.ker A P.subtype_injective
    rw [hkmap,hAmap, ← inf_relIndex_left, hUW] at he
    rw [← he]
    exact F.binary_U_action_index hn L hL hsquare hspan hne
  have hcardB : Nat.card (B.map f) = 2 := by
    change Nat.card ((conjugate A gp).map f) = 2
    rw [map_binary_conjugate, conjugate,
      card_map_of_injective (MulAut.conj (f gp)⁻¹).injective, hcardA]
  have hdiff : A.map f ≠ B.map f := by
    intro he
    have hh := congrArg (fun C : Subgroup (Equiv.Perm (Fin 3)) => (C.comap f).map P.subtype) he
    simp only [comap_map_eq, Subgroup.map_sup, hAmap, hBmap, hkmap] at hh
    have hUc : F.U ≤ centralizer (F.Vi 1 : Set G) := F.U_le_H.trans
      (normalizer_le_centralizer_of_card_two _ (by simpa using F.card 1 (by omega)))
    have hUgc : conjugate F.U g ≤ centralizer (conjugate (F.Vi 1) g : Set G) :=
      (map_mono hUc).trans (map_centralizer_le_centralizer_image _ _)
    have hKc : K ≤ centralizer (conjugate (F.Vi 1) g : Set G) :=
      hKC.ge.trans inf_le_right |>.trans (centralizer_le
        (conjugate_le_of_normalizes (F.monotone (by omega)) g (F.P_le_G₂ hn L hL hgP)))
    have hUgfix : F.U ≤ centralizer (conjugate (F.Vi 1) g : Set G) :=
      (le_sup_left.trans hh.le).trans (sup_le hUgc hKc)
    apply F.binary_U_not_centralizes_plane hspan hne
    apply le_centralizer_iff.mpr
    rw [← F.binary_plane_point_span hn L hL g hgP hgH]
    exact sup_le (le_centralizer_iff.mp hUc) (le_centralizer_iff.mp hUgfix)
  have htop : (A ⊔ B).map f = ⊤ := by
    rw [Subgroup.map_sup]
    exact two_subgroups_generate_three _ _ hcardA hcardB hdiff
  have hcover : P = K ⊔ J := by
    have hh := congrArg (fun C : Subgroup (Equiv.Perm (Fin 3)) => (C.comap f).map P.subtype) htop
    rw [comap_map_eq, comap_top] at hh
    simp only [Subgroup.map_sup, hAmap,hBmap,hkmap,
      ← MonoidHom.range_eq_map, range_subtype] at hh
    exact hh.symm.trans (sup_comm _ _)
  have hKN : P ≤ normalizer (K : Set G) := P.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image P (pCore 2 P))
  have hKU : K ≤ normalizer (F.U : Set G) := hKH.trans (le_normalizer_conjugateSpanBy V F.H)
  have hKUg : K ≤ normalizer (conjugate F.U g : Set G) := by
    have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hKU
    rw [map_equiv_normalizer_eq] at hh
    change conjugate K g ≤ normalizer (conjugate F.U g : Set G) at hh
    rwa [(conjugate_eq_iff K g).mpr (hKN hgP)] at hh
  have hKJ : K ≤ normalizer (J : Set G) := (le_inf hKU hKUg).trans
    (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hPJ : P ≤ normalizer (J : Set G) := by
    rw [hcover]
    exact sup_le hKJ J.le_normalizer
  have hJI : J = F.I₂ L := le_antisymm (F.U_sup_conjugate_le_I₂ L g hgP)
    (conjugateSpanBy_le le_sup_left hPJ)
  exact ⟨hJI, hcover.trans (congrArg (K ⊔ ·) hJI)⟩

end CFSG.Quasithin.Chapter12.Section08.InvariantFlag
