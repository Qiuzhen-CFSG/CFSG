module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.LocalAlternating
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.DihedralCubicTail
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.ElementaryCubicTail
public import Theory.GroupTheory.DirectProduct.DihedralElementaryRemainder
public import Theory.ElementaryAbelian.PrimePlane


/-!
# Goldschmidt's two finite local classification lemmas

Under the original S3 core-quotient and characteristic obstruction hypotheses,
(2.14) gives an actual direct-product isomorphism with S3 times an elementary
group, or S4 times a power of D8 times an elementary group. The residual
producer reduces to C3 or A4; the two product constructions, maximal dihedral
splitting and elementary-remainder theorem discharge every intermediate input.

For the cubic Sylow automorphism in (2.15), the invariant elementary-subgroup
cube excludes the S4 alternative. The elementary factor then has order one,
two or four, giving the three explicit groups in the source conclusion.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), (2.14)--(2.15),
printed pp.384--386. These source lemmas supply the local arguments in (4.2),
(4.4) and (5.3); no model alternative is assumed by either final theorem.
-/

open Subgroup
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
variable {G H : Type*} [Group G] [Group H] [Finite G]

private theorem no_characteristic_normal_map (P : Sylow 2 G) (e : G ≃* H)
    (hP : ∀ K : Subgroup P, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (P : Subgroup G).subtype).Normal) :
    let P' := P.mapSurjective (f := e.toMonoidHom) e.surjective
    ∀ K : Subgroup P', K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (P' : Subgroup H).subtype).Normal := by
  let P' := P.mapSurjective (f := e.toMonoidHom) e.surjective
  let ep : P ≃* P' := (P : Subgroup G).equivMapOfInjective e.toMonoidHom e.injective
  change ∀ K : Subgroup P', K.Characteristic → K ≠ ⊥ →
    ¬ (K.map (P' : Subgroup H).subtype).Normal
  intro K hK hKne hKN
  let L := K.comap ep.toMonoidHom
  have hL : L.Characteristic := by
    apply characteristic_iff_le_comap.mpr
    intro a x hx
    have hh := characteristic_iff_le_comap.mp hK (MulAut.congr ep a) hx
    change ep.toMonoidHom (a x) ∈ K
    simpa [MulAut.congr] using hh
  have hLK : L.map ep.toMonoidHom = K := by
    rw [map_comap_eq, MonoidHom.range_eq_top.mpr ep.surjective, top_inf_eq]
  have hLn : L ≠ ⊥ := by
    intro hh
    apply hKne
    rw [← hLK, hh, Subgroup.map_bot]
  have hLN : (L.map (P : Subgroup G).subtype).Normal := by
    apply (MulEquiv.normal_map_iff (f := e)).mp
    have he : e.toMonoidHom.comp (P : Subgroup G).subtype =
        (P' : Subgroup H).subtype.comp ep.toMonoidHom := by
      apply MonoidHom.ext
      intro x
      rfl
    change ((L.map (P : Subgroup G).subtype).map e.toMonoidHom).Normal
    rw [map_map, he, ← map_map, hLK]
    exact hKN
  exact hP L hL hLn hLN

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt

public section
open Subgroup
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
variable {G : Type*} [Group G] [Finite G]

/-- Goldschmidt (2.14), with the elementary factor retained as an actual ambient subgroup. -/
theorem goldschmidt_2_14
    (e : (G ⧸ pCore 2 G) ≃* Equiv.Perm (Fin 3)) (P : Sylow 2 G)
    (hP : ∀ K : Subgroup P, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (P : Subgroup G).subtype).Normal) :
    ∃ E : Subgroup G, IsElementaryAbelian 2 E ∧
      (Nonempty (G ≃* Equiv.Perm (Fin 3) × E) ∨
        ∃ n : ℕ, Nonempty (G ≃* Equiv.Perm (Fin 4) × ((Fin n → DihedralGroup 4) × E))) := by
  rcases local_residual_cubic_or_alternatingFour e P hP with hc | ha
  · obtain ⟨eR⟩ := hc
    have hcard : Nat.card (pResidual 2 G) = 3 := by
      rw [Nat.card_congr eR.toEquiv]
      simp
    obtain ⟨hE, he⟩ := local_product_of_cubic e P hP hcard
    exact ⟨pCore 2 G, hE, Or.inl he⟩
  · obtain ⟨eR⟩ := ha
    let B := pCore 2 G ⊓ centralizer ((pResidual 2 G : Subgroup G) : Set G)
    obtain ⟨eG⟩ := local_product_of_alternating e P hP eR
    let P' := P.mapSurjective (f := eG.toMonoidHom) eG.surjective
    have hP' := no_characteristic_normal_map P eG hP
    have hB : IsPGroup 2 B := pCore_isPGroup.of_injective
      (inclusion (show B ≤ pCore 2 G from inf_le_left)) (inclusion_injective _)
    obtain ⟨n, A, ⟨eB⟩, hA⟩ :=
      Theory.GroupTheory.DihedralFactorExtraction.symmetricFour_exists_elementary_remainder
        B hB P' hP'
    let := hA
    let E := A.map B.subtype
    let eA : A ≃* E := A.equivMapOfInjective B.subtype B.subtype_injective
    have hE : IsElementaryAbelian 2 E :=
      IsElementaryAbelian.of_injective eA.symm.toMonoidHom eA.symm.injective
    refine ⟨E, hE, Or.inr ⟨n, ⟨?_⟩⟩⟩
    exact eG.trans (MulEquiv.prodCongr (MulEquiv.refl _) (eB.trans
      (MulEquiv.prodCongr (MulEquiv.refl _) eA)))

private theorem elementary_product_of_cube
    (e : (G ⧸ pCore 2 G) ≃* Equiv.Perm (Fin 3)) (P : Sylow 2 G)
    (a : MulAut P) (ha : a ^ 3 = 1)
    (hno : ∀ K : Subgroup P, K.map a.toMonoidHom = K →
      (K.map (P : Subgroup G).subtype).Normal → K = ⊥) :
    ∃ E : Subgroup G, IsElementaryAbelian 2 E ∧
      Nonempty (G ≃* Equiv.Perm (Fin 3) × E) := by
  have hP : ∀ K : Subgroup P, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (P : Subgroup G).subtype).Normal := by
    intro K hK hKne hn
    exact hKne (hno K (characteristic_iff_map_eq.mp hK a) hn)
  obtain ⟨E, hE, hmodel⟩ := goldschmidt_2_14 e P hP
  let := hE
  rcases hmodel with he | hd
  · exact ⟨E, hE, he⟩
  · obtain ⟨n, ⟨eG⟩⟩ := hd
    exact (DihedralCubicTail.exclude_model P eG a ha hno).elim

/-- The local classification needs only the cube relation, including the
possibly trivial induced automorphism used in Goldschmidt (5.3). -/
theorem goldschmidt_2_15_of_cube
    (e : (G ⧸ pCore 2 G) ≃* Equiv.Perm (Fin 3)) (P : Sylow 2 G)
    (a : MulAut P) (ha : a ^ 3 = 1)
    (hno : ∀ K : Subgroup P, K.map a.toMonoidHom = K →
      (K.map (P : Subgroup G).subtype).Normal → K = ⊥) :
    Nonempty (G ≃* Equiv.Perm (Fin 3)) ∨
      Nonempty (G ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 3)) ∨
      Nonempty (G ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) ×
        Equiv.Perm (Fin 3)) := by
  obtain ⟨E, hE, ⟨eG⟩⟩ := elementary_product_of_cube e P a ha hno
  let := hE
  rcases elementary_product_cubic_card_cases P eG a ha hno with h1 | h2 | h4
  · let : Subsingleton E := (Nat.card_eq_one_iff_unique.mp h1).1
    let : Unique E := { default := 1, uniq := fun x => Subsingleton.elim x 1 }
    exact Or.inl ⟨eG.trans (MulEquiv.prodComm.trans MulEquiv.uniqueProd)⟩
  · let eE : E ≃* Multiplicative (ZMod 2) := mulEquivOfPrimeCardEq h2 (by simp)
    exact Or.inr (Or.inl ⟨eG.trans (MulEquiv.prodComm.trans
      (MulEquiv.prodCongr eE (MulEquiv.refl _)))⟩)
  · obtain ⟨eE⟩ := IsElementaryAbelian.nonempty_mulEquiv_plane_of_card
      (G := E) (p := 2) (by simpa using h4)
    exact Or.inr (Or.inr ⟨eG.trans (MulEquiv.prodComm.trans
      (MulEquiv.prodCongr eE (MulEquiv.refl _)))⟩)

/-- Goldschmidt (2.15), with the literal nontrivial-automorphism hypothesis. -/
theorem goldschmidt_2_15
    (e : (G ⧸ pCore 2 G) ≃* Equiv.Perm (Fin 3)) (P : Sylow 2 G)
    (a : MulAut P) (ha : a ^ 3 = 1) (_ha_ne : a ≠ 1)
    (hno : ∀ K : Subgroup P, K.map a.toMonoidHom = K →
      (K.map (P : Subgroup G).subtype).Normal → K = ⊥) :
    Nonempty (G ≃* Equiv.Perm (Fin 3)) ∨
      Nonempty (G ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 3)) ∨
      Nonempty (G ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) ×
        Equiv.Perm (Fin 3)) :=
  goldschmidt_2_15_of_cube e P a ha hno

private theorem normal_three_of_elementary_product
    {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (eG : G ≃* Equiv.Perm (Fin 3) × E) (S : Sylow 3 G) : S.Normal := by
  let N : Subgroup (Equiv.Perm (Fin 3) × E) := (alternatingGroup (Fin 3)).prod ⊥
  have hNc : Nat.card N = 3 := by
    rw [Nat.card_congr (prodEquiv (alternatingGroup (Fin 3)) (⊥ : Subgroup E)).toEquiv,
      Nat.card_prod, card_bot, mul_one, nat_card_alternatingGroup, Nat.card_fin]
    rfl
  have hNp : IsPGroup 3 N := IsPGroup.of_card (n := 1) (by simpa using hNc)
  have hNi : N.index = 2 * Nat.card E := by simp [N, Subgroup.index_prod]
  have hn3 : ¬ 3 ∣ N.index := by
    obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 E).exists_card_eq
    rw [hNi, hn]
    intro hd
    have hh : 3 ∣ 2 := Nat.prime_three.dvd_of_dvd_pow
      (n := n + 1) (by simpa only [pow_succ, Nat.mul_comm] using hd)
    norm_num at hh
  let T := hNp.toSylow hn3
  let S' := S.mapSurjective (f := eG.toMonoidHom) eG.surjective
  have hS : (S' : Subgroup (Equiv.Perm (Fin 3) × E)) = N :=
    T.is_maximal' S'.isPGroup' (hNp.le_sylow_of_normal S')
  have hSN : S'.Normal := hS.symm ▸ inferInstance
  exact (MulEquiv.normal_map_iff (f := eG)).mp hSN

/-- The precise consequence needed in Goldschmidt (5.3): the induced
Sylow automorphism may be trivial, and every original Sylow three is normal. -/
theorem goldschmidt_2_15_normal_sylow_three
    (e : (G ⧸ pCore 2 G) ≃* Equiv.Perm (Fin 3)) (P : Sylow 2 G)
    (a : MulAut P) (ha : a ^ 3 = 1)
    (hno : ∀ K : Subgroup P, K.map a.toMonoidHom = K →
      (K.map (P : Subgroup G).subtype).Normal → K = ⊥) :
    ∀ S : Sylow 3 G, S.Normal := by
  obtain ⟨E, hE, ⟨eG⟩⟩ := elementary_product_of_cube e P a ha hno
  let := hE
  exact normal_three_of_elementary_product eG

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
