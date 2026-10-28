module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Decomposable.PrimeResidual
public import Theory.GroupTheory.SymmetricThreeImage
public import Theory.GroupTheory.CyclicHallNormalizerEscape
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Maximality of the actual cubic decomposable Sylow image

Two commuting symmetric-three factors exchanged by the ambient group have
only two-group images in a degree-three permutation action. If one factor
survived as a full symmetric-three image, its commuting conjugate would lie
in its trivial center, contradicting conjugacy. Together with the actual
Sylow supplement this excludes index-three subgroups.

In the original prime-three decomposable action the two-residual lies in
the literal factor product, so the Sylow index divides nine. Thus the
original Sylow image is maximal, without any global Thompson residual
premise. The two original four-dimensional supports are retained.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open ChapterD ChapterD.UniqueFactor ChapterD.RatioDecomposition Section03 Section03.InitialSource ChapterA.Section05To06

private theorem symmetricThree_image_two_of_commuting_conjugate
    {D : Type*} [Group D] [Finite D] (L R : Subgroup D)
    (e : L ≃* Equiv.Perm (Fin 3))
    (hc : ∀ x ∈ L, ∀ y ∈ R, Commute x y)
    (t : D) (ht : L.map (MulAut.conj t).toMonoidHom = R)
    (f : D →* Equiv.Perm (Fin 3)) : IsPGroup 2 (L.map f) := by
  let a := f.comp L.subtype
  have hr : a.range = L.map f := by rw [MonoidHom.range_comp,L.range_subtype]
  by_contra hn
  obtain ⟨j⟩ := symmetricThree_image_of_not_isPGroup e a (hr ▸ hn)
  have ha : a.range = ⊤ := eq_of_le_of_card_ge le_top (by
    rw [Nat.card_congr j.toEquiv,card_top])
  have hR : R ≤ f.ker := by
    intro y hy
    change f y = 1
    apply NormalSymmetricThreePairRank.symmetricThree_center_trivial
    intro z
    obtain ⟨x,hx⟩ : ∃ x : L, a x = z := by
      have hz : z ∈ a.range := ha ▸ mem_top z
      exact hz
    change f (x : D) = z at hx
    simpa only [map_mul,hx] using congrArg f (hc x x.property y hy).eq
  have hL : L ≤ f.ker := by
    intro x hx
    have hy : t*x*t⁻¹ ∈ R := ht ▸ mem_map_of_mem (MulAut.conj t).toMonoidHom hx
    have hh := hR hy
    change f (t*x*t⁻¹) = 1 at hh
    rw [map_mul,map_mul,map_inv] at hh
    change f x = 1
    exact mul_left_cancel (a := f t) (by
      simpa only [mul_assoc,inv_mul_cancel,mul_one,one_mul] using congrArg (fun z => z * f t) hh)
  exact hn (by rw [(map_eq_bot_iff L).mpr hL]; exact IsPGroup.of_bot)

private theorem no_index_three_of_swapped_symmetricThree_supplement
    {D : Type*} [Group D] [Finite D] (L R : Subgroup D)
    (eL : L ≃* Equiv.Perm (Fin 3)) (eR : R ≃* Equiv.Perm (Fin 3))
    (hc : ∀ x ∈ L, ∀ y ∈ R, Commute x y)
    (t : D) (ht : L.map (MulAut.conj t).toMonoidHom = R)
    (ht' : R.map (MulAut.conj t).toMonoidHom = L)
    (S : Sylow 2 D) (hs : (L ⊔ R) ⊔ (S : Subgroup D) = ⊤)
    (hn : (L ⊔ R).Normal) (A : Subgroup D) : A.index ≠ 3 := by
  classical
  intro hA
  let e := Equiv.permCongrHom (Finite.equivFinOfCardEq
    (show Nat.card (D ⧸ A) = 3 by rw [←A.index_eq_card,hA]))
  let f : D →* Equiv.Perm (Fin 3) := e.toMonoidHom.comp (MulAction.toPermHom D (D ⧸ A))
  have hL := symmetricThree_image_two_of_commuting_conjugate L R eL hc t ht f
  have hR := symmetricThree_image_two_of_commuting_conjugate R L eR
    (fun y hy x hx => (hc x hx y hy).symm) t ht' f
  have hLR : L.map f ≤ normalizer (R.map f : Set (Equiv.Perm (Fin 3))) := by
    apply le_normalizer_iff.mpr
    rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩
    rw [←map_inv,←map_mul,←map_mul,(hc x hx y hy).eq,mul_inv_cancel_right]
    exact mem_map_of_mem f hy
  have hH : IsPGroup 2 ((L ⊔ R).map f) := by
    rw [Subgroup.map_sup]
    exact hL.to_sup_of_normal_right' hR hLR
  have hS : (S : Subgroup D).map f ≤ normalizer ((L ⊔ R).map f : Set _) :=
    (map_mono (show (S : Subgroup D) ≤ normalizer (L ⊔ R : Subgroup D) from
      @le_normalizer_of_normal _ _ _ _ hn)).trans (le_normalizer_map f)
  have hP : IsPGroup 2 f.range := by
    rw [MonoidHom.range_eq_map,←hs,Subgroup.map_sup]
    exact hH.to_sup_of_normal_left' (S.isPGroup'.map f) hS
  have hk : f.ker ≤ A := by
    intro x hx
    apply A.normalCore_le
    rw [A.normalCore_eq_ker]
    apply e.injective
    exact (show f x = 1 from hx).trans e.map_one.symm
  have hd : 3 ∣ Nat.card f.range := by
    rw [←index_ker]
    simpa only [hA] using index_dvd_of_le hk
  obtain ⟨n,hn⟩ := hP.exists_card_eq
  rw [hn] at hd
  exact (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd)

/-- The literal Sylow image in the prime-three decomposable source is
maximal. The argument uses its original exchanged factors and their
proved residual supplement, not global 15.1.14. -/
theorem DecomposableMarker.ThompsonPair.sylow_image_isCoatom_of_prime_three
    {G : Type*} [Group G] [Finite G]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M V : Subgroup G} [IsElementaryAbelian 2 V]
    (hM : IsOrderingMaximal T M) (hn : M ≤ normalizer (V : Set G))
    {U : Submodule (ZMod 2) (Additive V)}
    (c : FactorData (imageRepresentation M V hn) (Jhat (imageRepresentation M V hn)) U)
    (d : Decomposition c.representation) (s : DecomposableMarker.ThompsonPair (T := T) hn c d)
    (π : internalActionImage M V hn →* Equiv.Perm d.Index)
    (hp : ∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
      (c.ambientFactor d (π g k)).actor)
    (hs : ∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V hn g) =
      (c.ambientFactor d (π g k)).space)
    (hdec : SourceCases.Decomposable (imageRepresentation M V hn) (T : Subgroup G) M
      (actionHom M V hn).rangeRestrict c d π)
    (hthree : s.prime = 3) :
    IsCoatom (((T : Subgroup G).subgroupOf M).map (actionHom M V hn).rangeRestrict) := by
  let D := internalActionImage M V hn
  let ρ := imageRepresentation M V hn
  let f := (actionHom M V hn).rangeRestrict
  let S : Sylow 2 D := (T.subtype hM.1.2).mapSurjective (actionHom M V hn).rangeRestrict_surjective
  obtain ⟨_,_,_,_,_,i,j,_,_,hgen,hdis,hcom,_,t,ht,htij,htji⟩ := hdec
  let L := (c.ambientFactor d i).actor
  let R := (c.ambientFactor d j).actor
  have emark (k : d.Index) : (c.ambientFactor d k).actor ≃* Equiv.Perm (Fin 3) := by
    have hmark := (s.dihedral k).dihedral
    rw [hthree] at hmark
    exact (MonoidHom.ofInjective (c.ambientFactor d k).embedding.group_injective).symm.trans
      (hmark.some.trans nonempty_dihedralThreeEquivPerm.some)
  have hnormal : (L ⊔ R).Normal := by rw [hgen]; exact Jhat_normal ρ
  have hres := s.image_residual_le_core_of_prime_three hG T hM hn c d π hp hs hthree
  have hwhole : (L ⊔ R) ⊔ (S : Subgroup D) = ⊤ := by
    apply top_unique
    rw [←pResidual_sup_sylow_eq_top S]
    exact sup_le_sup (hgen ▸ hres) le_rfl
  have hswap : L.map (MulAut.conj (f t)).toMonoidHom = R := (hp (f t) i).trans (congrArg (fun k : d.Index => (c.ambientFactor d k).actor) htij)
  have hswap' : R.map (MulAut.conj (f t)).toMonoidHom = L := (hp (f t) j).trans (congrArg (fun k : d.Index => (c.ambientFactor d k).actor) htji)
  have hno := no_index_three_of_swapped_symmetricThree_supplement L R
    (emark i) (emark j) hcom (f t) hswap hswap' S hwhole hnormal
  have hcard : Nat.card (L ⊔ R : Subgroup D) = 36 := by
    rw [card_sup_eq_mul_of_normalizes_of_disjoint L R (by
      apply le_normalizer_iff.mpr
      intro r hr l hl
      rw [(hcom l hl r hr).symm.eq,mul_inv_cancel_right]
      exact hl) hdis,Nat.card_congr (emark i).toEquiv,Nat.card_congr (emark j).toEquiv]
    norm_num [Nat.card_eq_fintype_card,Fintype.card_perm]
  let := hnormal
  have hi36 : (S : Subgroup D).index ∣ 36 := hcard ▸ index_dvd_of_normal_supplement (L ⊔ R) S hwhole
  have hi9 : (S : Subgroup D).index ∣ 3^2 := by
    have hc : Nat.Coprime (S : Subgroup D).index 4 :=
      (Nat.prime_two.coprime_iff_not_dvd.mpr S.not_dvd_index).symm.pow_right 2
    exact hc.dvd_of_dvd_mul_left hi36
  have hne : (S : Subgroup D) ≠ ⊤ := by
    intro he
    have hpD : IsPGroup 2 D := S.isPGroup'.of_equiv
      ((MulEquiv.subgroupCongr he).trans topEquiv)
    have hpL := hpD.to_subgroup L
    have hL : Nat.card L = 6 := by rw [Nat.card_congr (emark i).toEquiv]; norm_num [Nat.card_eq_fintype_card,Fintype.card_perm]
    obtain ⟨n,hh⟩ := hpL.exists_card_eq
    rw [hL] at hh
    have hd : 3 ∣ 2^n := hh ▸ (by decide : 3 ∣ 6)
    exact (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd)
  change IsCoatom (S : Subgroup D)
  refine ⟨hne,?_⟩
  intro A hSA
  obtain ⟨n,hn,he⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp
    ((index_dvd_of_le hSA.le).trans hi9)
  interval_cases n
  · exact index_eq_one.mp (by simpa using he)
  · exact (hno A (by simpa using he)).elim
  · have hile : (S : Subgroup D).index ≤ 9 := Nat.le_of_dvd (by decide) hi9
    have hrel : (S : Subgroup D).relIndex A = 1 := by
      have hh := relIndex_mul_index hSA.le
      rw [he] at hh
      have hpos : 0 < (S : Subgroup D).relIndex A := Nat.pos_of_ne_zero (index_ne_zero_of_finite (H := (S : Subgroup D).subgroupOf A))
      norm_num only [Nat.reducePow] at hh
      omega
    exact (hSA.not_ge (relIndex_eq_one.mp hrel)).elim

end CFSG.Quasithin.Chapter15.Section01
