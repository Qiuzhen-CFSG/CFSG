module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Decomposable.Thompson
public import Theory.GroupTheory.InvolutionCentralizerControl

/-!
# Sylow overgroups in the original exchanged quintic factor product

Intersect an overgroup of the original Sylow image with the normal product
of the two original dihedral factors. Its intersections with the factors
have equal order by the original exchange. Each has order two or ten. If
they have order ten, the whole factor product is contained. Otherwise an
intersection of order twenty would supplement either factor to the full
product, making an order-two subgroup normal in a centerless dihedral
factor. Thus the intersection is precisely the original order-four Sylow
intersection and is normalized by the overgroup.

Extra actors outside the factor product, including an extra cubic subgroup,
are unrestricted. No maximality of the Sylow image, partner identification,
or global Thompson residual conclusion is asserted.

Source: Aschbacher--Smith 15.1.7(6), 15.1.13(4), printed pp.1087,1091.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01.DecomposableMarker
open ChapterD ChapterD.UniqueFactor ChapterD.RatioDecomposition
variable {G : Type*} [Group G] [Finite G]

private theorem sylow_intersection_card
    {D : Type*} [Group D] [Finite D] (S : Sylow 2 D)
    (L : Subgroup D) (hL : L.IsSubnormal) :
    Nat.card ((S : Subgroup D) ⊓ L : Subgroup D) =
      2 ^ Nat.factorization (Nat.card L) 2 := by
  obtain ⟨P,hP⟩ := S.exists_subgroupOf_eq_of_subnormal L hL
  have hh := P.card_eq_multiplicity
  rw [hP] at hh
  rw [←map_subgroupOf_eq_of_le (show (S : Subgroup D) ⊓ L ≤ L from inf_le_right)]
  simpa only [inf_subgroupOf_right,card_map_of_injective L.subtype_injective] using hh

private theorem no_normal_two_in_dihedral_five
    {D : Type*} [Group D] [Finite D] (L B : Subgroup D)
    (e : L ≃* DihedralGroup 5) (hBL : B ≤ L) (hB : Nat.card B = 2)
    (hn : L ≤ normalizer (B : Set D)) : False := by
  have hc : B ≤ centralizer (L : Set D) :=
    le_centralizer_iff.mp (hn.trans (normalizer_le_centralizer_of_card_two B hB))
  have hb : B = ⊥ := by
    apply bot_unique
    intro b hb
    have hz : (⟨b,hBL hb⟩ : L) ∈ center L := by
      apply mem_center_iff.mpr
      intro l
      exact Subtype.ext (hc hb l l.property)
    have he : e ⟨b,hBL hb⟩ ∈ center (DihedralGroup 5) :=
      (centerCongr e ⟨⟨b,hBL hb⟩,hz⟩).property
    rw [DihedralGroup.center_eq_bot_of_odd_ne_one (by decide) (by decide),mem_bot] at he
    exact congrArg Subtype.val (e.injective (he.trans e.map_one.symm))
  rw [hb,card_bot] at hB
  omega

private theorem even_subgroup_of_ten
    {D : Type*} [Group D] [Finite D] (H L : Subgroup D)
    (hHL : H ≤ L) (hL : Nat.card L = 10) (htwo : 2 ∣ Nat.card H) :
    Nat.card H = 2 ∨ Nat.card H = 10 := by
  have hd : Nat.card H ∣ 10 := hL ▸ card_dvd_of_le hHL
  have hh := Nat.mem_divisors.mpr ⟨hd,by decide⟩
  rw [show Nat.divisors 10 = {1,2,5,10} by decide] at hh
  simp only [Finset.mem_insert,Finset.mem_singleton] at hh
  rcases hh with hh | hh | hh | hh
  · rw [hh] at htwo; norm_num at htwo
  · exact Or.inl hh
  · rw [hh] at htwo; norm_num at htwo
  · exact Or.inr hh

private theorem intersection_eq_or_contains_of_swapped_dihedral_five
    {D : Type*} [Group D] [Finite D] (S : Sylow 2 D)
    (L R : Subgroup D) (eL : L ≃* DihedralGroup 5) (eR : R ≃* DihedralGroup 5)
    (hd : Disjoint L R) (hc : ∀ l ∈ L, ∀ r ∈ R, Commute l r)
    (hn : (L ⊔ R).Normal) (t : D) (ht : t ∈ (S : Subgroup D))
    (hswap : L.map (MulAut.conj t).toMonoidHom = R)
    (A : Subgroup D) (hSA : (S : Subgroup D) ≤ A) :
    A ⊓ (L ⊔ R) = (S : Subgroup D) ⊓ (L ⊔ R) ∨ L ⊔ R ≤ A := by
  let K := L ⊔ R
  let I := A ⊓ K
  let B := I ⊓ L
  let C := I ⊓ R
  have hKnorm : K.Normal := hn
  let := hKnorm
  have hRL : R ≤ normalizer (L : Set D) := by
    apply le_normalizer_iff.mpr
    intro r hr l hl
    rw [(hc l hl r hr).symm.eq,mul_inv_cancel_right]
    exact hl
  have hLR : L ≤ normalizer (R : Set D) := by
    apply le_normalizer_iff.mpr
    intro l hl r hr
    rw [(hc l hl r hr).eq,mul_inv_cancel_right]
    exact hr
  have hKL : K ≤ normalizer (L : Set D) := sup_le L.le_normalizer hRL
  have hKR : K ≤ normalizer (R : Set D) := sup_le hLR R.le_normalizer
  have hLn : (L.subgroupOf K).Normal := normal_subgroupOf_of_le_normalizer hKL
  have hLs : L.IsSubnormal :=
    Subgroup.IsSubnormal.trans le_sup_left hLn.isSubnormal hn.isSubnormal
  have hcL : Nat.card L = 10 := (Nat.card_congr eL.toEquiv).trans (by
    rw [DihedralGroup.nat_card])
  have hcR : Nat.card R = 10 := (Nat.card_congr eR.toEquiv).trans (by
    rw [DihedralGroup.nat_card])
  have hcK : Nat.card K = 100 := by
    rw [card_sup_eq_mul_of_normalizes_of_disjoint L R hRL hd,hcL,hcR]
  have hcSL : Nat.card ((S : Subgroup D) ⊓ L : Subgroup D) = 2 := by
    rw [sylow_intersection_card S L hLs,hcL]
    decide +kernel
  have hcSK : Nat.card ((S : Subgroup D) ⊓ K : Subgroup D) = 4 := by
    rw [sylow_intersection_card S K hn.isSubnormal,hcK]
    decide +kernel
  have hSB : (S : Subgroup D) ⊓ L ≤ B :=
    le_inf (le_inf (inf_le_left.trans hSA) (inf_le_right.trans le_sup_left)) inf_le_right
  have hfour : 4 ∣ Nat.card I := hcSK ▸ card_dvd_of_le (inf_le_inf_right K hSA)
  have htI : t ∈ normalizer (I : Set D) :=
    le_normalizer_inf A.le_normalizer (le_normalizer_of_normal (H := K)) (hSA ht)
  have hImap : I.map (MulAut.conj t).toMonoidHom = I :=
    mem_normalizer_iff_map_conj_eq.mp htI
  have hBC : B.map (MulAut.conj t).toMonoidHom = C := by
    change (I ⊓ L).map (MulAut.conj t).toMonoidHom = I ⊓ R
    rw [Subgroup.map_inf _ _ _ (MulAut.conj t).injective,hImap,hswap]
  have hBcC : Nat.card B = Nat.card C := by
    rw [←hBC,card_map_of_injective (MulAut.conj t).injective]
  have hBcases := even_subgroup_of_ten B L inf_le_right hcL
    (hcSL ▸ card_dvd_of_le hSB)
  rcases hBcases with hB | hB
  · have hC : Nat.card C = 2 := hBcC.symm.trans hB
    have hdiv : Nat.card I ∣ 100 := hcK ▸ card_dvd_of_le (show I ≤ K from inf_le_right)
    have hcards : Nat.card I = 4 ∨ Nat.card I = 20 ∨ Nat.card I = 100 := by
      have hh := Nat.mem_divisors.mpr ⟨hdiv,by decide⟩
      rw [show Nat.divisors 100 = {1,2,4,5,10,20,25,50,100} by decide] at hh
      simp only [Finset.mem_insert,Finset.mem_singleton] at hh
      rcases hh with hh | hh | hh | hh | hh | hh | hh | hh | hh
      all_goals omega
    rcases hcards with hI | hI | hI
    · left
      exact (eq_of_le_of_card_ge (inf_le_inf_right K hSA) (by rw [hcSK,hI])).symm
    · have hnorm : I ≤ normalizer (R : Set D) := inf_le_right.trans hKR
      have hprod := card_mul_eq_card_inf_mul_card_sup_of_normalizes R I hnorm
      have hmeet : Nat.card (R ⊓ I : Subgroup D) = 2 := by rw [inf_comm]; exact hC
      rw [hcR,hI,hmeet] at hprod
      have hjoin : I ⊔ R = K := by
        apply eq_of_le_of_card_ge (sup_le inf_le_right le_sup_right)
        change Nat.card K ≤ Nat.card (I ⊔ R : Subgroup D)
        rw [hcK]
        have hprod' : 10 * 20 = 2 * Nat.card (I ⊔ R : Subgroup D) := by
          simpa only [sup_comm] using hprod
        omega
      have hIB : I ≤ normalizer (B : Set D) :=
        le_normalizer_inf I.le_normalizer (inf_le_right.trans hKL)
      have hRB : R ≤ normalizer (B : Set D) := by
        apply (show R ≤ centralizer (B : Set D) from ?_).trans (Subgroup.centralizer_le_normalizer _)
        intro r hr b hb
        exact (hc b hb.2 r hr).eq
      have hLB : L ≤ normalizer (B : Set D) :=
        le_sup_left.trans (hjoin ▸ sup_le hIB hRB)
      exact (no_normal_two_in_dihedral_five L B eL inf_le_right hB hLB).elim
    · have hIK : I = K := eq_of_le_of_card_ge inf_le_right (by rw [hI,hcK])
      have hBL : B = L := by
        change I ⊓ L = L
        rw [hIK,inf_eq_right.mpr le_sup_left]
      rw [hBL,hcL] at hB
      omega
  · right
    have hBL : B = L := eq_of_le_of_card_ge inf_le_right (by rw [hB,hcL])
    have hCR : C = R := eq_of_le_of_card_ge inf_le_right (by rw [←hBcC,hB,hcR])
    exact sup_le (hBL ▸ (show B ≤ A from inf_le_left.trans inf_le_left))
      (hCR ▸ (show C ≤ A from inf_le_left.trans inf_le_left))

/-- An overgroup of the original Sylow image either contains the original
quintic factor product or meets it in precisely the original Sylow intersection. -/
theorem ThompsonPair.image_intersection_eq_or_contains_of_prime_five
    {T : Sylow 2 G} {M V : Subgroup G} [IsElementaryAbelian 2 V]
    (hTM : (T : Subgroup G) ≤ M) (hn : M ≤ normalizer (V : Set G))
    {U : Submodule (ZMod 2) (Additive V)}
    (c : FactorData (imageRepresentation M V hn) (Jhat (imageRepresentation M V hn)) U)
    (d : Decomposition c.representation) (s : ThompsonPair (T := T) hn c d)
    (π : internalActionImage M V hn →* Equiv.Perm d.Index)
    (hp : ∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
      (c.ambientFactor d (π g k)).actor)
    (hdec : SourceCases.Decomposable (imageRepresentation M V hn) (T : Subgroup G) M
      (actionHom M V hn).rangeRestrict c d π)
    (hfive : s.prime = 5)
    (A : Subgroup (internalActionImage M V hn))
    (hSA : ((T : Subgroup G).subgroupOf M).map (actionHom M V hn).rangeRestrict ≤ A) :
    A ⊓ Jhat (imageRepresentation M V hn) =
        ((T : Subgroup G).subgroupOf M).map (actionHom M V hn).rangeRestrict ⊓
          Jhat (imageRepresentation M V hn) ∨
      Jhat (imageRepresentation M V hn) ≤ A := by
  let D := internalActionImage M V hn
  let ρ := imageRepresentation M V hn
  let f := (actionHom M V hn).rangeRestrict
  let S : Sylow 2 D := (T.subtype hTM).mapSurjective (actionHom M V hn).rangeRestrict_surjective
  obtain ⟨_,_,_,_,_,i,j,_,_,hgen,hdis,hcom,_,t,ht,htij,_⟩ := hdec
  let L := (c.ambientFactor d i).actor
  let R := (c.ambientFactor d j).actor
  have emark (k : d.Index) : (c.ambientFactor d k).actor ≃* DihedralGroup 5 := by
    have hm := (s.dihedral k).dihedral
    rw [hfive] at hm
    exact (MonoidHom.ofInjective (c.ambientFactor d k).embedding.group_injective).symm.trans hm.some
  have hnormal : (L ⊔ R).Normal := by rw [hgen]; exact Jhat_normal ρ
  have hswap : L.map (MulAut.conj (f t)).toMonoidHom = R :=
    (hp (f t) i).trans (congrArg (fun k => (c.ambientFactor d k).actor) htij)
  have hh := intersection_eq_or_contains_of_swapped_dihedral_five S L R
    (emark i) (emark j) hdis hcom hnormal (f t) (mem_map_of_mem f ht) hswap A hSA
  rwa [hgen] at hh

/-- The surviving Sylow-overgroup intersection normalizes the literal
original Thompson image, allowing arbitrary actors outside J-hat. -/
theorem ThompsonPair.image_contains_or_normalizes_of_prime_five
    {T : Sylow 2 G} {M V : Subgroup G} [IsElementaryAbelian 2 V]
    (hTM : (T : Subgroup G) ≤ M) (hn : M ≤ normalizer (V : Set G))
    {U : Submodule (ZMod 2) (Additive V)}
    (c : FactorData (imageRepresentation M V hn) (Jhat (imageRepresentation M V hn)) U)
    (d : Decomposition c.representation) (s : ThompsonPair (T := T) hn c d)
    (π : internalActionImage M V hn →* Equiv.Perm d.Index)
    (hp : ∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
      (c.ambientFactor d (π g k)).actor)
    (hdec : SourceCases.Decomposable (imageRepresentation M V hn) (T : Subgroup G) M
      (actionHom M V hn).rangeRestrict c d π)
    (hfive : s.prime = 5)
    (A : Subgroup (internalActionImage M V hn))
    (hSA : ((T : Subgroup G).subgroupOf M).map (actionHom M V hn).rangeRestrict ≤ A) :
    Jhat (imageRepresentation M V hn) ≤ A ∨
      A ≤ normalizer (((((T : Subgroup G).subgroupOf M).map
        (actionHom M V hn).rangeRestrict ⊓ Jhat (imageRepresentation M V hn)) :
          Subgroup (internalActionImage M V hn)) : Set (internalActionImage M V hn)) := by
  rcases s.image_intersection_eq_or_contains_of_prime_five hTM hn c d π hp hdec hfive A hSA
    with he | hle
  · right
    let := Jhat_normal (imageRepresentation M V hn)
    have hnorm : A ≤ normalizer ((A ⊓ Jhat (imageRepresentation M V hn)) :
        Set (internalActionImage M V hn)) :=
      le_normalizer_inf A.le_normalizer le_normalizer_of_normal
    exact he ▸ hnorm
  · exact Or.inl hle

end CFSG.Quasithin.Chapter15.Section01.DecomposableMarker
