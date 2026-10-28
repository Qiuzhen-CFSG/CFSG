module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Diagonal.MaximalOvergroups.Intersection
public import GorensteinWalter.PGL2KleinFourSelfCentralizer
public import GorensteinWalter.KleinFourMapInjective
public import GorensteinWalter.A5
public import GorensteinWalter.AutAlternatingFour
public import GorensteinWalter.PGammaL2NormalExtension

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Diagonal.OvergroupModels
public import Theory.SpecificGroups.ProjectiveLinear.OrderFiveConjugacy

/-!
# Exceptional inner intersections in prime-field PGL₂

An embedded Klein four-group is self-centralizing in odd PGL₂. Thus each
centerless exceptional intersection is self-centralizing, and conjugation
acts faithfully. An A₄ intersection gives the full S₄ extension. An S₄
intersection has a characteristic A₄ subgroup and is incompatible with the
same faithful-action bound. An A₅ intersection would give S₅, whose actual
five-cycle normalizer induces squaring, excluded by the projective matrix
calculation in `OrderFiveConjugacy`.

This discharges the exceptional branch of the Dickson auxiliary calculation
for Aschbacher--Smith E.1.14(6), printed p.214, citing Aschbacher (1982),
Lemma 4.10. The canonical intersection, its relative normality and index two
are exactly those in `MaximalOvergroups.Intersection`. Maximality is not
needed for the branch calculations; it is retained in the consumer API.
-/

noncomputable section
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Diagonal.MaximalOvergroups
open Subgroup GorensteinWalter
variable {F : Type*} [Field F] [Finite F]

private theorem centralizer_eq_bot_of_kleinFour
    (hF : IsOddPrimePower (Nat.card F))
    {G : Type*} [Group G] (f : G →* PGL2 F) (hf : Function.Injective f)
    (H : Subgroup G) (V : Subgroup H) (hV : IsKleinFour V)
    (hZH : center H = ⊥) : centralizer (H : Set G) = ⊥ := by
  let j : H →* PGL2 F := f.comp H.subtype
  have hj : Function.Injective j := hf.comp H.subtype_injective
  have hC := pgl2_kleinFour_centralizer_eq_self F hF (V.map j)
    (isKleinFour_map_of_injective V hV j hj)
  apply le_bot_iff.mp
  intro x hx
  have hfx : f x ∈ centralizer (V.map j : Set (PGL2 F)) := by
    rw [mem_centralizer_iff]
    rintro _ ⟨v, hv, rfl⟩
    simpa only [j, MonoidHom.comp_apply, Subgroup.subtype_apply, map_mul] using
      congrArg f ((mem_centralizer_iff.mp hx) v v.property)
  rw [hC] at hfx
  obtain ⟨v, _hv, he⟩ := hfx
  have hvx : v.val = x := hf he
  have hxH : x ∈ H := hvx ▸ v.property
  have hxZ : (⟨x, hxH⟩ : H) ∈ center H := by
    rw [mem_center_iff]
    intro y
    exact Subtype.ext ((mem_centralizer_iff.mp hx) y y.property)
  rw [hZH] at hxZ
  exact mem_bot.mpr (congrArg Subtype.val (mem_bot.mp hxZ))

private theorem a4_normal_embedding_perm_four
    (hF : IsOddPrimePower (Nat.card F))
    {G : Type*} [Group G] (f : G →* PGL2 F) (hf : Function.Injective f)
    (H : Subgroup G) [H.Normal] (e : H ≃* alternatingGroup (Fin 4)) :
    ∃ j : G →* Equiv.Perm (Fin 4), Function.Injective j := by
  let V := (alternatingGroup.kleinFour (Fin 4)).map e.symm.toMonoidHom
  have hV : IsKleinFour V := isKleinFour_map_of_injective _
    (alternatingGroup.kleinFour_isKleinFour (by simp)) _ e.symm.injective
  have hZ : center H = ⊥ := center_eq_bot_of_mulEquiv e
    (alternatingGroup.center_eq_bot (by simp))
  have hC := centralizer_eq_bot_of_kleinFour hF f hf H V hV hZ
  let a : Equiv.Perm (Fin 4) ≃* MulAut (alternatingGroup (Fin 4)) :=
    MulEquiv.ofBijective _ GroupTheory.AutAlternating.aut_alternatingGroup_four_bijective_conj
  let j : G →* Equiv.Perm (Fin 4) := a.symm.toMonoidHom.comp
    ((MulAut.congr e).toMonoidHom.comp (MulAut.conjNormal (H := H)))
  exact ⟨j, a.symm.injective.comp ((MulAut.congr e).injective.comp
    (conjNormal_injective_of_centralizer_eq_bot H hC))⟩

private instance finitePGL : Finite (PGL2 F) :=
  Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective

/-- The literal A₄ intersection extends to the whole S₄ overgroup. -/
public theorem symmetric_four_of_inner_alternating_four
    (hF : IsOddPrimePower (Nat.card F))
    (T : Sylow 2 (PGL2 F)) (M : Subgroup (PGL2 F)) (hTM : (T : Subgroup _) ≤ M)
    (e : inner M ≃* alternatingGroup (Fin 4)) :
    Nonempty (M ≃* Equiv.Perm (Fin 4)) := by
  let : (innerIn M).Normal := innerIn_normal hF M
  obtain ⟨j, hj⟩ := a4_normal_embedding_perm_four hF M.subtype M.subtype_injective
    (innerIn M) ((innerEquiv M).symm.trans e)
  have hcard : Nat.card M = Nat.card (Equiv.Perm (Fin 4)) := by
    rw [card_eq_two_mul_inner hF T M hTM, Nat.card_congr e.toEquiv,
      alternatingGroup.card_of_card_eq_four (by simp), Nat.card_perm]
    norm_num [Nat.card_eq_fintype_card, Nat.factorial]
  exact ⟨MulEquiv.ofBijective j ((Nat.bijective_iff_injective_and_card j).mpr ⟨hj, hcard⟩)⟩

/-- An S₄ intersection would give a faithful action of an order-48 group on
its characteristic A₄ subgroup, contradicting Aut(A₄) ≃ S₄. -/
public theorem not_inner_symmetric_four
    (hF : IsOddPrimePower (Nat.card F))
    (T : Sylow 2 (PGL2 F)) (M : Subgroup (PGL2 F)) (hTM : (T : Subgroup _) ≤ M) :
    ¬ Nonempty (inner M ≃* Equiv.Perm (Fin 4)) := by
  rintro ⟨e⟩
  let H := innerIn M
  let : H.Normal := innerIn_normal hF M
  let eH : H ≃* Equiv.Perm (Fin 4) := (innerEquiv M).symm.trans e
  let A : Subgroup H := (alternatingGroup (Fin 4)).comap eH.toMonoidHom
  let : A.Characteristic := by
    apply characteristic_iff_le_comap.mpr
    intro φ x hx
    have hh := characteristic_iff_le_comap.mp
      (inferInstance : (alternatingGroup (Fin 4)).Characteristic)
      ((eH.symm.trans φ).trans eH) hx
    simpa [A] using hh
  let B : Subgroup M := A.map H.subtype
  let : B.Normal := by dsimp [B]; infer_instance
  let eA : A ≃* alternatingGroup (Fin 4) :=
    MulEquiv.ofBijective
      ({ toFun := fun a => ⟨eH a, a.property⟩
         map_one' := by ext; simp
         map_mul' := fun a b => by ext; simp } : A →* alternatingGroup (Fin 4))
      ⟨fun a b hab => Subtype.ext (eH.injective (congrArg Subtype.val hab)),
        fun a => ⟨⟨eH.symm a, by change eH (eH.symm a) ∈ alternatingGroup (Fin 4); simp⟩,
          Subtype.ext (eH.apply_symm_apply a)⟩⟩
  let eB : B ≃* alternatingGroup (Fin 4) :=
    (Subgroup.equivMapOfInjective A H.subtype H.subtype_injective).symm.trans eA
  obtain ⟨j, hj⟩ := a4_normal_embedding_perm_four hF M.subtype M.subtype_injective B eB
  have hle := Nat.card_le_card_of_injective j hj
  have hfour : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
    rw [Nat.card_perm]
    norm_num [Nat.card_eq_fintype_card, Nat.factorial]
  rw [card_eq_two_mul_inner hF T M hTM, Nat.card_congr e.toEquiv, hfour] at hle
  omega
/-- A hypothetical A₅ intersection realizes the whole overgroup as S₅.
The subsequent order-five argument rules out this projective embedding. -/
public theorem symmetric_five_of_inner_alternating_five
    (hF : IsOddPrimePower (Nat.card F))
    (T : Sylow 2 (PGL2 F)) (M : Subgroup (PGL2 F)) (hTM : (T : Subgroup _) ≤ M)
    (e : inner M ≃* alternatingGroup (Fin 5)) :
    Nonempty (M ≃* Equiv.Perm (Fin 5)) := by
  let H := innerIn M
  let : H.Normal := innerIn_normal hF M
  let eH : H ≃* alternatingGroup (Fin 5) := (innerEquiv M).symm.trans e
  let S : Sylow 2 (alternatingGroup (Fin 5)) := Classical.choice inferInstance
  let V := (S : Subgroup (alternatingGroup (Fin 5))).map eH.symm.toMonoidHom
  have hV : IsKleinFour V := isKleinFour_map_of_injective _
    (sylowTwo_alternatingGroupFive_isKleinFour S) _ eH.symm.injective
  have hZ : center H = ⊥ := center_eq_bot_of_mulEquiv eH
    (alternatingGroup.center_eq_bot (by simp))
  have hC := centralizer_eq_bot_of_kleinFour hF M.subtype M.subtype_injective H V hV hZ
  let a : Equiv.Perm (Fin 5) ≃* MulAut (alternatingGroup (Fin 5)) :=
    MulEquiv.ofBijective _
      (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 (by decide) (by decide))
  let j : M →* Equiv.Perm (Fin 5) := a.symm.toMonoidHom.comp
    ((MulAut.congr eH).toMonoidHom.comp (MulAut.conjNormal (H := H)))
  have hj : Function.Injective j := a.symm.injective.comp ((MulAut.congr eH).injective.comp
    (conjNormal_injective_of_centralizer_eq_bot H hC))
  have hcard : Nat.card M = Nat.card (Equiv.Perm (Fin 5)) := by
    rw [card_eq_two_mul_inner hF T M hTM, Nat.card_congr e.toEquiv,
      nat_card_alternatingGroup, Nat.card_perm]
    norm_num [Nat.card_eq_fintype_card, Nat.factorial]
  exact ⟨MulEquiv.ofBijective j ((Nat.bijective_iff_injective_and_card j).mpr ⟨hj, hcard⟩)⟩

private def fiveCycle : Equiv.Perm (Fin 5) :=
  Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3 * Equiv.swap 3 4

private def squareActor : Equiv.Perm (Fin 5) :=
  Equiv.swap 1 2 * Equiv.swap 2 4 * Equiv.swap 4 3

/-- The hypothetical extension supplies an actual order-five subgroup of PGL₂
and an actual projective element inducing squaring on it. -/
public theorem exists_order_five_square_pair_of_inner_alternating_five
    (hF : IsOddPrimePower (Nat.card F))
    (T : Sylow 2 (PGL2 F)) (M : Subgroup (PGL2 F)) (hTM : (T : Subgroup _) ≤ M)
    (e : inner M ≃* alternatingGroup (Fin 5)) :
    ∃ x y : PGL2 F, orderOf x = 5 ∧ y * x * y⁻¹ = x ^ 2 := by
  obtain ⟨a⟩ := symmetric_five_of_inner_alternating_five hF T M hTM e
  let j : Equiv.Perm (Fin 5) →* PGL2 F := M.subtype.comp a.symm.toMonoidHom
  have hj : Function.Injective j := M.subtype_injective.comp a.symm.injective
  have hx : orderOf fiveCycle = 5 := by
    let : Fact (Nat.Prime 5) := ⟨by decide⟩
    exact orderOf_eq_prime (by decide +kernel) (by decide +kernel)
  refine ⟨j fiveCycle, j squareActor, (orderOf_injective j hj _).trans hx, ?_⟩
  have hxy : squareActor * fiveCycle * squareActor⁻¹ = fiveCycle ^ 2 := by decide +kernel
  simpa only [map_mul, map_inv, map_pow] using congrArg j hxy

/-- The A₅ intersection is impossible in characteristic different from five. -/
public theorem not_inner_alternating_five
    (hF : IsOddPrimePower (Nat.card F)) (hfive : (5 : F) ≠ 0)
    (T : Sylow 2 (PGL2 F)) (M : Subgroup (PGL2 F)) (hTM : (T : Subgroup _) ≤ M) :
    ¬ Nonempty (inner M ≃* alternatingGroup (Fin 5)) := by
  rintro ⟨e⟩
  obtain ⟨x, y, hx, hxy⟩ := exists_order_five_square_pair_of_inner_alternating_five hF T M hTM e
  exact Matrix.ProjGenLinGroup.not_conjugate_square_of_order_five hfive x y hx hxy

/-- The exceptional-intersection premise of the maximal-overgroup assembly.
This identifies the whole subgroup M; the intersection is the literal toPGL preimage. -/
public theorem symmetric_four_of_inner_exceptional
    {p : ℕ} [Fact p.Prime] (hpodd : Odd p) (hp5 : 5 < p) (hFcard : Nat.card F = p)
    (T : Sylow 2 (PGL2 F)) (M : Subgroup (PGL2 F)) (_hM : IsCoatom M)
    (hTM : (T : Subgroup _) ≤ M)
    (he : Nonempty (inner M ≃* alternatingGroup (Fin 4)) ∨
      Nonempty (inner M ≃* Equiv.Perm (Fin 4)) ∨
      Nonempty (inner M ≃* alternatingGroup (Fin 5))) :
    Nonempty (M ≃* Equiv.Perm (Fin 4)) := by
  have hF : IsOddPrimePower (Nat.card F) :=
    ⟨p, 1, Fact.out, hpodd, le_rfl, by simpa using hFcard⟩
  have hfive : (5 : F) ≠ 0 := by
    let : Fintype F := Fintype.ofFinite F
    let : CharP F p := charP_of_card_eq_prime (by simpa only [Nat.card_eq_fintype_card] using hFcard)
    intro hz
    exact (Nat.not_dvd_of_pos_of_lt (by decide : 0 < 5) hp5)
      ((CharP.cast_eq_zero_iff F p 5).mp hz)
  rcases he with he | he | he
  · obtain ⟨e⟩ := he
    exact symmetric_four_of_inner_alternating_four hF T M hTM e
  · exact (not_inner_symmetric_four hF T M hTM he).elim
  · exact (not_inner_alternating_five hF hfive T M hTM he).elim

/-- The exceptional branch gives the actual model required by the prime-field
Sylow-overgroup consumer. -/
public theorem sylowOvergroupModel_of_inner_exceptional
    {p : ℕ} [Fact p.Prime] (hpodd : Odd p) (hp5 : 5 < p) (hFcard : Nat.card F = p)
    (T : Sylow 2 (PGL2 F)) (M : Subgroup (PGL2 F)) (hM : IsCoatom M)
    (hTM : (T : Subgroup _) ≤ M)
    (he : Nonempty (inner M ≃* alternatingGroup (Fin 4)) ∨
      Nonempty (inner M ≃* Equiv.Perm (Fin 4)) ∨
      Nonempty (inner M ≃* alternatingGroup (Fin 5))) :
    SylowOvergroupModel F M :=
  Or.inl (symmetric_four_of_inner_exceptional hpodd hp5 hFcard T M hM hTM he)

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Diagonal.MaximalOvergroups
