module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.Models
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.EscapeTransport
public import GorensteinWalter.PGL2KleinFourSelfCentralizer
public import GorensteinWalter.KleinFourMapInjective
public import GorensteinWalter.PSL2PerfectOfCard
public import GorensteinWalter.PGammaL2PSLRangeCentralizer
public import GorensteinWalter.PGammaL2PureSemilinear
public import Theory.GroupTheory.GeneralizedFitting.SimpleSocleStructure


/-!
# Elementary actors in quadratic semilinear PSL₂ extensions

The literal linear kernel embeds in odd PGL₂, so its elementary subgroups
have order at most four and its four-groups are self-centralizing. Counting
the kernel and field image shows that a rank-three actor meets the kernel in
a four-group and is self-centralizing in the ambient subgroup. The canonical
normal PSL₂ has trivial centralizer, forcing the ambient radical and two-core
to vanish. Consequently the rank-three actor equals its literal ambient tau.
The local E1 application below discharges E0 while retaining the intrinsic
odd-section and Sylow-intersection inputs.

A field involution, when one exists, is straightened by projective Hilbert--90
and an actual subgroup isomorphism. In the other branch every elementary
actor lies in the linear kernel, and that kernel is exactly the canonical
PSL₂ subgroup. These two branches feed `FieldWitnesses`; their escaping local
subgroups still need to be constructed. The arguments include p=3 and p=5,
and make no dihedral Sylow assumption on the semilinear ambient group.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
A.2.3(2), E.1.1--2 and E.1.14(6), printed pp.33, 209--210 and 214.
The final local calculation in E.1.14(6) cites Aschbacher (1982), Lemma 4.10.
Projective involution descent is proved in `PGammaL2PureSemilinear`.
-/

public section

open Subgroup GorensteinWalter Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses

private theorem elementary_intersection {G : Type*} [Group G]
    (A K : Subgroup G) [IsElementaryAbelian 2 A] :
    IsElementaryAbelian 2 (A.subgroupOf K) := by
  refine {
    toIsMulCommutative := Subgroup.subgroupOf_isMulCommutative K A
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_ }
  intro x
  apply Subtype.ext
  apply Subtype.ext
  exact elemPow_eq_one_of_isElementaryAbelian (A := A) x.1.1 x.2

private def intersectionEquiv {G : Type*} [Group G] (A K : Subgroup G) :
    K.subgroupOf A ≃* A.subgroupOf K where
  toFun x := ⟨⟨x.1.1, x.2⟩, x.1.2⟩
  invFun x := ⟨⟨x.1.1, x.2⟩, x.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

private theorem intersection_index_le {G : Type*} [Group G] [Finite G]
    (K A : Subgroup G) : (K.subgroupOf A).index ≤ K.index := by
  change K.relIndex A ≤ K.index
  simpa only [relIndex_top_right] using
    (relIndex_le_of_le_right (H := K) (K := A) (L := ⊤) le_top
      (by simpa only [relIndex_top_right] using K.index_ne_zero_of_finite))

private theorem elementary_card {A : Type*} [Group A] [Finite A]
    [IsElementaryAbelian 2 A] : Nat.card A = 2 ^ Group.rank A := by
  obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_card_eq
  have hr : Group.rank A = n := le_antisymm
    (IsElementaryAbelian.rank_le_of_card_le A hn.le)
    (IsElementaryAbelian.rank_ge_of_card hn)
  simpa only [hr] using hn

private theorem four_of_elementary_card {A : Type*} [Group A] [Finite A]
    [IsElementaryAbelian 2 A] (hcard : Nat.card A = 4) : IsKleinFour A := by
  refine ⟨hcard, ?_⟩
  rcases (Nat.dvd_prime Nat.prime_two).mp (IsElementaryAbelian.exponent_dvd_p 2 A) with h | h
  · let : Subsingleton A := Monoid.exp_eq_one_iff.mp h
    have hc : Nat.card A = 1 := by simp
    omega
  · exact h

universe u
variable {F : Type u} [Field F] [Finite F]

private theorem exists_linearKernel_embedding {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hF : Nat.card F = p ^ 2) (S : Subgroup (PGammaL2 F))
    (hS : pGammaL2PSLRange F ≤ S) :
    ∃ j : pGammaL2LinearKernel F S →* PGL2 F, Function.Injective j := by
  have hq : IsOddPrimePower (Nat.card F) := ⟨p, 2, hp, hodd, by decide, hF⟩
  rcases pGammaL2_linear_kernel_model F hq S hS with he | he
  · obtain ⟨e⟩ := he
    exact ⟨Matrix.ProjectiveSpecialLinearGroup.toPGL.comp e.toMonoidHom,
      Matrix.ProjectiveSpecialLinearGroup.toPGL_injective.comp e.injective⟩
  · obtain ⟨e⟩ := he
    exact ⟨e.toMonoidHom, e.injective⟩

/-- The elementary subgroups of the literal linear kernel have order at most four. -/
theorem linearKernel_elementary_card_le_four {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hF : Nat.card F = p ^ 2) (S : Subgroup (PGammaL2 F)) [Finite S]
    (hS : pGammaL2PSLRange F ≤ S) (D : Subgroup (pGammaL2LinearKernel F S))
    (hD : IsElementaryAbelian 2 D) : Nat.card D ≤ 4 := by
  obtain ⟨j, hj⟩ := exists_linearKernel_embedding hp hodd hF S hS
  have hq : IsOddPrimePower (Nat.card F) := ⟨p, 2, hp, hodd, by decide, hF⟩
  let : Finite (PGL2 F) := Finite.of_surjective
    Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  have hr : primeRank 2 (pGammaL2LinearKernel F S) ≤ 2 :=
    (primeRank_le_of_injective 2 j hj).trans (Theory.PSL2.odd_pgl_two_rank F hq)
  exact (primeRank_le_iff_elementary_card_le _).mp hr D hD

/-- Centralization is computed in the actual kernel, using its faithful PGL₂ action. -/
theorem linearKernel_four_selfCentralizing {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hF : Nat.card F = p ^ 2) (S : Subgroup (PGammaL2 F))
    (hS : pGammaL2PSLRange F ≤ S) (D : Subgroup (pGammaL2LinearKernel F S))
    (hD : IsKleinFour D) : centralizer (D : Set (pGammaL2LinearKernel F S)) = D := by
  obtain ⟨j, hj⟩ := exists_linearKernel_embedding hp hodd hF S hS
  have hq : IsOddPrimePower (Nat.card F) := ⟨p, 2, hp, hodd, by decide, hF⟩
  have hDj := isKleinFour_map_of_injective D hD j hj
  apply le_antisymm
  · intro x hx
    have hc : j x ∈ centralizer (D.map j : Set (PGL2 F)) := by
      rw [mem_centralizer_iff]
      rintro _ ⟨y, hy, rfl⟩
      simpa only [map_mul] using congrArg j (mem_centralizer_iff.mp hx y hy)
    rw [pgl2_kleinFour_centralizer_eq_self F hq _ hDj] at hc
    exact (mem_map_iff_mem hj).mp hc
  · let : IsKleinFour D := hD
    intro x hx
    rw [mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (IsKleinFour.isMulCommutative.is_comm.comm
      (⟨y, hy⟩ : D) ⟨x, hx⟩)

/-- A rank-three actor meets the literal linear kernel in a four-group. -/
theorem rank_three_linearIntersection_isKleinFour {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hF : Nat.card F = p ^ 2) (S : Subgroup (PGammaL2 F)) [Finite S]
    (hS : pGammaL2PSLRange F ≤ S) (A : Subgroup S)
    (hA : IsElementaryAbelian 2 A) (hr : Group.rank A = 3) :
    IsKleinFour (A.subgroupOf (pGammaL2LinearKernel F S)) := by
  let := hA
  let K := pGammaL2LinearKernel F S
  let D := A.subgroupOf K
  let : IsElementaryAbelian 2 D := elementary_intersection A K
  have hAc : Nat.card A = 8 := by simpa [hr] using elementary_card (A := A)
  have hDupper : Nat.card D ≤ 4 :=
    linearKernel_elementary_card_le_four hp hodd hF S hS D inferInstance
  have hKi : K.index ≤ 2 := by
    change (pGammaL2LinearKernel F S).index ≤ 2
    rcases linearKernel_index_eq_one_or_two hp hF S with h | h <;> omega
  have hi : (K.subgroupOf A).index ≤ 2 := (intersection_index_le K A).trans hKi
  have hprod : Nat.card D * (K.subgroupOf A).index = 8 := by
    rw [← Nat.card_congr (intersectionEquiv A K).toEquiv,
      (K.subgroupOf A).card_mul_index, hAc]
  apply four_of_elementary_card
  nlinarith [Nat.mul_le_mul_left (Nat.card D) hi]

/-- The field factor cannot enlarge the centralizer of a rank-three actor. -/
theorem rank_three_selfCentralizing {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hF : Nat.card F = p ^ 2) (S : Subgroup (PGammaL2 F)) [Finite S]
    (hS : pGammaL2PSLRange F ≤ S) (A : Subgroup S)
    (hA : IsElementaryAbelian 2 A) (hr : Group.rank A = 3) :
    centralizer (A : Set S) = A := by
  let := hA
  let K := pGammaL2LinearKernel F S
  let C := centralizer (A : Set S)
  let D := A.subgroupOf K
  have hD : IsKleinFour D := rank_three_linearIntersection_isKleinFour hp hodd hF S hS A hA hr
  have hcent := linearKernel_four_selfCentralizing hp hodd hF S hS D hD
  have hCK : C.subgroupOf K ≤ D := by
    intro x hx
    apply hcent.le
    rw [mem_centralizer_iff]
    intro y hy
    exact Subtype.ext (mem_centralizer_iff.mp hx y hy)
  have hKc : Nat.card (K.subgroupOf C) ≤ 4 := by
    rw [Nat.card_congr (intersectionEquiv C K).toEquiv]
    exact (card_le_of_le hCK).trans hD.card_four.le
  have hKi : K.index ≤ 2 := by
    change (pGammaL2LinearKernel F S).index ≤ 2
    rcases linearKernel_index_eq_one_or_two hp hF S with h | h <;> omega
  have hi : (K.subgroupOf C).index ≤ 2 := (intersection_index_le K C).trans hKi
  have hCc : Nat.card C ≤ 8 := by
    rw [← (K.subgroupOf C).card_mul_index]
    exact Nat.mul_le_mul hKc hi
  have hAC : A ≤ C := by
    intro x hx
    rw [mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (IsMulCommutative.is_comm.comm (⟨y, hy⟩ : A) ⟨x, hx⟩)
  have hAc : Nat.card A = 8 := by simpa [hr] using elementary_card (A := A)
  exact (eq_of_le_of_card_ge hAC (by omega)).symm

/-- A rank-three actor itself maps onto the field factor. This does not
choose a complement for the ambient extension. -/
theorem rank_three_fieldProjection_surjective {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hF : Nat.card F = p ^ 2) (S : Subgroup (PGammaL2 F)) [Finite S]
    (hS : pGammaL2PSLRange F ≤ S) (A : Subgroup S)
    (hA : IsElementaryAbelian 2 A) (hr : Group.rank A = 3) :
    Function.Surjective ((pGammaL2FieldProjection F S).comp A.subtype) := by
  let := hA
  let K := pGammaL2LinearKernel F S
  let f := (pGammaL2FieldProjection F S).comp A.subtype
  let : Finite (F ≃+* F) := Finite.of_injective
    (fun a : F ≃+* F => (a : F → F)) DFunLike.coe_injective
  have hD := rank_three_linearIntersection_isKleinFour hp hodd hF S hS A hA hr
  have hk : f.ker = K.subgroupOf A := by
    ext x
    exact (mem_pGammaL2LinearKernel_iff F S x.val).symm
  have hcard : Nat.card f.ker = 4 := by
    rw [hk, Nat.card_congr (intersectionEquiv A K).toEquiv]
    exact hD.card_four
  have hAc : Nat.card A = 8 := by simpa [hr] using elementary_card (A := A)
  have hprod := f.ker.card_mul_index
  rw [hcard, hAc, index_ker] at hprod
  apply MonoidHom.range_eq_top.mp
  apply eq_top_of_card_eq
  rw [FiniteField.card_ringAut_of_card_prime_pow hp hF]
  change Nat.card f.range = 2
  omega

/-- The full semilinear subgroup containing PSL₂ has trivial solvable radical. -/
theorem solvableRadical_eq_bot {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hF : Nat.card F = p ^ 2) (hlarge : 5 < p ^ 2)
    (S : Subgroup (PGammaL2 F)) [Finite S]
    (hS : pGammaL2PSLRange F ≤ S) : solvableRadical S = ⊥ := by
  let L := pGammaL2PSLRange F
  let D := L.subgroupOf S
  have hq : IsOddPrimePower (Nat.card F) := ⟨p, 2, hp, hodd, by decide, hF⟩
  have hc : 3 < Nat.card F := by omega
  let : L.Normal := pGammaL2PSLRange_normal F hq hc
  let : D.Normal := inferInstance
  let e : D ≃* PSL2 F := (subgroupOfEquivOfLe hS).trans (pGammaL2PSLRangeEquiv F).symm
  let : IsSimpleGroup (PSL2 F) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
  let : Group.IsPerfect (PSL2 F) := psl2_isPerfect_of_card_gt_three F hc
  let : IsSimpleGroup D := e.isSimpleGroup
  let : Group.IsPerfect D := Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  apply SimpleSocle.radical_eq_bot D
  apply le_bot_iff.mp
  intro x hx
  have hxC : (x : PGammaL2 F) ∈ centralizer (L : Set (PGammaL2 F)) := by
    rw [mem_centralizer_iff]
    intro y hy
    have hyD : (⟨y, hS hy⟩ : S) ∈ D := hy
    exact congrArg Subtype.val (mem_centralizer_iff.mp hx ⟨y, hS hy⟩ hyD)
  rw [pGammaL2_pslRange_centralizer_eq_bot F hq hc, mem_bot] at hxC
  exact Subtype.ext hxC

/-- In particular the tau quotient in the ambient group has trivial kernel. -/
theorem twoCore_eq_bot {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hF : Nat.card F = p ^ 2) (hlarge : 5 < p ^ 2)
    (S : Subgroup (PGammaL2 F)) [Finite S]
    (hS : pGammaL2PSLRange F ≤ S) : pCore 2 S = ⊥ :=
  SimpleSocle.pCore_eq_bot (solvableRadical_eq_bot hp hodd hF hlarge S hS) 2

/-- For a rank-three actor the literal ambient tau equals the actor. -/
theorem tau_eq_of_rank_three {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hF : Nat.card F = p ^ 2) (hlarge : 5 < p ^ 2)
    (S : Subgroup (PGammaL2 F)) [Finite S]
    (hS : pGammaL2PSLRange F ≤ S) (T : Sylow 2 S) (A : Subgroup S)
    (hA : IsElementaryAbelian 2 A) (hAT : A ≤ (T : Subgroup S))
    (hr : Group.rank A = 3) : tau (T : Subgroup S) A = A := by
  let := hA
  have hcore := twoCore_eq_bot hp hodd hF hlarge S hS
  have hcent := rank_three_selfCentralizing hp hodd hF S hS A hA hr
  apply le_antisymm
  · intro x hx
    apply hcent.le
    rw [mem_centralizer_iff]
    intro a ha
    have hcomm := (mem_centralizerModulo_iff.mp hx).2 a ha
    rw [hcore, mem_bot] at hcomm
    exact commutatorElement_eq_one_iff_mul_comm.mp hcomm
  · exact le_sup_left.trans (sup_pCore_le_tau T A hAT)

/-- Application to an actual local candidate: rank three discharges its E0
ambient tau condition. The intrinsic E1 section and Sylow placement remain
separate inputs for the torus/subfield construction. -/
theorem isEMemberAt_of_rank_three_odd {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hF : Nat.card F = p ^ 2) (hlarge : 5 < p ^ 2)
    (S : Subgroup (PGammaL2 F)) [Finite S]
    (hS : pGammaL2PSLRange F ≤ S) (T : Sylow 2 S) (A H : Subgroup S)
    (hA : IsElementaryAbelian 2 A) (hAT : A ≤ (T : Subgroup S))
    (hr : Group.rank A = 3) (hAH : A ≤ H)
    (hSyl : ∃ U : Sylow 2 H, (U : Subgroup H) = (T : Subgroup S).subgroupOf H)
    (ho : ECaseOdd A H) : IsEMemberAt 1 (T : Subgroup S) A H := by
  have htau := tau_eq_of_rank_three hp hodd hF hlarge S hS T A hA hAT hr
  have hbound : Group.rank ((A.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))) = 1 := by
    obtain ⟨r, _, _, _, _, _, hb⟩ := ho
    exact hb
  exact ⟨⟨hA, hAT, hAH, by rw [htau]; exact le_inf hAT hAH, hSyl, Or.inl ho⟩,
    Or.inl ⟨ho, hbound.le⟩⟩

omit [Finite F] in
/-- If no involution has nontrivial field image, every elementary actor lies
in the literal linear kernel. No assertion about splitting or Sylow shape is used. -/
theorem elementary_le_linearKernel_of_no_field_involutions
    (S : Subgroup (PGammaL2 F))
    (hnofield : ∀ x : S, orderOf x = 2 → pGammaL2FieldProjection F S x = 1)
    (A : Subgroup S) (hA : IsElementaryAbelian 2 A) :
    A ≤ pGammaL2LinearKernel F S := by
  let := hA
  intro x hx
  rw [mem_pGammaL2LinearKernel_iff]
  by_cases he : x = 1
  · simp [he]
  · apply hnofield x
    apply (orderOf_eq_prime_iff (x := x)).mpr
    exact ⟨elemPow_eq_one_of_isElementaryAbelian (A := A) x hx, he⟩

/-- All nontrivial large actors in the branch without field involutions are
four-groups, even when the ambient Sylow two-subgroup is not dihedral. -/
theorem large_actor_isKleinFour_of_no_field_involutions
    {p : ℕ} (hp : p.Prime) (hodd : Odd p) (hF : Nat.card F = p ^ 2)
    (S : Subgroup (PGammaL2 F)) [Finite S] (hS : pGammaL2PSLRange F ≤ S)
    (hnofield : ∀ x : S, orderOf x = 2 → pGammaL2FieldProjection F S x = 1)
    (A : Subgroup S) (hA : IsElementaryAbelian 2 A) (hr : 1 < Group.rank A) :
    IsKleinFour A := by
  let := hA
  have hAK := elementary_le_linearKernel_of_no_field_involutions S hnofield A hA
  let e := subgroupOfEquivOfLe hAK
  have hD : IsElementaryAbelian 2 (A.subgroupOf (pGammaL2LinearKernel F S)) :=
    elementary_intersection _ _
  have hc : Nat.card A ≤ 4 := by
    rw [← Nat.card_congr e.toEquiv]
    exact linearKernel_elementary_card_le_four hp hodd hF S hS _ hD
  have hu : Group.rank A ≤ 2 := IsElementaryAbelian.rank_le_of_card_le (p := 2) A hc
  have he : Group.rank A = 2 := by omega
  apply four_of_elementary_card
  simpa [he] using elementary_card (A := A)

/-- A supplied field involution can be straightened by an actual projective
linear conjugation. This is not an existence theorem for involutory lifts. -/
theorem exists_pureField_model_of_field_involution {p : ℕ}
    (hp : p.Prime) (hodd : Odd p) (hF : Nat.card F = p ^ 2) (hlarge : 5 < p ^ 2)
    (S : Subgroup (PGammaL2 F)) (hS : pGammaL2PSLRange F ≤ S)
    (x : S) (hx : orderOf x = 2) (hf : pGammaL2FieldProjection F S x ≠ 1) :
    ∃ (S' : Subgroup (PGammaL2 F)) (_e : S ≃* S') (σ : F ≃+* F),
      σ ^ 2 = 1 ∧ σ ≠ 1 ∧ pGammaL2PSLRange F ≤ S' ∧
        SemidirectProduct.inr σ ∈ S' := by
  have hq : IsOddPrimePower (Nat.card F) := ⟨p, 2, hp, hodd, by decide, hF⟩
  have hc : 3 < Nat.card F := by omega
  have hxo : orderOf (x : PGammaL2 F) = 2 := (Subgroup.orderOf_coe x).trans hx
  have hxf : (x : PGammaL2 F).right ≠ 1 := hf
  obtain ⟨C, hC⟩ := projective_semilinear_involution_conj_inr hq x hxo hxf
  let c : PGammaL2 F := SemidirectProduct.inl C
  let a := MulAut.conj c⁻¹
  let S' := S.map a.toMonoidHom
  let e : S ≃* S' := S.equivMapOfInjective a.toMonoidHom a.injective
  let σ := (x : PGammaL2 F).right
  have hσ : σ ^ 2 = 1 := by
    change (pGammaL2FieldProjection F S x) ^ 2 = 1
    have hxp : x ^ 2 = 1 := by simpa only [hx] using pow_orderOf_eq_one x
    rw [← map_pow, hxp, map_one]
  have ha : a x = SemidirectProduct.inr σ := by
    simpa [a, MulAut.conj_apply, c, σ] using hC
  let : (pGammaL2PSLRange F).Normal := pGammaL2PSLRange_normal F hq hc
  have hPSL : pGammaL2PSLRange F ≤ S' := by
    intro y hy
    refine ⟨c * y * c⁻¹, hS ((inferInstance : (pGammaL2PSLRange F).Normal).conj_mem y hy c), ?_⟩
    change c⁻¹ * (c * y * c⁻¹) * (c⁻¹)⁻¹ = y
    group
  refine ⟨S', e, σ, hσ, hxf, hPSL, ?_⟩
  rw [← ha]
  exact mem_map.mpr ⟨x, x.property, rfl⟩


/-- A subgroup with full linear layer and nontrivial quadratic field image
contains a field involution. The lift is constructed by removing its linear part. -/
theorem exists_field_involution_of_pgl_le {p : ℕ} (hp : p.Prime)
    (hF : Nat.card F = p ^ 2) (S : Subgroup (PGammaL2 F))
    (hP : pGammaL2PGLRange F ≤ S) (hindex : (pGammaL2LinearKernel F S).index = 2) :
    ∃ x : S, orderOf x = 2 ∧ pGammaL2FieldProjection F S x ≠ 1 := by
  classical
  have hex : ∃ x : S, pGammaL2FieldProjection F S x ≠ 1 := by
    by_contra! h
    have hk : pGammaL2LinearKernel F S = ⊤ := by
      apply top_unique
      intro x _
      exact (mem_pGammaL2LinearKernel_iff F S x).mpr (h x)
    have hi := Subgroup.index_eq_one.mpr hk
    omega
  obtain ⟨x, hx⟩ := hex
  let σ := (x : PGammaL2 F).right
  let : Finite (F ≃+* F) := Finite.of_injective
    (fun a : F ≃+* F => (a : F → F)) DFunLike.coe_injective
  have hsq : σ ^ 2 = 1 := by
    have h := pow_card_eq_one' (x := σ)
    rwa [FiniteField.card_ringAut_of_card_prime_pow hp hF] at h
  have hne : σ ≠ 1 := hx
  have ho : orderOf σ = 2 := (orderOf_eq_prime_iff (x := σ)).mpr ⟨hsq, hne⟩
  have hi : SemidirectProduct.inl (x : PGammaL2 F).left ∈ S :=
    hP ⟨_, rfl⟩
  have hpure : SemidirectProduct.inr σ ∈ S := by
    apply (S.mul_mem_cancel_left hi).mp
    exact (SemidirectProduct.inl_left_mul_inr_right (x : PGammaL2 F)).symm ▸ x.property
  let t : S := ⟨SemidirectProduct.inr σ, hpure⟩
  refine ⟨t, ?_, hne⟩
  rw [← Subgroup.orderOf_coe t]
  exact (orderOf_injective SemidirectProduct.inr SemidirectProduct.inr_injective σ).trans ho

/-- The branch without field involutions has exactly the canonical PSL₂
linear kernel, not merely an abstract PSL₂/PGL₂ alternative. -/
theorem linearKernel_eq_inner_of_no_field_involutions {p : ℕ}
    (hp : p.Prime) (hodd : Odd p) (hF : Nat.card F = p ^ 2)
    (S : Subgroup (PGammaL2 F)) (hS : pGammaL2PSLRange F ≤ S)
    (hindex : (pGammaL2LinearKernel F S).index = 2)
    (hnofield : ∀ x : S, orderOf x = 2 → pGammaL2FieldProjection F S x = 1) :
    pGammaL2LinearKernel F S = (pGammaL2PSLRange F).subgroupOf S := by
  let K := pGammaL2LinearKernel F S
  let M := K.map S.subtype
  have hLM : pGammaL2PSLRange F ≤ M := by
    intro x hx
    refine ⟨⟨x, hS hx⟩, ?_, rfl⟩
    change (⟨x, hS hx⟩ : S) ∈ pGammaL2LinearKernel F S
    rw [mem_pGammaL2LinearKernel_iff]
    obtain ⟨y, rfl⟩ := (mem_pGammaL2PSLRange_iff F x).mp hx
    simp [pGammaL2FieldProjection]
  have hMP : M ≤ pGammaL2PGLRange F := by
    rintro x ⟨y, hy, rfl⟩
    rw [pGammaL2PGLRange, SemidirectProduct.range_inl_eq_ker_rightHom]
    exact (mem_pGammaL2LinearKernel_iff F S y).mp hy
  have hq : IsOddPrimePower (Nat.card F) := ⟨p, 2, hp, hodd, by decide, hF⟩
  have hmul := relIndex_mul_relIndex (pGammaL2PSLRange F) M
    (pGammaL2PGLRange F) hLM hMP
  rw [pGammaL2_psl_range_relIndex_pgl_eq_two F hq] at hmul
  have hdiv : (pGammaL2PSLRange F).relIndex M ∣ 2 :=
    ⟨M.relIndex (pGammaL2PGLRange F), hmul.symm⟩
  have heq : M = pGammaL2PSLRange F := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdiv with h | h
    · exact le_antisymm (relIndex_eq_one.mp h) hLM
    · have hi : M.relIndex (pGammaL2PGLRange F) = 1 := by
        rw [h] at hmul
        omega
      have hPM := relIndex_eq_one.mp hi
      have hMS : M ≤ S := map_subtype_le K
      obtain ⟨x, hx, hf⟩ := exists_field_involution_of_pgl_le hp hF S
        (hPM.trans hMS) hindex
      exact (hf (hnofield x hx)).elim
  apply map_subtype_inj.mp
  rw [map_subgroupOf_eq_of_le hS]
  exact heq

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses
