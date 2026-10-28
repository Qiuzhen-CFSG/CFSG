module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.TerminalLinear.Exterior.Seed
public import Theory.SpecificGroups.BinaryLinear.ExteriorParabolicResidual
public import Theory.GroupTheory.PResidual.CubicCoreQuotient
public import Theory.GroupTheory.PrimeRankSquareFree
public import Theory.GroupTheory.PrimeRankZero

/-!
# The original exterior residual and its cubic subgroup

The marked 2+3 parabolic image of M₁ has two-group kernel, so its intrinsic
two-core quotient is SL₂(2) × SL₃(2). Normal residual transport gives the
printed K_I/O₂(K_I) ≅ C₃ × SL₃(2), retaining the literal K_I=O^{3′}(M₁).
The cubic residual of the actual O₂,₃ preimage has a two-core quotient of
order three, hence has precisely three-rank one. Its containment in K_I
and normalization by K_I are proved on the original ambient subgroups.

Source: Aschbacher--Smith 15.2.23(d), printed p.1117.
-/

set_option backward.isDefEq.respectTransparency false
public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section02.TerminalLinear
open ChapterB.QuasisimpleSource Section01
variable {G : Type*} [Group G] [Finite G]

/-- The literal exterior parabolic image gives the intrinsic M₁ two-core quotient. -/
theorem M1_quotient_of_exterior_image {X ZS : Subgroup G}
    (e : (X ⧸ pCore 2 X) ≃* SL(5,ZMod 2))
    (hmark : (((M1 X ZS).subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))).map
      e.toMonoidHom = SL5ExteriorSquare.parabolic 2) :
    Nonempty ((M1 X ZS ⧸ pCore 2 (M1 X ZS)) ≃* (SL(2,ZMod 2) × SL(3,ZMod 2))) := by
  let A := M1 X ZS
  let P := SL5ExteriorSquare.parabolic 2
  let j : A →* X := inclusion inf_le_left
  let q := QuotientGroup.mk' (pCore 2 X)
  let f0 := e.toMonoidHom.comp (q.comp j)
  have hmem (a : A) : f0 a ∈ P := by
    dsimp only [P]
    rw [← hmark]
    exact mem_map_of_mem e.toMonoidHom (mem_map_of_mem q a.property)
  let f := f0.codRestrict P hmem
  have hf : Function.Surjective f := by
    intro p
    obtain ⟨y,⟨x,hx,rfl⟩,he⟩ := hmark.symm.le p.property
    exact ⟨⟨x,hx⟩,Subtype.ext he⟩
  have hk : IsPGroup 2 f.ker := by
    let k : f.ker →* pCore 2 X :=
      (j.comp f.ker.subtype).codRestrict _ (by
        intro a
        have he := congrArg P.subtype a.property
        change e (q (j a.val)) = 1 at he
        exact (QuotientGroup.eq_one_iff _).mp (e.map_eq_one_iff.mp he))
    apply pCore_isPGroup.of_injective k
    intro a b he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : pCore 2 X => (x.val : G)) he
  exact ⟨(f.pCoreQuotientEquiv hf hk).trans SL5ExteriorSquare.parabolicTwoQuotientEquiv⟩

/-- Residual transport keeps the actual KI and the intrinsic two-core denominator. -/
noncomputable def KI_quotientEquiv_residual {X ZS : Subgroup G} :
    (KI X ZS ⧸ pCore 2 (KI X ZS)) ≃*
      primeToResidual 3 (M1 X ZS ⧸ pCore 2 (M1 X ZS)) := by
  let ei : primeToResidual 3 (M1 X ZS) ≃* KI X ZS :=
    (primeToResidual 3 (M1 X ZS)).equivMapOfInjective (M1 X ZS).subtype
      (M1 X ZS).subtype_injective
  exact (QuotientGroup.congr _ _ ei (pCore_map_iso 2 ei)).symm.trans
    (primeToResidualCoreQuotientImage 3 2)

/-- The exterior row constructs the printed C₃ × L₃(2) quotient of KI. -/
theorem KI_quotient_of_exterior
    {T : Sylow 2 G} {M Mc V H ZS I X : Subgroup G}
    {hsource : ChosenSmallSource T M Mc V}
    (d : PlaneUniquenessPreceding hsource H ZS)
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (hXI : X ≤ I) (hn : I ≤ normalizer (X : Set G))
    {r : ℕ} (hr : r = 2 ∨ r = 3) :
    letI := U_elementary d hI hfit hXI
    Nonempty (ActionEquiv (U_representation d hI hfit hXI hn) (SL5TenDimensional.exteriorAction r)) →
    Nonempty ((KI X ZS ⧸ pCore 2 (KI X ZS)) ≃*
      (alternatingGroup (Fin 3) × SL(3,ZMod 2))) := by
  let := U_elementary d hI hfit hXI
  rintro ⟨e⟩
  obtain ⟨f,g,_,hg⟩ := M1_image_parabolic_of_exterior d hI hfit hXI hn hr e
  let a := f.groupEquiv.trans (MulAut.conj g)
  have hmark : (((M1 X ZS).subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))).map
      a.toMonoidHom = SL5ExteriorSquare.parabolic 2 := by
    rw [show a.toMonoidHom = (MulAut.conj g).toMonoidHom.comp f.groupEquiv.toMonoidHom from rfl,
      ← map_map]
    exact hg
  obtain ⟨em⟩ := M1_quotient_of_exterior_image a hmark
  exact ⟨KI_quotientEquiv_residual.trans ((primeToResidualEquiv 3 em).trans
    BinaryLinear.ExteriorParabolic.leviResidualEquiv)⟩

/-- The actual exterior KI quotient has cubic core of order three. -/
theorem KI_cubicCore_card_of_exterior
    {T : Sylow 2 G} {M Mc V H ZS I X : Subgroup G}
    {hsource : ChosenSmallSource T M Mc V}
    (d : PlaneUniquenessPreceding hsource H ZS)
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (hXI : X ≤ I) (hn : I ≤ normalizer (X : Set G))
    {r : ℕ} (hr : r = 2 ∨ r = 3) :
    letI := U_elementary d hI hfit hXI
    Nonempty (ActionEquiv (U_representation d hI hfit hXI hn) (SL5TenDimensional.exteriorAction r)) →
    Nat.card (pCore 3 (KI X ZS ⧸ pCore 2 (KI X ZS))) = 3 := by
  let := U_elementary d hI hfit hXI
  rintro ⟨e⟩
  obtain ⟨f,g,_,hg⟩ := M1_image_parabolic_of_exterior d hI hfit hXI hn hr e
  let a := f.groupEquiv.trans (MulAut.conj g)
  have hmark : (((M1 X ZS).subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))).map
      a.toMonoidHom = SL5ExteriorSquare.parabolic 2 := by
    rw [show a.toMonoidHom = (MulAut.conj g).toMonoidHom.comp f.groupEquiv.toMonoidHom from rfl,
      ← map_map]
    exact hg
  obtain ⟨em⟩ := M1_quotient_of_exterior_image a hmark
  let er := KI_quotientEquiv_residual.trans (primeToResidualEquiv 3 em)
  rw [← card_map_of_injective (f := er.toMonoidHom) er.injective,pCore_map_iso 3 er]
  exact BinaryLinear.ExteriorParabolic.residual_levi_cubicCore_card

/-- The characteristic cubic subgroup uses the literal O₂,₃ preimage and
has the intrinsic cubic core as its two-core quotient. -/
noncomputable def cubicResidual_quotientEquiv (X ZS : Subgroup G) :
    (cubicResidual X ZS ⧸ pCore 2 (cubicResidual X ZS)) ≃*
      pCore 3 (KI X ZS ⧸ pCore 2 (KI X ZS)) := by
  let A := KI X ZS
  let C := (pCore 3 (A ⧸ pCore 2 A)).comap (QuotientGroup.mk' (pCore 2 A))
  let eC : C ≃* twoThreeIn A := C.equivMapOfInjective A.subtype A.subtype_injective
  let eR : primeToResidual 3 C ≃* cubicResidual X ZS :=
    (primeToResidualEquiv 3 eC).trans
      ((primeToResidual 3 (twoThreeIn A)).equivMapOfInjective (twoThreeIn A).subtype
        (twoThreeIn A).subtype_injective)
  exact (QuotientGroup.congr _ _ eR (pCore_map_iso 2 eR)).symm.trans
    (Subgroup.cubicResidualQuotientEquiv (A := A))

omit [Finite G] in
/-- The original rank-one subgroup is contained in KI. -/
theorem cubicResidual_le_KI (X ZS : Subgroup G) : cubicResidual X ZS ≤ KI X ZS :=
  (map_subtype_le _).trans (map_subtype_le _)

omit [Finite G] in
/-- KI normalizes its original characteristic cubic subgroup. -/
theorem KI_normalizes_cubicResidual (X ZS : Subgroup G) :
    KI X ZS ≤ normalizer (cubicResidual X ZS : Set G) := by
  let A := KI X ZS
  let C := (pCore 3 (A ⧸ pCore 2 A)).comap (QuotientGroup.mk' (pCore 2 A))
  let : C.Characteristic := Characteristic.comap_quotient_mk inferInstance
  exact A.le_normalizer.trans
    ((normalizer_le_normalizer_characteristic_image A C).trans
      (normalizer_le_normalizer_characteristic_image _ (primeToResidual 3 _)))

/-- The source exterior row constructs a nontrivial cubic quotient on the
actual subgroup O^{3′}(O₂,₃(KI)), rather than on an abstract model. -/
theorem cubicResidual_quotient_card_of_exterior
    {T : Sylow 2 G} {M Mc V H ZS I X : Subgroup G}
    {hsource : ChosenSmallSource T M Mc V}
    (d : PlaneUniquenessPreceding hsource H ZS)
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (hXI : X ≤ I) (hn : I ≤ normalizer (X : Set G))
    {r : ℕ} (hr : r = 2 ∨ r = 3) :
    letI := U_elementary d hI hfit hXI
    Nonempty (ActionEquiv (U_representation d hI hfit hXI hn) (SL5TenDimensional.exteriorAction r)) →
    Nat.card (cubicResidual X ZS ⧸ pCore 2 (cubicResidual X ZS)) = 3 := by
  let := U_elementary d hI hfit hXI
  intro he
  rw [Nat.card_congr (cubicResidual_quotientEquiv X ZS).toEquiv]
  exact KI_cubicCore_card_of_exterior d hI hfit hXI hn hr he

/-- The constructed original cubic subgroup has precisely three-rank one. -/
theorem cubicResidual_rank_of_exterior
    {T : Sylow 2 G} {M Mc V H ZS I X : Subgroup G}
    {hsource : ChosenSmallSource T M Mc V}
    (d : PlaneUniquenessPreceding hsource H ZS)
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (hXI : X ≤ I) (hn : I ≤ normalizer (X : Set G))
    {r : ℕ} (hr : r = 2 ∨ r = 3) :
    letI := U_elementary d hI hfit hXI
    Nonempty (ActionEquiv (U_representation d hI hfit hXI hn) (SL5TenDimensional.exteriorAction r)) →
    primeRank 3 (cubicResidual X ZS) = 1 := by
  let := U_elementary d hI hfit hXI
  intro he
  have hc := cubicResidual_quotient_card_of_exterior d hI hfit hXI hn hr he
  rw [← primeRank_quotient_eq_of_isTwoGroup 3 (by decide)
    (pCore 2 (cubicResidual X ZS)) pCore_isPGroup]
  have hu : primeRank 3 (cubicResidual X ZS ⧸ pCore 2 (cubicResidual X ZS)) ≤ 1 := by
    apply primeRank_le_one_of_square_not_dvd
    rw [hc]
    decide
  have hnz : primeRank 3 (cubicResidual X ZS ⧸ pCore 2 (cubicResidual X ZS)) ≠ 0 := by
    intro hz
    have hh := PrimeRank.eq_zero_iff_not_dvd_card.mp hz
    rw [hc] at hh
    exact hh dvd_rfl
  omega

end CFSG.Quasithin.Chapter15.Section02.TerminalLinear
