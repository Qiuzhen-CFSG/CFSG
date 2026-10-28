module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Nonquasisimple
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.FullSieve.SourceInterface.Geometry
public import CFSG.Quasithin.ChapterA.Section04.Signalizers.SectionCentralizer
public import Theory.SpecificGroups.SymplecticFour.RootCoreTori.Quotients
public import Theory.SpecificGroups.SymplecticFour.RootTori
public import Theory.SpecificGroups.SymplecticFour.EvenProjective
public import Theory.GroupTheory.PCoreRestriction

/-!
# Cubic scalar tori centralizing the intrinsic two-core sections

The point scalar matrices diag(s,1,s⁻¹,1) and plane scalar matrices
diag(s,s,s⁻¹,s⁻¹) are central modulo their parabolics' intrinsic two-cores.
If a parabolic contains and normalizes B, each commutator also lies in B;
intersecting with the parabolic core puts it in O₂(B). Thus the actual
field-unit group embeds in C(B/O₂(B)). Over the field of order four it
has order three. Transport uses an actual symplectic model isomorphism and
preserves both normalization and the intrinsic core of the marked subgroup.

The source application is Aschbacher–Smith 14.7.68(2), combined manuscript
of 1 March 2004, printed p.1072 (PDF p.1089). The matrix scalar and Levi
calculations are reused from `RootCoreTori.Quotients`; no enumeration of
Sp₄(4), or choice of an unrelated A₅ subgroup, is involved.
-/

public section
noncomputable section
open Subgroup Matrix
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Nonquasisimple.SymplecticCentralizer
open ChapterA.Section04 Theory.SpecificGroups.SymplecticFour
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface

private theorem coreCenter_le_sectionCentralizer {Q : Type*} [Group Q]
    {B P : Subgroup Q} (hBP : B ≤ P) (hn : P ≤ normalizer (B : Set Q)) :
    P.coreCenterIn 2 ≤ twoSectionCentralizer B ⊤ := by
  intro z hz
  obtain ⟨hzP, hc⟩ := (mem_coreCenterIn_iff 2 P z).mp hz
  have hzN := hn hzP
  refine ⟨mem_top _, hzN, ?_⟩
  intro b hb
  apply inf_pCoreIn_le_of_le 2 hBP
  refine ⟨?_, hc b (hBP hb)⟩
  exact le_normalizer_iff_commutator_le_right.mp (zpowers_le.mpr hzN)
    (commutator_mem_commutator (mem_zpowers z) hb)

private theorem sectionCentralizer_map {Q R : Type*} [Group Q] [Group R]
    (e : Q ≃* R) (B : Subgroup Q) :
    (twoSectionCentralizer B ⊤).map e.toMonoidHom =
      twoSectionCentralizer (B.map e.toMonoidHom) ⊤ := by
  ext z
  rw [mem_map_equiv]
  simp only [mem_twoSectionCentralizer, mem_top, true_and]
  have hn : e.symm z ∈ normalizer (B : Set Q) ↔
      z ∈ normalizer (B.map e.toMonoidHom : Set R) := by
    rw [← map_equiv_normalizer_eq, mem_map_equiv]
  rw [hn]
  apply and_congr_right
  intro _
  constructor
  · intro hc b hb
    obtain ⟨a, ha, rfl⟩ := hb
    rw [← map_pCoreIn_of_injective 2 B e.toMonoidHom e.injective]
    have hh := mem_map_of_mem e.toMonoidHom (hc a ha)
    simpa only [map_commutatorElement, MulEquiv.coe_toMonoidHom,
      MulEquiv.apply_symm_apply] using hh
  · intro hc b hb
    have hh := hc (e b) (mem_map_of_mem e.toMonoidHom hb)
    rw [← map_pCoreIn_of_injective 2 B e.toMonoidHom e.injective] at hh
    have he : ⁅z, e b⁆ = e ⁅e.symm z, b⁆ := by simp only [map_commutatorElement,
      MulEquiv.apply_symm_apply]
    rw [he] at hh
    exact (mem_map_iff_mem e.injective).mp hh

variable {F : Type*} [Field F]

private def planeScalar : Fˣ →* Sp F := by
  exact {
    toFun := fun s => diagonalTorus s s
    map_one' := by
      apply Subtype.ext
      ext i j
      rcases i with i | i <;> rcases j with j | j <;>
        fin_cases i <;> fin_cases j <;> simp [diagonalTorus, Matrix.diagonal]
    map_mul' := by
      intro s t
      apply Subtype.ext
      change (diagonalTorus (s * t) (s * t)).val =
        (diagonalTorus s s).val * (diagonalTorus t t).val
      simp only [diagonalTorus, Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      rcases i with i | i <;> fin_cases i <;> simp [mul_comm] }

private theorem planeScalar_injective : Function.Injective (planeScalar (F := F)) := by
  intro s t h
  apply Units.ext
  have he := congrArg (fun g : Sp F => g.val (.inl 0) (.inl 0)) h
  simpa [planeScalar, diagonalTorus, Matrix.diagonal] using he

variable [Finite F] [CharP F 2]

/-- The actual point scalar torus embeds into the centralizer of B/O₂(B)
whenever the point parabolic contains and normalizes B. -/
def pointScalarEmbedding (B : Subgroup (Sp F))
    (hBP : B ≤ pointParabolic) (hn : pointParabolic ≤ normalizer (B : Set (Sp F)))
    (hF : Nat.card F = 4) : Fˣ →* twoSectionCentralizer B ⊤ :=
  (RootTori.parameter 0).codRestrict _ (fun s =>
    coreCenter_le_sectionCentralizer hBP hn
      (RootCoreTori.point_scalar_mem_coreCenter (n := 2) hF (by decide) s))

/-- The scalar parameter is recovered from its first diagonal entry. -/
theorem pointScalarEmbedding_injective (B : Subgroup (Sp F))
    (hBP : B ≤ pointParabolic) (hn : pointParabolic ≤ normalizer (B : Set (Sp F)))
    (hF : Nat.card F = 4) : Function.Injective (pointScalarEmbedding B hBP hn hF) := by
  intro s t h
  exact RootTori.parameter_injective 0 (congrArg Subtype.val h)

/-- The plane scalar torus also acts trivially on the intrinsic core quotient. -/
def planeScalarEmbedding (B : Subgroup (Sp F))
    (hBP : B ≤ planeParabolic) (hn : planeParabolic ≤ normalizer (B : Set (Sp F)))
    (hF : Nat.card F = 4) : Fˣ →* twoSectionCentralizer B ⊤ :=
  planeScalar.codRestrict _ (fun s =>
    coreCenter_le_sectionCentralizer hBP hn
      (RootCoreTori.plane_scalar_mem_coreCenter (n := 2) hF (by decide) s))

theorem planeScalarEmbedding_injective (B : Subgroup (Sp F))
    (hBP : B ≤ planeParabolic) (hn : planeParabolic ≤ normalizer (B : Set (Sp F)))
    (hF : Nat.card F = 4) : Function.Injective (planeScalarEmbedding B hBP hn hF) := by
  intro s t h
  exact planeScalar_injective (congrArg Subtype.val h)

/-- Both actual maximal parabolics supply a cubic section-centralizer subgroup. -/
theorem three_dvd_sectionCentralizer_of_parabolic
    {Q : Type*} [Group Q] [Finite Q] (B P : Subgroup Q)
    (hBP : B ≤ P) (hn : P ≤ normalizer (B : Set Q))
    (hp : IsSp4FourMaximalParabolic P) :
    3 ∣ Nat.card (twoSectionCentralizer B ⊤) := by
  obtain ⟨k, _, _, hk, e, hp⟩ := hp
  let := Fintype.ofFinite k
  let : CharP k 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2)
    (by simpa [Nat.card_eq_fintype_card] using hk)
  let B' := B.map e.toMonoidHom
  have hn' : P.map e.toMonoidHom ≤ normalizer (B' : Set (Sp k)) := by
    rw [← map_equiv_normalizer_eq]
    exact map_mono hn
  have hle : B' ≤ P.map e.toMonoidHom := map_mono hBP
  have hd : 3 ∣ Nat.card (twoSectionCentralizer B' ⊤) := by
    rcases hp with hp | hp
    · rw [hp] at hle hn'
      have hd := card_dvd_of_injective (pointScalarEmbedding B' hle hn' hk)
        (pointScalarEmbedding_injective B' hle hn' hk)
      simpa only [Nat.card_units, hk] using hd
    · rw [hp] at hle hn'
      have hd := card_dvd_of_injective (planeScalarEmbedding B' hle hn' hk)
        (planeScalarEmbedding_injective B' hle hn' hk)
      simpa only [Nat.card_units, hk] using hd
  have he := Nat.card_congr
    ((twoSectionCentralizer B ⊤).equivMapOfInjective e.toMonoidHom e.injective).toEquiv
  rw [sectionCentralizer_map] at he
  exact he.symm ▸ hd

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Nonquasisimple.SymplecticCentralizer

@[expose] public section
noncomputable section
open Subgroup Representation Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
namespace Data
variable (d : Data T L V F W)

theorem fixedComponent_core_inter_normalizes_K_image
    (u : F.U) {Lu : Subgroup G} (h : Nonquasisimple.Case d u Lu) :
    (((F.H ⊓ Lu).subgroupOf Lu).map (QuotientGroup.mk' (pCore 2 Lu))) ≤
      normalizer ((((K F).subgroupOf Lu).map (QuotientGroup.mk' (pCore 2 Lu))) :
        Set (Lu ⧸ pCore 2 Lu)) := by
  have hn : (F.H ⊓ Lu).subgroupOf Lu ≤
      normalizer ((K F).subgroupOf Lu : Set Lu) := by
    rw [← subgroupOf_normalizer_eq h.larger.le]
    intro a ha
    exact H_normalizes_K F ha.1
  exact (map_mono hn).trans (le_normalizer_map _)



open Chapter1.RadicalExclusions.ModelReduction
open FullSieve.SourceInterface

/-- Literal C.2.7 parabolic placement gives the required cubic divisor.
Only the placement clause remains explicit; the K-image normalization and
intrinsic core convention are discharged here. -/
theorem fixedComponent_sectionCentralizer_three_of_core_parabolic
    (u : F.U) {Lu : Subgroup G} (h : Nonquasisimple.Case d u Lu)
    (hp : IsSp4FourMaximalParabolic
      (((F.H ⊓ Lu).subgroupOf Lu).map (QuotientGroup.mk' (pCore 2 Lu)))) :
    3 ∣ Nat.card (ChapterA.Section04.twoSectionCentralizer
      (((K F).subgroupOf Lu).map (QuotientGroup.mk' (pCore 2 Lu))) ⊤) := by
  apply Nonquasisimple.SymplecticCentralizer.three_dvd_sectionCentralizer_of_parabolic
    _ _ ?_ (d.fixedComponent_core_inter_normalizes_K_image u h) hp
  exact map_mono (subgroupOf_mono _ (le_inf (K_le_H F) h.larger.le))

/-- The new cubic divisor is applied to the original section-centralizer
exclusion, with no additional ambient lifting assumption. -/
theorem fixedComponent_false_of_core_sp4_parabolic
    (u : F.U) {Lu : Subgroup G} (h : Nonquasisimple.Case d u Lu)
    (hp : IsSp4FourMaximalParabolic
      (((F.H ⊓ Lu).subgroupOf Lu).map (QuotientGroup.mk' (pCore 2 Lu)))) : False :=
  d.fixedComponent_sectionCentralizer_image_not_three u h
    (d.fixedComponent_sectionCentralizer_three_of_core_parabolic u h hp)

/-- The star/core comparison uses the actual quotient maps. Sp₄(4) has
trivial center, so C.2.7's central kernel is trivial. -/
theorem fixedComponent_core_parabolic_of_sp4_star_parabolic
    (u : F.U) {Lu : Subgroup G} (h : Nonquasisimple.Case d u Lu)
    (hm : ChapterC.IsSp4FourBlock Lu)
    (c27 : FullSieve.SourceInterface.Conclusion KnownSimple.IsKnownSimple
      (d.fixedCentralizer u) Lu (d.fixedCore u) (F.H ⊓ d.fixedCentralizer u))
    (hp : IsSp4FourMaximalParabolic
      ((starM Lu (d.fixedCore u) (F.H ⊓ d.fixedCentralizer u)).subgroupOf
        (starImage Lu (d.fixedCore u) Lu))) :
    IsSp4FourMaximalParabolic
      (((F.H ⊓ Lu).subgroupOf Lu).map (QuotientGroup.mk' (pCore 2 Lu))) := by
  obtain ⟨_, k, _, _, hk, rho, ⟨model⟩, _⟩ := hm
  let : CharP k 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card
    (f := 2) hk
  have hz : center (Lu ⧸ pCore 2 Lu) = ⊥ := by
    apply bot_unique
    intro x hx
    have he := (centerCongr model.quotientIso ⟨x, hx⟩).property
    change model.quotientIso x ∈ center (Matrix.symplecticGroup (Fin 2) k) at he
    rw [Theory.SpecificGroups.SymplecticFour.EvenProjective.center_eq_bot,
      mem_bot] at he
    exact model.quotientIso.injective (he.trans model.quotientIso.map_one.symm)
  have hRK : d.fixedCore u ≤ normalizer (Lu : Set G) :=
    ((pCoreIn_le 2 _).trans inf_le_right).trans
      ((normal_subgroupOf_iff_le_normalizer h.le_centralizer).mp h.normal)
  have hinj : Function.Injective (coreToStar hRK) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    exact bot_unique (hz ▸ FullSieve.coreToStar_ker_le_center_of_bound hRK c27.kernel.upper)
  let e := MulEquiv.ofBijective (coreToStar hRK) ⟨hinj, coreToStar_surjective hRK⟩
  have he (x : Lu) : e (QuotientGroup.mk' (pCore 2 Lu) x) =
      toStarImage Lu (d.fixedCore u) x := rfl
  have hM : ((((F.H ⊓ Lu).subgroupOf Lu).map (QuotientGroup.mk' (pCore 2 Lu))).map
      e.toMonoidHom) =
      (starM Lu (d.fixedCore u) (F.H ⊓ d.fixedCentralizer u)).subgroupOf
        (starImage Lu (d.fixedCore u) Lu) := by
    ext x
    constructor
    · rintro ⟨y, ⟨a, ha, rfl⟩, rfl⟩
      rw [MulEquiv.coe_toMonoidHom, he]
      exact ⟨⟨(a : G), (show Lu ≤ Lu ⊔ d.fixedCore u from le_sup_left) a.property⟩,
        ⟨⟨ha.1, h.le_centralizer a.property⟩, a.property⟩, rfl⟩
    · intro hx
      obtain ⟨a, ha, haeq⟩ := hx
      let aL : Lu := ⟨(a : G), ha.2⟩
      refine ⟨QuotientGroup.mk' (pCore 2 Lu) aL, mem_map_of_mem _
        (show aL ∈ (F.H ⊓ Lu).subgroupOf Lu from ⟨ha.1.1, ha.2⟩), ?_⟩
      apply Subtype.ext
      exact haeq
  obtain ⟨k', _, _, hk', f, hf⟩ := hp
  refine ⟨k', inferInstance, inferInstance, hk', e.trans f, ?_⟩
  have hcomp : (e.trans f).toMonoidHom = f.toMonoidHom.comp e.toMonoidHom := rfl
  simpa only [hcomp, ← Subgroup.map_map, hM] using hf

/-- Full section-centralizer calculation for the symplectic branch. The
C.2.7 parabolic is an explicit input from its rank-two alternative; the
preceding theorem transports it to the original quotient through the actual
core-to-star map. -/
theorem fixedComponent_sp4_sectionCentralizer
    (u : F.U) {Lu : Subgroup G} (h : Nonquasisimple.Case d u Lu)
    (hm : ChapterC.IsSp4FourBlock Lu)
    (c27 : FullSieve.SourceInterface.Conclusion KnownSimple.IsKnownSimple
      (d.fixedCentralizer u) Lu (d.fixedCore u) (F.H ⊓ d.fixedCentralizer u))
    (hp : IsSp4FourMaximalParabolic
      ((starM Lu (d.fixedCore u) (F.H ⊓ d.fixedCentralizer u)).subgroupOf
        (starImage Lu (d.fixedCore u) Lu))) :
    3 ∣ Nat.card (ChapterA.Section04.twoSectionCentralizer
      (((K F).subgroupOf Lu).map (QuotientGroup.mk' (pCore 2 Lu))) ⊤) := by
  exact d.fixedComponent_sectionCentralizer_three_of_core_parabolic u h
    (d.fixedComponent_core_parabolic_of_sp4_star_parabolic u h hm c27 hp)

/-- Applying the preceding divisor to the original fixed-centralizer
exclusion gives the required contradiction. -/
theorem fixedComponent_sp4_contradiction
    (u : F.U) {Lu : Subgroup G} (h : Nonquasisimple.Case d u Lu)
    (hm : ChapterC.IsSp4FourBlock Lu)
    (c27 : FullSieve.SourceInterface.Conclusion KnownSimple.IsKnownSimple
      (d.fixedCentralizer u) Lu (d.fixedCore u) (F.H ⊓ d.fixedCentralizer u))
    (hp : IsSp4FourMaximalParabolic
      ((starM Lu (d.fixedCore u) (F.H ⊓ d.fixedCentralizer u)).subgroupOf
        (starImage Lu (d.fixedCore u) Lu))) : False :=
  d.fixedComponent_sectionCentralizer_image_not_three u h
    (d.fixedComponent_sp4_sectionCentralizer u h hm c27 hp)

end Data
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
