module
public import CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuHermitianCubicCentralizer
public import CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuHermitianRadicalControl
public import Theory.GroupTheory.QuasisimpleNineSpaceKernel
import all CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.HallFaithfulness.SmallRadical

/-!
# The original Hermitian residual has no central covering ambiguity

Transport the actual nine-space and intersection residual through the same
ordinary J₄ cover. The native cubic-centralizer bound makes the nine-space's
full pointwise centralizer three-free. Irreducibility descends through these
literal maps, so the normal nine-space theorem kills the center of the
residual's two-core quotient. The established quotient correspondence then
kills the center of the original L/O₂(L) as well, and gives an actual
PSL₃(4) equivalence for the native residual quotient.

Every SQTK premise on J₄ is transported from the original component of
the pushing-up witness. No central kernel is dropped before it is proved
trivial; in particular a projective marking alone is not used as a simple
quotient marking. The subsequent full-radical action uses this result.
Source: Aschbacher--Smith 4.2.13, printed p.612, as used in 8.2.7, p.718,
refs/quasithin.pdf. Native model facts retain their imported attribution.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

private theorem native_sqtk {K : Type*} [Group K] [Finite K]
    (hK : IsSQTK KnownSimple.IsKnownSimple K)
    (e : (K ⧸ center K) ≃* Janko4.Model) (hZ : IsPGroup 2 (center K)) :
    IsSQTK KnownSimple.IsKnownSimple Janko4.Model := by
  refine ⟨?_,?_⟩
  · intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    rw [←primeRank_equiv p e]
    exact (primeRank_quotient_le_of_isTwoGroup p ho (center K) hZ).trans
      (hK.stronglyQuasithin p hp ho)
  · intro Y _ hY U g hg
    let := hY
    let f := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
    let W := U.comap f
    let r := g.comp (f.subgroupComap U)
    have hr : Function.Surjective r := hg.comp (f.subgroupComap_surjective_of_surjective U
      (e.surjective.comp (QuotientGroup.mk'_surjective _)))
    let a := QuotientGroup.quotientKerEquivOfSurjective r hr
    let : IsSimpleGroup (W ⧸ r.ker) := a.isSimpleGroup
    exact (hK.isKGroup (W ⧸ r.ker) inferInstance W (QuotientGroup.mk' r.ker)
      (QuotientGroup.mk'_surjective _)).of_mulEquiv a.symm

/-- Remove the full odd central kernel on the literal native and original quotients. -/
theorem sourceOrbit_hermitian_ordinary_center_kernel_of_card
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hfix : V ⊓ centralizer (L : Set G) = ⊥) (hcardV : Nat.card V = 512)
    {k : Type*} [Field k] [Finite k]
    (eQ : (D.orbitComponent ⧸ center D.orbitComponent) ≃* PSL(3,k))
    (hfield : Nat.card k = 4)
    {A J H W : Subgroup G} (hw : Witness L V A J H W)
    (K : Subgroup H) (hK : IsComponent H K)
    (e : (K ⧸ center K) ≃* Janko4.Model) :
    let j := H.subtype.comp K.subtype
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
    let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    let E := (V.comap j).map q
    let B := (F.comap j).map q
    (¬ 3 ∣ Nat.card (centralizer (E : Set Janko4.Model))) ∧
      center (B ⧸ pCore 2 B) = ⊥ ∧ center (L ⧸ pCore 2 L) = ⊥ ∧
      Nonempty ((B ⧸ pCore 2 B) ≃* PSL(3,k)) := by
  let j := H.subtype.comp K.subtype
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  let E := (V.comap j).map q
  let B := (F.comap j).map q
  have hc := hw.2.2.2.2.2.2.1
  let := hK.2
  have hZ : IsPGroup 2 (center K) := by
    rw [IsQuasisimple.center_eq_pCore (hK.1.pPrimeCore_eq_bot hc.oddCore_eq_bot K)]
    exact pCore_isPGroup
  have hs := native_sqtk (hc.sqtk.subgroup K) e hZ
  have hn := D.sourceOrbit_pushingUp_native_radical hfix hw K hK e
  dsimp only at hn
  have hBE : B ≤ normalizer (E : Set Janko4.Model) := hn.2.2.2.2.1
  let : IsElementaryAbelian 2 E := hn.2.2.2.2.2.2.1
  have hcard : Nat.card E = 512 := hn.2.2.2.2.2.2.2.1.trans hcardV
  let a : (B ⧸ pCore 2 B) ≃* (L ⧸ pCore 2 L) := hn.2.2.2.2.2.2.2.2.some
  let eq : ((B ⧸ pCore 2 B) ⧸ center (B ⧸ pCore 2 B)) ≃* PSL(3,k) :=
    ((centerQuotientCongr a).trans (D.orbitCentralQuotientEquiv h)).trans eQ
  have h3 : ¬ 3 ∣ Nat.card (centralizer (E : Set Janko4.Model)) :=
    hermitian_janko_large_elementary_centralizer_three_free hs E (by rw [hcard]; decide)
  have hEB : E ≤ B := map_mono (comap_mono hw.2.2.2.2.2.2.2.2.2.2.1)
  let Ec := E.subgroupOf B
  let : Ec.Normal := normal_subgroupOf_of_le_normalizer hBE
  let : IsElementaryAbelian 2 Ec := IsElementaryAbelian.subgroupOf hEB
  have hirr := D.sourceOrbit_pushingUp_native_irreducible hfix hw K hK e
  have hirrc (X : Subgroup B) (hXE : X ≤ Ec) (hnX : X.Normal) : X = ⊥ ∨ X = Ec := by
    have hXE' : X.map B.subtype ≤ E :=
      (map_mono hXE).trans_eq (map_subgroupOf_eq_of_le hEB)
    have hBX : B ≤ normalizer (X.map B.subtype : Set Janko4.Model) := by
      apply le_normalizer_iff.mpr
      intro b hb x hx
      obtain ⟨x,hx,rfl⟩ := hx
      exact ⟨⟨b,hb⟩*x*⟨b,hb⟩⁻¹,hnX.conj_mem x hx ⟨b,hb⟩,rfl⟩
    rcases hirr _ hXE' hBX with hX | hX
    · exact .inl ((X.map_eq_bot_iff_of_injective B.subtype_injective).mp hX)
    · exact .inr (map_injective B.subtype_injective
        (hX.trans (map_subgroupOf_eq_of_le hEB).symm))
  have h3c : ¬ 3 ∣ Nat.card (centralizer (Ec : Set B)) := by
    let f : centralizer (Ec : Set B) →* centralizer (E : Set Janko4.Model) := {
      toFun b := ⟨b.val.val, fun v hv =>
        congrArg B.subtype (b.property ⟨v,hEB hv⟩ hv)⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
    have hf : Function.Injective f := fun x y he => Subtype.ext (Subtype.ext
      (congrArg (fun z : centralizer (E : Set Janko4.Model) => (z : Janko4.Model)) he))
    exact fun hd => h3 (hd.trans (card_dvd_of_injective f hf))
  let := h.quasisimple
  let : IsQuasisimple (B ⧸ pCore 2 B) := IsQuasisimple.of_mulEquiv a.symm
  have hb := psl3_four_twoCore_center_eq_bot_of_nineSpace Ec
    (IsElementaryAbelian.isPGroup 2 Ec) hirrc
    ((Nat.card_congr (subgroupOfEquivOfLe hEB).toEquiv).trans hcard) h3c hfield eq
  have hl : center (L ⧸ pCore 2 L) = ⊥ := by
    apply card_eq_one.mp
    rw [←Nat.card_congr (centerCongr a).toEquiv,hb,card_bot]
  exact ⟨h3,hb,hl,⟨((QuotientGroup.quotientMulEquivOfEq hb).trans
    QuotientGroup.quotientBot).symm.trans eq⟩⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
