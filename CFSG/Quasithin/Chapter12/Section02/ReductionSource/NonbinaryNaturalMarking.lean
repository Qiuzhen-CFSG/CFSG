module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonbinaryNaturalInput
public import Theory.Representation.GeneralLinearNatural
public import Theory.Representation.G2NaturalFaithfulness

/-!
# Full natural markings for the original nonbinary quotient

The natural actions of SL₃, rank-two Sp₄ and the concrete octonion G₂
are faithful without a simplicity assumption. Their intertwiners therefore
detect the kernel of the original chosen action, including the retained
center of SL₃(4).

A source marking on L/N transfers along the explicit equality N=O₂(L).
The induced group equivalence agrees with the original quotient projection,
and the binary intertwiner is unchanged. The final constructor applies this
to the three natural rows of 3.2.8 on D.space's literal fixed-space quotient,
retaining FF, Sylow normalization, the field degree and hmany.

This does not prove the source equality C_L(V)=O₂(L) from a marking only of
L/C_L(V). That equality remains an input of the quotient-transfer application,
owned by qt-d-1222-modules. Kernel detection from a full L/O₂(L) marking is
a separate consequence and must not be used circularly to produce that marking.
Source: Aschbacher--Smith, 3.2.8(2--4), 11.0.2 and 12.2.2,
refs/quasithin.pdf, printed pp.582,759--760,795.
-/

@[expose] public noncomputable section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)

private theorem faithful_of_marking {J W : Type*} [Group J]
    [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) J W}
    (m : ActionEquiv D.centralQuotientAction ρ) (hρ : Function.Injective ρ) :
    Function.Injective D.centralQuotientAction := by
  intro a b hab
  apply m.groupEquiv.injective
  apply hρ
  apply LinearMap.ext
  intro w
  obtain ⟨v, rfl⟩ := m.linearEquiv.surjective w
  rw [← m.intertwines, ← m.intertwines, hab]

/-- Every retained full natural marking is faithful, including full SL₃(4). -/
theorem centralQuotientAction_injective_of_natural {F : BinaryField}
    (h : D.NaturalRankTwoAction F) : Function.Injective D.centralQuotientAction := by
  cases h with
  | sl3 h =>
    apply faithful_of_marking D h.some
    intro a b hab
    apply specialLinearNatural_injective 3
    apply LinearMap.ext
    intro v
    exact LinearMap.congr_fun hab v
  | sp4 h =>
    apply faithful_of_marking D h.some
    intro a b hab
    apply Subtype.ext
    ext i j
    have hv := congrFun (LinearMap.congr_fun hab (Pi.single j 1)) i
    simpa [restrictScalars, symplecticNatural, Matrix.mulVec_single] using hv
  | g2 h =>
    apply faithful_of_marking D h.some
    intro a b hab
    apply Atlas.G2.Natural.action_injective F.Carrier
    apply LinearMap.ext
    intro v
    exact LinearMap.congr_fun hab v

/-- The faithful action of the full two-core quotient gives its exact kernel. -/
theorem centralAction_ker_eq_core_of_faithful
    (hf : Function.Injective D.centralQuotientAction) :
    D.chosenCentralAction.ker = pCore 2 L := by
  apply le_antisymm _ D.centralAction_core
  intro l hl
  apply (QuotientGroup.eq_one_iff l).mp
  apply hf
  change D.centralQuotientAction (QuotientGroup.mk' (pCore 2 L) l) =
    D.centralQuotientAction 1
  rw [D.centralQuotientAction_mk, map_one]
  exact hl

/-- Kernel detection on the actual V, without requiring a simple actor. -/
theorem centralizer_eq_core_of_faithful
    (hf : Function.Injective D.centralQuotientAction) :
    (centralizer (V : Set G)).subgroupOf L = pCore 2 L := by
  apply le_antisymm
  · intro l hl
    apply (D.centralAction_ker_eq_core_of_faithful hf).le
    apply LinearMap.ext
    intro q
    induction q using Submodule.Quotient.induction_on with
    | _ v =>
      have hv : (v.val.toMul.val : G) ∈ V :=
        D.image_eq.le (mem_map_of_mem _ (mem_map_of_mem _ v.property))
      have hc : D.chosenAction l v = v := by
        apply Subtype.ext
        apply Additive.toMul.injective
        apply Subtype.ext
        apply Subtype.ext
        change (l : G) * (v.val.toMul.val : G) * (l : G)⁻¹ = (v.val.toMul.val : G)
        exact mul_inv_eq_iff_eq_mul.mpr ((mem_centralizer_iff.mp hl) _ hv).symm
      change Submodule.Quotient.mk (D.chosenAction l v) = Submodule.Quotient.mk v
      rw [hc]
  · intro l hl
    apply mem_centralizer_iff.mpr
    intro v hv
    obtain ⟨v', hv'⟩ := D.spaceEquiv.surjective ⟨v, hv⟩
    have hh := LinearMap.congr_fun (show D.chosenAction l = 1 from
      D.chosenAction_core hl) v'.toAdd
    have he := congrArg (fun w : D.space => (w.val.toMul.val : G)) hh
    have hv'' : (v'.toAdd.val.toMul.val : G) = v :=
      (D.spaceEquiv_apply v'.toAdd).symm.trans (congrArg Subtype.val hv')
    change (l : G) * (v'.toAdd.val.toMul.val : G) * (l : G)⁻¹ =
      (v'.toAdd.val.toMul.val : G) at he
    rw [hv''] at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm

/-- Transport a marking along equality of the literal quotient kernels. -/
noncomputable def centralQuotientMarkingOfKernel
    {N : Subgroup L} [N.Normal]
    (ρ : Representation (ZMod 2) (L ⧸ N) D.chosenCentralQuotient)
    (hρ : ∀ l : L, ρ (QuotientGroup.mk' N l) = D.chosenCentralAction l)
    (hN : N = pCore 2 L)
    {J W : Type*} [Group J] [AddCommGroup W] [Module (ZMod 2) W]
    {σ : Representation (ZMod 2) J W} (m : ActionEquiv ρ σ) :
    ActionEquiv D.centralQuotientAction σ where
  groupEquiv := (QuotientGroup.quotientMulEquivOfEq hN.symm).trans m.groupEquiv
  linearEquiv := m.linearEquiv
  intertwines q v := by
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) q
    change m.linearEquiv (D.chosenCentralAction l v) =
      σ (m.groupEquiv (QuotientGroup.mk' N l)) (m.linearEquiv v)
    rw [← hρ]
    exact m.intertwines _ v

/-- A marked natural source quotient transfers to the original two-core quotient. -/
theorem naturalRankTwoAction_of_quotient {N : Subgroup L} [N.Normal]
    (ρ : Representation (ZMod 2) (L ⧸ N) D.chosenCentralQuotient)
    (hρ : ∀ l : L, ρ (QuotientGroup.mk' N l) = D.chosenCentralAction l)
    (hN : N = pCore 2 L) (F : BinaryField)
    (hm : Nonempty (ActionEquiv ρ (linearNatural F 3)) ∨
      Nonempty (ActionEquiv ρ
        (restrictScalars (k := ZMod 2) (symplecticNatural (k := F.Carrier) 2))) ∨
      Nonempty (ActionEquiv ρ
        (restrictScalars (k := ZMod 2) (g2Natural F.Carrier)))) :
    D.NaturalRankTwoAction F := by
  rcases hm with m | m | m
  · exact .sl3 ⟨D.centralQuotientMarkingOfKernel ρ hρ hN m.some⟩
  · exact .sp4 ⟨D.centralQuotientMarkingOfKernel ρ hρ hN m.some⟩
  · exact .g2 ⟨D.centralQuotientMarkingOfKernel ρ hρ hN m.some⟩

/-- The nonbinary input needs no separate simplicity or faithfulness premise
once the full marked natural action has been supplied. -/
def nonbinaryNaturalInputOfNatural_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnorm : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hff : IsFFModule (normalizerRepresentation D.chosenAction))
    (F : BinaryField) (hF : 1 < F.degree) (hm : D.NaturalRankTwoAction F) :
    D.NonbinaryNaturalInput where
  source := h
  many := hmany
  sylow_normalizes := hnorm
  ff := hff
  field := F
  nonbinary := hF
  faithful := D.centralQuotientAction_injective_of_natural hm
  natural := hm

/-- The full natural marking detects the centralizer of the original seed. -/
theorem centralizer_eq_core_of_natural {F : BinaryField}
    (hm : D.NaturalRankTwoAction F) :
    (centralizer (V : Set G)).subgroupOf L = pCore 2 L :=
  D.centralizer_eq_core_of_faithful (D.centralQuotientAction_injective_of_natural hm)

/-- Application to the three source 3.2.8 natural rows. The source kernel
identity is explicit and is not deduced from a projective marking. -/
def nonbinaryNaturalInputOfSourceQuotient_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnorm : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hff : IsFFModule (normalizerRepresentation D.chosenAction))
    {N : Subgroup L} [N.Normal]
    (ρ : Representation (ZMod 2) (L ⧸ N) D.chosenCentralQuotient)
    (hρ : ∀ l : L, ρ (QuotientGroup.mk' N l) = D.chosenCentralAction l)
    (hN : N = pCore 2 L) (F : BinaryField) (hF : 1 < F.degree)
    (hm : Nonempty (ActionEquiv ρ (linearNatural F 3)) ∨
      Nonempty (ActionEquiv ρ
        (restrictScalars (k := ZMod 2) (symplecticNatural (k := F.Carrier) 2))) ∨
      Nonempty (ActionEquiv ρ
        (restrictScalars (k := ZMod 2) (g2Natural F.Carrier)))) :
    D.NonbinaryNaturalInput :=
  D.nonbinaryNaturalInputOfNatural_of_many h hmany hnorm hff F hF
    (D.naturalRankTwoAction_of_quotient ρ hρ hN F hm)

/-- The transported full actor marking uses the original quotient projection. -/
theorem centralQuotientMarkingOfKernel_mk
    {N : Subgroup L} [N.Normal]
    (ρ : Representation (ZMod 2) (L ⧸ N) D.chosenCentralQuotient)
    (hρ : ∀ l : L, ρ (QuotientGroup.mk' N l) = D.chosenCentralAction l)
    (hN : N = pCore 2 L)
    {J W : Type*} [Group J] [AddCommGroup W] [Module (ZMod 2) W]
    {σ : Representation (ZMod 2) J W} (m : ActionEquiv ρ σ) (l : L) :
    (D.centralQuotientMarkingOfKernel ρ hρ hN m).groupEquiv
      (QuotientGroup.mk' (pCore 2 L) l) = m.groupEquiv (QuotientGroup.mk' N l) := rfl

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
