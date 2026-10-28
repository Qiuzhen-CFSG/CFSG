module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryCoreEnlargement.SourceKernel
public import Theory.Representation.SL3.AdjointCubicCentralizer.GraphExtension.FrattiniDescent

/-!
# Descent of the fully marked Frattini action through the source kernel

An element trivial on the component quotient commutes with its action on a
fully marked adjoint module. The binary commutant theorem makes that element
an F₄ scalar, so its module action has order dividing three. The proved
prime-to-three order of the actual source kernel forces that action to be
trivial. All coordinates and the original component quotient map are retained.

The full Frattini marking remains an explicit source premise. This result
removes scalar compensation once that marking has been constructed.
Source: Aschbacher–Smith A.3.18, B.4.14 and the terminal argument for original
4.3.2, printed pp.51–53,98,618–619.
-/

public noncomputable section
open Subgroup Matrix Representation
open scoped MatrixGroups
open Representation.SL3.AdjointCubicCentralizer
open Representation.SL3.AdjointCubicCentralizer.GraphExtension
open Representation.SL3.AdjointCubicCentralizer.GraphExtension.FrattiniDescent
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
attribute [local instance] ZMod.algebra
set_option backward.isDefEq.respectTransparency false

private theorem adjoint_commuting_aut_cube
    {F W : Type*} [Field F] [Finite F] [CharP F 2] [Group W]
    (hF : Nat.card F = 4) (e : W ≃* Multiplicative (TraceZero F))
    (a : MulAut W)
    (ha : ∀ (g : PSL(3,F)) v,
      (e (a (e.symm (Multiplicative.ofAdd (projectiveSpecialAdjoint F g v))))).toAdd =
        projectiveSpecialAdjoint F g (e (a (e.symm (Multiplicative.ofAdd v)))).toAdd) :
    a ^ 3 = 1 := by
  let f : Module.End (ZMod 2) (TraceZero F) :=
    (AddMonoidHom.toMultiplicative.symm (MulAut.congr e a).toMonoidHom).toZModLinearMap 2
  obtain ⟨c,hc⟩ := commutant_scalar F hF f ha
  have hc' (w : W) : (e (a w)).toAdd = c • (e w).toAdd := by
    have hh := hc (e w).toAdd
    change (e (a (e.symm (e w)))).toAdd = _ at hh
    rwa [e.symm_apply_apply] at hh
  have hn : c ≠ 0 := by
    intro hz
    have hh := hc (highestRoot F)
    rw [hz,zero_smul] at hh
    have hi : Function.Injective f := (MulAut.congr e a).injective
    exact highestRoot_ne_zero F (hi (hh.trans (map_zero f).symm))
  have hcube : c ^ 3 = 1 := by
    exact congrArg Units.val (units_cube_of_card_four F hF (Units.mk0 c hn))
  apply MulEquiv.ext
  intro w
  apply e.injective
  apply Multiplicative.toAdd.injective
  change (e (a (a (a w)))).toAdd = (e w).toAdd
  rw [hc',hc',hc',smul_smul,smul_smul,←pow_two,←pow_succ,hcube,one_smul]

private theorem full_adjoint_action_kernel_le
    {N F W : Type*} [Group N] [Finite N] [Field F] [Finite F] [CharP F 2] [Group W]
    (B : Subgroup N) [B.Normal]
    (hF : Nat.card F = 4)
    (mark : (B ⧸ pCore 2 B) ≃* PSL(3,F))
    (α : N →* MulAut W) (e : W ≃* Multiplicative (TraceZero F))
    (he : ∀ (b : B) w, (e (α (b : N) w)).toAdd =
      projectiveSpecialAdjoint F (mark (QuotientGroup.mk' (pCore 2 B) b)) (e w).toAdd)
    (hcop : Nat.Coprime 3 (Nat.card (normalQuotientAction B (pCore 2 B)).ker)) :
    (normalQuotientAction B (pCore 2 B)).ker ≤ α.ker := by
  let f := normalQuotientAction B (pCore 2 B)
  intro k hk
  have hcomm (b : B) : α k * α (b : N) = α (b : N) * α k := by
    let b' : B := MulAut.conjNormal k b
    have hq : QuotientGroup.mk' (pCore 2 B) b' = QuotientGroup.mk' (pCore 2 B) b := by
      have hh := DFunLike.congr_fun (show f k = 1 from hk) (QuotientGroup.mk' (pCore 2 B) b)
      simpa only [f,normalQuotientAction_apply_mk,MulAut.one_apply] using hh
    have hb : α (b' : N) = α (b : N) := by
      ext w
      apply e.injective
      apply Multiplicative.toAdd.injective
      rw [he,he,hq]
    calc
      α k * α (b : N) = α ((b' : N) * k) := by
        rw [←map_mul]
        congr 1
        change k * (b : N) = (k * (b : N) * k⁻¹) * k
        group
      _ = α (b : N) * α k := by rw [map_mul,hb]
  have ha3 : (α k)^3 = 1 := adjoint_commuting_aut_cube hF e (α k) (by
    intro g v
    obtain ⟨z,rfl⟩ := mark.surjective g
    obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 B) z
    let w := e.symm (Multiplicative.ofAdd v)
    have hw : (e w).toAdd = v := congrArg Multiplicative.toAdd (e.apply_symm_apply _)
    have hb := he b w
    rw [hw] at hb
    have hbw : e.symm (Multiplicative.ofAdd
        (projectiveSpecialAdjoint F (mark (QuotientGroup.mk' _ b)) v)) = α (b : N) w := by
      apply e.injective
      rw [e.apply_symm_apply]
      exact Multiplicative.toAdd.injective hb.symm
    rw [hbw]
    have hh := DFunLike.congr_fun (hcomm b) w
    change α k (α (b : N) w) = α (b : N) (α k w) at hh
    rw [hh,he])
  have hd : orderOf (α k) ∣ Nat.card f.ker :=
    (orderOf_map_dvd (α.comp f.ker.subtype) (⟨k,hk⟩ : f.ker)).trans (orderOf_dvd_natCard _)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop
    (orderOf_dvd_of_pow_eq_one ha3) hd)


variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]
  {T : Sylow 2 G} {L V : Subgroup G} {c : SourceConfiguration T L} {n : ℕ}
attribute [local instance] SecondaryActionData.normal

/-- The whole marked Frattini action kills the original quotient-action kernel.
The field transport used to count that kernel does not change the given module
coordinates or the component marking in the equivariance equation. -/
theorem SecondaryActionData.action_kernel_le_frattini_kernel
    (s : SecondaryActionData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hF : Nat.card F = 4)
    (mark : (s.component ⧸ pCore 2 s.component) ≃* PSL(3,F))
    (e : Frattini s.component ≃* Multiplicative (TraceZero F))
    (he : ∀ (b : s.component) v,
      (e (coreAction s.component (b : rootNormalizer c) v)).toAdd =
        projectiveSpecialAdjoint F (mark (QuotientGroup.mk' (pCore 2 s.component) b))
          (e v).toAdd) :
    s.action.ker ≤ (coreAction s.component).ker := by
  let : Fintype F := Fintype.ofFinite F
  let : Fintype Matrix.PSL3Four.F := Fintype.ofFinite _
  let i : F ≃+* Matrix.PSL3Four.F := FiniteField.ringEquivOfCardEq (by
    rw [←Nat.card_eq_fintype_card,←Nat.card_eq_fintype_card,hF,Matrix.PSL3Four.card_F])
  exact full_adjoint_action_kernel_le s.component hF mark (coreAction s.component) e he
    (s.action_kernel_coprime_three D h (mark.trans (Atlas.fieldEquivPSL 3 i)))

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
