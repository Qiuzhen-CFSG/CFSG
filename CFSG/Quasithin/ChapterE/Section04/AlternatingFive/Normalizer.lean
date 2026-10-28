module
public import CFSG.Quasithin.ChapterE.Section04.AlternatingFive
public import Theory.Representation.OrthogonalFourMinusRankOne.FivePoint.Ambient
public import Theory.Representation.BinaryPermutation.Faithful

/-!
# The full normalizer of the deleted alternating-five action

The binary normalizer of A₅ acts on the same five coordinates as S₅.
The already proved five-point fixed-space calculation therefore bounds its
parameter by one, including all outer actors.
Source: Aschbacher–Smith, 10.2.12, printed p.754.
-/

public noncomputable section
open Subgroup BinaryPermutation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterE

theorem moduleA_fiveDeleted_normalizer_le_one :
    moduleA (normalizerRepresentation ((naturalRepresentation (Fin 5)).comp
      (alternatingGroup (Fin 5)).subtype)) ≤ 1 := by
  let σ : Representation (ZMod 2) (alternatingGroup (Fin 5)) (natural (Fin 5)) := (naturalRepresentation (Fin 5)).comp (alternatingGroup (Fin 5)).subtype
  let J := actionImage σ
  let K := J.subgroupOf (linearNormalizer σ)
  let τ := normalizerRepresentation σ
  have hσ : Function.Injective σ.asGroupHom := by
    intro a b h
    apply Subtype.ext
    exact naturalRepresentation_injective (Fin 5) (by decide) (congrArg Units.val h)
  let e₀ : alternatingGroup (Fin 5) ≃* J := MonoidHom.ofInjective hσ
  let e : K ≃* alternatingGroup (Fin 5) :=
    (subgroupOfEquivOfLe J.le_normalizer).trans e₀.symm
  let : K.Normal := J.normal_in_normalizer
  have hf : Function.Injective τ := by
    intro a b h
    exact Subtype.ext (Units.ext h)
  have he (k : K) (v : natural (Fin 5)) :
      τ k.val v = naturalRepresentation (Fin 5) (e k).val v := by
    have hh := e₀.apply_symm_apply ((subgroupOfEquivOfLe J.le_normalizer) k)
    exact (congrArg (fun u : J => u.val.val v) hh).symm
  obtain ⟨p,hp,hact,_⟩ :=
    Representation.OrthogonalFourMinus.FivePoint.exists_ambient_permutation
      τ K e (LinearEquiv.refl _ _) he hf
  exact moduleA_le_one_of_fiveNatural τ p hp (LinearEquiv.refl _ _) hact
end CFSG.Quasithin.ChapterE
