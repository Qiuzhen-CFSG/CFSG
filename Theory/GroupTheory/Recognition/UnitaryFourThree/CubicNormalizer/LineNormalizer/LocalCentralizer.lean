module

public import Theory.GroupTheory.NormalizerProductCentralizer
public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicNormalizer.LineNormalizer.FixedCore
public import Theory.GroupTheory.Recognition.UnitaryFourThree.RootPair.ReflectedMarking.LocalNormalizer

/-!
# Local centralizer control of the reflected cubic

Frattini gives H=Q N_H(X).  The reflected line U=C_X(t) has C_Q(U)=⟨z⟩,
and Q∩X=1.  Hence every H-element centralizing U normalizes X.  The proof
uses the original H, Q and X, with no local-normalizer assumption.

Source: Aschbacher, *Sporadic Groups* (1994),45.7(1),printed p.245.
-/

public section
open Subgroup
namespace Theory.GroupTheory.Recognition.UnitaryFourThree.IsType
variable {G : Type*} [Group G] [Finite G] {z : G}

theorem reflected_line_centralizer_le (h : IsType z)
    (P : Sylow 3 (centralizer z))
    (m : CubicNormalizer.ReflectedMarking z
      ((P : Subgroup (centralizer z)).map (centralizer z).subtype))
    (htB : h.toCentralizerHypothesis.factorData.leftCore.map
      (MulAut.conj m.t).toMonoidHom = h.toCentralizerHypothesis.factorData.rightCore)
    (htC : h.toCentralizerHypothesis.factorData.rightCore.map
      (MulAut.conj m.t).toMonoidHom = h.toCentralizerHypothesis.factorData.leftCore) :
    centralizer z ⊓ Subgroup.centralizer
      (((P : Subgroup (centralizer z)).map (centralizer z).subtype ⊓
        Subgroup.centralizer ({m.t} : Set G) : Subgroup G) : Set G) ≤
      normalizer ((P : Subgroup (centralizer z)).map (centralizer z).subtype : Set G) := by
  let X := (P : Subgroup (centralizer z)).map (centralizer z).subtype
  let U := X ⊓ Subgroup.centralizer ({m.t} : Set G)
  have hX : Nat.card X=9 := h.cubic_sylow_image_card P
  have hXH : X≤centralizer z := map_subtype_le _
  apply centralizer_le_of_normalizer_product (centralizer z) (core z) X U
    CentralizerHypothesis.centralizer_normalizes_core hXH inf_le_left
    (disjoint_of_coprime_natCard (by rw [h.toCentralizerHypothesis.core_card,hX];decide)).eq_bot
    (h.centralizer_eq_core_sup_cubic_normalizer X hX hXH)
  rw [h.reflected_line_core_centralizer P m htB htC]
  apply (zpowers_le.mpr ?_).trans (centralizer_le_normalizer _)
  exact fun x hx => mem_centralizer_singleton_iff.mp (hXH hx)

/-- The original line has the same local normalizer as the Sylow nine. -/
theorem reflected_line_normalizer_eq (h : IsType z)
    (P : Sylow 3 (centralizer z))
    (m : CubicNormalizer.ReflectedMarking z
      ((P : Subgroup (centralizer z)).map (centralizer z).subtype))
    (htB : h.toCentralizerHypothesis.factorData.leftCore.map
      (MulAut.conj m.t).toMonoidHom = h.toCentralizerHypothesis.factorData.rightCore)
    (htC : h.toCentralizerHypothesis.factorData.rightCore.map
      (MulAut.conj m.t).toMonoidHom = h.toCentralizerHypothesis.factorData.leftCore) :
    centralizer z ⊓ normalizer
      (((P : Subgroup (centralizer z)).map (centralizer z).subtype ⊓
        Subgroup.centralizer ({m.t} : Set G) : Subgroup G) : Set G) =
      centralizer z ⊓ normalizer
        ((P : Subgroup (centralizer z)).map (centralizer z).subtype : Set G) := by
  let X := (P : Subgroup (centralizer z)).map (centralizer z).subtype
  let U := X ⊓ Subgroup.centralizer ({m.t} : Set G)
  have htH : m.t∈centralizer z := mem_centralizer_singleton_iff.mpr m.zt_commute.symm.eq
  have hsH : m.s∈centralizer z := by
    simpa only [mul_inv_cancel_right] using (centralizer z).mul_mem m.rotation_centralizes
      ((centralizer z).inv_mem htH)
  have hsinv : ∀u∈U,m.s*u*m.s⁻¹=u⁻¹ := by
    intro u hu
    have htfix : m.t*u*m.t⁻¹=u :=
      mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hu.2).symm
    calc
      m.s*u*m.s⁻¹=m.s*(m.t*u*m.t⁻¹)*m.s⁻¹ := congrArg (fun x:G=>m.s*x*m.s⁻¹) htfix.symm
      _ = (m.s*m.t)*u*(m.s*m.t)⁻¹ := by group
      _ = u⁻¹ := m.rotation_inverts u hu.1
  have hle := normalizer_le_of_cubic_inverter_centralizer (centralizer z)
    (normalizer (X:Set G)) U m.common_fixed_card m.s hsH m.s_normalizes hsinv
    (h.reflected_line_centralizer_le P m htB htC)
  apply le_antisymm (le_inf inf_le_left hle)
  refine le_inf inf_le_left ?_
  apply normalizes_fixed_of_square_centralizes (centralizer z⊓normalizer (X:Set G)) X inf_le_right
  · intro n hn
    exact h.cubic_normalizer_square_centralizes X (h.cubic_sylow_image_card P)
      (map_subtype_le _) n ⟨hn.2,hn.1⟩
  · exact ⟨htH,m.t_normalizes⟩

/-- The local reflected-line normalizer has its source order seventy-two. -/
theorem reflected_line_local_normalizer_card (h : IsType z)
    (P : Sylow 3 (centralizer z))
    (m : CubicNormalizer.ReflectedMarking z
      ((P : Subgroup (centralizer z)).map (centralizer z).subtype))
    (htB : h.toCentralizerHypothesis.factorData.leftCore.map
      (MulAut.conj m.t).toMonoidHom = h.toCentralizerHypothesis.factorData.rightCore)
    (htC : h.toCentralizerHypothesis.factorData.rightCore.map
      (MulAut.conj m.t).toMonoidHom = h.toCentralizerHypothesis.factorData.leftCore) :
    Nat.card (centralizer z ⊓ normalizer
      (((P : Subgroup (centralizer z)).map (centralizer z).subtype ⊓
        Subgroup.centralizer ({m.t} : Set G) : Subgroup G) : Set G) : Subgroup G) = 72 := by
  rw [h.reflected_line_normalizer_eq P m htB htC]
  exact h.cubic_local_normalizer_card _ (h.cubic_sylow_image_card P) (map_subtype_le _)

end Theory.GroupTheory.Recognition.UnitaryFourThree.IsType
