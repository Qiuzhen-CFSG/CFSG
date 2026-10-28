module
public import CFSG.Quasithin.ChapterD.Section02.Conjugacy
public import CFSG.Quasithin.ChapterD.Section02.QuadraticOrbit
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.OriginalModule.Exchanged.SourceGeometry

/-!
# A minimum-ratio actor on the selected exchanged component

Select a minimum-ratio subgroup of the original quadratic actor. It cannot
centralize both components. If it centralizes the selected one, conjugate
it by the given exchanger. The component return identity makes its Sylow
normalizer stable under that conjugation; the quadratic ratio is unchanged.

Source: Aschbacher–Smith D.2.5 and F.9.18(3–4), applied in 15.3.65, p.1152.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.OriginalModule.Exchanged
open RepresentationReduction.SourceRestrictions.Cases.Exchanged
variable {D V : Type*} [Group D] [Finite D]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) D V) {K K₀ T B C A : Subgroup D}

omit [Finite D] [FiniteDimensional (ZMod 2) V] in
private theorem quadratic_conjugate {A : Subgroup D} (hq : IsQuadratic ρ A) (g : D) :
    IsQuadratic ρ (A.conjBy g) := by
  rintro _ ⟨a,ha,rfl⟩ _ ⟨b,hb,rfl⟩ v
  change ρ (g*a*g⁻¹) (ρ (g*b*g⁻¹) v-v) = ρ (g*b*g⁻¹) v-v
  have hh := congrArg (ρ g) (hq a ha b hb (ρ g⁻¹ v))
  simpa only [map_mul,Module.End.mul_apply,map_sub,ρ.inv_self_apply,
    ρ.self_inv_apply] using hh

omit [Finite D] in
private theorem preserving_conjugate_mem_normalizer
    (geo : ExchangedGeometry K K₀ T B C) {t c : D}
    (ht : t ∈ T) (hc : c ∈ T) (hn : c ∈ normalizer (K : Set D)) :
    t*c*t⁻¹ ∈ normalizer (K : Set D) := by
  let N := normalizer (K : Set D)
  have hsq {s : D} (hs : s ∈ T) : s^2 ∈ N := by
    by_cases hn : s ∈ N
    · exact N.pow_mem hn 2
    · have hret := (geo.pair s hs hn).2.2.2.1
      have he := congrArg (fun U : Subgroup D => U.conjBy s) hret
      rw [conjBy_conjBy,conjBy_conjBy,mul_inv_cancel,conjBy_one] at he
      apply mem_normalizer_iff_map_conj_eq.mpr
      simpa only [pow_two,conjBy,MulEquiv.toMonoidHom_eq_coe] using he
  have he : (t*c)^2*c⁻¹*(t^2)⁻¹ = t*c*t⁻¹ := by simp [pow_two,mul_assoc]
  rw [← he]
  exact N.mul_mem (N.mul_mem (hsq (T.mul_mem ht hc)) (N.inv_mem hn)) (N.inv_mem (hsq ht))

/-- A placed quadratic actor supplies a minimum-ratio quadratic subgroup
which preserves and acts nontrivially on the specified component. -/
theorem exists_minimal_actor_on_component
    (geo : ExchangedGeometry K K₀ T B C) (hAT : A ≤ T)
    (hA : IsElementaryTwo A) (hq : IsQuadratic ρ A)
    (hd : fixedCodim ρ A ≤ 2 * rank A)
    (hAC : A ⊓ centralizer (K₀ : Set D) = ⊥)
    (hp : A ≤ normalizer (K : Set D)) :
    ∃ J, J ≤ normalizer (K : Set D) ∧ ¬J ≤ centralizer (K : Set D) ∧
      J ∈ ChapterD.RPlusBound ρ 2 ∧ IsQuadratic ρ J := by
  obtain ⟨J,hJA,hJ⟩ := ChapterD.exists_RPlusBound_subgroup ρ hA
    ((actionRatio_le_nat_iff ρ hA 2).mpr hd)
  have hqJ : IsQuadratic ρ J := fun a ha b hb v => hq a (hJA ha) b (hJA hb) v
  have hn0 : ¬J ≤ centralizer (K₀ : Set D) := by
    intro hj
    apply hJ.1.1.1
    exact le_bot_iff.mp ((le_inf hJA hj).trans_eq hAC)
  by_cases hn : J ≤ centralizer (K : Set D)
  · obtain ⟨t,ht,hout⟩ := geo.moved
    have hpair := (geo.pair t ht hout).1
    refine ⟨J.conjBy t,?_,?_,ChapterD.RPlusBound.map_conj ρ hJ t,quadratic_conjugate ρ hqJ t⟩
    · rintro _ ⟨j,hj,rfl⟩
      exact preserving_conjugate_mem_normalizer geo ht (hAT (hJA hj)) (hp (hJA hj))
    · intro hj
      apply hn0
      apply le_centralizer_iff.mpr
      rw [← hpair]
      refine sup_le (le_centralizer_iff.mp hn) ?_
      apply le_centralizer_iff.mp
      intro j hjJ l hl
      obtain ⟨k,hk,rfl⟩ := hl
      have hh := hj (mem_map_of_mem (MulAut.conj t).toMonoidHom hjJ) k hk
      have he := congrArg (MulAut.conj t⁻¹) hh
      simpa only [map_mul,MulEquiv.coe_toMonoidHom,MulAut.conj_apply,inv_inv,mul_assoc,
        inv_mul_cancel_left,mul_inv_cancel_left,inv_mul_cancel,mul_inv_cancel,mul_one,one_mul] using he
  · exact ⟨J,hJA.trans hp,hn,hJ,hqJ⟩

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.OriginalModule.Exchanged
