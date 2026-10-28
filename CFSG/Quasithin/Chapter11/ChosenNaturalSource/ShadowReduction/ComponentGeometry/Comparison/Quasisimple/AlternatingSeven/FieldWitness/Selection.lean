module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.AlternatingSeven.FieldWitness.Permutation
/-!
# An outer seed transposition in the original Sylow image

Conjugate the chosen Sylow subgroup to the sixteen-word model. Its only
central transposition is (45), so a perfect seed of order sixty centralizing
that transposition is the alternating group on the other five letters.
The transposition (01) gives an outer seed action. Transport back through
the same conjugation preserves the original seed and Sylow subgroup.

Source: Aschbacher--Smith, 11.4.2, printed p.777.
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
open Subgroup Equiv Equiv.Perm
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.AlternatingSeven.FieldWitness

section Transport
variable {Q R : Type*} [Group Q] [Group R]
theorem outer_transport (e : Q ≃* R) (B : Subgroup Q) (C : Subgroup R)
    (he : B.map e.toMonoidHom = C) (x : Q)
    (hn : x ∈ normalizer (B : Set Q)) (hn' : e x ∈ normalizer (C : Set R))
    (ho : ¬ ∃ b : C, C.normalizerMonoidHom ⟨e x,hn'⟩ = MulAut.conj b) :
    ¬ ∃ b : B, B.normalizerMonoidHom ⟨x,hn⟩ = MulAut.conj b := by
  rintro ⟨b,hb⟩
  apply ho
  let eb : C := ⟨e b,he ▸ mem_map_of_mem e.toMonoidHom b.property⟩
  refine ⟨eb,?_⟩
  apply MulEquiv.ext
  intro k
  have hk : (k : R) ∈ B.map e.toMonoidHom := he.symm ▸ k.property
  obtain ⟨y,hy,hyk⟩ := hk
  apply Subtype.ext
  have hh := congrArg (fun a : MulAut B => (a ⟨y,hy⟩).val) hb
  change x*y*x⁻¹ = b.val*y*b.val⁻¹ at hh
  have hh' := congrArg e hh
  change e x * k.val * (e x)⁻¹ = e b.val * k.val * (e b.val)⁻¹
  change e y = k.val at hyk
  simpa only [map_mul,map_inv,hyk] using hh'
end Transport

namespace Permutation
open Representation.AlternatingSevenConjugatePair.ElementaryGeometry

theorem standard_central_swap (s : S7) (hs : s ∈ sylowTwo) (ht : s.IsSwap)
    (hc : sylowTwo ≤ centralizer ({s} : Set S7)) : s = swap45 := by
  obtain ⟨v,rfl⟩ := hs
  have hh : ∀ w : Quadruple, word w * word v = word v * word w := by
    intro w
    exact mem_centralizer_singleton_iff.mp (hc ⟨w,rfl⟩)
  exact (by decide +kernel : ∀ v : Quadruple, (word v).support.card = 2 →
    (∀ w : Quadruple, word w * word v = word v * word w) → word v = swap45)
    v (Perm.card_support_eq_two.mpr ht) hh

theorem exists_outer_swap (P : Sylow 2 S7) (B : Subgroup S7) [Group.IsPerfect B]
    (hcard : Nat.card B = 60) (s : S7) (hs : s ∈ P) (ht : s.IsSwap)
    (hPs : (P : Subgroup S7) ≤ centralizer ({s} : Set S7))
    (hBs : B ≤ centralizer ({s} : Set S7)) :
    ∃ x ∈ P, x.IsSwap ∧ ∃ hn : x ∈ normalizer (B : Set S7),
      ¬ ∃ b : B, B.normalizerMonoidHom ⟨x,hn⟩ = MulAut.conj b := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq S7 P standardSylow
  let e := MulAut.conj g
  have hP : (P : Subgroup S7).map e.toMonoidHom = sylowTwo := congrArg Sylow.toSubgroup hg
  have heSwap (y : S7) (hy : y.IsSwap) : (e y).IsSwap := by
    obtain ⟨i,j,hij,rfl⟩ := hy
    exact ⟨g i,g j,g.injective.ne hij,by
      change g * swap i j * g⁻¹ = swap (g i) (g j)
      rw [mul_swap_eq_swap_mul,mul_inv_cancel_right]⟩
  have hes : e s = swap45 := standard_central_swap (e s)
    (hP ▸ mem_map_of_mem e.toMonoidHom hs) (heSwap s ht) (by
      rintro _ ⟨v,hv⟩
      have hm : word v ∈ (P : Subgroup S7).map e.toMonoidHom := hP.symm ▸ ⟨v,rfl⟩
      obtain ⟨p,hp,hpv⟩ := hm
      rw [←hv,←hpv]
      exact mem_centralizer_singleton_iff.mpr (by
        simpa only [map_mul,MulEquiv.coe_toMonoidHom] using congrArg e (mem_centralizer_singleton_iff.mp (hPs hp))))
  let B' := B.map e.toMonoidHom
  let : Group.IsPerfect B' := Group.IsPerfect.map _
  have hB' : B' = five := perfect_eq_five B' (by
    rintro _ ⟨b,hb,rfl⟩
    rw [←hes]
    exact mem_centralizer_singleton_iff.mpr (by
      simpa only [map_mul,MulEquiv.coe_toMonoidHom] using congrArg e (mem_centralizer_singleton_iff.mp (hBs hb))))
    (by rw [card_map_of_injective e.injective,hcard])
  let x := e.symm swap01
  have hxP : x ∈ P := by
    have hm : swap01 ∈ (P : Subgroup S7).map e.toMonoidHom := by
      rw [hP]
      exact ⟨(1,0,0,0),by decide +kernel⟩
    obtain ⟨p,hp,hpe⟩ := hm
    have hpx : p = x := e.injective (hpe.trans (e.apply_symm_apply swap01).symm)
    exact hpx ▸ hp
  have hxswap : x.IsSwap := by
    change (g⁻¹ * swap01 * g).IsSwap
    change (g⁻¹ * swap 0 1 * g).IsSwap
    rw [mul_swap_eq_swap_mul,mul_assoc,inv_mul_cancel,mul_one]
    exact swap_isSwap_iff.mpr ((g⁻¹).injective.ne (by decide))
  have hnx : x ∈ normalizer (B : Set S7) := by
    have hm : e x ∈ (normalizer (B : Set S7)).map e.toMonoidHom := by
      rw [map_equiv_normalizer_eq]
      change e x ∈ normalizer (B' : Set S7)
      rw [hB']
      change e (e.symm swap01) ∈ _
      rw [e.apply_symm_apply]
      exact swap01_normalizes
    obtain ⟨p,hp,hpe⟩ := hm
    exact e.injective hpe ▸ hp
  refine ⟨x,hxP,hxswap,hnx,?_⟩
  apply outer_transport e B five hB' x hnx (by
    simpa only [x,e.apply_symm_apply] using swap01_normalizes)
  simpa only [x,e.apply_symm_apply] using swap01_not_inner
end Permutation
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.AlternatingSeven.FieldWitness
