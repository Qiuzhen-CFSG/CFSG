module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.TwoBlock.CoverNormalizer
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.Centralizer

/-!
# Displacement of a full module fixer

An automorphism fixing the actual U acts trivially on K/O₂(K), since that
quotient acts faithfully on U. C.1.8's two-perfect central-cover rigidity
then makes it trivial already on K/U. Thus [K,P]≤U for the actual
normalizer elements centralizing U, before any identification O₂(K)=U.

Source: Aschbacher–Smith, C.1.8 and C.5.6(7), printed pp.123,159.
-/
public section
open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
variable {G : Type*} [Group G] [Finite G] {K P : Subgroup G}

omit [Finite G] in
theorem block_fixer_displacement (h : IsShort K)
    (hPN : P ≤ normalizer (K : Set G)) (hPU : P ≤ centralizer (U K : Set G)) :
    ⁅K,P⁆ ≤ U K := by
  rw [commutator_comm]
  apply commutator_le.mpr
  intro p hp k hk
  let α := K.normalizerMonoidHom ⟨p,hPN hp⟩
  have hfix (u : K) (hu : u ∈ blockU K) : α u = u := by
    apply Subtype.ext
    change p * (u : G) * p⁻¹ = u
    rw [← hPU hp u (mem_map_of_mem K.subtype hu),mul_inv_cancel_right]
  have hα (a : K) : α a * a⁻¹ ∈ pCore 2 K := by
    have hd : (α a)⁻¹ * a ∈ centralizer (blockU K : Set K) := by
      intro u hu
      have he := hfix (a*u*a⁻¹) ((inferInstance : (blockU K).Normal).conj_mem u hu a)
      rw [map_mul,map_mul,map_inv,hfix u hu] at he
      calc
        u*((α a)⁻¹*a) = (α a)⁻¹*(α a*u*(α a)⁻¹)*a := by group
        _ = (α a)⁻¹*(a*u*a⁻¹)*a := by rw [he]
        _ = ((α a)⁻¹*a)*u := by group
    rw [h.centralizer_blockU] at hd
    have he : QuotientGroup.mk' (pCore 2 K) ((α a)⁻¹*a) = 1 := (QuotientGroup.eq_one_iff _).mpr hd
    rw [map_mul,map_inv,inv_mul_eq_one] at he
    simpa only [div_eq_mul_inv] using QuotientGroup.eq_iff_div_mem.mp he
  have he := DFunLike.congr_fun (h.quotient_blockU_aut_eq_one α hα)
    (QuotientGroup.mk' (blockU K) (⟨k,hk⟩ : K))
  rw [quotientAut_apply_mk] at he
  have hm : α ⟨k,hk⟩ * (⟨k,hk⟩ : K)⁻¹ ∈ blockU K :=
    by simpa only [div_eq_mul_inv] using QuotientGroup.eq_iff_div_mem.mp he
  exact mem_map_of_mem K.subtype hm
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
