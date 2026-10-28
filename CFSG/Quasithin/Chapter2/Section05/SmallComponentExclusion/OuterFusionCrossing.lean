module
public import CFSG.Quasithin.Chapter2.Section05.SmallComponentExclusion.OuterSplit
/-!
# The original crossing moves a four outside its central product

If every displacement of the selected four E lay in ⟨t,z⟩, the crossing
would normalize the normal two-subgroup ⟨t⟩E of the largest local pair.
Source 2.5.12(4) forbids this. The displacement also belongs to C_S(R),
since E normalizes the actual residual R and the crossing centralizes R.
This produces the outer fusion witness without assuming it.
Source: Aschbacher--Smith 2.5.15, printed p.559.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.Section05
open A6Shadow.Frattini ComponentRefinement ComponentSelection ClassificationModels
variable {G : Type*} [Group G] [Finite G] {H K M U L E R : Subgroup G}
  {S : Sylow 2 H} {z x : G}

omit [Finite G] in
private theorem displacement_mem_centralizer (Y : Subgroup G)
    (hEY : E ≤ Y) (hER : E ≤ normalizer (R:Set G))
    (hxN : x ∈ normalizer (Y:Set G)) (hxR : x ∈ centralizer (R:Set G))
    (a : G) (ha : a∈E) :
    a⁻¹*(x⁻¹*a*x) ∈ Y ⊓ centralizer (R:Set G) := by
  have hxN' := (normalizer (Y:Set G)).inv_mem hxN
  have has : x⁻¹*a*x ∈ Y := by simpa only [SetLike.mem_coe,inv_inv] using (hxN' a).mp (hEY ha)
  refine ⟨Y.mul_mem (Y.inv_mem (hEY ha)) has,?_⟩
  let N := normalizer (R:Set G)
  let xx : N := ⟨x,Subgroup.centralizer_le_normalizer _ hxR⟩
  let aa : N := ⟨a,hER ha⟩
  have hxx : R.normalizerMonoidHom xx = 1 := by
    rw [← MonoidHom.mem_ker,normalizerMonoidHom_ker]
    exact hxR
  have hh : aa⁻¹*(xx⁻¹*aa*xx)∈R.normalizerMonoidHom.ker := by
    apply MonoidHom.mem_ker.mpr
    rw [map_mul,map_inv,map_mul,map_mul,map_inv,hxx]
    simp only [inv_one,one_mul,mul_one,inv_mul_cancel]
  rw [normalizerMonoidHom_ker] at hh
  exact hh

 theorem source_crossing_displacement_outside_center
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hp : (U,L) ∈ largestLocalPairs M H) (hUS : U ≤ (S:Subgroup H).map H.subtype)
    (t : G) (htS : t ∈ (S:Subgroup H).map H.subtype)
    (htH : H ≤ centralizer ({t}:Set G))
    (hES : E ≤ (S:Subgroup H).map H.subtype)
    (hL : L = H ⊓ normalizer (E:Set G)) (hzE : z∈E)
    (hER : E ≤ normalizer (R:Set G))
    (hxT : x∈c.T) (hxS : x∉(S:Subgroup H).map H.subtype)
    (hxN : x∈normalizer ((S:Subgroup H).map H.subtype:Set G))
    (hxR : x∈centralizer (R:Set G)) (htx : x⁻¹*t*x=t*z) :
    ∃ a : G, a∈E ∧ a⁻¹*(x⁻¹*a*x)∈
      (S:Subgroup H).map H.subtype ⊓ centralizer (R:Set G) ∧
      a⁻¹*(x⁻¹*a*x)∉zpowers t ⊔ zpowers z := by
  classical
  by_contra hn
  push Not at hn
  let Y := (S:Subgroup H).map H.subtype
  let Q := zpowers t ⊔ E
  have hQS : Q≤Y := sup_le (zpowers_le.mpr htS) hES
  have hQN : L≤normalizer (Q:Set G) := by
    apply le_trans _ (normalizer_inf_normalizer_le_normalizer_sup _ _)
    apply le_inf
    · have hct : L ≤ centralizer ({t}:Set G) := by rw [hL]; exact inf_le_left.trans htH
      have hct' : L ≤ centralizer (zpowers t:Set G) := by
        simpa only [zpowers_eq_closure,centralizer_closure] using hct
      exact hct'.trans (Subgroup.centralizer_le_normalizer _)
    · rw [hL]; exact inf_le_right
  have hxn := largest_pair_normal_two_not_normalized_by_crossing c hG hp hUS
    ((S.isPGroup'.map H.subtype).to_le hQS) (show z∈Q from mem_sup_right hzE) hQN hxT hxS
  apply hxn
  have hmap : Q.map (MulAut.conj x⁻¹).toMonoidHom ≤ Q := by
    dsimp only [Q]
    rw [Subgroup.map_sup,MonoidHom.map_zpowers]
    apply sup_le
    · apply zpowers_le.mpr
      change x⁻¹*t*(x⁻¹)⁻¹ ∈ zpowers t ⊔ E
      rw [inv_inv,htx]
      exact mul_mem (mem_sup_left (mem_zpowers t)) (mem_sup_right hzE)
    · rintro _ ⟨a,ha,rfl⟩
      have hd := hn a ha (displacement_mem_centralizer Y hES hER hxN hxR a ha)
      have hdQ : a⁻¹*(x⁻¹*a*x)∈Q := (sup_le le_sup_left
        ((zpowers_le.mpr hzE).trans le_sup_right)) hd
      have hh := Q.mul_mem (mem_sup_right ha) hdQ
      change x⁻¹*a*(x⁻¹)⁻¹ ∈ Q
      simpa only [inv_inv,mul_inv_cancel_left] using hh
  have heq : Q.map (MulAut.conj x⁻¹).toMonoidHom = Q :=
    eq_of_le_of_card_ge hmap (by rw [card_map_of_injective (MulAut.conj x⁻¹).injective])
  have hmem := mem_normalizer_iff_map_conj_eq.mpr heq
  simpa only [inv_inv] using (normalizer (Q:Set G)).inv_mem hmem
end CFSG.Quasithin.Chapter2.Section05
