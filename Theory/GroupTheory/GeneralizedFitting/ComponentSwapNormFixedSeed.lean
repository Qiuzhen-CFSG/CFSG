module
public import Theory.GroupTheory.GeneralizedFitting.ComponentSwapNormAction
public import Theory.GroupTheory.GeneralizedFitting.RelativeComponent
public import Theory.GroupTheory.GeneralizedFitting.ComponentSwapNormSylow
public import Theory.GroupTheory.GeneralizedFitting.SylowNormalizedComponent
public import Theory.GroupTheory.IndexTwoIntersection

/-!
# The ordinary fixed component of an exchanged pair

A component of the swapping involution centralizer contained in two exchanged components is their norm image: any different fixed component commutes with that image and consequently with both factors. The odd-rank bound limits the component orbit to two elements. It gives normalization of the fixed component and identifies its pointwise kernel with the component stabilizer of index two. Source: Aschbacher–Smith 2.5.19, printed p.561.
-/

public section
open Subgroup
namespace Theory.GroupTheory.NormPair
variable {G : Type*} [Group G] {L K : Subgroup G} {a : G}

theorem fixed_component_eq_norm
    (hL : IsComponent G L) (hm : L.map (MulAut.conj a).toMonoidHom ≠ L)
    (ha : a ^ 2 = 1) (hK : IsComponentIn K (centralizer ({a} : Set G)))
    (hKP : K ≤ L ⊔ L.map (MulAut.conj a).toMonoidHom) :
    K = normRange hL hm := by
  let D := normRange hL hm
  let P := L ⊔ L.map (MulAut.conj a).toMonoidHom
  let C := P ⊓ centralizer ({a} : Set G)
  have hc : L.map (MulAut.conj a).toMonoidHom ≤ centralizer (L : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp ((hL.map_conj a).commutator_eq_bot_of_ne hL hm)
  have hPN : P ≤ normalizer (L : Set G) :=
    sup_le L.le_normalizer (hc.trans (centralizer_le_normalizer _))
  have hDC : D ≤ C := le_inf (norm_le_pair hL hm)
    (componentSwapNorm_range_le_centralizer hL hm ha)
  have hKC : K ≤ C := le_inf hKP hK.1
  have hCN : C ≤ normalizer (D : Set G) := by
    intro b hb
    exact normalizes_norm hL hm (mem_centralizer_singleton_iff.mp hb.2) (hPN hb.1)
  let : (D.subgroupOf C).Normal := normal_subgroupOf_of_le_normalizer hCN
  have hD : IsComponentIn D C := by
    refine ⟨hDC, (inferInstance : (D.subgroupOf C).Normal).isSubnormal, ?_⟩
    let : IsQuasisimple D := componentSwapNorm_range_quasisimple hL hm
    exact IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hDC).symm
  have hKr := hK.restrict hKC inf_le_right
  by_cases he : K = D
  · exact he
  have hKD : K ≤ centralizer (D : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp (hKr.commutator_eq_bot_of_ne hD he)
  have hKL : K ≤ centralizer (L : Set G) := by
    intro b hb
    exact centralizes_norm_normalizes_component hL hm
      (mem_centralizer_singleton_iff.mp (hK.1 hb)) (hPN (hKP hb)) (hKD hb)
  have hKLa : K ≤ centralizer (L.map (MulAut.conj a).toMonoidHom : Set G) := by
    intro b hb x hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hba : Commute b a := mem_centralizer_singleton_iff.mp (hK.1 hb)
    have hby : Commute b y := (hKL hb y hy).symm
    exact ((hba.mul_right hby).mul_right hba.inv_right).eq.symm
  have hself : K ≤ centralizer (K : Set G) :=
    le_centralizer_iff.mp (hKP.trans (sup_le (le_centralizer_iff.mp hKL)
      (le_centralizer_iff.mp hKLa)))
  let : IsQuasisimple K := hK.quasisimple
  have hbot : K = ⊥ := by
    simpa only [commutator_eq_self] using commutator_eq_bot_iff_le_centralizer.mpr hself
  exact (hK.ne_bot hbot).elim

variable [Finite G]

theorem centralizer_normalizes_fixed_component
    (hrank : ∀ p : ℕ, p.Prime → Odd p → primeRank p G ≤ 2)
    (hL : IsComponent G L) (hm : L.map (MulAut.conj a).toMonoidHom ≠ L)
    (ha : a ^ 2 = 1) (hK : IsComponentIn K (centralizer ({a} : Set G)))
    (hKP : K ≤ L ⊔ L.map (MulAut.conj a).toMonoidHom) :
    centralizer ({a} : Set G) ≤ normalizer (K : Set G) := by
  have hi : (normalizer (L : Set G)).index = 2 := by
    rcases hL.normal_or_index_two_of_odd_rank_le_two hrank with hn | hi
    · exact (hm (normal_iff_map_conj_eq.mp hn a)).elim
    · exact hi
  rw [fixed_component_eq_norm hL hm ha hK hKP]
  intro b hb
  exact normalizes_norm_of_pair hL hm ha (mem_centralizer_singleton_iff.mp hb)
    (conjugate_eq_or_eq_of_normalizer_index_two hi hm b)

theorem fixed_component_pair_kernel_index
    (hrank : ∀ p : ℕ, p.Prime → Odd p → primeRank p G ≤ 2)
    (hL : IsComponent G L) (hm : L.map (MulAut.conj a).toMonoidHom ≠ L)
    (ha : a ^ 2 = 1) (hK : IsComponentIn K (centralizer ({a} : Set G)))
    (hKP : K ≤ L ⊔ L.map (MulAut.conj a).toMonoidHom)
    (R : Subgroup G) (hRa : R ≤ centralizer ({a} : Set G))
    (hRK : R ≤ centralizer (K : Set G)) (haR : a ∈ R) :
    ((R ⊓ centralizer ((L ⊔ L.map (MulAut.conj a).toMonoidHom : Subgroup G) : Set G)).subgroupOf R).index = 2 := by
  have hi : (normalizer (L : Set G)).index = 2 := by
    rcases hL.normal_or_index_two_of_odd_rank_le_two hrank with hn | hi
    · exact (hm (normal_iff_map_conj_eq.mp hn a)).elim
    · exact hi
  have hRnot : ¬ R ≤ normalizer (L : Set G) := fun h =>
    hm (mem_normalizer_iff_map_conj_eq.mp (h haR))
  have he : (R ⊓ centralizer ((L ⊔ L.map (MulAut.conj a).toMonoidHom : Subgroup G) : Set G)).subgroupOf R =
      (normalizer (L : Set G)).subgroupOf R := by
    ext b
    constructor
    · intro hb
      change (b : G) ∈ normalizer (L : Set G)
      apply centralizer_le_normalizer (L : Set G)
      exact fun x hx => hb.2 x (mem_sup_left hx)
    · intro hb
      refine ⟨b.property, ?_⟩
      have hba : Commute (b : G) a := mem_centralizer_singleton_iff.mp (hRa b.property)
      have hnorm : (b : G) ∈ centralizer (normRange hL hm : Set G) := by
        rw [← fixed_component_eq_norm hL hm ha hK hKP]
        exact hRK b.property
      have hLcent := centralizes_norm_normalizes_component hL hm hba hb hnorm
      have hLacent : (b : G) ∈ centralizer (L.map (MulAut.conj a).toMonoidHom : Set G) := by
        rintro x ⟨y, hy, rfl⟩
        have hby : Commute (b : G) y := (hLcent y hy).symm
        exact ((hba.mul_right hby).mul_right hba.inv_right).eq.symm
      have hp : L ⊔ L.map (MulAut.conj a).toMonoidHom ≤ centralizer ({(b : G)} : Set G) :=
        sup_le (fun x hx => mem_centralizer_singleton_iff.mpr (hLcent x hx))
          (fun x hx => mem_centralizer_singleton_iff.mpr (hLacent x hx))
      exact fun x hx => mem_centralizer_singleton_iff.mp (hp hx)
  rw [he]
  exact subgroupOf_index_eq_two (normalizer (L : Set G)) R hi hRnot
end Theory.GroupTheory.NormPair
