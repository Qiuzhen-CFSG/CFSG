module
public import Theory.GroupTheory.GeneralizedFitting.ComponentSwapPerfectActor

/-! A perfect actor normalizing a commuting exchanged pair and fixing
its full diagonal pointwise centralizes the pair. The component argument
is applied in the pair normalizer, not in the whole ambient group.
Source 2.5.19, printed p.564. -/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.Section05.Overcomponents
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem map_conj_inclusion {N : Subgroup G} (P : Subgroup N) (t : N) :
    (P.map (MulAut.conj t).toMonoidHom).map N.subtype =
      (P.map N.subtype).map (MulAut.conj (t:G)).toMonoidHom := by
  rw [map_map,map_map]
  rfl

/-- The actual pair normalizer suffices for the perfect-actor argument. -/
theorem perfect_actor_centralizes_exchanged_pair
    (P C : Subgroup G) [IsQuasisimple P] [Group.IsPerfect C]
    (t : G) (ht : t ^ 2 = 1)
    (hne : P.map (MulAut.conj t).toMonoidHom ≠ P)
    (hcomm : P ≤ centralizer (P.map (MulAut.conj t).toMonoidHom : Set G))
    (hCN : C ≤ normalizer ((P ⊔ P.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G))
    (hCt : C ≤ centralizer ({t} : Set G))
    (hnorm : ∀ c ∈ C, ∀ x ∈ P,
      (x * (t*x*t⁻¹)) * c = c * (x * (t*x*t⁻¹))) :
    C ≤ centralizer ((P ⊔ P.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) := by
  let X := P ⊔ P.map (MulAut.conj t).toMonoidHom
  let N := normalizer (X : Set G)
  have hPX : P ≤ X := le_sup_left
  have hPN : P ≤ N := hPX.trans X.le_normalizer
  have htN : t ∈ N := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    change X.map (MulAut.conj t).toMonoidHom = X
    rw [Subgroup.map_sup,map_map]
    have he : (MulAut.conj t).toMonoidHom.comp (MulAut.conj t).toMonoidHom = MonoidHom.id G := by
      ext x
      change t*(t*x*t⁻¹)*t⁻¹=x
      have htt : t*t=1 := by simpa only [pow_two] using ht
      calc
        t*(t*x*t⁻¹)*t⁻¹ = (t*t)*x*(t*t)⁻¹ := by group
        _ = x := by rw [htt]; simp
    rw [he,map_id,sup_comm]
  let tt : N := ⟨t,htN⟩
  let F := P.subgroupOf N
  let C₀ := C.subgroupOf N
  have hXNP : X ≤ normalizer (P : Set G) :=
    sup_le P.le_normalizer ((le_centralizer_iff.mp hcomm).trans (Subgroup.centralizer_le_normalizer _))
  have hPbase : IsComponentIn P (normalizer (P : Set G)) := by
    refine ⟨P.le_normalizer,(inferInstance : (P.subgroupOf (normalizer (P : Set G))).Normal).isSubnormal,?_⟩
    exact IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe P.le_normalizer).symm
  have hPcomp : IsComponent N F := ((hPbase.restrict hPX hXNP).of_subnormal
    X.le_normalizer (inferInstance : (X.subgroupOf N).Normal).isSubnormal).2
  have hpair : F ⊔ F.map (MulAut.conj tt).toMonoidHom = X.subgroupOf N := by
    apply map_injective N.subtype_injective
    rw [Subgroup.map_sup,map_conj_inclusion,map_subgroupOf_eq_of_le hPN,
      map_subgroupOf_eq_of_le X.le_normalizer]
  have hm : F.map (MulAut.conj tt).toMonoidHom ≠ F := by
    intro he
    apply hne
    have hh := congrArg (map N.subtype) he
    rw [map_conj_inclusion] at hh
    change ((P.subgroupOf N).map N.subtype).map (MulAut.conj t).toMonoidHom =
      (P.subgroupOf N).map N.subtype at hh
    simpa only [map_subgroupOf_eq_of_le hPN] using hh
  let : (F ⊔ F.map (MulAut.conj tt).toMonoidHom).Normal :=
    hpair.symm ▸ (inferInstance : (X.subgroupOf N).Normal)
  let : Group.IsPerfect C₀ := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hCN).symm.toMonoidHom) (subgroupOfEquivOfLe hCN).symm.surjective
  have hc := NormPair.perfect_actor_centralizes_normal_pair hPcomp hm C₀
    (fun c hc => mem_centralizer_singleton_iff.mpr
      (Subtype.ext (mem_centralizer_singleton_iff.mp (hCt hc)))) (by
      intro c hc x hx
      obtain ⟨y,rfl⟩ := hx
      apply Subtype.ext
      exact hnorm c hc y y.property)
  intro c hcC x hx
  have h := hc (show (⟨c,hCN hcC⟩ : N) ∈ C₀ from hcC)
    (⟨x,X.le_normalizer hx⟩ : N) (hpair.symm ▸ hx)
  exact congrArg Subtype.val h
end CFSG.Quasithin.Chapter2.Section05.Overcomponents
