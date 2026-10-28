module
public import Theory.GroupTheory.GeneralizedFitting.RelativeComponent
public import Theory.GroupTheory.GeneralizedFitting.InvariantFixedSeed
public import CFSG.Quasithin.Chapter2.Section05.Overcomponents.Prime.FixedRankLift

/-! The second overcomponent already normalizes the first component's
intersection centralizer.  A common perfect subgroup forces containment;
for a swapped pair its full norm diagonal supplies the same obstruction.
Source: the second pumpup in 2.5.19, printed pp.563–564. -/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.Section05.Overcomponents
variable {G : Type*} [Group G]

theorem centralizer_component_le_normal_of_common_perfect
    (P C Y K : Subgroup G) (hP : IsComponentIn P C) [Y.Normal]
    [Group.IsPerfect K] (hne : K ≠ ⊥) (hKP : K ≤ P) (hKY : K ≤ Y) : P ≤ Y := by
  let N := Y.subgroupOf C
  rcases hP.2.normal_dichotomy N with hh | hh
  · intro x hx
    exact hh (show (⟨x,hP.1 hx⟩ : C) ∈ P.subgroupOf C from hx)
  · have hc := commutator_eq_bot_iff_le_centralizer.mp hh
    have hKK : K ≤ centralizer (K : Set G) := by
      intro x hx y hy
      exact congrArg Subtype.val
        (hc (show (⟨x,hP.1 (hKP hx)⟩ : C) ∈ P.subgroupOf C from hKP hx)
          (⟨y,hP.1 (hKP hy)⟩ : C) (hKY hy))
    have hb : K = ⊥ := by
      simpa only [commutator_eq_self] using commutator_eq_bot_iff_le_centralizer.mpr hKK
    exact (hne hb).elim

/-- A normal overgroup containing a full swapped norm diagonal contains
the first factor.  This form retains the original norm word explicitly. -/
theorem centralizer_component_le_normal_of_norm_words
    (P C Y : Subgroup G) (hP : IsComponentIn P C) [Y.Normal]
    (t : G) (htC : t ∈ C)
    (hcomm : P ≤ centralizer (P.map (MulAut.conj t).toMonoidHom : Set G))
    (hnorm : ∀ x ∈ P, x * (t * x * t⁻¹) ∈ Y) : P ≤ Y := by
  let N := Y.subgroupOf C
  rcases hP.2.normal_dichotomy N with hh | hh
  · intro x hx
    exact hh (show (⟨x,hP.1 hx⟩ : C) ∈ P.subgroupOf C from hx)
  · have hc := commutator_eq_bot_iff_le_centralizer.mp hh
    have hPP : P ≤ centralizer (P : Set G) := by
      intro x hx y hy
      have hnC : y * (t * y * t⁻¹) ∈ C :=
        C.mul_mem (hP.1 hy) (C.mul_mem (C.mul_mem htC (hP.1 hy)) (C.inv_mem htC))
      have hwhole : (y * (t*y*t⁻¹)) * x = x * (y * (t*y*t⁻¹)) :=
        congrArg Subtype.val (hc (show (⟨x,hP.1 hx⟩ : C) ∈ P.subgroupOf C from hx)
          (⟨y*(t*y*t⁻¹),hnC⟩ : C) (hnorm y hy))
      have hright : (t*y*t⁻¹) * x = x * (t*y*t⁻¹) :=
        hcomm hx _ (mem_map_of_mem (MulAut.conj t).toMonoidHom hy)
      apply mul_right_cancel (b := t*y*t⁻¹)
      calc
        (y*x)*(t*y*t⁻¹) = y*((t*y*t⁻¹)*x) := by rw [hright]; group
        _ = (y*(t*y*t⁻¹))*x := by group
        _ = x*(y*(t*y*t⁻¹)) := hwhole
        _ = (x*y)*(t*y*t⁻¹) := by group
    let : IsQuasisimple P := hP.quasisimple
    have hb : P = ⊥ := by
      simpa only [commutator_eq_self] using commutator_eq_bot_iff_le_centralizer.mpr hPP
    exact (hP.ne_bot hb).elim

variable [Finite G]

/-- The actual fixed-component bound identifies a rank-two component in
a normal quasisimple containing group. -/
theorem rank_two_component_eq_normal_overgroup
    (P Y : Subgroup G) (i : G) (hi : orderOf i = 2)
    (hP : IsComponentIn P (centralizer ({i} : Set G)))
    (hY : IsComponent G Y) [Y.Normal] (hPY : P ≤ Y)
    (hr : 2 ≤ primeRank 3 (P ⧸ center P))
    (hfixed : ∀ b : MulAut (Y ⧸ center Y), orderOf b = 2 →
      ∀ C : Subgroup b.fixedSubgroup, IsComponent b.fixedSubgroup C → primeRank 3 C ≤ 1) :
    P = Y := by
  by_cases hPG : IsComponent G P
  · exact hPG.eq_of_le hY hPY
  obtain ⟨a,ha,hact,hB⟩ := invariant_component_fixed_seed i hi hP hY hPY
    (normal_iff_map_conj_eq.mp inferInstance i) hPG
  let B := P.subgroupOf Y
  let : IsQuasisimple Y := hY.2
  let : IsQuasisimple P := hP.quasisimple
  let : IsQuasisimple B := hB.quasisimple
  let : Nontrivial B := (nontrivial_iff_ne_bot _).mpr hB.ne_bot
  let e : P ≃* B := (subgroupOfEquivOfLe hPY).symm
  let eQ : (P ⧸ center P) ≃* (B ⧸ center B) :=
    IsQuasisimple.centralQuotientEquiv e.toMonoidHom e.surjective
  have hrB : 2 ≤ primeRank 3 (B ⧸ center B) := by rwa [primeRank_equiv 3 eQ] at hr
  have ha1 := fixed_component_actor_eq_one_of_central_quotient_rank_two a
    (ha ▸ pow_orderOf_eq_one a) B hB hrB hfixed
  rw [ha1,orderOf_one] at ha
  omega
end CFSG.Quasithin.Chapter2.Section05.Overcomponents
