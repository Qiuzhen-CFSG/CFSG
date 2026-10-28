module
public import Theory.GroupTheory.SmallFittingResidual
public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents

/-!
# Absorbing a two-perfect actor through the generalized Fitting subgroup

Let F*(G)=KQ with Q a normal two-group commuting with the normal factor K.
A two-perfect subgroup with faithful action on K and two-group outer image
lies in K whenever Q normalizes it. The normalizing core must centralize the
actor, and generalized-Fitting self-centralization then absorbs the remaining
centralizer coordinate. The final quotient is a two-group.

Source: the projected cubic-block placement in Aschbacher–Smith 2.4.32, p.547.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

theorem twoPerfect_le_component_of_normalized_core
    (K L Q : Subgroup G) [K.Normal] [Q.Normal]
    (hF : generalizedFitting G = K ⊔ Q)
    (hKC : K ≤ centralizer (Q : Set G))
    (hp : IsPGroup 2 Q) (hL : IsPPerfect 2 L)
    (ho : IsPGroup 2 (MulAut.Outer K))
    (hn : Q ≤ normalizer (L : Set G))
    (hf : L ⊓ centralizer (K : Set G) = ⊥) : L ≤ K := by
  have hLC : L ≤ centralizer (Q : Set G) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply bot_unique
    rw [←hf]
    refine le_inf ?_ ?_
    · exact le_normalizer_iff_commutator_le_left.mp hn
    · exact (commutator_le_right L Q).trans (le_centralizer_iff.mp hKC)
  have hinner : L ≤ K ⊔ centralizer (K : Set G) := by
    rw [←MulAut.conjNormal_comap_innerSubgroup K]
    let f : L →* MulAut.Outer K := (QuotientGroup.mk' (MulAut.innerSubgroup K)).comp
      ((MulAut.conjNormal : G →* MulAut K).comp L.subtype)
    have h := hL.hom_eq_one_of_isPGroup ho f
    intro l hl
    change (MulAut.conjNormal l : MulAut K) ∈ MulAut.innerSubgroup K
    exact (QuotientGroup.eq_one_iff _).mp
      (congrArg (fun a : L →* MulAut.Outer K => a ⟨l,hl⟩) h)
  apply twoPerfect_le_of_le_sup_twoGroup K L Q hL hp
  intro l hl
  obtain ⟨k,hk,a,ha,hka⟩ := mem_sup_of_normal_left.mp (hinner hl)
  have hac : a ∈ centralizer (Q : Set G) := by
    have he : a = k⁻¹*l := by rw [←hka]; group
    rw [he]
    exact (centralizer (Q : Set G)).mul_mem
      ((centralizer (Q : Set G)).inv_mem (hKC hk)) (hLC hl)
  have haf : a ∈ centralizer (generalizedFitting G : Set G) := by
    have hle : K ⊔ Q ≤ centralizer ({a} : Set G) := sup_le
      (fun k hk => mem_centralizer_singleton_iff.mpr (ha k hk))
      (fun q hq => mem_centralizer_singleton_iff.mpr (hac q hq))
    intro y hy
    exact mem_centralizer_singleton_iff.mp (hle (hF ▸ hy))
  rw [←hka]
  exact (K ⊔ Q).mul_mem (mem_sup_left hk)
    (hF ▸ centralizer_generalizedFitting_le G haf)
end Theory.GroupTheory
