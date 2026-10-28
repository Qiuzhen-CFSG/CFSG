module
public import Theory.GroupTheory.Recognition.UnitaryFourThree.RootPair.MaximumPlanes
public import Theory.GroupTheory.CentralInvolutionCocycles

/-!
# The original core reflection has trivial root-subgroup cocycles

The core has eighteen noncentral involutions and its root factor has order
sixteen, so a genuine involution exists outside that factor. Its conjugation
action on the root center has fixed subgroup of order two; the action on the
elementary central quotient has fixed subgroup of order four. Both elementary
cocycle criteria are therefore exact. All actions and maps are the original
ambient conjugation maps.

Source: Aschbacher, *Sporadic Groups*, Exercise 2.8 and45.5(4), printed p.244.
-/

@[expose] public section
open Subgroup
open scoped commutatorElement
namespace Theory.GroupTheory.Recognition.UnitaryFourThree
variable {G : Type*} [Group G] [Finite G] {z : G}
namespace RootPair
variable (P : RootPair z)

theorem exists_core_reflection (h : IsType z) :
    ∃ s ∈ core z, orderOf s = 2 ∧ s ∉ P.leftCore := by
  by_contra hn
  push Not at hn
  let X := {s : core z // orderOf s = 2 ∧ s ∉ center (core z)}
  let f : X → P.leftCore := fun s => ⟨s.val,hn s.val s.val.property
    ((orderOf_coe s.val).trans s.property.1)⟩
  have hf : Function.Injective f := by
    intro a b he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun w : P.leftCore => (w:G)) he
  have hc := Nat.card_le_card_of_injective f hf
  have hx : Nat.card X = 18 := h.toCentralizerHypothesis.coreData.noncentral_involutions_card
  rw [hx,P.leftCore_card h] at hc
  omega

noncomputable def coreReflection (h : IsType z) (s : G) (hs : s∈core z) : MulAut P.R :=
  P.R.normalizerMonoidHom ⟨s,P.N_normalizes_R h (P.core_le_N h hs)⟩

theorem coreReflection_apply (h : IsType z) (s : G) (hs : s∈core z) (x : P.R) :
    (P.coreReflection h s hs x : G) = s*(x:G)*s⁻¹ := rfl

theorem root_center_mem_iff (h : IsType z) (x : P.R) :
    x∈center P.R ↔ (x:G)∈P.E := by
  rw [← P.R_center h]
  constructor
  · exact fun hx => ⟨x,hx,rfl⟩
  · rintro ⟨y,hy,he⟩
    exact (Subtype.ext he : y=x) ▸ hy

theorem coreReflection_square (h : IsType z) (s : G) (hs : s∈core z)
    (hs2 : s^2=1) (x : P.R) :
    P.coreReflection h s hs (P.coreReflection h s hs x) = x := by
  apply Subtype.ext
  simp only [coreReflection_apply]
  calc
    _ = s^2*(x:G)*(s^2)⁻¹ := by simp only [pow_two]; group
    _ = x := by rw [hs2]; simp

theorem coreReflection_quotient_fixed_card (h : IsType z) (s : G)
    (hs : s∈core z) (hsA : s∉P.leftCore) :
    Nat.card ((centerQuotientAction (P.coreReflection h s hs)).toMonoidHom.eqLocus
      (MonoidHom.id (P.R ⧸ center P.R))) = 4 := by
  let α := P.coreReflection h s hs
  let q := QuotientGroup.mk' (center P.R)
  let F := (centerQuotientAction α).toMonoidHom.eqLocus (MonoidHom.id _)
  have hf : F.comap q = P.leftCore.subgroupOf P.R := by
    ext x
    change centerQuotientAction α (q x) = q x ↔ (x:G)∈P.leftCore
    rw [centerQuotientAction_apply]
    have he : q (α x) = q x ↔ α x*x⁻¹∈center P.R := by
      rw [← QuotientGroup.eq_one_iff (α x*x⁻¹)]
      change q (α x) = q x ↔ q (α x*x⁻¹)=1
      rw [map_mul,map_inv,mul_inv_eq_one]
    rw [he,P.root_center_mem_iff h]
    exact P.reflection_fixed_coset_iff h s hs hsA x x.property
  have hB : Nat.card (F.comap q)=16 := by
    rw [hf,Nat.card_congr (subgroupOfEquivOfLe (show P.leftCore≤P.R from le_sup_left)).toEquiv,
      P.leftCore_card h]
  have hidx := (F.comap q).card_mul_index
  rw [hB,P.R_card h, F.index_comap_of_surjective (QuotientGroup.mk'_surjective _)] at hidx
  have hFidx : F.index=4 := by omega
  have hQ : Nat.card (P.R ⧸ center P.R)=16 := by
    have hh := (center P.R).card_mul_index
    rw [(P.hyperbolicFactors h).center_card,P.R_card h] at hh
    change 4 * Nat.card (P.R ⧸ center P.R) = 64 at hh
    omega
  have hcard := F.card_mul_index
  rw [hFidx,hQ] at hcard
  change Nat.card F = 4
  omega

theorem coreReflection_center_fixed_card (h : IsType z) (s : G)
    (hs : s∈core z) (hsA : s∉P.leftCore) :
    Nat.card ((centerCongr (P.coreReflection h s hs)).toMonoidHom.eqLocus
      (MonoidHom.id (center P.R))) = 2 := by
  let α := P.coreReflection h s hs
  let F := (centerCongr α).toMonoidHom.eqLocus (MonoidHom.id (center P.R))
  let f : center P.R →* G := P.R.subtype.comp (center P.R).subtype
  let D := P.E ⊓ centralizer s
  have hf : Function.Injective f := P.R.subtype_injective.comp (center P.R).subtype_injective
  have hmap : F.map f = D := by
    ext x
    constructor
    · rintro ⟨a,ha,rfl⟩
      refine ⟨(P.root_center_mem_iff h a).mp a.property,?_⟩
      apply mem_centralizer_singleton_iff.mpr
      have he := congrArg (fun y : center P.R => (y:G)) ha
      change s*(a:G)*s⁻¹=(a:G) at he
      exact (mul_inv_eq_iff_eq_mul.mp he).symm
    · rintro ⟨hxE,hxs⟩
      let a : P.R := ⟨x,P.E_le_R h hxE⟩
      let b : center P.R := ⟨a,(P.root_center_mem_iff h a).mpr hxE⟩
      refine ⟨b,?_,rfl⟩
      apply Subtype.ext
      apply Subtype.ext
      change s*x*s⁻¹=x
      rw [← mem_centralizer_singleton_iff.mp hxs,mul_inv_cancel_right]
  have hd : Nat.card D ∣ 4 := by
    simpa only [P.E_card h] using card_dvd_of_le (show D≤P.E from inf_le_left)
  have hle : Nat.card D≤4 := Nat.le_of_dvd (by decide) hd
  have hlow : 2≤Nat.card D := by
    have hz : zpowers z ≤ D := zpowers_le.mpr ⟨P.z_mem_E,
      mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp (core_le_centralizer hs)).symm⟩
    have hh := Nat.card_le_card_of_injective (inclusion hz) (inclusion_injective hz)
    simpa only [Nat.card_zpowers,h.involution] using hh
  have hn4 : Nat.card D≠4 := by
    intro hd4
    have he : D=P.E := eq_of_le_of_card_ge inf_le_left (by rw [hd4,P.E_card h])
    have hc : s∈Subgroup.centralizer (P.E:Set G) := by
      intro x hx
      exact mem_centralizer_singleton_iff.mp ((show P.E≤centralizer s from he ▸ inf_le_right) hx)
    have hsR : s∈P.R := (P.R_eq_centralizer_E h).ge hc
    exact hsA ((P.R_inf_core h).le ⟨hsR,hs⟩)
  have hn3 : Nat.card D≠3 := by intro hh; rw [hh] at hd; norm_num at hd
  have hD : Nat.card D=2 := by omega
  change Nat.card F=2
  rw [← card_map_of_injective hf, hmap, hD]


theorem coreReflection_cocycle (h : IsType z) (s : G)
    (hs : s∈core z) (hsA : s∉P.leftCore) (hs2 : s^2=1)
    (x : P.R) (hx : x * P.coreReflection h s hs x = 1) :
    ∃ y : P.R, x = y * P.coreReflection h s hs y⁻¹ := by
  let : IsElementaryAbelian 2 (center P.R) := (P.hyperbolicFactors h).center_elementary
  let : IsElementaryAbelian 2 (P.R ⧸ center P.R) := P.R_quotient_elementary h
  apply central_involution_cocycle (P.coreReflection h s hs)
    (P.coreReflection_square h s hs hs2) ?_ ?_ x hx
  · rw [P.coreReflection_center_fixed_card h s hs hsA,(P.hyperbolicFactors h).center_card]
    norm_num
  · rw [P.coreReflection_quotient_fixed_card h s hs hsA]
    have hh := (center P.R).card_mul_index
    rw [(P.hyperbolicFactors h).center_card,P.R_card h] at hh
    change 4 * Nat.card (P.R ⧸ center P.R) = 64 at hh
    norm_num
    omega

end RootPair
end Theory.GroupTheory.Recognition.UnitaryFourThree
