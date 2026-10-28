module

public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.SourceStatements
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.GlobalClosure.Restriction
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.GlobalClosure.LocalGeometry.PairGeometry

/-!
# Centralizer Sylow reselection in Aschbacher 3.4(d)

A Sylow subgroup of C_G(u) containing C_S(u) lies in H by source (c).
Sylow conjugacy inside H moves it into S. At the conjugate v of u, its
image equals C_S(v), so the restriction theorem applies to the actual
centralizer and the actual relative factors.

The old relative factors return to the union of the new ones by (*).
If they both enter one factor, v enters that factor too, and the other full
factor centralizes v. Thus both new relative factors still have rank at least
two. A nested new pair would force the corresponding full ambient factors
to be nested, contradicting the original nonnesting clauses.

The induction reduction excludes the nested alternative and explicitly leaves
the exceptional dihedral/semidihedral alternative to its model-transport
consumer. It is not the unconditional source assertion (d).

Source: M. Aschbacher, *On finite groups of component type*, Illinois J. Math.
19 (1975), Lemma 3.4(d), printed p.95, DOI 10.1215/ijm/1256050927.
-/

public section
namespace CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75
open Subgroup Theory.GroupTheory BenderSuzuki.PFchapter1section1
open scoped Pointwise
universe u
variable {G : Type u} [Group G] {S : Sylow 2 G} {A₁ A₂ : Subgroup G}

private theorem rank_injective {X Y : Type*} [Group X] [Group Y]
    (f : X →* Y) (hf : Function.Injective f) (hr : TwoRankAtLeastTwo X) :
    TwoRankAtLeastTwo Y := by
  obtain ⟨E, hE, hs⟩ := hr
  refine ⟨E.map f, (card_map_of_injective hf).trans hE, ?_⟩
  rintro ⟨y, x, hx, rfl⟩
  apply Subtype.ext
  change f x ^ 2 = 1
  rw [← map_pow, show x ^ 2 = 1 from congrArg Subtype.val (hs ⟨x, hx⟩), map_one]

/-- A product of the commuting factors decomposes into elements of its two
actual relative centralizers. -/
theorem centralizer_reselection_factorization (hc : ⁅A₁, A₂⁆ = ⊥) {u : G}
    (hu : u ∈ A₁ ⊔ A₂) :
    ∃ a ∈ A₁, ∃ b ∈ A₂, a * b = u ∧
      a ∈ centralizer ({u} : Set G) ∧ b ∈ centralizer ({u} : Set G) := by
  have hab : ∀ a ∈ A₁, ∀ b ∈ A₂, Commute a b := by
    intro a ha b hb
    exact (mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hc ha) b hb).symm
  have hp : u ∈ (A₁ : Set G) * (A₂ : Set G) := by
    rw [← coe_mul_of_left_le_normalizer_right A₁ A₂
      ((commutator_eq_bot_iff_le_centralizer.mp hc).trans (Subgroup.centralizer_le_normalizer _))]
    exact hu
  obtain ⟨a, ha, b, hb, rfl⟩ := hp
  exact ⟨a, ha, b, hb, rfl,
    mem_centralizer_singleton_iff.mpr ((Commute.refl a).mul_right (hab a ha b hb)).eq,
    mem_centralizer_singleton_iff.mpr ((hab a ha b hb).symm.mul_right (Commute.refl b)).eq⟩

private theorem centralizer_map (e : G ≃* G) (u : G) :
    (centralizer ({u} : Set G)).map e.toMonoidHom = centralizer ({e u} : Set G) := by
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    simpa only [map_mul, MulEquiv.coe_toMonoidHom] using congrArg e (mem_centralizer_singleton_iff.mp hx)
  · intro y hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    apply mem_centralizer_singleton_iff.mpr
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using mem_centralizer_singleton_iff.mp hy

/-- Right conjugation identifies the actual element centralizers. -/
def centralizerReselectionEquiv (u g : G) :
    centralizer ({u} : Set G) ≃* centralizer ({g⁻¹ * u * g} : Set G) :=
  ((MulAut.conj g⁻¹).subgroupMap (centralizer ({u} : Set G))).trans
    (MulEquiv.subgroupCongr (by simpa using centralizer_map (MulAut.conj g⁻¹) u))

/-- The centralizer equivalence uses the source right-conjugation convention. -/
theorem centralizerReselectionEquiv_apply (u g : G) (x : centralizer ({u} : Set G)) :
    (centralizerReselectionEquiv u g x : G) = g⁻¹ * (x : G) * g := by
  simp [centralizerReselectionEquiv]

private theorem rank_mono {X : Type*} [Group X] {A B : Subgroup X}
    (hAB : A ≤ B) (hr : TwoRankAtLeastTwo A) : TwoRankAtLeastTwo B :=
  rank_injective (inclusion hAB) (inclusion_injective hAB) hr

variable [Finite G]

/-- Move a Sylow subgroup of the actual centralizer into S by conjugation
inside H. The original relative factors return to the union, and both new
relative factors still have rank at least two and are nonnested. -/
theorem Hypotheses.exists_centralizer_reselection (h : Hypotheses S A₁ A₂)
    (hperm : ∀ s ∈ S,
      (conjugate A₁ s = A₁ ∧ conjugate A₂ s = A₂) ∨
      (conjugate A₁ s = A₂ ∧ conjugate A₂ s = A₁))
    (u : G) (hu : u ∈ A₁ ⊔ A₂)
    (hr₁ : TwoRankAtLeastTwo (A₁.subgroupOf (centralizer ({u} : Set G))))
    (hr₂ : TwoRankAtLeastTwo (A₂.subgroupOf (centralizer ({u} : Set G))))
    (hn₁ : ¬ A₁ ⊓ centralizer ({u} : Set G) ≤ A₂)
    (hn₂ : ¬ A₂ ⊓ centralizer ({u} : Set G) ≤ A₁) :
    ∃ g ∈ intersectionGenerated A₁ A₂,
      let v := g⁻¹ * u * g
      let L := centralizer ({v} : Set G)
      v ∈ A₁ ⊔ A₂ ∧
      (∀ x ∈ (A₁ : Set G) ∪ A₂, x ∈ centralizer ({u} : Set G) →
        g⁻¹ * x * g ∈ (A₁ : Set G) ∪ A₂) ∧
      (∃ Q : Sylow 2 L, (Q : Subgroup L) = (S : Subgroup G).subgroupOf L) ∧
      TwoRankAtLeastTwo (A₁.subgroupOf L) ∧
      TwoRankAtLeastTwo (A₂.subgroupOf L) ∧
      (¬ A₁ ⊓ L ≤ A₂) ∧ (¬ A₂ ⊓ L ≤ A₁) := by
  let K := centralizer ({u} : Set G)
  let H := intersectionGenerated A₁ A₂
  obtain ⟨P, hSP, hPH⟩ := h.exists_centralizer_sylow_le_generated u hr₁
  have hSH : (S : Subgroup G) ≤ H := h.sylow_le_generated_of_permuting hperm
  obtain ⟨T, hET⟩ := ((P.isPGroup'.map K.subtype).comap_subtype (K := H)).exists_le_sylow
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq H T (S.subtype hSH)
  let g := (k : G)⁻¹
  have hg : g ∈ H := H.inv_mem k.property
  let v := g⁻¹ * u * g
  let L := centralizer ({v} : Set G)
  let e : K ≃* L := centralizerReselectionEquiv u g
  have he (x : K) : (e x : G) = g⁻¹ * (x : G) * g := centralizerReselectionEquiv_apply u g x
  have hplace (x : K) (hx : x ∈ P) : (e x : G) ∈ S := by
    let y : H := ⟨x, hPH (mem_map_of_mem K.subtype hx)⟩
    have hy : y ∈ T := hET (mem_map_of_mem K.subtype hx)
    have hky : k * y * k⁻¹ ∈ S.subtype hSH := by
      rw [← hk]
      exact mem_map_of_mem (MulAut.conj k).toMonoidHom hy
    change (k : G) * (x : G) * (k : G)⁻¹ ∈ S at hky
    change (centralizerReselectionEquiv u g x : G) ∈ S
    rw [centralizerReselectionEquiv_apply]
    simpa only [g, inv_inv] using hky
  let Q : Sylow 2 L := P.mapSurjective (f := e.toMonoidHom) e.surjective
  have hQle : (Q : Subgroup L) ≤ (S : Subgroup G).subgroupOf L := by
    rintro _ ⟨x, hx, rfl⟩
    exact hplace x hx
  have hQ : (Q : Subgroup L) = (S : Subgroup G).subgroupOf L :=
    (Q.is_maximal' (S.isPGroup'.comap_subtype (K := L)) hQle).symm
  have hreturn (x : G) (hx : x ∈ (A₁ : Set G) ∪ A₂) (hxK : x ∈ K) :
      g⁻¹ * x * g ∈ (A₁ : Set G) ∪ A₂ := by
    have hxP : (⟨x, hxK⟩ : K) ∈ P := hSP
      (hx.elim (fun ha => h.left_le ha) (fun ha => h.right_le ha))
    apply h.closed_in_generated.2 x hx g hg
    exact ⟨H.mul_mem (H.mul_mem (H.inv_mem hg) (h.union_subset_generated hx)) hg,
      by
        change g⁻¹ * x * g ∈ S
        simpa only [he] using hplace ⟨x, hxK⟩ hxP⟩
  obtain ⟨a, ha, b, hb, hab, haK, hbK⟩ := centralizer_reselection_factorization h.commute hu
  have hev : e ⟨a, haK⟩ * e ⟨b, hbK⟩ = (⟨v, mem_centralizer_singleton_iff.mpr rfl⟩ : L) := by
    apply Subtype.ext
    change (e ⟨a, haK⟩ : G) * (e ⟨b, hbK⟩ : G) = v
    rw [he, he]
    change g⁻¹ * a * g * (g⁻¹ * b * g) = g⁻¹ * u * g
    rw [← hab]
    group
  have hv : v ∈ A₁ ⊔ A₂ := by
    have hm := (A₁ ⊔ A₂).mul_mem
      ((hreturn a (Or.inl ha) haK).elim (fun hh => mem_sup_left hh) (fun hh => mem_sup_right hh))
      ((hreturn b (Or.inr hb) hbK).elim (fun hh => mem_sup_left hh) (fun hh => mem_sup_right hh))
    simpa only [← hab, v, mul_assoc, mul_inv_cancel_left] using hm
  let D₁ := (A₁.subgroupOf K).map e.toMonoidHom
  let D₂ := (A₂.subgroupOf K).map e.toMonoidHom
  have hDr₁ : TwoRankAtLeastTwo D₁ := rank_injective
    (e.subgroupMap (A₁.subgroupOf K)).toMonoidHom (e.subgroupMap _).injective hr₁
  have hDr₂ : TwoRankAtLeastTwo D₂ := rank_injective
    (e.subgroupMap (A₂.subgroupOf K)).toMonoidHom (e.subgroupMap _).injective hr₂
  have hD₁ : D₁ ≤ A₁.subgroupOf L ∨ D₁ ≤ A₂.subgroupOf L := by
    apply SubgroupClass.subset_union.mp
    rintro _ ⟨x, hx, rfl⟩
    change (e.toMonoidHom x : G) ∈ (A₁ : Set G) ∪ A₂
    simpa only [MulEquiv.coe_toMonoidHom, he] using hreturn x (Or.inl hx) x.property
  have hD₂ : D₂ ≤ A₁.subgroupOf L ∨ D₂ ≤ A₂.subgroupOf L := by
    apply SubgroupClass.subset_union.mp
    rintro _ ⟨x, hx, rfl⟩
    change (e.toMonoidHom x : G) ∈ (A₁ : Set G) ∪ A₂
    simpa only [MulEquiv.coe_toMonoidHom, he] using hreturn x (Or.inr hx) x.property
  have haD : e ⟨a, haK⟩ ∈ D₁ := mem_map_of_mem e.toMonoidHom ha
  have hbD : e ⟨b, hbK⟩ ∈ D₂ := mem_map_of_mem e.toMonoidHom hb
  have hcentral {A B : Subgroup G} (hc : ⁅A, B⁆ = ⊥) (hvB : v ∈ B) : A ≤ L := by
    intro x hx
    exact mem_centralizer_singleton_iff.mpr
      ((mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hc hx) v hvB).symm)
  have hranks : TwoRankAtLeastTwo (A₁.subgroupOf L) ∧
      TwoRankAtLeastTwo (A₂.subgroupOf L) := by
    rcases hD₁ with hD₁ | hD₁ <;> rcases hD₂ with hD₂ | hD₂
    · have hvA : v ∈ A₁ := by
        have hh := (A₁.subgroupOf L).mul_mem (hD₁ haD) (hD₂ hbD)
        rw [hev] at hh
        exact hh
      let e₂ := subgroupOfEquivOfLe (hcentral (by simpa only [commutator_comm] using h.commute) hvA)
      exact ⟨rank_mono hD₁ hDr₁, rank_injective e₂.symm.toMonoidHom e₂.symm.injective h.right_rank⟩
    · exact ⟨rank_mono hD₁ hDr₁, rank_mono hD₂ hDr₂⟩
    · exact ⟨rank_mono hD₂ hDr₂, rank_mono hD₁ hDr₁⟩
    · have hvA : v ∈ A₂ := by
        have hh := (A₂.subgroupOf L).mul_mem (hD₁ haD) (hD₂ hbD)
        rw [hev] at hh
        exact hh
      let e₁ := subgroupOfEquivOfLe (hcentral h.commute hvA)
      exact ⟨rank_injective e₁.symm.toMonoidHom e₁.symm.injective h.left_rank, rank_mono hD₁ hDr₁⟩
  have hnleft : ¬ A₁ ⊓ L ≤ A₂ := by
    intro hnest
    obtain ⟨c, hc, d, hd, hcd, hcL, _⟩ := centralizer_reselection_factorization h.commute hv
    have hvA : v ∈ A₂ := hcd ▸ A₂.mul_mem (hnest ⟨hc, hcL⟩) hd
    exact hn₁ (inf_le_left.trans (fun x hx => hnest ⟨hx, hcentral h.commute hvA hx⟩))
  have hnright : ¬ A₂ ⊓ L ≤ A₁ := by
    intro hnest
    obtain ⟨c, hc, d, hd, hcd, _, hdL⟩ := centralizer_reselection_factorization h.commute hv
    have hvA : v ∈ A₁ := hcd ▸ A₁.mul_mem hc (hnest ⟨hd, hdL⟩)
    exact hn₂ (inf_le_left.trans (fun x hx => hnest ⟨hx, hcentral (by simpa only [commutator_comm] using h.commute) hvA hx⟩))
  exact ⟨g, hg, hv, hreturn, ⟨Q, hQ⟩, hranks.1, hranks.2, hnleft, hnright⟩

/-- The actual centralizer induction after Sylow reselection. The only
remaining premise excludes the third source alternative for the new relative
factors. In particular, no local Sylow-placement premise remains.

The exceptional-model transport must derive `hexclude` from the original
rank, nonnesting and model assumptions before using this as source (d). -/
theorem MinimalCounterexample.centralizer_alternative_of_reselection_exclusions
    (m : MinimalCounterexample S A₁ A₂)
    (hperm : ∀ s ∈ S,
      (conjugate A₁ s = A₁ ∧ conjugate A₂ s = A₂) ∨
      (conjugate A₁ s = A₂ ∧ conjugate A₂ s = A₁))
    (u : G) (hu : u ∈ A₁ ⊔ A₂)
    (hr₁ : TwoRankAtLeastTwo (A₁.subgroupOf (centralizer ({u} : Set G))))
    (hr₂ : TwoRankAtLeastTwo (A₂.subgroupOf (centralizer ({u} : Set G))))
    (hn₁ : ¬ A₁ ⊓ centralizer ({u} : Set G) ≤ A₂)
    (hn₂ : ¬ A₂ ⊓ centralizer ({u} : Set G) ≤ A₁)
    (hexclude : ∀ g ∈ intersectionGenerated A₁ A₂,
      let v := g⁻¹ * u * g
      v ∈ A₁ ⊔ A₂ →
      (∀ x ∈ (A₁ : Set G) ∪ A₂, x ∈ centralizer ({u} : Set G) →
        g⁻¹ * x * g ∈ (A₁ : Set G) ∪ A₂) →
      ¬ Exceptional (A₁.subgroupOf (centralizer ({v} : Set G)))
        (A₂.subgroupOf (centralizer ({v} : Set G)))) :
    centralizer ({u} : Set G) = ⊤ ∨
      centralizer ({u} : Set G) ≤ intersectionGenerated A₁ A₂ := by
  obtain ⟨g, hg, hv, hreturn, ⟨Q, hQ⟩, hrL₁, hrL₂, hnL₁, hnL₂⟩ :=
    m.setup.exists_centralizer_reselection hperm u hu hr₁ hr₂ hn₁ hn₂
  let v := g⁻¹ * u * g
  let L := centralizer ({v} : Set G)
  by_cases hL : L = ⊤
  · left
    apply top_unique
    intro x _
    have hx : g⁻¹ * x * g ∈ L := hL.symm ▸ mem_top _
    apply mem_centralizer_singleton_iff.mpr
    apply (MulAut.conj g⁻¹).injective
    simpa only [map_mul, MulAut.conj_apply, inv_inv] using
      mem_centralizer_singleton_iff.mp hx
  · have hcard : Nat.card L < Nat.card G :=
      lt_of_le_of_ne (card_le_card_group L) (fun he => hL (L.eq_top_of_card_eq he))
    have hlocal : Hypotheses Q (A₁.subgroupOf L) (A₂.subgroupOf L) := by
      apply m.setup.restrict L Q hQ hrL₁ hrL₂
      · intro x hx hN
        have hxS : (x : G) ∈ S := by
          change x ∈ (Q : Subgroup L) at hx
          rw [hQ] at hx
          exact hx
        exact normalizer_restriction_of_permuting
          (fun s hs => (hperm s hs).imp And.left And.left) hnL₁ x hxS hN
      · intro x hx hN
        have hxS : (x : G) ∈ S := by
          change x ∈ (Q : Subgroup L) at hx
          rw [hQ] at hx
          exact hx
        exact normalizer_restriction_of_permuting
          (fun s hs => (hperm s hs).imp And.right And.right) hnL₂ x hxS hN
    rcases m.smaller hcard Q (A₁.subgroupOf L) (A₂.subgroupOf L) hlocal with
      hgen | ⟨hnest, _⟩ | he
    · have hLH : L ≤ intersectionGenerated A₁ A₂ := by
        intro x hx
        apply intersectionGenerated_subgroupOf_le L (x := ⟨x, hx⟩)
        rw [hgen]
        exact mem_top _
      right
      intro x hx
      have hxe : (centralizerReselectionEquiv u g ⟨x, hx⟩ : G) ∈ L :=
        (centralizerReselectionEquiv u g ⟨x, hx⟩).property
      rw [centralizerReselectionEquiv_apply] at hxe
      simpa only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel_right, mul_inv_cancel, mul_one] using
        (intersectionGenerated A₁ A₂).mul_mem
          ((intersectionGenerated A₁ A₂).mul_mem hg (hLH hxe))
          ((intersectionGenerated A₁ A₂).inv_mem hg)
    · rcases hnest with hnest | hnest
      · exact (hnL₁ (fun x hx => hnest
          (show (⟨x, hx.2⟩ : L) ∈ A₁.subgroupOf L from hx.1))).elim
      · exact (hnL₂ (fun x hx => hnest
          (show (⟨x, hx.2⟩ : L) ∈ A₂.subgroupOf L from hx.1))).elim
    · exact (hexclude g hg hv hreturn he).elim

end CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75

end
