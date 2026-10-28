module
public import CFSG.Quasithin.Chapter6.SourceReduction.LocalSieve.RightHall
public import CFSG.Quasithin.Chapter6.SourceReduction.LocalCentralization.Contracts

/-!
# The actual Hall plane in the local A₇ configuration

The literal residual quotient in a local Cartan witness identifies the
prescribed right Hall subgroup B as cubic. Its commuting escaping cubic D
meets B trivially, so BD is elementary abelian of order nine inside X.
The two-core of the A₇ overcomponent cannot kill a nontrivial part of this
plane. Thus its actual quotient image also has order nine, as required
by the four/six-dimensional geometry in the A₇ exclusion.

Source: Aschbacher–Smith 5.1.13, printed pp.637–638.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
namespace LocalCartanWitness
variable {T : Sylow 2 G} {L W H A B Y X D : Subgroup G} {n : ℕ}

/-- The original right Hall subgroup is cubic in a local Cartan witness. -/
theorem right_hall_card_three (d : LocalCartanWitness T H A Y X D)
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B) :
    Nat.card B = 3 := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := d.residual_linear
  obtain ⟨a⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF
  let r := (pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective
  exact LocalSieve.right_hall_card_three_of_residual_A5 h hH hgen c
    ⟨(QuotientGroup.congr _ _ r (pCore_map_iso 2 r)).symm.trans (e.trans a)⟩

/-- The prescribed Hall subgroup and escaping cubic form the actual plane in X. -/
theorem hall_cubic_plane (d : LocalCartanWitness T H A Y X D)
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B) :
    IsElementaryAbelian 3 (B ⊔ D : Subgroup G) ∧ Nat.card (B ⊔ D : Subgroup G) = 9 ∧
      B ⊔ D ≤ X ∧ Disjoint B D := by
  have hBc := d.right_hall_card_three h hH hgen c
  let : IsCyclic D := isCyclic_of_prime_card d.cubic_card
  let : IsCyclic B := isCyclic_of_prime_card hBc
  let : IsElementaryAbelian 3 D := {
    toIsMulCommutative := inferInstance
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x => by
      simpa only [d.cubic_card] using (pow_card_eq_one' (x := x))) }
  let : IsElementaryAbelian 3 B := {
    toIsMulCommutative := inferInstance
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x => by
      simpa only [hBc] using (pow_card_eq_one' (x := x))) }
  have hc := c.centralizes_fermat_actor h (Or.inl rfl)
    (d.cubic_le.trans inf_le_left) d.cubic_card
  have hdis : Disjoint B D := by
    let : Fact (Nat.card D).Prime := ⟨d.cubic_card ▸ (by decide : Nat.Prime 3)⟩
    rcases (B.subgroupOf D).eq_bot_or_eq_top_of_prime_card with hb | ht
    · apply disjoint_iff.mpr
      apply eq_bot_iff.mpr
      intro x hx
      have hx' : (⟨x,hx.2⟩ : D) ∈ B.subgroupOf D := hx.1
      rw [hb] at hx'
      exact congrArg Subtype.val (mem_bot.mp hx')
    · exact (d.cubic_escape ((subgroupOf_eq_top.mp ht).trans
        ((Global.right_cartan_le_residual c).trans (residual H).le_normalizer))).elim
  refine ⟨IsElementaryAbelian.sup_of_le_centralizer (le_centralizer_iff.mp hc),?_,
    sup_le ((Global.right_cartan_le_residual c).trans d.residual_le)
      (d.cubic_le.trans inf_le_right),hdis⟩
  rw [card_sup_eq_mul_of_normalizes_of_disjoint B D
    ((le_centralizer_iff.mp hc).trans (Subgroup.centralizer_le_normalizer _)) hdis,
    hBc,d.cubic_card]

end LocalCartanWitness

/-- The same plane injects into the literal two-core quotient of the A₇ overcomponent. -/
theorem LocalA7Configuration.hall_cubic_plane_quotient
    {T : Sylow 2 G} {L W H A B Y X D K : Subgroup G} {n : ℕ}
    (a : LocalA7Configuration T L H X K)
    (d : LocalCartanWitness T H A Y X D)
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B) :
    let P := ((B ⊔ D).subgroupOf K).map (QuotientGroup.mk' (pCore 2 K))
    IsElementaryAbelian 3 P ∧ Nat.card P = 9 := by
  obtain ⟨he,hcard,hle,_⟩ := d.hall_cubic_plane h hH hgen c
  let := he
  have hPK : B ⊔ D ≤ K := hle.trans a.contains
  let : IsElementaryAbelian 3 ((B ⊔ D).subgroupOf K) := IsElementaryAbelian.subgroupOf hPK
  let q := QuotientGroup.mk' (pCore 2 K)
  have hi : Function.Injective (q.subgroupMap ((B ⊔ D).subgroupOf K)) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply eq_bot_iff.mpr
    intro x hx
    apply Subtype.ext
    have hdis : Disjoint ((B ⊔ D).subgroupOf K) (pCore 2 K) :=
      (IsElementaryAbelian.isPGroup 3 _).disjoint_of_coprime pCore_isPGroup (by decide)
    exact mem_bot.mp (hdis.le_bot ⟨x.property,
      (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val (show q.subgroupMap _ x = 1 from hx))⟩)
  refine ⟨IsElementaryAbelian.of_surjective (q.subgroupMap _) (q.subgroupMap_surjective _),?_⟩
  exact (Nat.card_congr (MulEquiv.ofBijective (q.subgroupMap _)
    ⟨hi,q.subgroupMap_surjective _⟩).toEquiv).symm.trans
      ((Nat.card_congr (subgroupOfEquivOfLe hPK).toEquiv).trans hcard)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
