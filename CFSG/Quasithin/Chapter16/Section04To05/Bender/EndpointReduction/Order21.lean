module

public import CFSG.Quasithin.Chapter16.Section04To05.Bender.Contracts
public import Theory.GroupAction.BinarySingerRegularity

/-!
# The exceptional order-21 action in the Bender branch

The actual normalizer action on V is faithful. Cauchy's theorem supplies an
order-seven subgroup; the binary Singer calculation makes it regular on the
seven nonidentity elements of V. Thus every invariant subgroup is trivial or V.
The constructed actor acts faithfully by its regular action on the moved
subgroup. Its order-three image and its conjugate have different fixed
subgroups, so they are distinct and generate the order-21 action image.
Lifting generation through the action kernel gives the ambient normalizer
containment used by the Frattini obstruction.

The final lemma excludes the unitary endpoint conditional on the genuine
embedded Sylow identity Φ(T_L) = Ω₁(T_L) and trivial component center. It
proves the generation and irreducibility premises; it does not assert either
of those model facts or complete Proposition 16.5.1.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed
p.1194, proof of Proposition 16.5.1, final paragraph.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter16.Intersections.Bender
variable {G : Type*} [Group G] [Finite G]

theorem actionImage_transitive {V : Subgroup G} [IsElementaryAbelian 2 V]
    (hV : Nat.card V = 8) (hA : Nat.card (ActionImage V) = 21)
    (x y : V) (hx : x ≠ 1) (hy : y ≠ 1) :
    ∃ a : ActionImage V, a.1 x = y := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := ActionImage V) 7
    (by rw [hA]; decide)
  let A := zpowers a
  let ρ : A →* MulAut V := (ActionImage V).subtype.comp A.subtype
  have hρ : Function.Injective ρ := Subtype.val_injective.comp Subtype.val_injective
  obtain ⟨b, hb, _⟩ := Theory.GroupAction.faithful_cyclic_binary_singer_regular ρ hρ
    (n := 3) (by decide) (by change Nat.card (zpowers a) = _; rw [Nat.card_zpowers, ha]; decide)
    hV x y hx hy
  exact ⟨b.1, hb⟩

theorem actionImage_irreducible {V : Subgroup G} [IsElementaryAbelian 2 V]
    (hV : Nat.card V = 8) (hA : Nat.card (ActionImage V) = 21)
    (W : Subgroup G) (hWV : W ≤ V)
    (hW : normalizer (V : Set G) ≤ normalizer (W : Set G)) : W = ⊥ ∨ W = V := by
  by_cases he : W = ⊥
  · exact Or.inl he
  right
  apply le_antisymm hWV
  obtain ⟨x, hx1⟩ := W.ne_bot_iff_exists_ne_one.mp he
  intro y hy
  by_cases hy1 : y = 1
  · simp [hy1]
  obtain ⟨a, ha⟩ := actionImage_transitive hV hA
    (⟨x, hWV x.property⟩ : V) ⟨y, hy⟩
    (fun h => hx1 (Subtype.ext (congrArg (fun v : V => (v : G)) h)))
    (fun h => hy1 (congrArg Subtype.val h))
  obtain ⟨g, hg⟩ := V.normalizerMonoidHom.rangeRestrict_surjective a
  have hgxy : (g : G) * x * (g : G)⁻¹ = y := by
    have hh := congrArg (fun b : ActionImage V => b.1 ⟨x, hWV x.property⟩) hg
    exact congrArg Subtype.val (hh.trans ha)
  exact hgxy ▸ (mem_normalizer_iff.mp (hW g.property) x).mp x.property

private theorem sup_eq_top_of_card_three {A : Type*} [Group A] [Finite A]
    (hA : Nat.card A = 21) {X Y : Subgroup A}
    (hX : Nat.card X = 3) (hY : Nat.card Y = 3) (hne : X ≠ Y) : X ⊔ Y = ⊤ := by
  have hd := (X ⊔ Y).card_subgroup_dvd_card
  rw [hA] at hd
  have hd3 := card_dvd_of_le (show X ≤ X ⊔ Y from le_sup_left)
  rw [hX] at hd3
  have hchoices : Nat.card ↥(X ⊔ Y) = 3 ∨ Nat.card ↥(X ⊔ Y) = 21 := by
    have hm := Nat.mem_divisors.mpr ⟨hd, (by decide : 21 ≠ 0)⟩
    rw [show Nat.divisors 21 = {1, 3, 7, 21} from by decide] at hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with h | h | h | h
    · norm_num [h] at hd3
    · exact Or.inl h
    · norm_num [h] at hd3
    · exact Or.inr h
  rcases hchoices with h | h
  · exact False.elim (hne ((eq_of_le_of_card_ge le_sup_left (by omega)).trans
      (eq_of_le_of_card_ge le_sup_right (by omega)).symm))
  · exact (X ⊔ Y).eq_top_of_card_eq (h.trans hA.symm)

omit [Finite G] in
private theorem inducedActor_conjugate {V X : Subgroup G}
    (hX : X ≤ normalizer (V : Set G)) {g : G}
    (hg : g ∈ normalizer (V : Set G)) :
    inducedActor V (X.conjBy g) = (inducedActor V X).conjBy
      (V.normalizerMonoidHom.rangeRestrict ⟨g, hg⟩) := by
  let N := normalizer (V : Set G)
  let a : N := ⟨g, hg⟩
  have he : (X.conjBy g).subgroupOf N = (X.subgroupOf N).conjBy a := by
    ext x
    constructor
    · rintro ⟨y, hy, hyx⟩
      exact ⟨⟨y, hX hy⟩, hy, Subtype.ext hyx⟩
    · rintro ⟨y, hy, hyx⟩
      exact ⟨y, hy, congrArg Subtype.val hyx⟩
  change ((X.conjBy g).subgroupOf N).map _ = _
  rw [he]
  change ((X.subgroupOf N).map (MulAut.conj a).toMonoidHom).map _ =
    ((X.subgroupOf N).map _).map (MulAut.conj _).toMonoidHom
  rw [map_map, map_map]
  congr 1
  apply MonoidHom.ext
  intro x
  change V.normalizerMonoidHom.rangeRestrict (a * x * a⁻¹) =
    V.normalizerMonoidHom.rangeRestrict a * V.normalizerMonoidHom.rangeRestrict x *
      (V.normalizerMonoidHom.rangeRestrict a)⁻¹
  simp only [map_mul, map_inv]

omit [Finite G] in
private theorem fixed_eq_of_inducedActor_eq {V X Y : Subgroup G}
    (hX : X ≤ normalizer (V : Set G)) (hY : Y ≤ normalizer (V : Set G))
    (he : inducedActor V X = inducedActor V Y) :
    V ⊓ centralizer (X : Set G) = V ⊓ centralizer (Y : Set G) := by
  suffices h : ∀ X Y : Subgroup G, X ≤ normalizer (V : Set G) →
      Y ≤ normalizer (V : Set G) → inducedActor V X = inducedActor V Y →
      V ⊓ centralizer (X : Set G) ≤ V ⊓ centralizer (Y : Set G) from
    le_antisymm (h X Y hX hY he) (h Y X hY hX he.symm)
  intro X Y _ hY he v hv
  refine ⟨hv.1, ?_⟩
  intro y hy
  have hm : V.normalizerMonoidHom.rangeRestrict ⟨y, hY hy⟩ ∈ inducedActor V X := by
    rw [he]
    exact mem_map_of_mem _ hy
  obtain ⟨x, hx, hxy⟩ := hm
  have heval := congrArg (fun a : ActionImage V => ((a : MulAut V) ⟨v, hv.1⟩ : G)) hxy
  change (x : G) * v * (x : G)⁻¹ = y * v * y⁻¹ at heval
  have hxv : (x : G) * v * (x : G)⁻¹ = v := by
    rw [hv.2 (x : G) hx, mul_inv_cancel_right]
  exact (mul_inv_eq_iff_eq_mul.mp (heval.symm.trans hxv))

private theorem conjugate_image_ne_of_moving_fixed {V X U : Subgroup G}
    (hX : X ≤ normalizer (V : Set G)) {g : G}
    (hg : g ∈ normalizer (V : Set G))
    (hfixed : V ⊓ centralizer (X : Set G) = U)
    (hmove : g ∉ normalizer (U : Set G)) :
    inducedActor V X ≠ inducedActor V (X.conjBy g) := by
  intro he
  have hY : X.conjBy g ≤ normalizer (V : Set G) := by
    calc
      X.conjBy g ≤ (normalizer (V : Set G)).conjBy g := map_mono hX
      _ = normalizer (V : Set G) := mem_normalizer_iff_map_conj_eq.mp
        ((normalizer (V : Set G)).le_normalizer hg)
  have hf := fixed_eq_of_inducedActor_eq hX hY he
  have hle : U.conjBy g ≤ U := by
    rw [← hfixed, hf]
    rw [← hf]
    calc
      (V ⊓ centralizer (X : Set G)).conjBy g ≤
          V ⊓ centralizer (X.conjBy g : Set G) := by
        apply le_inf
        · exact (map_mono inf_le_left).trans_eq (mem_normalizer_iff_map_conj_eq.mp hg)
        · exact (map_mono inf_le_right).trans (map_centralizer_le_centralizer_image _ _)
      _ = V ⊓ centralizer (X : Set G) := hf.symm
  apply hmove
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply eq_of_le_of_card_ge hle
  rw [show U.conjBy g = U.map (MulAut.conj g).toMonoidHom from rfl,
    card_map_of_injective (MulAut.conj g).injective]

theorem Geometry.actorAction_injective {T : Sylow 2 G} {L R : Subgroup G} {n : ℕ}
    (d : Geometry T L R n) :
    Function.Injective ((benderSpace T L).normalizerMonoidHom.rangeRestrict.comp
      (inclusion d.actor_normalizes)) := by
  let f := (benderSpace T L).normalizerMonoidHom.rangeRestrict.comp
    (inclusion d.actor_normalizes)
  apply (MonoidHom.ker_eq_bot_iff f).mp
  apply f.ker.eq_bot_iff_forall.mpr
  intro a ha
  have hne : (⁅benderSpace T L, d.actor⁆ : Subgroup G) ≠ ⊥ := by
    apply (Subgroup.one_lt_card_iff_ne_bot _).mp
    rw [d.moved_card]
    have hn := d.degree
    have hp := Nat.lt_two_pow_self (n := n)
    omega
  obtain ⟨v, hv1⟩ := ne_bot_iff_exists_ne_one.mp hne
  have hv : (v : G) ∈ benderSpace T L := (le_sup_right.trans_eq d.span) v.property
  have hv1' : (v : G) ≠ 1 := fun h => hv1 (Subtype.ext h)
  obtain ⟨b, _, hb⟩ := d.regular v v.property hv1' v v.property hv1'
  have ha' : MulAut.conj (a : G) v = v := by
    have hh := congrArg (fun f : ActionImage (benderSpace T L) =>
      ((f : MulAut (benderSpace T L)) ⟨v, hv⟩ : G)) ha
    exact hh
  exact (hb a ha').trans (hb 1 (by simp)).symm

theorem Geometry.inducedActor_card {T : Sylow 2 G} {L R : Subgroup G} {n : ℕ}
    (d : Geometry T L R n) :
    Nat.card (inducedActor (benderSpace T L) d.actor) = 2 ^ n - 1 := by
  let f := (benderSpace T L).normalizerMonoidHom.rangeRestrict.comp
    (inclusion d.actor_normalizes)
  have he : f.range = inducedActor (benderSpace T L) d.actor := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact mem_map_of_mem _ a.property
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, ha⟩, rfl⟩
  rw [← he, ← Nat.card_congr (MonoidHom.ofInjective d.actorAction_injective).toEquiv]
  exact d.actor_card

theorem Geometry.actor_images_generate {T : Sylow 2 G} {z : G} {L R : Subgroup G} {n : ℕ}
    (d : Geometry T L R n) (h : StandardSetup T z L)
    (hfaith : Disjoint R (centralizer (L : Set G)))
    (hUC : Nat.card (omegaOneAmbient (commutingSylow T L)) = 2)
    (hV : Nat.card (benderSpace T L) = 8)
    (hA : Nat.card (ActionImage (benderSpace T L)) = 21) :
    inducedActor (benderSpace T L) d.actor ⊔
      inducedActor (benderSpace T L) (d.actor.conjBy d.mover) = ⊤ := by
  have hn := d.degree_eq_two hUC hV
  have hc : Nat.card (inducedActor (benderSpace T L) d.actor) = 3 := by
    rw [d.inducedActor_card, hn]
    decide
  apply sup_eq_top_of_card_three hA hc
  · rw [inducedActor_conjugate d.actor_normalizes d.mover_normalizes]
    rw [show (inducedActor (benderSpace T L) d.actor).conjBy _ =
      (inducedActor (benderSpace T L) d.actor).map (MulAut.conj _).toMonoidHom from rfl,
      card_map_of_injective (MulAut.conj _).injective, hc]
  · exact conjugate_image_ne_of_moving_fixed d.actor_normalizes d.mover_normalizes
      d.fixed_eq (moving_commuting_omega h hfaith d.mover_eq.symm)

theorem Geometry.normalizer_le_actor_join {T : Sylow 2 G} {z : G}
    {L R : Subgroup G} {n : ℕ} (d : Geometry T L R n) (h : StandardSetup T z L)
    (hfaith : Disjoint R (centralizer (L : Set G)))
    (hUC : Nat.card (omegaOneAmbient (commutingSylow T L)) = 2)
    (hV : Nat.card (benderSpace T L) = 8)
    (hA : Nat.card (ActionImage (benderSpace T L)) = 21) :
    normalizer (benderSpace T L : Set G) ≤ centralizer (benderSpace T L : Set G) ⊔
      (d.actor ⊔ d.actor.conjBy d.mover) := by
  let V := benderSpace T L
  let N := normalizer (V : Set G)
  let f := V.normalizerMonoidHom.rangeRestrict
  have hY : d.actor.conjBy d.mover ≤ N := by
    calc
      d.actor.conjBy d.mover ≤ N.conjBy d.mover := map_mono d.actor_normalizes
      _ = N := mem_normalizer_iff_map_conj_eq.mp (N.le_normalizer d.mover_normalizes)
  have hm : ((d.actor ⊔ d.actor.conjBy d.mover).subgroupOf N).map f = ⊤ := by
    rw [subgroupOf_sup d.actor_normalizes hY, Subgroup.map_sup]
    exact d.actor_images_generate h hfaith hUC hV hA
  intro a ha
  have hh : f ⟨a, ha⟩ ∈ ((d.actor ⊔ d.actor.conjBy d.mover).subgroupOf N).map f :=
    hm ▸ mem_top _
  obtain ⟨b, hb, hba⟩ := hh
  have hk : (⟨a, ha⟩ : N) * b⁻¹ ∈ V.normalizerMonoidHom.ker := by
    have hf : f ((⟨a, ha⟩ : N) * b⁻¹) = 1 := by rw [map_mul, map_inv, hba, mul_inv_cancel]
    exact congrArg Subtype.val hf
  rw [normalizerAction_kernel] at hk
  have hc : a * (b : G)⁻¹ ∈ centralizer (V : Set G) := hk
  simpa only [inv_mul_cancel_right] using mul_mem_sup hc
    (show (b : G) ∈ d.actor ⊔ d.actor.conjBy d.mover from hb)

omit [Finite G] in
theorem component_omega_ne_bot {T : Sylow 2 G} {L : Subgroup G}
    (hUC : Nat.card (omegaOneAmbient (commutingSylow T L)) = 2)
    (hV : Nat.card (benderSpace T L) = 8) :
    omegaOneAmbient (componentSylow T L) ≠ ⊥ := by
  intro he
  have hv : benderSpace T L = omegaOneAmbient (commutingSylow T L) := by
    simp [benderSpace, he]
  rw [hv, hUC] at hV
  contradiction

omit [Finite G] in
theorem component_omega_ne_space {T : Sylow 2 G} {L : Subgroup G}
    (hc : center L = ⊥)
    (hUC : Nat.card (omegaOneAmbient (commutingSylow T L)) = 2) :
    omegaOneAmbient (componentSylow T L) ≠ benderSpace T L := by
  intro he
  have hbot : omegaOneAmbient (commutingSylow T L) = ⊥ := by
    apply (omegaOneAmbient (commutingSylow T L)).eq_bot_iff_forall.mpr
    intro x hx
    have hxV : x ∈ benderSpace T L := mem_sup_left hx
    have hxL : x ∈ L := ((omegaOneAmbient_le _).trans inf_le_right) (he.symm ▸ hxV)
    have hxC : x ∈ centralizer (L : Set G) :=
      ((omegaOneAmbient_le _).trans inf_le_right) hx
    have hz : (⟨x, hxL⟩ : L) ∈ center L := by
      rw [mem_center_iff]
      intro y
      exact Subtype.ext (hxC y y.property)
    rw [hc, mem_bot] at hz
    exact congrArg Subtype.val hz
  rw [hbot, card_bot] at hUC
  contradiction

theorem Geometry.unitary_frattini_contradiction {T : Sylow 2 G} {z : G}
    {L R : Subgroup G} {n : ℕ} (d : Geometry T L R n) (h : StandardSetup T z L)
    (hfaith : Disjoint R (centralizer (L : Set G)))
    (hUC : Nat.card (omegaOneAmbient (commutingSylow T L)) = 2)
    (hV : Nat.card (benderSpace T L) = 8)
    (hA : Nat.card (ActionImage (benderSpace T L)) = 21)
    (hc : center L = ⊥)
    (hu : ClassicalGroup.IsPSU (L ⧸ center L) 3 (2 ^ n))
    (hphi : (frattini (componentSylow T L)).map (componentSylow T L).subtype =
      omegaOneAmbient (componentSylow T L)) : False := by
  let := d.elementary
  apply frattini_obstruction (d.actor_le.trans inf_le_right) (d.unitary_mover hu)
    (d.normalizer_le_actor_join h hfaith hUC hV hA)
  · rw [hphi]
    exact le_sup_right
  · rw [hphi]
    exact component_omega_ne_bot hUC hV
  · rw [hphi]
    exact component_omega_ne_space hc hUC
  · exact actionImage_irreducible hV hA

end CFSG.Quasithin.Chapter16.Intersections.Bender
