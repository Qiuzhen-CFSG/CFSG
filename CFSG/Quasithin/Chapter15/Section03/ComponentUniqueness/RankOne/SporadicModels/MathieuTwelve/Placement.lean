module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.SporadicModels.LocalConfiguration
public import Theory.Mathieu.M12.SmallParabolicPair.NormalFour
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# Placing the source normal four in the M₁₂ component

The equality V = [V,Y] puts V inside the normal component K. Restricting
the ambient Sylow subgroup to K and conjugating inside M₁₂ aligns V with
the unique marked normal four. Hence M ∩ K lies in its normalizer and
contains the marked Sylow subgroup, of index three in that normalizer.
It is larger than the Sylow subgroup because a three-residual contained
in a two-group is trivial, contrary to the full action on V.

Thus the same component marking identifies M ∩ K with the second
parabolic and puts its three-residual inside the image of Y. This applies
to every faithful almost-simple ambient group in the local configuration.
Source: Aschbacher–Smith, 15.3.43, sporadic paragraph, printed p.1140.
-/

public section
open Subgroup Sporadic.Mathieu Sporadic.Mathieu.M12SmallPair
namespace CFSG.Quasithin.Chapter15.Section03.RankOne.SporadicModels.MathieuTwelve

variable {G : Type*} [Group G] {K S M Y V : Subgroup G}

/-- The moving normal four-group lies in the component. -/
theorem plane_le_component (c : LocalConfiguration K S M Y V) : V ≤ K := by
  let : K.Normal := c.normal
  rw [← c.plane_commutator]
  exact (commutator_mono le_rfl c.y_le_component).trans (commutator_le_right V K)

variable [Finite G]

/-- A marking of the component simultaneously aligns its Sylow subgroup and its normal four. -/
theorem exists_plane_marking (c : LocalConfiguration K S M Y V) (e : K ≃* M12) :
    ∃ f : K ≃* M12,
      (S.subgroupOf K).map f.toMonoidHom = sylowCandidate ∧
      (V.subgroupOf K).map f.toMonoidHom = natural := by
  let : K.Normal := c.normal
  obtain ⟨P, hP⟩ := c.sylow
  obtain ⟨T, hT⟩ := P.exists_subgroupOf_eq_of_normal K
  have hT' : (T : Subgroup K) = S.subgroupOf K := hT.trans (congrArg (fun Q : Subgroup G => Q.subgroupOf K) hP)
  let T' : Sylow 2 M12 := T.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M12 T' commonSylow
  let f : K ≃* M12 := e.trans (MulAut.conj g)
  have hfS : (S.subgroupOf K).map f.toMonoidHom = sylowCandidate := by
    rw [← hT']
    have he := congrArg (fun Q : Sylow 2 M12 => (Q : Subgroup M12)) hg
    change ((T : Subgroup K).map e.toMonoidHom).map (MulAut.conj g).toMonoidHom = sylowCandidate at he
    rw [map_map] at he
    exact he
  refine ⟨f, hfS, ?_⟩
  have hVK := plane_le_component c
  let : IsElementaryAbelian 2 V := c.plane_elementary
  let : IsElementaryAbelian 2 (V.subgroupOf K) := IsElementaryAbelian.subgroupOf hVK
  let : IsElementaryAbelian 2 ((V.subgroupOf K).map f.toMonoidHom) :=
    IsElementaryAbelian.map f.toMonoidHom
  apply normal_four_eq_natural
  · rw [card_map_of_injective f.injective,
      Nat.card_congr (subgroupOfEquivOfLe hVK).toEquiv, c.plane_card]
  · rw [← hfS]
    exact map_mono (fun _ hx => c.plane_le_sylow hx)
  · have hn : S ≤ normalizer (V : Set G) := c.sylow_le_local.trans
      ((normal_subgroupOf_iff_le_normalizer c.plane_le_local).mp c.plane_normal)
    have hnK : S.subgroupOf K ≤ normalizer (V.subgroupOf K : Set K) := by
      rw [← subgroupOf_normalizer_eq hVK]
      exact fun _ hx => hn hx
    rw [← hfS]
    exact (map_mono hnK).trans ((V.subgroupOf K).le_normalizer_map f.toMonoidHom)

omit [Finite G] in
private theorem residual_not_le_sylow (c : LocalConfiguration K S M Y V) : ¬ Y ≤ S := by
  intro hYS
  obtain ⟨P, hP⟩ := c.sylow
  have hpS : IsPGroup 2 S := hP ▸ P.isPGroup'
  have hbot : primePowerGenerated 3 M = ⊥ := by
    apply eq_bot_iff.mpr
    rw [primePowerGenerated_le_iff]
    intro x n hx
    have hxY : (x : G) ∈ Y := by
      rw [c.residual]
      exact ⟨x, mem_primePowerGenerated_of_pow hx, rfl⟩
    let s : S := ⟨x, hYS hxY⟩
    have hs : s ^ (3 ^ n) = 1 := Subtype.ext (congrArg (fun a : M => (a : G)) hx)
    have he : s = 1 := (hpS.powEquiv ((by decide : Nat.Coprime 2 3).pow_right n)).injective
      (hs.trans (one_pow _).symm)
    exact Subtype.ext (congrArg (fun a : S => (a : G)) he)
  have hY : Y = ⊥ := by rw [c.residual, threeResidualIn, hbot, Subgroup.map_bot]
  have hV : V = ⊥ := by simpa only [hY, commutator_bot_right] using c.plane_commutator.symm
  have := Subgroup.card_eq_one.mpr hV
  have := c.plane_card
  omega

/-- The same marking identifies the inner part of the local overgroup with the natural-four parabolic. -/
theorem exists_local_marking (c : LocalConfiguration K S M Y V) (e : K ≃* M12) :
    ∃ f : K ≃* M12,
      (S.subgroupOf K).map f.toMonoidHom = sylowCandidate ∧
      (V.subgroupOf K).map f.toMonoidHom = natural ∧
      (M.subgroupOf K).map f.toMonoidHom = secondParabolic := by
  obtain ⟨f, hS, hV⟩ := exists_plane_marking c e
  refine ⟨f, hS, hV, ?_⟩
  let H := (M.subgroupOf K).map f.toMonoidHom
  have hSH : sylowCandidate ≤ H := by
    rw [← hS]
    exact map_mono (fun _ hx => c.sylow_le_local hx)
  have hHP : H ≤ secondParabolic := by
    change H ≤ normalizer (natural : Set M12)
    rw [← hV]
    apply le_trans (map_mono ?_) ((V.subgroupOf K).le_normalizer_map f.toMonoidHom)
    rw [← subgroupOf_normalizer_eq (plane_le_component c)]
    exact fun _ hx => ((normal_subgroupOf_iff_le_normalizer c.plane_le_local).mp c.plane_normal) hx
  have hne : H ≠ sylowCandidate := by
    intro he
    apply residual_not_le_sylow c
    intro y hy
    let k : K := ⟨y, c.y_le_component hy⟩
    have hkM : k ∈ M.subgroupOf K := by
      have hYM : Y ≤ M := by rw [c.residual]; exact map_subtype_le _
      exact hYM hy
    have hm : f k ∈ H := mem_map_of_mem f.toMonoidHom hkM
    rw [he, ← hS] at hm
    obtain ⟨a, ha, hea⟩ := hm
    have : a = k := f.injective hea
    change k ∈ S.subgroupOf K
    exact this ▸ ha
  have hd64 : 64 ∣ Nat.card H := card_sylowCandidate ▸ card_dvd_of_le hSH
  have hd192 : Nat.card H ∣ 192 := card_secondParabolic ▸ card_dvd_of_le hHP
  obtain ⟨a, ha⟩ := hd64
  have hd : a ∣ 3 := Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < 64) (by
    simpa only [ha] using hd192)
  rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h
  · have hc : Nat.card H = 64 := by rw [ha, h, mul_one]
    exact (hne (eq_of_le_of_card_ge hSH (by rw [hc, card_sylowCandidate])).symm).elim
  · exact eq_of_le_of_card_ge hHP (by rw [ha, h, card_secondParabolic])

omit [Finite G] in
/-- The marked three-residual is contained in the transported source residual. -/
theorem marked_residual_le (c : LocalConfiguration K S M Y V)
    (f : K ≃* M12) (hM : (M.subgroupOf K).map f.toMonoidHom = secondParabolic) :
    threeResidualIn secondParabolic ≤ (Y.subgroupOf K).map f.toMonoidHom := by
  rw [threeResidualIn, map_primePowerGenerated_subtype]
  apply (closure_le _).mpr
  rintro x ⟨hx, n, hp⟩
  rw [← hM] at hx
  obtain ⟨k, hk, rfl⟩ := hx
  refine ⟨k, ?_, rfl⟩
  change f k ^ (3 ^ n) = 1 at hp
  have hpK : k ^ (3 ^ n) = 1 := f.injective (by simpa only [map_pow, map_one] using hp)
  change (k : G) ∈ Y
  rw [c.residual]
  exact ⟨⟨k, hk⟩, mem_primePowerGenerated_of_pow
    (Subtype.ext (congrArg (fun a : K => (a : G)) hpK)), rfl⟩

end CFSG.Quasithin.Chapter15.Section03.RankOne.SporadicModels.MathieuTwelve
