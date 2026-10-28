module

public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.FullElementaryEight.Coordinates
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.ElementaryCentralizer

/-!
# Elementary eights in the full binary G₂ first parabolic

The five-root core and its six-element Levi complement give coordinates for
the full first parabolic. An elementary subgroup normal in this parabolic
lies in the core; commuting with its cubic conjugate then forces every element
into the central involution subgroup. Every element outside the common Sylow
commutes with at most four involutions in that Sylow, so a self-centralizing
elementary eight stays self-centralizing in the first parabolic.

These are the full-group elementary-eight facts used in Aschbacher--Smith,
Lemma 14.2.22, following the model calculation in Lemma 14.2.21, printed p.988
of the combined 1 March 2004 manuscript. Coordinates come from the licensed
ATLAS port; see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public section

namespace Atlas.G2.BinaryParabolicPair
open Subgroup BinaryCore FullElementaryEight

set_option maxRecDepth 100000 in
private theorem elementary_full_cubic_coordinate : ∀ x : Coordinates,
    x ^ 2 = 1 → x * cubicConjugate x = cubicConjugate x * x →
      x = 1 ∨ x = involution := by
  decide +kernel

/-- A normal elementary subgroup of the full first parabolic is central of
order at most two. -/
theorem elementary_normal_full_first_le (E : Subgroup (Model (ZMod 2)))
    [IsElementaryAbelian 2 E] (hE : E ≤ firstParabolic)
    (hn : firstParabolic ≤ normalizer (E : Set (Model (ZMod 2)))) :
    E ≤ distinguished := by
  have hcore := le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 E) hE hn
  rw [firstParabolic_pCore] at hcore
  intro x hx
  obtain ⟨t, rfl⟩ := hcore hx
  have hs : t ^ 2 = 1 := embedding_injective (by
    rw [map_pow, map_one]
    exact elemPow_eq_one_of_isElementaryAbelian (p := 2) _ hx)
  have hay : cubicActor * embedding t * cubicActor⁻¹ ∈ E :=
    (mem_normalizer_iff.mp (hn cubicActor_mem) _).mp hx
  have hc : t * cubicConjugate t = cubicConjugate t * t := by
    apply embedding_injective
    rw [map_mul, map_mul, ← cubic_conjugate]
    exact congrArg Subtype.val
      ((inferInstance : IsMulCommutative E).is_comm.comm
        ⟨_, hx⟩ ⟨_, hay⟩)
  rcases elementary_full_cubic_coordinate t hs hc with ht | ht
  · rw [ht, map_one]
    exact one_mem _
  · rw [ht, embedding_involution]
    exact mem_zpowers _

/-- No elementary eight in the common Sylow is normalized by the full first
parabolic. -/
theorem elementary_eight_not_normalized_first (E : Subgroup (Model (ZMod 2)))
    [IsElementaryAbelian 2 E] (hE : E ≤ commonSylow) (hcard : Nat.card E = 8) :
    ¬ firstParabolic ≤ normalizer (E : Set (Model (ZMod 2))) := by
  intro hn
  have hb := card_le_of_le
    (elementary_normal_full_first_le E (hE.trans commonSylow_le_first) hn)
  rw [hcard, card_distinguished] at hb
  omega

private theorem first_form {g : Model (ZMod 2)} (hg : g ∈ firstParabolic) :
    ∃ (x : Coordinates) (l : DihedralGroup 3), embedding x * leviHom l = g := by
  rw [firstParabolic_eq_core_sup_levi, ← SetLike.mem_coe,
    coe_mul_of_right_le_normalizer_left core leviHom.range
      (levi_le_first.trans firstParabolic_normalizes_core)] at hg
  obtain ⟨_, ⟨x, rfl⟩, _, ⟨l, rfl⟩, he⟩ := hg
  exact ⟨x, l, he⟩

private theorem form_injective {x y : Coordinates} {l k : DihedralGroup 3}
    (h : embedding x * leviHom l = embedding y * leviHom k) : x = y ∧ l = k := by
  have he : embedding (x⁻¹ * y) = leviHom (l * k⁻¹) := by
    rw [map_mul, map_inv, map_mul, map_inv]
    calc
      _ = (embedding x)⁻¹ * (embedding y * leviHom k) * (leviHom k)⁻¹ := by group
      _ = _ := by rw [← h]; group
  have hc : leviHom (l * k⁻¹) ∈ core := ⟨x⁻¹ * y, he⟩
  have hk : l = k := mul_inv_eq_one.mp ((leviHom_mem_core_iff _).mp hc)
  refine ⟨embedding_injective ?_, hk⟩
  rw [hk] at h
  exact mul_right_cancel h

private theorem cubic_pow_conjugate (n : ℕ) (x : Coordinates) :
    cubicActor ^ n * embedding x * (cubicActor ^ n)⁻¹ =
      embedding ((cubicConjugate^[n]) x) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ']
    calc
      _ = cubicActor * (cubicActor ^ n * embedding x * (cubicActor ^ n)⁻¹) *
          cubicActor⁻¹ := by group
      _ = _ := by rw [ih, cubic_conjugate, Function.iterate_succ_apply']

private theorem levi_conjugate (l : DihedralGroup 3) (x : Coordinates) :
    leviHom l * embedding x * (leviHom l)⁻¹ = embedding (leviAction l x) := by
  cases l with
  | r i => exact cubic_pow_conjugate i.val x
  | sr i =>
    change (shortRoot * cubicActor ^ i.val) * embedding x *
      (shortRoot * cubicActor ^ i.val)⁻¹ = _
    calc
      _ = shortRoot * (cubicActor ^ i.val * embedding x * (cubicActor ^ i.val)⁻¹) *
          shortRoot⁻¹ := by group
      _ = _ := by rw [cubic_pow_conjugate, short_conjugate]; rfl

private theorem form_mul (x y : Coordinates) (l k : DihedralGroup 3) :
    (embedding x * leviHom l) * (embedding y * leviHom k) =
      embedding (x * leviAction l y) * leviHom (l*k) := by
  rw [map_mul, map_mul, ← levi_conjugate]
  group

private theorem sylow_form {g : Model (ZMod 2)} (hg : g ∈ commonSylow) :
    ∃ (x : Coordinates) (b : Bool),
      embedding x * leviHom (if b then .sr 0 else 1) = g := by
  change g ∈ unipotent at hg
  rw [unipotent_eq_core_sup, ← SetLike.mem_coe,
    coe_mul_of_right_le_normalizer_left core (closure {shortRoot})
      ((closure_le _).mpr (by
        rintro y (rfl : y = shortRoot)
        exact shortRoot_normalizes_core))] at hg
  obtain ⟨_, ⟨x, rfl⟩, u, hu, he⟩ := hg
  have hu' : u = 1 ∨ u = shortRoot := by
    have hh : u ∈ closure ({shortRoot} : Set (Model (ZMod 2))) := hu
    obtain ⟨n, hn⟩ := mem_closure_singleton.mp hh
    have hpow : ∀ n : ℤ, shortRoot ^ n = 1 ∨ shortRoot ^ n = shortRoot := by
      intro n
      have hmod := zpow_eq_zpow_emod' n shortRoot_sq
      change shortRoot ^ n = shortRoot ^ (n % 2) at hmod
      have hn0 : n % 2 = 0 ∨ n % 2 = 1 := by omega
      rcases hn0 with hn0 | hn1
      · left; rw [hmod, hn0, zpow_zero]
      · right; rw [hmod, hn1, zpow_one]
    exact hn ▸ hpow n
  rcases hu' with rfl | rfl
  · exact ⟨x, false, by simpa using he⟩
  · exact ⟨x, true, by simpa only [Bool.true_eq, ↓reduceIte, leviHom_short] using he⟩

private theorem involution_centralizer_bound (E : Subgroup (Model (ZMod 2)))
    [IsElementaryAbelian 2 E] (hE : E ≤ commonSylow)
    {g : Model (ZMod 2)} (hg : g ∈ firstParabolic) (hnot : g ∉ commonSylow)
    (hc : g ∈ centralizer (E : Set (Model (ZMod 2)))) : Nat.card E ≤ 4 := by
  classical
  obtain ⟨n, l, rfl⟩ := first_form hg
  have hl1 : l ≠ 1 := by
    intro hl
    apply hnot
    rw [hl, map_one, mul_one]
    exact core_le_unipotent ⟨n, rfl⟩
  have hls : l ≠ .sr 0 := by
    intro hl
    apply hnot
    rw [hl, leviHom_short]
    exact unipotent.mul_mem (core_le_unipotent ⟨n, rfl⟩) shortRoot_mem_unipotent
  choose x b hform using fun e : E => sylow_form (hE e.prop)
  have hmem (e : E) : (x e, b e) ∈ centralizingInvolutions n l := by
    have hsquare := elemPow_eq_one_of_isElementaryAbelian (p := 2) e.val e.prop
    rw [← hform e, pow_two, form_mul] at hsquare
    have hs : x e * leviAction (binaryLevi (b e)) (x e) = 1 := by
      have he : embedding (x e * leviAction (binaryLevi (b e)) (x e)) *
          leviHom (binaryLevi (b e) * binaryLevi (b e)) = embedding 1 * leviHom 1 := by
        simpa only [binaryLevi, map_one, one_mul] using hsquare
      exact (form_injective he).1
    have hcomm := (mem_centralizer_iff.mp hc e e.prop).symm
    rw [← hform e, form_mul, form_mul] at hcomm
    have hm := form_injective hcomm
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs, hm.1, hm.2⟩
  let f : E → ↥(centralizingInvolutions n l) := fun e => ⟨(x e, b e), hmem e⟩
  have hf : Function.Injective f := by
    intro e v he
    have hev : (x e, b e) = (x v, b v) := congrArg Subtype.val he
    apply Subtype.ext
    rw [← hform e, ← hform v, (Prod.mk.inj hev).1, (Prod.mk.inj hev).2]
  have hb := Nat.card_le_card_of_injective f hf
  rw [Nat.card_eq_fintype_card (α := ↥(centralizingInvolutions n l)),
    Fintype.card_coe] at hb
  exact hb.trans (centralizingInvolutions_card n l hl1 hls)

/-- An elementary eight self-centralizing in the common Sylow is also
self-centralizing in the full first parabolic. -/
theorem elementary_eight_centralizer_first (E : Subgroup (Model (ZMod 2)))
    [IsElementaryAbelian 2 E] (hE : E ≤ commonSylow) (hcard : Nat.card E = 8)
    (hself : (commonSylow : Subgroup (Model (ZMod 2))) ⊓
      centralizer (E : Set (Model (ZMod 2))) ≤ E) :
    firstParabolic ⊓ centralizer (E : Set (Model (ZMod 2))) = E := by
  apply le_antisymm
  · rintro g ⟨hg, hc⟩
    apply hself
    refine ⟨?_, hc⟩
    by_contra hn
    have hb := involution_centralizer_bound E hE hg hn hc
    omega
  · intro e he
    refine ⟨commonSylow_le_first (hE he), ?_⟩
    intro x hx
    exact congrArg Subtype.val
      ((inferInstance : IsMulCommutative E).is_comm.comm ⟨x, hx⟩ ⟨e, he⟩)

/-- The literal marked elementary eight is self-centralizing in the full
first parabolic. This applies the general bound to the root-defined subgroup. -/
theorem marked_elementary_centralizer_first :
    firstParabolic ⊓ centralizer (elementary : Set (Model (ZMod 2))) = elementary := by
  apply elementary_eight_centralizer_first elementary
    (elementary_le_core.trans core_le_unipotent) card_elementary
  exact unipotent_centralizer_elementary.le

end Atlas.G2.BinaryParabolicPair
