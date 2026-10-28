module
public import Theory.GroupTheory.GeneralizedFitting.ComponentSwapNormSylow
public import Theory.GroupTheory.DisjointCommutingProduct
public import Mathlib.Tactic.Group
/-!
# Central lifts in a two-component Sylow orbit

A centerless component with normalizer of index two has two commuting
Sylow conjugates. A central Sylow actor induced by an element `t` of the
component Sylow center is induced on the whole orbit by `t * s*t*s⁻¹`.
Uniqueness of inner implementers in the centerless orbit makes this diagonal
lift central in the Sylow subgroup. If the available implementers form a
group of order two and the original marked action is nontrivial, the Sylow
center is the direct product of its order-two orbit factor and its orbit
centralizer factor. The marked actor projects to the nonidentity element
of the first factor.

This is the two-component orbit argument in Aschbacher--Smith 2.5.8(4),
printed pp.556--557. The component normalizer index, Sylow center size, and
innerness of the actual central actions are separate earlier inputs.
-/
public section
open Subgroup
namespace Theory.GroupTheory.TwoComponentCenter
variable {G : Type*} [Group G]

private lemma center_image (S : Subgroup G) :
    (center S).map S.subtype = S ⊓ centralizer (S : Set G) := by
  ext x
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x.property, ?_⟩
    intro y hy
    exact congrArg Subtype.val (mem_center_iff.mp hx (⟨y, hy⟩ : S))
  · intro hx
    exact ⟨⟨x, hx.1⟩, mem_center_iff.mpr (fun y => Subtype.ext (hx.2 y y.property)), rfl⟩

private lemma centerless_of_equiv {X Y : Type*} [Group X] [Group Y]
    (e : X ≃* Y) (hX : center X = ⊥) : center Y = ⊥ := by
  apply eq_bot_iff.mpr
  intro y hy
  have hx : e.symm y ∈ center X := ((centerCongr e).symm ⟨y, hy⟩).property
  have hx1 : e.symm y = 1 := by simpa only [hX, mem_bot] using hx
  apply mem_bot.mpr
  apply e.symm.injective
  simpa using hx1

private lemma pair_centerless {K L : Subgroup G}
    (hK : center K = ⊥) (hL : center L = ⊥)
    (hc : K ≤ centralizer (L : Set G)) :
    (K ⊔ L) ⊓ centralizer ((K ⊔ L : Subgroup G) : Set G) = ⊥ := by
  have hd : Disjoint K L := by
    apply disjoint_def.mpr
    intro x hxK hxL
    have hz : (⟨x, hxK⟩ : K) ∈ center K :=
      mem_center_iff.mpr (fun y => Subtype.ext (hc y.property x hxL).symm)
    have hx1 : (⟨x, hxK⟩ : K) = 1 := by simpa only [hK, mem_bot] using hz
    exact congrArg Subtype.val hx1
  obtain ⟨e, _⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting K L hd hc
  have hp : center (K × L) = ⊥ := by simp [Subgroup.center_prod, hK, hL]
  rw [← center_image, centerless_of_equiv e hp, Subgroup.map_bot]

private lemma centralizer_join {K L : Subgroup G} {x : G}
    (hK : x ∈ centralizer (K : Set G)) (hL : x ∈ centralizer (L : Set G)) :
    x ∈ centralizer ((K ⊔ L : Subgroup G) : Set G) := by
  rw [sup_eq_closure, centralizer_closure]
  intro y hy
  exact hy.elim (hK y) (hL y)

private lemma residual_of_action {K : Subgroup G} {y d : G}
    (ha : ∀ k ∈ K, y * k * y⁻¹ = d * k * d⁻¹) :
    d⁻¹ * y ∈ centralizer (K : Set G) := by
  intro k hk
  have he : (d⁻¹ * y) * k * (d⁻¹ * y)⁻¹ = k := by
    calc
      _ = d⁻¹ * (y * k * y⁻¹) * d := by group
      _ = k := by rw [ha k hk]; group
  exact (mul_inv_eq_iff_eq_mul.mp he).symm

private lemma action_of_residual {K : Subgroup G} {y d : G}
    (hr : d⁻¹ * y ∈ centralizer (K : Set G)) (k : G) (hk : k ∈ K) :
    y * k * y⁻¹ = d * k * d⁻¹ := by
  have hh := hr k hk
  calc
    _ = d * ((d⁻¹ * y) * k) * y⁻¹ := by group
    _ = d * (k * (d⁻¹ * y)) * y⁻¹ := by rw [hh]
    _ = _ := by group

private lemma diagonal_residual {K S : Subgroup G} {s y t : G}
    (hc : K ≤ centralizer (K.map (MulAut.conj s).toMonoidHom : Set G))
    (hs : s ∈ S) (hy : y ∈ centralizer (S : Set G)) (ht : t ∈ K)
    (ha : ∀ k ∈ K, y * k * y⁻¹ = t * k * t⁻¹) :
    (t * (s * t * s⁻¹))⁻¹ * y ∈
      centralizer ((K ⊔ K.map (MulAut.conj s).toMonoidHom : Subgroup G) : Set G) := by
  let L := K.map (MulAut.conj s).toMonoidHom
  let u := s * t * s⁻¹
  let d := t * u
  have hu : u ∈ L := mem_map_of_mem (MulAut.conj s).toMonoidHom ht
  have hys : Commute y s := (hy s hs).symm
  apply centralizer_join
  · apply residual_of_action
    intro k hk
    have huk : u * k * u⁻¹ = k := by
      rw [hc hk u hu, mul_inv_cancel_right]
    calc
      y * k * y⁻¹ = t * k * t⁻¹ := ha k hk
      _ = t * (u * k * u⁻¹) * t⁻¹ := by rw [huk]
      _ = d * k * d⁻¹ := by dsimp [d]; group
  · apply residual_of_action
    rintro k ⟨k, hk, rfl⟩
    have haL : y * (s * k * s⁻¹) * y⁻¹ = u * (s * k * s⁻¹) * u⁻¹ := by
      calc
        _ = s * (y * k * y⁻¹) * s⁻¹ := by
          calc
            _ = (y * s) * k * (s⁻¹ * y⁻¹) := by group
            _ = (s * y) * k * (y⁻¹ * s⁻¹) := by rw [hys.eq, hys.inv_inv.eq.symm]
            _ = _ := by group
        _ = s * (t * k * t⁻¹) * s⁻¹ := by rw [ha k hk]
        _ = _ := by dsimp [u]; group
    have hv : u * (s * k * s⁻¹) * u⁻¹ ∈ L :=
      L.mul_mem (L.mul_mem hu (mem_map_of_mem (MulAut.conj s).toMonoidHom hk)) (L.inv_mem hu)
    have htv : t * (u * (s * k * s⁻¹) * u⁻¹) * t⁻¹ = u * (s * k * s⁻¹) * u⁻¹ := by
      rw [← hc ht _ hv, mul_inv_cancel_right]
    change y * (s * k * s⁻¹) * y⁻¹ = d * (s * k * s⁻¹) * d⁻¹
    rw [haL]
    calc
      _ = t * (u * (s * k * s⁻¹) * u⁻¹) * t⁻¹ := htv.symm
      _ = _ := by dsimp [d]; group

private lemma inner_lift_central {D S : Subgroup G}
    (hfaith : D ⊓ centralizer (D : Set G) = ⊥)
    (hn : S ≤ normalizer (D : Set G)) {y d : G}
    (hy : y ∈ centralizer (S : Set G)) (hd : d ∈ D) (hdS : d ∈ S)
    (hr : d⁻¹ * y ∈ centralizer (D : Set G)) :
    d ∈ S ⊓ centralizer (S : Set G) := by
  refine ⟨hdS, ?_⟩
  intro a ha
  have hda : a * d * a⁻¹ ∈ D := (hn ha d).mp hd
  have he : ∀ k ∈ D,
      (a * d * a⁻¹) * k * (a * d * a⁻¹)⁻¹ = y * k * y⁻¹ := by
    intro k hk
    have hka : a⁻¹ * k * a ∈ D := by simpa using (hn (S.inv_mem ha) k).mp hk
    have hact := action_of_residual hr (a⁻¹ * k * a) hka
    have hay : Commute a y := hy a ha
    calc
      _ = a * (d * (a⁻¹ * k * a) * d⁻¹) * a⁻¹ := by group
      _ = a * (y * (a⁻¹ * k * a) * y⁻¹) * a⁻¹ := by rw [hact]
      _ = y * k * y⁻¹ := by
        calc
          _ = (a * y) * (a⁻¹ * k * a) * (y⁻¹ * a⁻¹) := by group
          _ = (y * a) * (a⁻¹ * k * a) * (a⁻¹ * y⁻¹) := by rw [hay.eq, hay.inv_inv.eq.symm]
          _ = _ := by group
  have hc : d⁻¹ * (a * d * a⁻¹) ∈ centralizer (D : Set G) := by
    apply residual_of_action
    intro k hk
    exact (he k hk).trans (action_of_residual hr k hk)
  have hb : d⁻¹ * (a * d * a⁻¹) = 1 := by
    have hh : d⁻¹ * (a * d * a⁻¹) ∈ D ⊓ centralizer (D : Set G) :=
      ⟨D.mul_mem (D.inv_mem hd) hda, hc⟩
    simpa only [hfaith, mem_bot] using hh
  have hh : a * d * a⁻¹ = d := (inv_mul_eq_one.mp hb).symm
  exact mul_inv_eq_iff_eq_mul.mp hh


/-- The genuine index-two component normalizer gives the two actual Sylow
conjugates, and distinctness makes these factors commute. -/
theorem exists_two_component_orbit [Finite G] (H K : Subgroup G)
    (hKH : K ≤ H) (hK : IsComponent H (K.subgroupOf H)) (S : Sylow 2 H)
    (hi : (normalizer (K.subgroupOf H : Set H)).index = 2) :
    let Y := (S : Subgroup H).map H.subtype
    ∃ s ∈ Y,
      K ≤ centralizer (K.map (MulAut.conj s).toMonoidHom : Set G) ∧
      ∀ a ∈ Y, K.map (MulAut.conj a).toMonoidHom = K ∨
        K.map (MulAut.conj a).toMonoidHom = K.map (MulAut.conj s).toMonoidHom := by
  let B := K.subgroupOf H
  have hs : ¬ (S : Subgroup H) ≤ normalizer (B : Set H) := by
    intro hs
    have hd := index_dvd_of_le hs
    rw [hi] at hd
    exact S.not_dvd_index hd
  obtain ⟨s, hs, hsn⟩ := Set.not_subset.mp hs
  have hm : B.map (MulAut.conj s).toMonoidHom ≠ B :=
    fun h => hsn (mem_normalizer_iff_map_conj_eq.mpr h)
  have hmap (a : H) : (B.map (MulAut.conj a).toMonoidHom).map H.subtype =
      K.map (MulAut.conj (a : G)).toMonoidHom := by
    rw [map_map]
    have he : H.subtype.comp (MulAut.conj a).toMonoidHom =
        (MulAut.conj (a : G)).toMonoidHom.comp H.subtype := by ext x; rfl
    rw [he, ← map_map, map_subgroupOf_eq_of_le hKH]
  refine ⟨s, mem_map_of_mem H.subtype hs, ?_, ?_⟩
  · apply commutator_eq_bot_iff_le_centralizer.mp
    have he := congrArg (Subgroup.map H.subtype)
      (hK.commutator_eq_bot_of_ne (hK.map_conj s) hm.symm)
    rwa [map_commutator, map_subgroupOf_eq_of_le hKH, hmap s, Subgroup.map_bot] at he
  · rintro a ⟨b, hb, rfl⟩
    rcases NormPair.conjugate_eq_or_eq_of_normalizer_index_two hi hm b with h | h
    · left
      have he := congrArg (Subgroup.map H.subtype) h
      rwa [hmap, map_subgroupOf_eq_of_le hKH] at he
    · right
      have he := congrArg (Subgroup.map H.subtype) h
      rwa [hmap, hmap] at he

/-- A centerless two-factor orbit has a central diagonal lift of every central
actor. If the possible inner conjugators form a group of order two, the
Sylow center splits over the orbit centralizer, with the original nontrivial
central actor marking its order-two orbit factor. -/
theorem center_split_of_two_orbit
    (K S T : Subgroup G) (s z : G) (hs : s ∈ S)
    (hK : center K = ⊥)
    (hc : K ≤ centralizer (K.map (MulAut.conj s).toMonoidHom : Set G))
    (horbit : ∀ a ∈ S, K.map (MulAut.conj a).toMonoidHom = K ∨
      K.map (MulAut.conj a).toMonoidHom = K.map (MulAut.conj s).toMonoidHom)
    (hTK : T ≤ K) (hTS : T ≤ S) (hT : Nat.card T = 2)
    (hinner : ∀ y ∈ S ⊓ centralizer (S : Set G), ∃ t ∈ T,
      ∀ k ∈ K, y * k * y⁻¹ = t * k * t⁻¹)
    (hz : z ∈ S ⊓ centralizer (S : Set G))
    (hzK : z ∉ centralizer (K : Set G)) :
    let D := componentOrbit K S
    let Z := (center S).map S.subtype
    Z = (Z ⊓ D) ⊔ (Z ⊓ centralizer (D : Set G)) ∧
    Disjoint (Z ⊓ D) (Z ⊓ centralizer (D : Set G)) ∧
    Nat.card ↥(Z ⊓ D) = 2 ∧
    ∃ d : G, d ≠ 1 ∧ Z ⊓ D = zpowers d ∧
      d⁻¹ * z ∈ Z ⊓ centralizer (D : Set G) := by
  let L := K.map (MulAut.conj s).toMonoidHom
  let D := componentOrbit K S
  let Z := S ⊓ centralizer (S : Set G)
  have hD : D = K ⊔ L := by
    apply le_antisymm
    · apply iSup_le
      intro a
      rcases horbit a a.property with h | h
      · rw [h]; exact le_sup_left
      · rw [h]; exact le_sup_right
    · exact sup_le (le_componentOrbit K S) (le_iSup_of_le (⟨s, hs⟩ : S) le_rfl)
  have hfaith : D ⊓ centralizer (D : Set G) = ⊥ := by
    rw [hD]
    exact pair_centerless hK (centerless_of_equiv ((MulAut.conj s).subgroupMap K) hK) hc
  have hdiag (t : G) (ht : t ∈ T) : t * (s * t * s⁻¹) ∈ D ∧
      t * (s * t * s⁻¹) ∈ S := by
    constructor
    · rw [hD]
      exact mul_mem_sup (hTK ht) (mem_map_of_mem (MulAut.conj s).toMonoidHom (hTK ht))
    · exact S.mul_mem (hTS ht) (S.mul_mem (S.mul_mem hs (hTS ht)) (S.inv_mem hs))
  have hlift (y : G) (hy : y ∈ Z) (t : G) (ht : t ∈ T)
      (ha : ∀ k ∈ K, y * k * y⁻¹ = t * k * t⁻¹) :
      t * (s * t * s⁻¹) ∈ Z ⊓ D ∧
      (t * (s * t * s⁻¹))⁻¹ * y ∈ Z ⊓ centralizer (D : Set G) := by
    have hr : (t * (s * t * s⁻¹))⁻¹ * y ∈ centralizer (D : Set G) := by
      rw [hD]
      exact diagonal_residual hc hs hy.2 (hTK ht) ha
    have hdZ : t * (s * t * s⁻¹) ∈ Z :=
      inner_lift_central hfaith (le_normalizer_componentOrbit K S)
        hy.2 (hdiag t ht).1 (hdiag t ht).2 hr
    exact ⟨⟨hdZ, (hdiag t ht).1⟩, Z.mul_mem (Z.inv_mem hdZ) hy, hr⟩
  obtain ⟨t₀, ht₀, ha₀⟩ := hinner z hz
  let d := t₀ * (s * t₀ * s⁻¹)
  obtain ⟨hd, hr⟩ := hlift z hz t₀ ht₀ ha₀
  have ht₀ne : t₀ ≠ 1 := by
    intro h
    apply hzK
    intro k hk
    have he := ha₀ k hk
    rw [h, one_mul, inv_one, mul_one] at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  have hdne : d ≠ 1 := by
    intro h
    have hr' : d⁻¹ * z ∈ centralizer (D : Set G) := hr.2
    have hzC : z ∈ centralizer (D : Set G) := by simpa only [h, inv_one, one_mul] using hr' 
    exact hzK (centralizer_le (le_componentOrbit K S) hzC)
  have hcases (t : G) (ht : t ∈ T) : t = 1 ∨ t = t₀ := by
    by_cases he : t = 1
    · exact Or.inl he
    · right
      obtain ⟨u, hu, huniq⟩ := (Nat.card_eq_two_iff' (1 : T)).mp hT
      have htu : (⟨t, ht⟩ : T) = u := huniq _ (fun h => he (congrArg Subtype.val h))
      have htu₀ : (⟨t₀, ht₀⟩ : T) = u := huniq _ (fun h => ht₀ne (congrArg Subtype.val h))
      exact congrArg Subtype.val (htu.trans htu₀.symm)
  have hlifts (y : G) (hy : y ∈ Z) :
      ∃ w ∈ Z ⊓ D, (w = 1 ∨ w = d) ∧ w⁻¹ * y ∈ Z ⊓ centralizer (D : Set G) := by
    obtain ⟨t, ht, ha⟩ := hinner y hy
    obtain ⟨hw, hr⟩ := hlift y hy t ht ha
    refine ⟨t * (s * t * s⁻¹), hw, ?_, hr⟩
    rcases hcases t ht with h | h
    · left; simp [h]
    · right; rw [h]
  have hZDcases (x : G) (hx : x ∈ Z ⊓ D) : x = 1 ∨ x = d := by
    obtain ⟨w, hw, hcases, hres⟩ := hlifts x hx.1
    have he : w⁻¹ * x = 1 := by
      have hmem : w⁻¹ * x ∈ D ⊓ centralizer (D : Set G) :=
        ⟨D.mul_mem (D.inv_mem hw.2) hx.2, hres.2⟩
      simpa only [hfaith, mem_bot] using hmem
    have hxw : x = w := (inv_mul_eq_one.mp he).symm
    exact hxw ▸ hcases
  have hsplit : Z = (Z ⊓ D) ⊔ (Z ⊓ centralizer (D : Set G)) := by
    apply le_antisymm
    · intro x hx
      obtain ⟨w, hw, _, hr⟩ := hlifts x hx
      have hh := mul_mem_sup hw hr
      simpa only [mul_inv_cancel_left] using hh
    · exact sup_le inf_le_left inf_le_left
  have hdis : Disjoint (Z ⊓ D) (Z ⊓ centralizer (D : Set G)) := by
    apply disjoint_def.mpr
    intro x hx hy
    have hh : x ∈ D ⊓ centralizer (D : Set G) := ⟨hx.2, hy.2⟩
    simpa only [hfaith, mem_bot] using hh
  have hcard : Nat.card ↥(Z ⊓ D) = 2 := by
    apply (Nat.card_eq_two_iff' (1 : ↥(Z ⊓ D))).mpr
    refine ⟨⟨d, hd⟩, (fun h => hdne (congrArg Subtype.val h)), ?_⟩
    intro x hx
    apply Subtype.ext
    exact (hZDcases x x.property).resolve_left (fun h => hx (Subtype.ext h))
  have hcyclic : Z ⊓ D = zpowers d := by
    apply le_antisymm
    · intro x hx
      rcases hZDcases x hx with h | h
      · rw [h]; exact one_mem _
      · rw [h]; exact mem_zpowers d
    · exact zpowers_le.mpr hd
  simpa only [center_image] using
    (show Z = (Z ⊓ D) ⊔ (Z ⊓ centralizer (D : Set G)) ∧
      Disjoint (Z ⊓ D) (Z ⊓ centralizer (D : Set G)) ∧
      Nat.card ↥(Z ⊓ D) = 2 ∧ ∃ d : G, d ≠ 1 ∧ Z ⊓ D = zpowers d ∧
      d⁻¹ * z ∈ Z ⊓ centralizer (D : Set G) from ⟨hsplit, hdis, hcard, d, hdne, hcyclic, hr⟩)

end Theory.GroupTheory.TwoComponentCenter
