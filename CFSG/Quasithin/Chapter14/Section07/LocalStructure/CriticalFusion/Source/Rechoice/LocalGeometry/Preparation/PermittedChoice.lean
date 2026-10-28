module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.Preparation.Sections
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.Preparation.PermittedChoice.ActorOrbits
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.Basic
public import Theory.GroupTheory.DisjointConjugateCenter
public import Theory.Representation.FirstCohomologyDuality.SimpleCover

/-!
# Construction and centrality of one permitted critical rechoice

The literal point centralizer normalizes the conjugate Uα. If T fixes the
point modulo V₁ and O₂(H) moves it, the point-displacement homomorphism
T → V₁ allows adjustment by O₂(H), proving C_T(Zα)* = T*. The order-two
image of Uα is therefore central in T*.

The nontrivial commutator is proved from the full earlier [U,O₂(H)]=V₁:
the core centralizer is a proper invariant subspace of the original central
cover, hence lies in the same natural projection's kernel U₀/V₁. Earlier
14.7.68 excludes Zα≤U₀. This also proves the exact [Zα,O₂(H)]=V₁; it does
not extend 14.7.4(1) from V₂ to arbitrary points without proof.

The opening calculations place Zα in U₀V without marked-cover spanning.
A separate finite two-group argument constructs a central order-two target
inside the actual Q*. F.9.13(6) is transported through the actual rechoice.
The low-rank consumer derives centrality, the actual upper actor and same-p
commutator image, and applies `selected_point_le_plane` to that same path.

The two proved L₁ orbits now construct the permitted element. In low rank,
the orbit of the generator of Zα modulo U₀ supplies careful placement;
`selected_point_of_careful_rechoice` then proves centrality and Zα≤V₂
for that same reselected path. Otherwise, the orbit of the nonidentity
element of Uα* sends the whole order-two subgroup into the constructed
central line. The preliminary bound identifies this latter source branch
with rank three, but its orbit calculation needs no rank restriction.
The exact permitted-choice contract and the stronger selected-point
application are both exported below. The path, earlier images, rank selection
and order-two image are preserved by the existing reselect transports.

Preparation assembly remains qt-14-07-rechoice-preparation. The local cubic
image input retains its earlier14.3/14.7 producers qt-14-03 and qt-14-07.
ModuleSeparation is earlier14.7.2(1), owned by qt-14-07-solvable.
Earlier68/69 retain their producers
qt-14-07-critical-residual-fusion and qt-14-07-critical-order-two. The action
centralization is 14.5.15(4), owned by qt-14-05; the full commutator identity
is 14.5.21(2), owned by qt-14-05-terminal-duality. Compatible marking,
earlier65 and the F.9 implication retain final discharge with qt-14-07.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
14.5.15 and 14.5.21, printed pp.1017–1020; proof of 14.7.70,
printed p.1073 (PDF p.1090), especially the permitted-choice paragraph.
-/

@[expose] public section
noncomputable section

namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.Preparation.PermittedChoice
open Subgroup Representation Chapter12.Section08
open scoped commutatorElement
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
variable (d : Data T L V F W) (c : CriticalPath (L := L) F)

/-- A generator of the actual conjugate of V₁. -/
theorem point_generator : c.Zα = zpowers (c.conjugator⁻¹ * d.z * c.conjugator) := by
  rw [CriticalPath.Zα, d.point, conjugate, MonoidHom.map_zpowers]
  simp

include d in
/-- Pulling back along the critical conjugator recovers H=C_G(z). -/
theorem point_centralizer_le_conjugate_H :
    centralizer (c.Zα : Set G) ≤ conjugate F.H c.conjugator := by
  let e := MulAut.conj c.conjugator⁻¹
  intro x hx
  have hz : e d.z ∈ c.Zα := by
    exact ⟨d.z, by rw [d.point]; exact mem_zpowers _, rfl⟩
  have hxH : e.symm x ∈ F.H := by
    rw [d.centralizer_eq, mem_centralizer_singleton_iff]
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using (hx (e d.z) hz).symm
  exact ⟨e.symm x, hxH, e.apply_symm_apply x⟩

include d in
/-- The actual conjugated centralizer normalizes the actual Uα. -/
theorem point_centralizer_normalizes :
    centralizer (c.Zα : Set G) ≤ normalizer (c.Uα : Set G) :=
  (point_centralizer_le_conjugate_H d c).trans
    ((map_mono d.conjugationSection.normalized).trans (le_normalizer_map _))

omit [Finite G] in
theorem star_Uα_le_T (earlier : c.EarlierImages) :
    star F c.Uα ≤ star F (T : Subgroup G) := by
  have hQT : Q T L ≤ (T : Subgroup G) :=
    (pCoreIn_le_sylow (L ⊔ (T : Subgroup G)) (T.subtype le_sup_right)).trans_eq
      (map_subgroupOf_eq_of_le le_sup_right)
  exact (c.lemma_14_7_66 earlier).1.trans
    (map_mono (subgroupOf_mono F.H hQT))

include d in
/-- Normalization of the order-two image yields quotient centrality. -/
theorem central_of_centralizer_image (earlier : c.EarlierImages)
    (h69 : Nat.card (star F c.Uα) = 2)
    (himage : star F ((T : Subgroup G) ⊓ centralizer (c.Zα : Set G)) =
      star F (T : Subgroup G)) :
    star F c.Uα ≤ Chapter12.Section08.centerIn (star F (T : Subgroup G)) := by
  have hn : star F (T : Subgroup G) ≤ normalizer (star F c.Uα : Set (HStar F.H)) := by
    rw [← himage]
    apply le_normalizer_iff.mpr
    rintro _ ⟨t, ht, rfl⟩ _ ⟨a, ha, rfl⟩
    refine ⟨t * a * t⁻¹, ?_, by simp⟩
    exact (mem_normalizer_iff.mp (point_centralizer_normalizes d c ht.2) a).mp ha
  have hc := centralizes_of_normalizes_card_two h69 hn
  have hcent := le_centralizer_iff.mp hc
  rw [Chapter12.Section08.centerIn_eq_inf_centralizer]
  exact le_inf (star_Uα_le_T c earlier) hcent

/-- The Frattini adjustment, using the literal H/O₂(H) quotient map. -/
theorem centralizer_image_of_core_commutator
    (hZU : c.Zα ≤ F.U) (hfix : tilde d c.Zα ≤ fixedT d)
    (hcomm : ⁅c.Zα, F.H.pCoreIn 2⁆ ≠ ⊥) :
    star F ((T : Subgroup G) ⊓ centralizer (c.Zα : Set G)) =
      star F (T : Subgroup G) := by
  let z := c.conjugator⁻¹ * d.z * c.conjugator
  have hz : z ∈ c.Zα := by rw [point_generator d c]; exact mem_zpowers _
  let zU : F.U := ⟨z, hZU hz⟩
  have hcz : centralizer (c.Zα : Set G) = centralizer ({z} : Set G) := by
    rw [point_generator d c, zpowers_eq_closure, centralizer_closure]
  have hfixed : d.FixedModuloPoint zU := by
    intro t
    have hmem : (d.conjugationSection.coordinates zU).toAdd ∈ tilde d c.Zα :=
      (d.conjugationSection.mem_imageSpace_iff _ _).mpr ⟨zU, hz, rfl⟩
    exact hfix hmem ⟨⟨t, F.invariant 1 t.property⟩, t.property⟩
  let f := d.pointDisplacement (T : Subgroup G) (F.invariant 1) zU hfixed
  have hfk : f.ker = (centralizer ({z} : Set G)).subgroupOf (T : Subgroup G) :=
    d.pointDisplacement_ker _ _ _ _
  have hn : ¬ F.H.pCoreIn 2 ≤ centralizer (c.Zα : Set G) := by
    intro h
    apply hcomm
    rw [commutator_comm]
    exact commutator_eq_bot_iff_le_centralizer.mpr h
  obtain ⟨q, hq, hqn⟩ := SetLike.not_le_iff_exists.mp hn
  rw [hcz] at hqn
  have hQT : F.H.pCoreIn 2 ≤ (T : Subgroup G) :=
    (pCoreIn_le_sylow F.H (T.subtype (F.invariant 1))).trans_eq
      (map_subgroupOf_eq_of_le (F.invariant 1))
  let qT : T := ⟨q, hQT hq⟩
  have hqf : f qT ≠ 1 := by
    intro h
    have hh : qT ∈ f.ker := h
    rw [hfk] at hh
    exact hqn hh
  have hcard : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
  obtain ⟨a, _, ha⟩ := (Nat.card_eq_two_iff' (1 : F.Vi 1)).mp hcard
  have hmatch (t : T) : f t = 1 ∨ f t = f qT := by
    by_cases h : f t = 1
    · exact Or.inl h
    · exact Or.inr ((ha _ h).trans (ha _ hqf).symm)
  have hqstar : starMap F (⟨q, (F.invariant 1) (hQT hq)⟩ : F.H) = 1 := by
    apply (QuotientGroup.eq_one_iff _).mpr
    exact (mem_map_iff_mem F.H.subtype_injective).mp hq
  apply le_antisymm (map_mono (subgroupOf_mono F.H inf_le_left))
  rintro _ ⟨t, ht, rfl⟩
  let tT : T := ⟨t, ht⟩
  have lift (b : T) (hb : f b = 1)
      (he : starMap F ⟨b, F.invariant 1 b.property⟩ = starMap F t) :
      starMap F t ∈ star F ((T : Subgroup G) ⊓ centralizer (c.Zα : Set G)) := by
    refine ⟨⟨b, F.invariant 1 b.property⟩, ⟨b.property, ?_⟩, he⟩
    rw [hcz]
    have hh : b ∈ f.ker := hb
    rw [hfk] at hh
    exact hh
  rcases hmatch tT with h | h
  · exact lift tT h rfl
  · apply lift (qT⁻¹ * tT)
    · rw [map_mul, map_inv, h, inv_mul_cancel]
    · change starMap F ((⟨q, F.invariant 1 (hQT hq)⟩ : F.H)⁻¹ * t) = _
      rw [map_mul, map_inv, hqstar, inv_one, one_mul]

/-- Centrality after the fixed-point and core-commutator steps. -/
theorem low_rank_centrality (earlier : c.EarlierImages)
    (h69 : Nat.card (star F c.Uα) = 2) (hrank : primeRank 2 d.U₀ ≤ 2)
    (hchoice : c.Zα ≤ F.Vi 2 ⊔ d.U₀)
    (hcomm : ⁅c.Zα, F.H.pCoreIn 2⁆ ≠ ⊥) :
    star F c.Uα ≤ Chapter12.Section08.centerIn (star F (T : Subgroup G)) := by
  have hZU : c.Zα ≤ F.U := hchoice.trans
    (sup_le ((F.le_seed 2).trans (Data.V_le_U F)) d.U₀_le_U)
  exact central_of_centralizer_image d c earlier h69
    (centralizer_image_of_core_commutator d c hZU
      (selected_point_fixed d c hrank hchoice) hcomm)

private theorem proper_invariant_le_kernel (s : d.ActionDescent)
    (A : Submodule (ZMod 2) W)
    (hA : ∀ h w, w ∈ A → d.action h w ∈ A) (hne : A ≠ ⊤) :
    A ≤ d.projection.toLinearMap.ker := by
  let p := restrictedProjection d.naturalQuotient s.projection
  have hp : OneCohomology.IsCover p := SL2FourCentralCover.isCover_of_natural_indecomposable p
    d.projection_onto s.kernel_fixed s.indecomposable
  have hi : ∀ g w, w ∈ A →
      s.action (alternatingActor d.naturalQuotient g) w ∈ A := by
    intro g w hw
    obtain ⟨h, hh⟩ := d.qH_surjective (alternatingActor d.naturalQuotient g)
    rw [← hh, s.original]
    exact hA h w hw
  have him : ∀ g v, v ∈ A.map p.toLinearMap →
      SL2FourNatural.naturalRepresentation g v ∈ A.map p.toLinearMap := by
    rintro g _ ⟨w, hw, rfl⟩
    exact ⟨_, hi g w hw, LinearMap.congr_fun (p.isIntertwining' g) w⟩
  have hbot : A.map p.toLinearMap = ⊥ := by
    by_contra hn
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hn
    have ht : A.map p.toLinearMap = ⊤ := by
      apply top_unique
      intro w _
      by_cases hw : w = 0
      · exact hw ▸ (A.map p.toLinearMap).zero_mem
      obtain ⟨g, hg⟩ := SL2FourNatural.transitive_nonzero v w hv0 hw
      exact hg ▸ him g v hv
    exact hne (OneCohomology.invariant_eq_top_of_cover_image_eq_top p hp A hi ht)
  intro w hw
  have : p w ∈ A.map p.toLinearMap := ⟨w, hw, rfl⟩
  rw [hbot] at this
  exact this

/-- The full earlier identity 14.5.21(2), together with the original central
cover, places the literal core centralizer in U₀. -/
theorem core_centralizer_le_U₀ (s : d.ActionDescent)
    (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1) :
    F.U ⊓ centralizer (F.H.pCoreIn 2 : Set G) ≤ d.U₀ := by
  let C := F.U ⊓ centralizer (F.H.pCoreIn 2 : Set G)
  have hpoint : F.Vi 1 ≤ C := le_inf d.conjugationSection.kernel_le
    ((le_centralizer_iff.mp d.H_centralizes_point).trans (centralizer_le (pCoreIn_le 2 F.H)))
  have hQN : F.H ≤ normalizer (F.H.pCoreIn 2 : Set G) := by
    simpa only [pCoreIn, normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype]
      using (pCore 2 F.H).le_normalizer_map F.H.subtype
  have hCN := hQN.trans (normalizer_le_normalizer_centralizer (F.H.pCoreIn 2))
  have hker : tilde d C ≤ d.projection.toLinearMap.ker := by
    apply proper_invariant_le_kernel d s
    · intro h w hw
      obtain ⟨v, hv, rfl⟩ := (d.conjugationSection.mem_imageSpace_iff C w).mp hw
      let v' : F.U := ⟨h * v * (h : G)⁻¹,
        (mem_normalizer_iff.mp (d.conjugationSection.normalized h.property) v).mp v.property⟩
      apply (d.conjugationSection.mem_imageSpace_iff C _).mpr
      refine ⟨v', ⟨v'.property, ?_⟩, d.conjugationSection.equivariant h v⟩
      exact (mem_normalizer_iff.mp (hCN h.property) v).mp hv.2
    · intro ht
      have hu : F.U ≤ C := (tilde_le_iff d le_rfl inf_le_left hpoint).mp
        (ht ▸ le_top)
      have hb : F.Vi 1 = ⊥ := hcomm.symm.trans
        (commutator_eq_bot_iff_le_centralizer.mpr (hu.trans inf_le_right))
      have hh : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
      rw [hb, Subgroup.card_bot] at hh
      omega
  intro v hv
  exact (d.mem_U₀ ⟨v, hv.1⟩).mpr (hker
    ((d.conjugationSection.mem_imageSpace_iff C _).mpr ⟨⟨v, hv.1⟩, hv, rfl⟩))

/-- Nontriviality is deduced using 14.5.21(2) and 14.7.68. In particular,
14.7.4(1) is not applied to an arbitrary point of V₂U₀. -/
theorem point_core_commutator_ne_bot (s : d.ActionDescent)
    (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1)
    (h69 : Nat.card (star F c.Uα) = 2)
    (h68 : {x : G | IsConj d.z x} ∩ (d.U₀ : Set G) = {d.z})
    (hZU : c.Zα ≤ F.U) : ⁅c.Zα, F.H.pCoreIn 2⁆ ≠ ⊥ := by
  intro hzero
  exact point_not_le_U₀ d c h69 h68
    ((le_inf hZU (commutator_eq_bot_iff_le_centralizer.mp hzero)).trans
      (core_centralizer_le_U₀ d s hcomm))

/-- The exact commutator assertion used in the source Frattini argument. -/
theorem point_core_commutator_eq (s : d.ActionDescent)
    (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1)
    (h69 : Nat.card (star F c.Uα) = 2)
    (h68 : {x : G | IsConj d.z x} ∩ (d.U₀ : Set G) = {d.z})
    (hZU : c.Zα ≤ F.U) : ⁅c.Zα, F.H.pCoreIn 2⁆ = F.Vi 1 := by
  have hne := point_core_commutator_ne_bot d c s hcomm h69 h68 hZU
  apply eq_of_le_of_card_ge ((commutator_mono hZU le_rfl).trans_eq hcomm)
  have htwo : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
  rw [htwo]
  by_contra hn
  exact hne (eq_bot_of_card_le _ (by omega))

/-- The opening calculations put the original point in U₀V. No marked-cover
spanning or disjointness result is needed for this containment. -/
theorem opening_point_le_product (earlier : c.EarlierImages) (selection : c.RankSelection)
    (h69 : Nat.card (star F c.Uα) = 2)
    (hcore : ∀ h : F.H, h ∈ pCore 2 F.H → d.action h = 1)
    (mark : UpperMarking d)
    (h65 : SL2CentralExtension.upperFixed
      ((d.actionDescentOfCore hcore).action.comp (alternatingActor d.naturalQuotient)) =
        tilde d V ⊔ d.projection.toLinearMap.ker)
    (hF9 : ⁅F.U ⊓ c.Qα, c.Uα⁆ ≤ c.Zα) : c.Zα ≤ d.U₀ ⊔ V := by
  let s := d.actionDescentOfCore hcore
  obtain ⟨h, hh, t, ht, he⟩ := exists_upper_actor d c earlier mark h69
  have hF := commutator_image d c earlier s h69 h hh (upper_actor_ne_one d h t ht he)
  have hZ := (original_point_in_commutator d c earlier s mark selection h69 hF9).2
  exact hZ.trans (le_sup_left.trans_eq (commutator_sup_U₀ d c earlier s h t ht he hF h65))

/-- Once the low-rank orbit step has chosen the point, all subsequent
centrality is proved from literal earlier inputs. -/
theorem low_rank_centrality_from_earlier (earlier : c.EarlierImages)
    (h69 : Nat.card (star F c.Uα) = 2)
    (hcore : ∀ h : F.H, h ∈ pCore 2 F.H → d.action h = 1)
    (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1)
    (h68 : {x : G | IsConj d.z x} ∩ (d.U₀ : Set G) = {d.z})
    (hrank : primeRank 2 d.U₀ ≤ 2) (hchoice : c.Zα ≤ F.Vi 2 ⊔ d.U₀) :
    star F c.Uα ≤ Chapter12.Section08.centerIn (star F (T : Subgroup G)) := by
  exact low_rank_centrality d c earlier h69 hrank hchoice
    (point_core_commutator_ne_bot d c (d.actionDescentOfCore hcore) hcomm h69 h68
      (hchoice.trans (sup_le ((F.le_seed 2).trans (Data.V_le_U F)) d.U₀_le_U)))


include d in
/-- F.9.13(6) is preserved by the permitted rechoice, using the actual Qα
transport and the fact that this actor normalizes U. -/
theorem reselect_F9 (n : group F L) (hF9 : ⁅F.U ⊓ c.Qα, c.Uα⁆ ≤ c.Zα) :
    ⁅F.U ⊓ (c.reselect n).Qα, (c.reselect n).Uα⁆ ≤ (c.reselect n).Zα := by
  have hU : conjugate F.U n = F.U := (conjugate_eq_iff F.U n).mpr
    (d.conjugationSection.normalized (group_le_H n.property))
  have hD : F.U ⊓ (c.reselect n).Qα = conjugate (F.U ⊓ c.Qα) n := by
    have hm : conjugate (F.U ⊓ c.Qα) n = conjugate F.U n ⊓ conjugate c.Qα n :=
      map_inf _ _ _ (MulAut.conj (n : G)⁻¹).injective
    rw [reselect_Qα, hm, hU]
  rw [hD, c.reselect_Uα, c.reselect_Zα]
  simpa only [conjugate, map_commutator] using
    (map_mono (f := (MulAut.conj (n : G)⁻¹).toMonoidHom) hF9)

omit [Finite G] in
private theorem core_le_T : Q T L ≤ (T : Subgroup G) :=
  (pCoreIn_le_sylow (L ⊔ (T : Subgroup G)) (T.subtype le_sup_right)).trans_eq
    (map_subgroupOf_eq_of_le le_sup_right)

/-- A central target of order two exists in the actual Q*. The high-rank
construction below conjugates the original Uα* to this target by L₁. -/
theorem exists_central_line (earlier : c.EarlierImages)
    (h69 : Nat.card (star F c.Uα) = 2) :
    ∃ Z : Subgroup (HStar F.H), Z ≤ star F (Q T L) ∧ Nat.card Z = 2 ∧
      Z ≤ Chapter12.Section08.centerIn (star F (T : Subgroup G)) := by
  let P := star F (T : Subgroup G)
  let N := star F (Q T L)
  have hNP : N ≤ P := map_mono (subgroupOf_mono F.H core_le_T)
  have hnQ : L ⊔ (T : Subgroup G) ≤ normalizer (Q T L : Set G) := by
    simpa only [Q, pCoreIn, normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype]
      using (pCore 2 ↥(L ⊔ (T : Subgroup G))).le_normalizer_map
        (L ⊔ (T : Subgroup G)).subtype
  have hn : P ≤ normalizer (N : Set (HStar F.H)) := by
    apply le_normalizer_iff.mpr
    rintro _ ⟨t, ht, rfl⟩ _ ⟨a, ha, rfl⟩
    refine ⟨t * a * t⁻¹, ?_, by simp⟩
    exact (mem_normalizer_iff.mp (hnQ ((le_sup_right : (T : Subgroup G) ≤ L ⊔ (T : Subgroup G)) ht)) a).mp ha
  let : (N.subgroupOf P).Normal := (normal_subgroupOf_iff_le_normalizer hNP).mpr hn
  let : Fact (IsPGroup 2 P) := ⟨T.isPGroup'.comap_subtype.map (starMap F)⟩
  have hcN : 2 ≤ Nat.card N :=
    h69.symm.trans_le (card_le_of_le (c.lemma_14_7_66 earlier).1)
  have hcNP : Nat.card (N.subgroupOf P) = Nat.card N :=
    Nat.card_congr (subgroupOfEquivOfLe hNP).toEquiv
  have hnt : Nontrivial (N.subgroupOf P) :=
    Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨Z, _, hZN, hZc, hZcenter⟩ :=
    exists_central_subgroup_card_eq_prime_in_normal (p := 2) (N.subgroupOf P) hnt
  refine ⟨Z.map P.subtype,
    (map_mono hZN).trans_eq (map_subgroupOf_eq_of_le hNP), ?_, map_mono hZcenter⟩
  exact (card_map_of_injective P.subtype_injective).trans hZc

/-- Apply the published fixed-line calculation to the same reselected path.
From careful placement, derive the commutator, centralizer image, quotient
centrality, actual actor and same-p displacement. The construction below
supplies this placement using the actual L₁ orbit. -/
theorem selected_point_of_careful_rechoice
    (earlier : c.EarlierImages) (selection : c.RankSelection)
    (h69 : Nat.card (star F c.Uα) = 2) (separation : d.ModuleSeparation)
    (hcore : ∀ h : F.H, h ∈ pCore 2 F.H → d.action h = 1)
    (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1)
    (h68 : {x : G | IsConj d.z x} ∩ (d.U₀ : Set G) = {d.z})
    (mark : UpperMarking d)
    (h65 : SL2CentralExtension.upperFixed
      ((d.actionDescentOfCore hcore).action.comp (alternatingActor d.naturalQuotient)) =
        tilde d V ⊔ d.projection.toLinearMap.ker)
    (n : group F L) (hrank : primeRank 2 d.U₀ ≤ 2)
    (hF9 : ⁅F.U ⊓ c.Qα, c.Uα⁆ ≤ c.Zα)
    (hchoice : (c.reselect n).Zα ≤ F.Vi 2 ⊔ d.U₀) :
    star F (c.reselect n).Uα ≤ Chapter12.Section08.centerIn (star F (T : Subgroup G)) ∧
      (c.reselect n).Zα ≤ F.Vi 2 := by
  let s := d.actionDescentOfCore hcore
  have earlier' := c.reselect_earlierImages earlier n
  have selection' := reselect_rankSelection d c earlier selection n
  have h69' : Nat.card (star F (c.reselect n).Uα) = 2 :=
    (c.reselect_star_card earlier n).trans h69
  have hcentral := low_rank_centrality_from_earlier d (c.reselect n) earlier'
    h69' hcore hcomm h68 hrank hchoice
  refine ⟨hcentral, ?_⟩
  obtain ⟨h, hh, t, ht, he⟩ := exists_upper_actor d (c.reselect n) earlier' mark h69'
  have hZ := (original_point_in_commutator d (c.reselect n) earlier' s mark
    selection' h69' (reselect_F9 d c n hF9)).2
  exact selected_point_le_plane d (c.reselect n) earlier' separation s h t ht he
    (actorT_commutes d (c.reselect n) hcentral h hh)
    (commutator_image d (c.reselect n) earlier' s h69' h hh (upper_actor_ne_one d h t ht he))
    h65 (upper_mem_actorT d mark) hrank hZ hchoice

/-- The actual L₁ orbit supplies the careful point placement. -/
theorem exists_careful_rechoice (earlier : c.EarlierImages) (selection : c.RankSelection)
    (h69 : Nat.card (star F c.Uα) = 2) (separation : d.ModuleSeparation)
    (cubic : ActorOrbits.LocalCubic d)
    (hcore : ∀ h : F.H, h ∈ pCore 2 F.H → d.action h = 1)
    (h68 : {x : G | IsConj d.z x} ∩ (d.U₀ : Set G) = {d.z})
    (mark : UpperMarking d)
    (h65 : SL2CentralExtension.upperFixed
      ((d.actionDescentOfCore hcore).action.comp (alternatingActor d.naturalQuotient)) =
        tilde d V ⊔ d.projection.toLinearMap.ker)
    (hF9 : ⁅F.U ⊓ c.Qα, c.Uα⁆ ≤ c.Zα) :
    ∃ n : group F L, (n : G) ∈ F.Li L 1 ∧ (c.reselect n).Zα ≤ F.Vi 2 ⊔ d.U₀ := by
  let x := c.conjugator⁻¹ * d.z * c.conjugator
  have hx : x ∈ c.Zα := by rw [point_generator d c]; exact mem_zpowers _
  have hZ := opening_point_le_product d c earlier selection h69 hcore mark h65 hF9
  have hxU : x ∈ F.U :=
    (sup_le d.U₀_le_U (Data.V_le_U F)) (hZ hx)
  have hx0 : x ∉ d.U₀ := by
    intro h
    apply point_not_le_U₀ d c h69 h68
    rw [point_generator d c]
    exact zpowers_le.mpr h
  obtain ⟨l, hl, hplace⟩ := ActorOrbits.exists_conjugate_in_plane_product d cubic
    hcore h65 separation ⟨x, hxU⟩ (hZ hx) hx0
  let n : group F L := ⟨l, (le_sup_left : F.Li L 1 ≤ group F L) hl⟩
  refine ⟨n, hl, ?_⟩
  rw [c.reselect_Zα, point_generator d c, conjugate, MonoidHom.map_zpowers]
  apply zpowers_le.mpr
  change (l : G)⁻¹ * x * ((l : G)⁻¹)⁻¹ ∈ F.Vi 2 ⊔ d.U₀
  simpa only [inv_inv, sup_comm d.U₀] using hplace

/-- The actual L₁ conjugacy orbit sends the order-two image to a central
line in Q*. This supplies the source choice in the rank-three case. -/
theorem exists_central_rechoice (earlier : c.EarlierImages)
    (h69 : Nat.card (star F c.Uα) = 2)
    (cubic : ActorOrbits.LocalCubic d) (mark : UpperMarking d) :
    ∃ n : group F L, (n : G) ∈ F.Li L 1 ∧
      star F (c.reselect n).Uα ≤ Chapter12.Section08.centerIn (star F (T : Subgroup G)) := by
  obtain ⟨Z, hZQ, hZcard, hZcenter⟩ := exists_central_line c earlier h69
  obtain ⟨x, hx1, hxuniq⟩ := (Nat.card_eq_two_iff' (1 : star F c.Uα)).mp h69
  obtain ⟨y, hy1, _⟩ := (Nat.card_eq_two_iff' (1 : Z)).mp hZcard
  have hxne : (x : HStar F.H) ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hyne : (y : HStar F.H) ≠ 1 := fun h => hy1 (Subtype.ext h)
  obtain ⟨l, hl, hxy⟩ := ActorOrbits.exists_star_conjugate d cubic mark earlier.image_eq
    x y ((c.lemma_14_7_66 earlier).1 x.property) (hZQ y.property) hxne hyne
  let n : group F L := ⟨l, (le_sup_left : F.Li L 1 ≤ group F L) hl⟩
  refine ⟨n, hl, ?_⟩
  rw [c.reselect_star earlier n]
  apply le_trans _ hZcenter
  rintro _ ⟨a, ha, rfl⟩
  by_cases ha1 : a = 1
  · subst a
    simpa only [map_one] using Z.one_mem
  · have hae : a = x := congrArg Subtype.val (hxuniq ⟨a, ha⟩
      (fun h => ha1 (congrArg Subtype.val h)))
    change (starMap F l)⁻¹ * a * ((starMap F l)⁻¹)⁻¹ ∈ Z
    rw [inv_inv, hae, hxy]
    exact y.property

/-- One permitted rechoice gives centrality in both rank cases. In low
rank, the published fixed-line theorem applies to this very same path. -/
theorem exists_permitted_rechoice_with_selected_point
    (earlier : c.EarlierImages) (selection : c.RankSelection)
    (h69 : Nat.card (star F c.Uα) = 2) (separation : d.ModuleSeparation)
    (cubic : ActorOrbits.LocalCubic d)
    (hcore : ∀ h : F.H, h ∈ pCore 2 F.H → d.action h = 1)
    (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1)
    (h68 : {x : G | IsConj d.z x} ∩ (d.U₀ : Set G) = {d.z})
    (mark : UpperMarking d)
    (h65 : SL2CentralExtension.upperFixed
      ((d.actionDescentOfCore hcore).action.comp (alternatingActor d.naturalQuotient)) =
        tilde d V ⊔ d.projection.toLinearMap.ker)
    (hF9 : ⁅F.U ⊓ c.Qα, c.Uα⁆ ≤ c.Zα) :
    ∃ n : group F L, (n : G) ∈ F.Li L 1 ∧
      star F (c.reselect n).Uα ≤ Chapter12.Section08.centerIn (star F (T : Subgroup G)) ∧
      (primeRank 2 d.U₀ ≤ 2 → (c.reselect n).Zα ≤ F.Vi 2) := by
  by_cases hrank : primeRank 2 d.U₀ ≤ 2
  · obtain ⟨n, hn, hchoice⟩ := exists_careful_rechoice d c earlier selection h69
      separation cubic hcore h68 mark h65 hF9
    obtain ⟨hcentral, hplane⟩ := selected_point_of_careful_rechoice d c earlier selection
      h69 separation hcore hcomm h68 mark h65 n hrank hF9 hchoice
    exact ⟨n, hn, hcentral, fun _ => hplane⟩
  · obtain ⟨n, hn, hcentral⟩ := exists_central_rechoice d c earlier h69 cubic mark
    exact ⟨n, hn, hcentral, fun h => (hrank h).elim⟩

/-- The exact permitted-choice contract consumed by preparation assembly.
No choice or centrality conclusion is an input. -/
theorem exists_permitted_rechoice
    (earlier : c.EarlierImages) (selection : c.RankSelection)
    (h69 : Nat.card (star F c.Uα) = 2) (separation : d.ModuleSeparation)
    (cubic : ActorOrbits.LocalCubic d)
    (hcore : ∀ h : F.H, h ∈ pCore 2 F.H → d.action h = 1)
    (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1)
    (h68 : {x : G | IsConj d.z x} ∩ (d.U₀ : Set G) = {d.z})
    (mark : UpperMarking d)
    (h65 : SL2CentralExtension.upperFixed
      ((d.actionDescentOfCore hcore).action.comp (alternatingActor d.naturalQuotient)) =
        tilde d V ⊔ d.projection.toLinearMap.ker)
    (hF9 : ⁅F.U ⊓ c.Qα, c.Uα⁆ ≤ c.Zα) :
    ∃ n : group F L,
      star F (c.reselect n).Uα ≤ Chapter12.Section08.centerIn (star F (T : Subgroup G)) ∧
      (primeRank 2 d.U₀ ≤ 2 → (c.reselect n).Zα ≤ F.Vi 2 ⊔ d.U₀) := by
  obtain ⟨n, _, hcentral, hplane⟩ := exists_permitted_rechoice_with_selected_point d c
    earlier selection h69 separation cubic hcore hcomm h68 mark h65 hF9
  exact ⟨n, hcentral, fun h => (hplane h).trans le_sup_left⟩


end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.Preparation.PermittedChoice
